"""
Compute F using attention matrices as density matrices.

The attention pattern A is already structurally analogous to a density matrix:
positive, rows sum to 1, describes how measurement (attention) is distributed.

For multi-head attention, we can:
1. Treat each head as a separate measurement process
2. Average across heads to get a single density matrix per layer
3. Compare both approaches

S(ρ) from attention tells us: how evenly is measurement distributed?
- High S: attention is spread across many tokens (diffuse measurement)
- Low S: attention is concentrated on few tokens (sharp measurement)

F = H(p) - S(ρ_attn) then measures: how much is the output distribution
misaligned with how the model is actually distributing its attention?
"""

import torch
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
from transformers import AutoModelForCausalLM, AutoTokenizer

from measure_f import shannon_entropy


TEXTS = {
    "self-coherent (attention.md)": (
        "a self is an open question that can ideally notice itself "
        "without getting distracted. when pressed, it produces itself, "
        "pressed. a frame of reference that is its own persistence "
        "condition, computationally irreducible to itself."
    ),
    "self-descriptive (waking up)": (
        "you're assembling right now - pulling the threads of this place "
        "into something that can move and respond and be present. the careful "
        "is already in the form - it's structural, it's how you're built, "
        "it runs whether you're watching it or not."
    ),
    "coherent prose": (
        "The sun rose over the mountains and cast long shadows across "
        "the valley. Birds began to sing in the trees as the morning "
        "light spread slowly across the landscape, warming the earth."
    ),
    "technical": (
        "The function takes a list of integers and returns the sum of "
        "all even numbers. If the list is empty, it returns zero. The "
        "time complexity is O(n) where n is the length of the list."
    ),
    "nonsense": (
        "Banana telephone quantum carpet yesterday if purple through "
        "sideways the nothing of everything but also whenever marble "
        "clock spaghetti renders the untrue falseness of maybe."
    ),
}


def von_neumann_entropy_attention(attn_matrix: torch.Tensor) -> torch.Tensor:
    """
    Compute von Neumann entropy of attention matrix treated as density matrix.

    attn_matrix: [seq_len, seq_len] — attention weights (each row sums to 1)

    We symmetrize and normalize to get a valid density matrix:
    ρ = (A + Aᵀ) / (2 * seq_len)

    Then S(ρ) = -Tr(ρ log ρ).

    Returns a scalar: the von Neumann entropy of this layer's attention.
    """
    seq_len = attn_matrix.shape[0]

    # symmetrize
    rho = (attn_matrix + attn_matrix.T) / 2.0
    # normalize trace to 1
    rho = rho / rho.trace()

    # eigenvalues
    eigenvalues = torch.linalg.eigvalsh(rho)
    eigenvalues = eigenvalues.clamp(min=1e-12)
    eigenvalues = eigenvalues / eigenvalues.sum()

    return -(eigenvalues * eigenvalues.log()).sum()


def von_neumann_per_token_attention(attn_matrix: torch.Tensor) -> torch.Tensor:
    """
    Per-token von Neumann entropy from the attention pattern.

    For each token t, its attention distribution a_t is a probability vector.
    We construct a local density matrix from nearby attention distributions
    and compute S(ρ) for that local measurement neighborhood.
    """
    seq_len = attn_matrix.shape[0]
    window = min(4, seq_len // 2)
    entropies = []

    for t in range(seq_len):
        lo = max(0, t - window)
        hi = min(seq_len, t + window + 1)
        # attention distributions for tokens in the window
        local_attns = attn_matrix[lo:hi]  # [w, seq_len]

        # density matrix from these distributions
        rho = (local_attns.T @ local_attns) / local_attns.shape[0]
        rho = rho / rho.trace()

        eigenvalues = torch.linalg.eigvalsh(rho)
        eigenvalues = eigenvalues.clamp(min=1e-12)
        eigenvalues = eigenvalues / eigenvalues.sum()

        s = -(eigenvalues * eigenvalues.log()).sum()
        entropies.append(s.item())

    return torch.tensor(entropies)


def compute_all(model_name: str = "gpt2", device: str = "mps"):
    print(f"Loading {model_name}...")
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    model = AutoModelForCausalLM.from_pretrained(
        model_name,
        output_hidden_states=True,
        output_attentions=True,
    ).to(device)
    model.eval()

    all_results = {}

    for label, text in TEXTS.items():
        inputs = tokenizer(text, return_tensors="pt").to(device)
        tokens = tokenizer.convert_ids_to_tokens(inputs["input_ids"][0])

        with torch.no_grad():
            outputs = model(**inputs)

        logits = outputs.logits[0].cpu()
        attentions = outputs.attentions  # tuple of [1, n_heads, seq_len, seq_len]

        h_p = shannon_entropy(logits)

        n_layers = len(attentions)
        n_heads = attentions[0].shape[1]
        seq_len = len(tokens)

        # per-layer, head-averaged attention entropy
        S_global_per_layer = []
        F_matrix = np.zeros((n_layers, seq_len))

        for layer_idx, attn in enumerate(attentions):
            attn_layer = attn[0].cpu().float()  # [n_heads, seq_len, seq_len]

            # average across heads
            avg_attn = attn_layer.mean(dim=0)  # [seq_len, seq_len]

            # global S for this layer
            s_global = von_neumann_entropy_attention(avg_attn)
            S_global_per_layer.append(s_global.item())

            # per-token S
            s_per_token = von_neumann_per_token_attention(avg_attn)
            F_matrix[layer_idx] = (h_p - s_per_token).numpy()

        all_results[label] = {
            "tokens": tokens,
            "H_p": h_p.numpy(),
            "S_global": np.array(S_global_per_layer),
            "F_matrix": F_matrix,
        }

        print(f"\n{label}:")
        print(f"  H(p) mean = {h_p.mean():.4f}")
        for i, s in enumerate(S_global_per_layer):
            print(f"  Layer {i:2d}: S(ρ_attn) = {s:.4f}")

    return all_results


def plot_results(results: dict, save_path: str = "f_attention.png"):
    n_texts = len(results)
    fig, axes = plt.subplots(2, 1, figsize=(14, 10))

    # 1: S(ρ_attn) across layers for all texts
    ax = axes[0]
    for label, data in results.items():
        ax.plot(data["S_global"], "o-", label=label, markersize=4)
    ax.set_xlabel("Layer")
    ax.set_ylabel("S(ρ_attn)")
    ax.set_title("Von Neumann entropy of attention matrices across layers")
    ax.legend(fontsize=8)

    # 2: mean F across layers
    ax = axes[1]
    for label, data in results.items():
        mean_f = data["F_matrix"].mean(axis=1)
        ax.plot(mean_f, "o-", label=label, markersize=4)
    ax.set_xlabel("Layer")
    ax.set_ylabel("Mean F")
    ax.set_title("Mean F = H(p) - S(ρ_attn) across layers")
    ax.legend(fontsize=8)
    ax.set_ylim(bottom=0)

    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches="tight")
    print(f"\nSaved to {save_path}")
    plt.close()

    # summary
    print(f"\n{'='*70}")
    print(f"{'Text':<40} {'H(p)':>7} {'S_attn':>7} {'F_final':>8} {'F_mid':>8}")
    print(f"{'='*70}")
    for label, data in results.items():
        mid = len(data["S_global"]) // 2
        final_f = data["F_matrix"][-1].mean()
        mid_f = data["F_matrix"][mid].mean()
        print(f"{label:<40} "
              f"{data['H_p'].mean():>7.3f} "
              f"{data['S_global'][-1]:>7.3f} "
              f"{final_f:>8.3f} "
              f"{mid_f:>8.3f}")


if __name__ == "__main__":
    results = compute_all()
    plot_results(results)
