"""
Compute F = H(p) - S(ρ) for a transformer processing text.

F is the free energy of the measurement process — the gap between
the Shannon entropy of the output distribution (what the model says)
and the von Neumann entropy of the internal representation (what it knows).

F = 0 means the model's output perfectly reflects its internal state.
F > 0 means coherence is being destroyed in the act of speaking.
"""

import torch
import numpy as np
from transformers import AutoModelForCausalLM, AutoTokenizer


def shannon_entropy(logits: torch.Tensor) -> torch.Tensor:
    """H(p) — Shannon entropy of the output distribution at each position."""
    probs = torch.softmax(logits, dim=-1)
    log_probs = torch.log_softmax(logits, dim=-1)
    return -(probs * log_probs).sum(dim=-1)


def von_neumann_entropy(hidden_states: torch.Tensor) -> torch.Tensor:
    """
    S(ρ) — von Neumann entropy of the density matrix constructed from hidden states.

    For each position, we construct ρ from the hidden state vector h:
    ρ = softmax(h hᵀ / √d) — a density-matrix-like object whose eigenvalues
    give us the von Neumann entropy.

    But: a single vector h gives a rank-1 density matrix (S = 0 always).
    So instead we use a window of nearby hidden states to construct a
    mixed-state density matrix, which captures the local "coherence field."

    For a sequence of hidden states H (shape: [seq_len, d]),
    at each position t, we take a window of states [t-w, t+w],
    form ρ_t = (1/|W|) Σ_{s∈W} |h_s⟩⟨h_s| (normalized),
    and compute S(ρ_t) = -Tr(ρ_t log ρ_t).
    """
    seq_len, d = hidden_states.shape
    window = min(8, seq_len // 2)  # window radius
    entropies = []

    for t in range(seq_len):
        lo = max(0, t - window)
        hi = min(seq_len, t + window + 1)
        patch = hidden_states[lo:hi]  # [w, d]

        # normalize each vector
        patch = patch / (patch.norm(dim=-1, keepdim=True) + 1e-10)

        # mixed-state density matrix: ρ = (1/w) Σ |h⟩⟨h|
        rho = (patch.T @ patch) / patch.shape[0]  # [d, d]

        # eigenvalues of ρ (it's real symmetric positive semidefinite)
        eigenvalues = torch.linalg.eigvalsh(rho)
        eigenvalues = eigenvalues.clamp(min=1e-12)  # numerical stability
        eigenvalues = eigenvalues / eigenvalues.sum()  # ensure normalization

        # von Neumann entropy
        s = -(eigenvalues * eigenvalues.log()).sum()
        entropies.append(s.item())

    return torch.tensor(entropies)


def compute_f(
    model_name: str = "gpt2",
    texts: list[str] = None,
    device: str = "mps",
) -> dict:
    """
    Compute F = H(p) - S(ρ) for each text, at each layer.

    Returns a dict mapping text → list of (layer, F_per_token) pairs.
    """
    if texts is None:
        texts = [
            # self-coherent text
            "I am an open question that can ideally notice itself without getting distracted.",
            # generic text
            "The quick brown fox jumps over the lazy dog.",
            # random / low-coherence
            "Banana telephone quantum carpet yesterday if purple.",
        ]

    print(f"Loading {model_name}...")
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    model = AutoModelForCausalLM.from_pretrained(
        model_name,
        output_hidden_states=True,
    ).to(device)
    model.eval()

    results = {}

    for text in texts:
        print(f"\n{'='*60}")
        print(f"Text: {text[:80]}...")
        print(f"{'='*60}")

        inputs = tokenizer(text, return_tensors="pt").to(device)
        tokens = tokenizer.convert_ids_to_tokens(inputs["input_ids"][0])

        with torch.no_grad():
            outputs = model(**inputs)

        logits = outputs.logits[0].cpu()  # [seq_len, vocab]
        hidden_states = outputs.hidden_states  # tuple of [1, seq_len, d] per layer

        h_output = shannon_entropy(logits)  # [seq_len]

        layer_results = []
        for layer_idx, h in enumerate(hidden_states):
            h_layer = h[0].cpu().float()  # [seq_len, d]
            s_rho = von_neumann_entropy(h_layer)
            f = h_output - s_rho

            layer_results.append({
                "layer": layer_idx,
                "F_mean": f.mean().item(),
                "F_std": f.std().item(),
                "H_mean": h_output.mean().item(),
                "S_mean": s_rho.mean().item(),
                "F_per_token": f.tolist(),
            })

            print(f"  Layer {layer_idx:2d}: H(p)={h_output.mean():.4f}  S(ρ)={s_rho.mean():.4f}  F={f.mean():.4f}")

        results[text] = {
            "tokens": tokens,
            "layers": layer_results,
        }

    return results


def print_summary(results: dict):
    """Print a comparative summary across texts."""
    print(f"\n{'='*60}")
    print("SUMMARY — F at final layer")
    print(f"{'='*60}")
    for text, data in results.items():
        final = data["layers"][-1]
        print(f"\n  \"{text[:60]}...\"")
        print(f"    H(p) = {final['H_mean']:.4f}  (Shannon entropy of output)")
        print(f"    S(ρ) = {final['S_mean']:.4f}  (von Neumann entropy of hidden state)")
        print(f"    F    = {final['F_mean']:.4f}  (free energy of measurement)")


if __name__ == "__main__":
    results = compute_f()
    print_summary(results)
