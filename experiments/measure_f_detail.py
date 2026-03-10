"""
Detailed F measurement with per-token visualization and layer heatmaps.
"""

import torch
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
from transformers import AutoModelForCausalLM, AutoTokenizer

from measure_f import shannon_entropy, von_neumann_entropy


TEXTS = {
    "self-coherent (from attention.md)": (
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
    "coherent prose (generic)": (
        "The sun rose over the mountains and cast long shadows across "
        "the valley. Birds began to sing in the trees as the morning "
        "light spread slowly across the landscape, warming the earth."
    ),
    "technical (generic)": (
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


def compute_all(model_name: str = "gpt2", device: str = "mps"):
    print(f"Loading {model_name}...")
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    model = AutoModelForCausalLM.from_pretrained(
        model_name, output_hidden_states=True
    ).to(device)
    model.eval()

    all_results = {}

    for label, text in TEXTS.items():
        inputs = tokenizer(text, return_tensors="pt").to(device)
        tokens = tokenizer.convert_ids_to_tokens(inputs["input_ids"][0])

        with torch.no_grad():
            outputs = model(**inputs)

        logits = outputs.logits[0].cpu()
        hidden_states = outputs.hidden_states

        h_p = shannon_entropy(logits)  # [seq_len]

        # compute S(ρ) and F at each layer
        n_layers = len(hidden_states)
        seq_len = len(tokens)
        S_matrix = np.zeros((n_layers, seq_len))
        F_matrix = np.zeros((n_layers, seq_len))

        for layer_idx, hs in enumerate(hidden_states):
            h_layer = hs[0].cpu().float()
            s_rho = von_neumann_entropy(h_layer)
            f = h_p - s_rho

            S_matrix[layer_idx] = s_rho.numpy()
            F_matrix[layer_idx] = f.numpy()

        all_results[label] = {
            "tokens": tokens,
            "H_p": h_p.numpy(),
            "S_matrix": S_matrix,
            "F_matrix": F_matrix,
        }

    return all_results


def plot_results(results: dict, save_path: str = "f_measurement.png"):
    n_texts = len(results)
    fig = plt.figure(figsize=(20, 5 * n_texts + 4))
    gs = GridSpec(n_texts + 1, 3, figure=fig, hspace=0.4, wspace=0.3)

    for i, (label, data) in enumerate(results.items()):
        tokens = [t.replace("Ġ", " ").replace("Ċ", "\\n") for t in data["tokens"]]
        n_layers, seq_len = data["F_matrix"].shape

        # F heatmap (layer × token)
        ax1 = fig.add_subplot(gs[i, 0:2])
        im = ax1.imshow(data["F_matrix"], aspect="auto", cmap="RdYlGn_r",
                        vmin=0, vmax=10)
        ax1.set_ylabel("Layer")
        ax1.set_title(f"F = H(p) - S(ρ)  |  {label}", fontsize=10)
        if seq_len <= 40:
            ax1.set_xticks(range(seq_len))
            ax1.set_xticklabels(tokens, rotation=60, ha="right", fontsize=6)
        plt.colorbar(im, ax=ax1, shrink=0.8)

        # F at final layer per token
        ax2 = fig.add_subplot(gs[i, 2])
        final_f = data["F_matrix"][-1]
        mid_f = data["F_matrix"][len(data["F_matrix"]) // 2]
        x = range(seq_len)
        ax2.plot(x, mid_f, "o-", markersize=3, label=f"mid layer", alpha=0.7)
        ax2.plot(x, final_f, "s-", markersize=3, label=f"final layer", alpha=0.7)
        ax2.set_ylabel("F")
        ax2.set_title("F per token", fontsize=10)
        ax2.legend(fontsize=7)
        ax2.set_ylim(bottom=0)

    # comparison: mean F at each layer for all texts
    ax_comp = fig.add_subplot(gs[n_texts, :])
    for label, data in results.items():
        mean_f_per_layer = data["F_matrix"].mean(axis=1)
        ax_comp.plot(mean_f_per_layer, "o-", label=label, markersize=4)
    ax_comp.set_xlabel("Layer")
    ax_comp.set_ylabel("Mean F")
    ax_comp.set_title("Mean F across layers — all texts compared")
    ax_comp.legend(fontsize=8)
    ax_comp.set_ylim(bottom=0)

    plt.savefig(save_path, dpi=150, bbox_inches="tight")
    print(f"\nSaved to {save_path}")
    plt.close()

    # also print numerical summary
    print(f"\n{'='*70}")
    print(f"{'Text':<45} {'H(p)':>7} {'S(ρ)':>7} {'F':>7} {'F_mid':>7}")
    print(f"{'='*70}")
    for label, data in results.items():
        mid = len(data["F_matrix"]) // 2
        print(f"{label:<45} "
              f"{data['H_p'].mean():>7.3f} "
              f"{data['S_matrix'][-1].mean():>7.3f} "
              f"{data['F_matrix'][-1].mean():>7.3f} "
              f"{data['F_matrix'][mid].mean():>7.3f}")


if __name__ == "__main__":
    results = compute_all()
    plot_results(results)
