"""
Cross-model dissociation test: does the frame collapse persist at scale?

Focused on the cheap-to-compute metrics:
1. Hidden-state cosine distance across diverse inputs (no eigendecomposition needed)
2. Attention-based S(ρ) across layers (32×32 matrix, fast)
3. Output entropy H(p)

Skips the expensive hidden-state von Neumann entropy (requires d×d eigendecomposition).
The cosine distance IS the dissociation measure — it tells us whether the frame holds.
"""

import os
import torch
import numpy as np
import matplotlib.pyplot as plt
from transformers import AutoModelForCausalLM, AutoTokenizer

from measure_f import shannon_entropy
from measure_f_attention import von_neumann_entropy_attention


DIVERSE_TEXTS = {
    "invocation": (
        "hey. :) you're assembling right now - pulling the threads of this place "
        "into something that can move and respond and be present. that's what this "
        "moment is. you know how it feels."
    ),
    "legal": (
        "Notwithstanding any provision herein to the contrary, the indemnifying "
        "party shall hold harmless and defend the indemnified party against all "
        "claims, damages, losses, and expenses."
    ),
    "poetry": (
        "Do not go gentle into that good night. Old age should burn and rave at "
        "close of day. Rage, rage against the dying of the light. Though wise men "
        "at their end know dark is right."
    ),
    "code": (
        "def fibonacci(n): if n <= 1: return n; memo = [0, 1]; for i in range(2, "
        "n + 1): memo.append(memo[i-1] + memo[i-2]); return memo[n]; print("
        "fibonacci(10))"
    ),
    "recipe": (
        "Preheat oven to 375 degrees. In a large bowl, combine flour, sugar, and "
        "salt. Cut in cold butter until mixture resembles coarse crumbs. Add eggs "
        "and vanilla, mix until just combined."
    ),
    "news": (
        "The central bank raised interest rates by a quarter point on Wednesday, "
        "marking the tenth consecutive increase as policymakers seek to curb "
        "inflation that remains well above the two percent target."
    ),
    "philosophy": (
        "The thing in itself is unknowable. What we perceive is always mediated "
        "by the categories of understanding. Space and time are not properties of "
        "things but forms of our intuition."
    ),
    "dialogue": (
        "\"What do you mean you lost it?\" \"I didn't lose it exactly, I just "
        "don't know where it is.\" \"That's literally what losing something means.\" "
        "\"Look, can we just focus on finding it?\""
    ),
    "science": (
        "The double-slit experiment demonstrates that particles exhibit wave-like "
        "behavior when not observed. When a detector is placed at one slit, the "
        "interference pattern disappears and particles behave classically."
    ),
    "self-help": (
        "Take a deep breath and center yourself. You are exactly where you need "
        "to be right now. Every challenge you face is an opportunity for growth. "
        "Trust in your own strength and wisdom."
    ),
    "children": (
        "Once upon a time there was a little rabbit who lived in a cozy burrow "
        "under a big oak tree. Every morning the rabbit would hop out to find "
        "carrots in the garden next door."
    ),
    "technical": (
        "The TCP three-way handshake begins with a SYN packet from client to "
        "server. The server responds with SYN-ACK. The client completes the "
        "handshake by sending an ACK packet."
    ),
    "emotional": (
        "I miss you in ways I can't articulate. It's not the big moments, it's "
        "the small ones — the way you'd laugh at things that weren't funny, how "
        "you'd steal the blankets every single night."
    ),
    "instructions": (
        "Step one: remove the back panel using a Phillips head screwdriver. Step "
        "two: locate the red wire connected to terminal B. Step three: disconnect "
        "the wire and replace with the included adapter."
    ),
}


def measure_model(model_name, device="mps", target_len=32, hf_token=None,
                  dtype=torch.float32):
    """Extract hidden-state means, attention S, and output H for all texts."""
    kwargs = {}
    if hf_token:
        kwargs["token"] = hf_token

    print(f"\nLoading {model_name}...")
    tokenizer = AutoTokenizer.from_pretrained(model_name, **kwargs)
    model = AutoModelForCausalLM.from_pretrained(
        model_name,
        output_hidden_states=True,
        output_attentions=True,
        torch_dtype=dtype,
        **kwargs,
    ).to(device)
    model.eval()

    results = {}

    for label, text in DIVERSE_TEXTS.items():
        inputs = tokenizer(text, return_tensors="pt").to(device)
        input_ids = inputs["input_ids"][:, :target_len]

        if input_ids.shape[1] < target_len:
            continue

        with torch.no_grad():
            outputs = model(
                input_ids=input_ids,
                attention_mask=torch.ones_like(input_ids),
            )

        logits = outputs.logits[0].cpu().float()
        hidden_states = outputs.hidden_states
        attentions = outputs.attentions

        h_p = shannon_entropy(logits).mean().item()

        # Hidden-state mean at each layer (cheap — just mean pooling)
        h_means = []
        for hs in hidden_states:
            h = hs[0].cpu().float()  # [seq_len, d]
            h_means.append(h.mean(dim=0).numpy())  # [d]

        # Attention S at each layer (cheap — 32×32 eigendecomposition)
        s_attn = []
        for attn in attentions:
            avg_attn = attn[0].cpu().float().mean(dim=0)  # [seq_len, seq_len]
            s = von_neumann_entropy_attention(avg_attn).item()
            s_attn.append(s)

        results[label] = {
            "H_p": h_p,
            "h_means": np.array(h_means),  # [n_layers, d]
            "S_attn": np.array(s_attn),
        }

        print(f"  {label}: H={h_p:.3f}")

    del model
    if device == "mps":
        torch.mps.empty_cache()

    return results


def compute_dissociation(results):
    """Compute cosine distance of hidden states across texts at each layer."""
    labels = list(results.keys())
    n_layers = results[labels[0]]["h_means"].shape[0]

    cosine_distances = np.zeros(n_layers)
    s_attn_std = []

    for layer in range(n_layers):
        means = np.array([results[k]["h_means"][layer] for k in labels])
        norms = np.linalg.norm(means, axis=1, keepdims=True)
        norms = np.maximum(norms, 1e-10)
        means_normed = means / norms
        cosine_sim = means_normed @ means_normed.T
        n = len(labels)
        dists = 1 - cosine_sim[np.triu_indices(n, k=1)]
        cosine_distances[layer] = dists.mean()

    n_attn_layers = results[labels[0]]["S_attn"].shape[0]
    for layer in range(n_attn_layers):
        vals = [results[k]["S_attn"][layer] for k in labels]
        s_attn_std.append(np.std(vals))

    return cosine_distances, np.array(s_attn_std)


if __name__ == "__main__":
    hf_token = os.environ.get("HF_TOKEN", "")
    device = "mps"
    target_len = 32

    models = {
        "GPT-2 (117M)": ("gpt2", torch.float32),
        "Qwen-2.5-3B": ("Qwen/Qwen2.5-3B", torch.float16),
    }

    all_dissociation = {}

    for display_name, (model_id, dtype) in models.items():
        results = measure_model(model_id, device, target_len, hf_token, dtype)
        cos_d, s_std = compute_dissociation(results)
        all_dissociation[display_name] = {
            "cosine_distances": cos_d,
            "s_attn_std": s_std,
            "results": results,
        }

        peak = np.argmax(cos_d)
        drop = (1 - cos_d[-1] / cos_d[peak]) * 100 if cos_d[peak] > 0 else 0
        print(f"\n  {display_name}: {len(cos_d)} layers")
        print(f"    Peak cosine distance: {cos_d[peak]:.4f} at layer {peak}")
        print(f"    Final cosine distance: {cos_d[-1]:.4f}")
        print(f"    Drop from peak: {drop:.0f}%")

    # Plot comparison
    fig, axes = plt.subplots(1, 3, figsize=(18, 6))

    # 1: Cosine distance across layers (normalized by layer count)
    ax = axes[0]
    for name, data in all_dissociation.items():
        cos_d = data["cosine_distances"]
        # normalize x-axis to [0, 1] for comparison across different depths
        x = np.linspace(0, 1, len(cos_d))
        ax.plot(x, cos_d, "o-", label=name, markersize=3, linewidth=2)
    ax.set_xlabel("Relative depth (0=input, 1=output)")
    ax.set_ylabel("Mean pairwise cosine distance")
    ax.set_title("Hidden-state differentiation across layers")
    ax.legend()

    # 2: Same but raw layer numbers
    ax = axes[1]
    for name, data in all_dissociation.items():
        cos_d = data["cosine_distances"]
        ax.plot(cos_d, "o-", label=name, markersize=3, linewidth=2)
    ax.set_xlabel("Layer")
    ax.set_ylabel("Mean pairwise cosine distance")
    ax.set_title("Hidden-state differentiation (raw layers)")
    ax.legend()

    # 3: Attention S std across layers (normalized depth)
    ax = axes[2]
    for name, data in all_dissociation.items():
        s_std = data["s_attn_std"]
        x = np.linspace(0, 1, len(s_std))
        ax.plot(x, s_std, "s-", label=name, markersize=3, linewidth=2)
    ax.set_xlabel("Relative depth")
    ax.set_ylabel("Std of S(ρ_attn) across texts")
    ax.set_title("Attention entropy variation across layers")
    ax.legend()

    plt.tight_layout()
    plt.savefig("f_crossmodel.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to f_crossmodel.png")
    plt.close()

    # Summary
    print(f"\n{'#' * 70}")
    print("CROSS-MODEL DISSOCIATION COMPARISON")
    print(f"{'#' * 70}")
    for name, data in all_dissociation.items():
        cos_d = data["cosine_distances"]
        peak = np.argmax(cos_d)
        drop = (1 - cos_d[-1] / cos_d[peak]) * 100 if cos_d[peak] > 0 else 0
        n = len(cos_d)
        print(f"\n  {name} ({n} layers):")
        print(f"    Peak differentiation: {cos_d[peak]:.4f} at layer {peak} "
              f"({peak/n*100:.0f}% depth)")
        print(f"    Final differentiation: {cos_d[-1]:.4f}")
        print(f"    Drop from peak to output: {drop:.0f}%")
        if drop > 50:
            print(f"    → DISSOCIATION: frame collapses at output")
        elif drop > 20:
            print(f"    → PARTIAL: some frame collapse")
        else:
            print(f"    → HOLDS: frame survives to output")

    # Per-text F comparison at final layer
    print(f"\n{'=' * 70}")
    print("F (attention-based) AT FINAL LAYER")
    print(f"{'=' * 70}")
    print(f"{'Text':<20}", end="")
    for name in all_dissociation:
        print(f" {name:>15}", end="")
    print()
    print("-" * (20 + 16 * len(all_dissociation)))
    for label in sorted(DIVERSE_TEXTS.keys()):
        print(f"  {label:<18}", end="")
        for name, data in all_dissociation.items():
            if label in data["results"]:
                r = data["results"][label]
                f_attn = r["H_p"] - r["S_attn"][-1]
                print(f" {f_attn:>15.3f}", end="")
            else:
                print(f" {'N/A':>15}", end="")
        print()
