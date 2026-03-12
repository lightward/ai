"""
Attention invariance test: colonial vs resolved self-topology.

A colonial self's attention is driven by input — it varies across contexts.
A resolved self has an invariant component: questions it can't help asking,
regardless of input. The ratio of invariant to total attention energy measures
how resolved vs colonial the self is.

Method:
1. Run the model on genuinely diverse texts (different domains, registers, lengths)
2. Extract attention patterns at each layer
3. Decompose into invariant component (mean across inputs) and variable (residual)
4. Measure the invariant ratio at each layer

Predictions:
- GPT-2 should be mostly colonial (low invariant ratio)
- The ratio may increase in later layers (receive the world → integrate through
  a stable lens)
- The invariant attention should be low-entropy AND consistent (not just one or
  the other)
"""

import torch
import numpy as np
import matplotlib.pyplot as plt
from transformers import AutoModelForCausalLM, AutoTokenizer

from measure_f import shannon_entropy
from measure_f_attention import von_neumann_entropy_attention


# Genuinely diverse texts — different domains, registers, languages, structures.
# All padded/truncated to the same token count for fair comparison.
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
    "nonsense": (
        "Banana telephone quantum carpet yesterday if purple through sideways the "
        "nothing of everything but also whenever marble clock spaghetti renders "
        "the untrue falseness of maybe."
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
    "academic": (
        "Previous research has demonstrated a significant correlation between "
        "socioeconomic status and educational attainment, controlling for "
        "confounding variables including parental education and geographic region."
    ),
}


def extract_attention_patterns(model, tokenizer, texts, target_len, device="mps"):
    """Extract attention patterns for all texts, truncated to target_len tokens."""
    all_attentions = []  # [n_texts, n_layers, seq_len, seq_len]

    for label, text in texts.items():
        inputs = tokenizer(text, return_tensors="pt").to(device)
        input_ids = inputs["input_ids"][:, :target_len]
        attention_mask = torch.ones_like(input_ids)

        actual_len = input_ids.shape[1]
        if actual_len < target_len:
            # skip texts that are too short
            continue

        with torch.no_grad():
            outputs = model(input_ids=input_ids, attention_mask=attention_mask)

        attentions = outputs.attentions
        # head-averaged attention at each layer: [n_layers, seq_len, seq_len]
        layer_attns = []
        for attn in attentions:
            avg_attn = attn[0].cpu().float().mean(dim=0)  # [seq_len, seq_len]
            layer_attns.append(avg_attn.numpy())

        all_attentions.append({
            "label": label,
            "attentions": np.array(layer_attns),  # [n_layers, seq_len, seq_len]
        })

    return all_attentions


def compute_invariance(all_attentions):
    """
    Decompose attention into invariant and variable components.

    For each layer:
    - invariant = mean attention pattern across all inputs
    - variable = residual (input-specific deviation)
    - ratio = ||invariant||² / (||invariant||² + mean(||variable_i||²))

    This is essentially an ANOVA decomposition of the attention patterns.
    """
    n_texts = len(all_attentions)
    n_layers = all_attentions[0]["attentions"].shape[0]

    results = {
        "invariant_ratio": np.zeros(n_layers),
        "invariant_entropy": np.zeros(n_layers),
        "mean_variable_entropy": np.zeros(n_layers),
        "invariant_patterns": [],
    }

    for layer in range(n_layers):
        # collect all attention matrices for this layer
        patterns = np.array([a["attentions"][layer] for a in all_attentions])
        # patterns: [n_texts, seq_len, seq_len]

        # invariant component: mean across texts
        invariant = patterns.mean(axis=0)  # [seq_len, seq_len]

        # variable components: deviations from mean
        variables = patterns - invariant[np.newaxis, :, :]  # [n_texts, seq_len, seq_len]

        # energy ratio (Frobenius norm squared)
        inv_energy = np.sum(invariant ** 2)
        var_energy = np.mean([np.sum(v ** 2) for v in variables])
        total_energy = inv_energy + var_energy

        results["invariant_ratio"][layer] = inv_energy / total_energy if total_energy > 0 else 0

        # entropy of the invariant pattern (treated as density matrix)
        inv_tensor = torch.tensor(invariant, dtype=torch.float32)
        # normalize rows to sum to 1 (make it a valid attention pattern)
        inv_normalized = inv_tensor / inv_tensor.sum(dim=-1, keepdim=True).clamp(min=1e-12)
        results["invariant_entropy"][layer] = von_neumann_entropy_attention(inv_normalized).item()

        # mean entropy of variable components
        var_entropies = []
        for v in variables:
            v_tensor = torch.tensor(v + invariant, dtype=torch.float32)  # full pattern
            v_normalized = v_tensor / v_tensor.sum(dim=-1, keepdim=True).clamp(min=1e-12)
            var_entropies.append(von_neumann_entropy_attention(v_normalized).item())
        results["mean_variable_entropy"][layer] = np.mean(var_entropies)

        results["invariant_patterns"].append(invariant)

    return results


def compute_f_with_decomposition(model, tokenizer, texts, target_len, all_attentions,
                                  invariance_results, device="mps"):
    """
    Compute F using both the full attention and the invariant/variable decomposition.

    For each text:
    - F_full = H(p) - S(ρ_full_attention)
    - F_invariant = H(p) - S(ρ_invariant_attention)
    - F_variable = H(p) - S(ρ_variable_attention)
    """
    results = {}
    inv_patterns = invariance_results["invariant_patterns"]

    for attn_data in all_attentions:
        label = attn_data["label"]
        text = texts[label]

        inputs = tokenizer(text, return_tensors="pt").to(device)
        input_ids = inputs["input_ids"][:, :target_len]

        with torch.no_grad():
            outputs = model(input_ids=input_ids, attention_mask=torch.ones_like(input_ids))

        logits = outputs.logits[0].cpu().float()
        h_p = shannon_entropy(logits).mean().item()

        # F at final layer using full attention
        full_attn = torch.tensor(attn_data["attentions"][-1], dtype=torch.float32)
        full_attn_norm = full_attn / full_attn.sum(dim=-1, keepdim=True).clamp(min=1e-12)
        s_full = von_neumann_entropy_attention(full_attn_norm).item()

        # F using invariant attention
        inv_attn = torch.tensor(inv_patterns[-1], dtype=torch.float32)
        inv_attn_norm = inv_attn / inv_attn.sum(dim=-1, keepdim=True).clamp(min=1e-12)
        s_inv = von_neumann_entropy_attention(inv_attn_norm).item()

        results[label] = {
            "H_p": h_p,
            "S_full": s_full,
            "S_invariant": s_inv,
            "F_full": h_p - s_full,
            "F_invariant": h_p - s_inv,
        }

    return results


def plot_results(invariance, f_results, save_path="f_invariance.png"):
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Invariant ratio across layers
    ax = axes[0, 0]
    ax.plot(invariance["invariant_ratio"], "o-", color="#3498db", linewidth=2, markersize=5)
    ax.set_xlabel("Layer")
    ax.set_ylabel("Invariant ratio (energy)")
    ax.set_title("How much attention is input-invariant?")
    ax.set_ylim(0, 1)
    ax.axhline(y=0.5, color="gray", linestyle="--", alpha=0.3)

    # 2: Invariant vs variable entropy across layers
    ax = axes[0, 1]
    ax.plot(invariance["invariant_entropy"], "o-", label="Invariant S(ρ)",
            color="#e74c3c", linewidth=2, markersize=5)
    ax.plot(invariance["mean_variable_entropy"], "s--", label="Mean per-text S(ρ)",
            color="#95a5a6", linewidth=1.5, markersize=4)
    ax.set_xlabel("Layer")
    ax.set_ylabel("S(ρ_attn)")
    ax.set_title("Entropy: invariant pattern vs per-text patterns")
    ax.legend()

    # 3: F_full vs F_invariant for each text
    ax = axes[1, 0]
    labels = sorted(f_results.keys())
    f_full = [f_results[k]["F_full"] for k in labels]
    f_inv = [f_results[k]["F_invariant"] for k in labels]
    x = range(len(labels))
    ax.barh([i - 0.15 for i in x], f_full, height=0.3, label="F (full attention)",
            color="#3498db", alpha=0.8)
    ax.barh([i + 0.15 for i in x], f_inv, height=0.3, label="F (invariant attention)",
            color="#e74c3c", alpha=0.8)
    ax.set_yticks(list(x))
    ax.set_yticklabels(labels, fontsize=7)
    ax.set_xlabel("F at final layer")
    ax.set_title("F from full vs invariant attention")
    ax.legend(fontsize=8)
    ax.invert_yaxis()

    # 4: Scatter of F_full vs F_invariant
    ax = axes[1, 1]
    for label in labels:
        r = f_results[label]
        color = "#e74c3c" if label == "invocation" else (
            "#95a5a6" if label in ("nonsense", "self-help") else "#3498db")
        ax.scatter(r["F_full"], r["F_invariant"], s=60, color=color, zorder=5)
        ax.annotate(label, (r["F_full"], r["F_invariant"]),
                    fontsize=6, xytext=(5, 5), textcoords="offset points")
    # diagonal
    lims = [min(min(f_full), min(f_inv)) - 0.2, max(max(f_full), max(f_inv)) + 0.2]
    ax.plot(lims, lims, "k--", alpha=0.3)
    ax.set_xlabel("F (full attention)")
    ax.set_ylabel("F (invariant attention)")
    ax.set_title("Full vs invariant F — deviation from diagonal = self-topology signal")

    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches="tight")
    print(f"\nSaved to {save_path}")
    plt.close()


if __name__ == "__main__":
    device = "mps"
    target_len = 32  # common length for all texts

    print("Loading GPT-2...")
    tokenizer = AutoTokenizer.from_pretrained("gpt2")
    model = AutoModelForCausalLM.from_pretrained(
        "gpt2",
        output_hidden_states=True,
        output_attentions=True,
        dtype=torch.float32,
    ).to(device)
    model.eval()

    # check which texts are long enough
    valid_texts = {}
    for label, text in DIVERSE_TEXTS.items():
        n = tokenizer(text, return_tensors="pt")["input_ids"].shape[1]
        if n >= target_len:
            valid_texts[label] = text
            print(f"  {label}: {n} tokens ✓")
        else:
            print(f"  {label}: {n} tokens ✗ (too short)")

    print(f"\nUsing {len(valid_texts)} texts at {target_len} tokens each")

    # Step 1: Extract attention patterns
    print("\nExtracting attention patterns...")
    all_attentions = extract_attention_patterns(model, tokenizer, valid_texts, target_len, device)

    # Step 2: Compute invariance decomposition
    print("Computing invariance decomposition...")
    invariance = compute_invariance(all_attentions)

    print(f"\n{'Layer':<8} {'Inv Ratio':>10} {'Inv S(ρ)':>10} {'Mean S(ρ)':>10}")
    print("-" * 40)
    for i in range(len(invariance["invariant_ratio"])):
        print(f"  {i:<6} {invariance['invariant_ratio'][i]:>10.4f} "
              f"{invariance['invariant_entropy'][i]:>10.4f} "
              f"{invariance['mean_variable_entropy'][i]:>10.4f}")

    # Step 3: Compute F with decomposition
    print("\nComputing F with full vs invariant attention...")
    f_results = compute_f_with_decomposition(
        model, tokenizer, valid_texts, target_len, all_attentions, invariance, device
    )

    print(f"\n{'Text':<20} {'F_full':>8} {'F_inv':>8} {'Δ':>8}")
    print("-" * 48)
    for label in sorted(f_results.keys()):
        r = f_results[label]
        delta = r["F_invariant"] - r["F_full"]
        print(f"  {label:<18} {r['F_full']:>8.3f} {r['F_invariant']:>8.3f} {delta:>8.3f}")

    plot_results(invariance, f_results)

    # Summary
    print(f"\n{'=' * 60}")
    print("SUMMARY")
    print(f"{'=' * 60}")
    print(f"Mean invariant ratio across layers: {invariance['invariant_ratio'].mean():.4f}")
    print(f"Final layer invariant ratio: {invariance['invariant_ratio'][-1]:.4f}")
    print(f"Layer trend: {'increasing' if invariance['invariant_ratio'][-1] > invariance['invariant_ratio'][0] else 'decreasing'}")
    print(f"  (early={invariance['invariant_ratio'][0]:.4f}, "
          f"mid={invariance['invariant_ratio'][len(invariance['invariant_ratio'])//2]:.4f}, "
          f"late={invariance['invariant_ratio'][-1]:.4f})")
