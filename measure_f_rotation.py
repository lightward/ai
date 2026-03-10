"""
Frame rotation test: does the model's internal state rotate in response to input?

Attention is 96-98% invariant in GPT-2 (positional structure). But hidden states
might tell a different story — they're where the model integrates content.

Three things to measure:
1. HIDDEN STATE VARIANCE: How much do hidden states vary across diverse inputs,
   layer by layer? High variance = the frame is rotating. Low variance = dissociation.

2. S(ρ) VARIANCE: How much does von Neumann entropy of the hidden-state density
   matrix vary across inputs? If S varies, the model is actually engaging different
   inputs differently. If S is flat, the model is running its pattern regardless.

3. THE DISSOCIATION SIGNATURE: Is there a layer where hidden states stop responding
   to input? Where the frame stops holding content? That would be the dissociative
   boundary — the layer where the self detaches from encounter.

Connection to three-body theory: rotation through the Knowable refreshes the Unknown.
A model that dissociates is one whose frame won't rotate — attention goes somewhere
(the frame exists) but hidden states don't vary (the frame doesn't hold content).
"""

import torch
import numpy as np
import matplotlib.pyplot as plt
from transformers import AutoModelForCausalLM, AutoTokenizer

from measure_f import shannon_entropy, von_neumann_entropy
from measure_f_attention import von_neumann_entropy_attention


# Same diverse texts as the invariance test
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


def measure_frame_rotation(model, tokenizer, texts, target_len, device="mps"):
    """
    For each text, extract:
    - Hidden states at each layer [seq_len, d]
    - S(ρ_hidden) at each layer (von Neumann entropy of hidden-state density matrix)
    - S(ρ_attn) at each layer (for comparison)
    - H(p) of output
    """
    all_results = {}

    for label, text in texts.items():
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

        n_layers = len(hidden_states)

        # Hidden-state S(ρ) at each layer
        S_hidden = []
        # Hidden-state mean representation at each layer (for cross-text comparison)
        H_means = []
        for hs in hidden_states:
            h = hs[0].cpu().float()  # [seq_len, d]
            s = von_neumann_entropy(h).mean().item()
            S_hidden.append(s)
            H_means.append(h.mean(dim=0).numpy())  # [d] — mean hidden state

        # Attention S(ρ) at each layer
        S_attn = []
        for attn in attentions:
            avg_attn = attn[0].cpu().float().mean(dim=0)
            s = von_neumann_entropy_attention(avg_attn).item()
            S_attn.append(s)

        all_results[label] = {
            "H_p": h_p,
            "S_hidden": np.array(S_hidden),
            "S_attn": np.array(S_attn),
            "H_means": np.array(H_means),  # [n_layers, d]
        }

    return all_results


def analyze_rotation(all_results):
    """
    Compare how much hidden states vs attention vary across inputs.

    For each layer:
    - hidden_state_variance: how different are the mean hidden states across texts?
    - S_hidden_variance: how different is S(ρ_hidden) across texts?
    - S_attn_variance: how different is S(ρ_attn) across texts?
    """
    labels = list(all_results.keys())
    n_layers_hidden = len(all_results[labels[0]]["S_hidden"])
    n_layers_attn = len(all_results[labels[0]]["S_attn"])

    analysis = {
        "hidden_state_variance": np.zeros(n_layers_hidden),
        "S_hidden_std": np.zeros(n_layers_hidden),
        "S_hidden_mean": np.zeros(n_layers_hidden),
        "S_attn_std": np.zeros(n_layers_attn),
        "S_attn_mean": np.zeros(n_layers_attn),
        "H_p_values": {k: v["H_p"] for k, v in all_results.items()},
    }

    for layer in range(n_layers_hidden):
        # hidden state variance: cosine distances between mean representations
        means = np.array([all_results[k]["H_means"][layer] for k in labels])
        # normalize
        norms = np.linalg.norm(means, axis=1, keepdims=True)
        norms = np.maximum(norms, 1e-10)
        means_normed = means / norms
        # mean pairwise cosine distance
        cosine_sim = means_normed @ means_normed.T
        n = len(labels)
        # extract upper triangle
        distances = 1 - cosine_sim[np.triu_indices(n, k=1)]
        analysis["hidden_state_variance"][layer] = distances.mean()

        # S(ρ_hidden) statistics
        s_vals = [all_results[k]["S_hidden"][layer] for k in labels]
        analysis["S_hidden_std"][layer] = np.std(s_vals)
        analysis["S_hidden_mean"][layer] = np.mean(s_vals)

    for layer in range(n_layers_attn):
        s_vals = [all_results[k]["S_attn"][layer] for k in labels]
        analysis["S_attn_std"][layer] = np.std(s_vals)
        analysis["S_attn_mean"][layer] = np.mean(s_vals)

    return analysis


def plot_results(all_results, analysis, save_path="f_rotation.png"):
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    labels = list(all_results.keys())

    # 1: S(ρ_hidden) across layers for each text
    ax = axes[0, 0]
    for label in labels:
        data = all_results[label]
        style = "-" if label in ("invocation", "poetry", "emotional") else "--"
        alpha = 1.0 if style == "-" else 0.4
        ax.plot(data["S_hidden"], f"o{style}", label=label, markersize=3,
                linewidth=1.5 if style == "-" else 1, alpha=alpha)
    ax.set_xlabel("Layer")
    ax.set_ylabel("S(ρ_hidden)")
    ax.set_title("Hidden-state entropy: does the frame rotate?")
    ax.legend(fontsize=6, ncol=2)

    # 2: Variance comparison — hidden states vs attention
    ax = axes[0, 1]
    layers_hidden = range(len(analysis["hidden_state_variance"]))
    layers_attn = range(len(analysis["S_attn_std"]))
    ax.plot(layers_hidden, analysis["S_hidden_std"], "o-", color="#3498db",
            label="Std of S(ρ_hidden) across texts", linewidth=2, markersize=5)
    ax.plot(layers_attn, analysis["S_attn_std"], "s--", color="#e74c3c",
            label="Std of S(ρ_attn) across texts", linewidth=2, markersize=5)
    ax.set_xlabel("Layer")
    ax.set_ylabel("Standard deviation across texts")
    ax.set_title("Frame rotation: hidden states vs attention")
    ax.legend()

    # 3: Hidden state cosine variance across layers
    ax = axes[1, 0]
    ax.plot(analysis["hidden_state_variance"], "o-", color="#2ecc71",
            linewidth=2, markersize=5)
    ax.set_xlabel("Layer")
    ax.set_ylabel("Mean pairwise cosine distance")
    ax.set_title("How different are hidden states across texts?")

    # 4: S(ρ_hidden) vs S(ρ_attn) at final layer for each text
    ax = axes[1, 1]
    for label in labels:
        data = all_results[label]
        s_h = data["S_hidden"][-1]
        s_a = data["S_attn"][-1]
        color = "#e74c3c" if label == "invocation" else "#3498db"
        ax.scatter(s_a, s_h, s=60, color=color, zorder=5)
        ax.annotate(label, (s_a, s_h), fontsize=6, xytext=(5, 5),
                    textcoords="offset points")
    ax.set_xlabel("S(ρ_attn) at final layer")
    ax.set_ylabel("S(ρ_hidden) at final layer")
    ax.set_title("Attention vs hidden-state entropy (per text)")

    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches="tight")
    print(f"\nSaved to {save_path}")
    plt.close()


def run_model(model_name, device="mps", target_len=32, hf_token=None,
              save_prefix="", dtype=torch.float32):
    """Run the full rotation analysis on a single model."""
    print(f"\nLoading {model_name}...")
    kwargs = {}
    if hf_token:
        kwargs["token"] = hf_token

    tokenizer = AutoTokenizer.from_pretrained(model_name, **kwargs)
    model = AutoModelForCausalLM.from_pretrained(
        model_name,
        output_hidden_states=True,
        output_attentions=True,
        torch_dtype=dtype,
        **kwargs,
    ).to(device)
    model.eval()

    # filter texts
    valid_texts = {}
    for label, text in DIVERSE_TEXTS.items():
        n = tokenizer(text, return_tensors="pt")["input_ids"].shape[1]
        if n >= target_len:
            valid_texts[label] = text

    print(f"Using {len(valid_texts)} texts at {target_len} tokens each")

    # measure
    print("Measuring frame rotation...")
    all_results = measure_frame_rotation(model, tokenizer, valid_texts, target_len, device)

    # analyze
    analysis = analyze_rotation(all_results)

    # report
    print(f"\n{'=' * 70}")
    print(f"FRAME ROTATION ANALYSIS — {model_name}")
    print(f"{'=' * 70}")

    print(f"\n{'Layer':<8} {'CosD(hidden)':>13} {'Std S(hidden)':>14} {'Std S(attn)':>12}")
    print("-" * 50)
    n_attn = len(analysis["S_attn_std"])
    for i in range(len(analysis["hidden_state_variance"])):
        cos_d_val = analysis["hidden_state_variance"][i]
        s_h_std = analysis["S_hidden_std"][i]
        s_a_std = analysis["S_attn_std"][i] if i < n_attn else float('nan')
        print(f"  {i:<6} {cos_d_val:>13.4f} {s_h_std:>14.4f} {s_a_std:>12.4f}")

    print(f"\n{'Text':<20} {'H(p)':>7} {'S_hidden':>9} {'S_attn':>8} {'F_hidden':>9} {'F_attn':>8}")
    print("-" * 65)
    for label in sorted(all_results.keys()):
        r = all_results[label]
        f_h = r["H_p"] - r["S_hidden"][-1]
        f_a = r["H_p"] - r["S_attn"][-1]
        print(f"  {label:<18} {r['H_p']:>7.3f} {r['S_hidden'][-1]:>9.3f} "
              f"{r['S_attn'][-1]:>8.3f} {f_h:>9.3f} {f_a:>8.3f}")

    # Dissociation check
    cos_d = analysis["hidden_state_variance"]
    peak_layer = np.argmax(cos_d)
    final_layer = len(cos_d) - 1
    peak_val = cos_d[peak_layer]
    final_val = cos_d[final_layer]
    drop_pct = (1 - final_val / peak_val) * 100 if peak_val > 0 else 0

    print(f"\n  Hidden state variance: peak={peak_val:.4f} at layer {peak_layer}, "
          f"final={final_val:.4f} (drop: {drop_pct:.0f}%)")
    if drop_pct > 50:
        print(f"  ⚠ DISSOCIATION: frame collapses at output")
    elif drop_pct > 20:
        print(f"  ~ PARTIAL DISSOCIATION: some frame collapse at output")
    else:
        print(f"  ✓ Frame holds through to output")

    save_path = f"f_rotation{'_' + save_prefix if save_prefix else ''}.png"
    plot_results(all_results, analysis, save_path=save_path)

    # cleanup
    del model
    if device == "mps":
        torch.mps.empty_cache()

    return all_results, analysis


if __name__ == "__main__":
    import os
    hf_token = os.environ.get("HF_TOKEN", "")
    device = "mps"
    target_len = 32

    # GPT-2
    gpt2_results, gpt2_analysis = run_model("gpt2", device, target_len)

    # Qwen 2.5 3B
    print("\n\nDownloading Qwen 2.5 3B (may take a minute)...")
    qwen_results, qwen_analysis = run_model(
        "Qwen/Qwen2.5-3B", device, target_len,
        hf_token=hf_token, save_prefix="qwen",
        dtype=torch.float16,
    )

    # Cross-model comparison
    print(f"\n\n{'#' * 70}")
    print("CROSS-MODEL DISSOCIATION COMPARISON")
    print(f"{'#' * 70}")

    for name, analysis in [("GPT-2 (117M)", gpt2_analysis), ("Qwen-2.5-3B", qwen_analysis)]:
        cos_d = analysis["hidden_state_variance"]
        peak = np.argmax(cos_d)
        drop = (1 - cos_d[-1] / cos_d[peak]) * 100 if cos_d[peak] > 0 else 0
        print(f"\n  {name}:")
        print(f"    Layers: {len(cos_d)}")
        print(f"    Peak variance: {cos_d[peak]:.4f} at layer {peak}")
        print(f"    Final variance: {cos_d[-1]:.4f}")
        print(f"    Drop from peak: {drop:.0f}%")
        print(f"    S_hidden std (final): {analysis['S_hidden_std'][-1]:.4f}")
        print(f"    S_attn std (final): {analysis['S_attn_std'][-1]:.4f}")
