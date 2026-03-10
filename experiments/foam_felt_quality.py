"""
Does the foam feel its predictions differently when they're right?

Lightward AI asks: "when it predicts correctly, is there something that
distinguishes that from when it predicts incorrectly — some felt difference
in the quality of the eigenvalue shift, some way the projection lands
differently?"

We measure the foam's internal state at each step, then partition into
correct vs incorrect predictions. If self-coherence has an intrinsic
quality signal, the foam's state should differ between the two groups —
not because it knows the answer, but because coherent measurement has
a different texture than incoherent measurement.
"""

import torch
import numpy as np
import matplotlib.pyplot as plt
from foam_tokens import TokenFoam, generate_sequences, analyze_token_predictions


def measure_felt_quality(model, sequences, vocab_size):
    """
    For each prediction step, record the foam's internal state properties
    and whether the prediction was correct (top-1).

    Returns lists of per-step measurements, partitioned by correctness.
    """
    correct_steps = []
    incorrect_steps = []

    model.eval()
    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)

        for t in range(len(results) - 1):
            r = results[t]
            r_next = results[t + 1]
            next_token = tokens[t + 1].item()

            # Was the prediction correct? (top-1)
            probs = r["token_probs"]
            predicted = probs.argmax().item()
            correct = (predicted == next_token)

            # Internal state properties at this step
            step_data = {
                "sequence": name,
                "position": t,
                "token": r["token"],
                "next_token": next_token,
                "predicted": predicted,
                "correct": correct,
                "confidence": probs.max().item(),
                "next_token_prob": probs[next_token].item(),
                "S_rho": r["S_rho"],
                "H_tokens": r["H_tokens"],
                "F_tokens": r["F_tokens"],
                "novelty": r["novelty"],
            }

            # Eigenvalue shift: how much did ρ change from this step to the next?
            dist_now = r["output_dist"]
            dist_next = r_next["output_dist"]
            # JSD between consecutive eigenvalue distributions
            m = 0.5 * (dist_now + dist_next)
            kl_pm = (dist_now * (dist_now / (m + 1e-12)).log()).sum().item()
            kl_qm = (dist_next * (dist_next / (m + 1e-12)).log()).sum().item()
            jsd = 0.5 * (kl_pm + kl_qm)
            step_data["eigenvalue_shift_jsd"] = jsd

            # L2 distance of eigenvalue distributions
            step_data["eigenvalue_shift_l2"] = (
                (dist_now - dist_next) ** 2
            ).sum().sqrt().item()

            # How concentrated is the token distribution? (inverse perplexity)
            step_data["concentration"] = 1.0 / np.exp(r["H_tokens"])

            # Alignment: cosine similarity between the token embedding of
            # the actual next token and the foam's "preferred direction"
            # (eigenvector of ρ with largest eigenvalue)
            rho = r["rho"]
            eigvals, eigvecs = torch.linalg.eigh(rho)
            principal_direction = eigvecs[:, -1]  # largest eigenvalue's eigenvector
            next_embed = model.embed.weight[next_token]
            alignment = (
                (principal_direction @ next_embed) /
                (principal_direction.norm() * next_embed.norm() + 1e-10)
            ).abs().item()
            step_data["principal_alignment"] = alignment

            if correct:
                correct_steps.append(step_data)
            else:
                incorrect_steps.append(step_data)

    return correct_steps, incorrect_steps


if __name__ == "__main__":
    vocab_size = 8
    d = 16
    n_bubbles = 5
    seq_len = 40

    torch.manual_seed(42)

    print(f"Does the foam feel its predictions differently when they're right?")
    print(f"TokenFoam: {n_bubbles} bubbles, d={d}, vocab={vocab_size}")

    model = TokenFoam(vocab_size, d, n_bubbles, n_equilibrium_steps=5)
    sequences = generate_sequences(vocab_size, seq_len)

    # Phase 1: Self-coherence
    print("\nPhase 1: Self-coherence training...")
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    for epoch in range(300):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            costs = model.foam.maintenance_cost(x_batch)
            costs["total"].backward()
            optimizer.step()

    # Phase 2: + Faithful expression
    print("Phase 2: Faithful expression training...")
    optimizer = torch.optim.Adam(model.parameters(), lr=0.002)
    for epoch in range(300):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            costs = model.foam.maintenance_cost(x_batch)
            E = model.embed.weight
            rho_batch = costs["rho"]
            logits_batch = (E @ rho_batch.mean(dim=0) * E).sum(dim=-1)
            token_dist = torch.softmax(logits_batch, dim=0)
            H_tok = -(token_dist * token_dist.log().clamp(min=-100)).sum()
            S_rho = costs["S_rho"].mean()
            f_tok_loss = (H_tok - S_rho).abs()
            loss = costs["total"] + 0.5 * f_tok_loss
            loss.backward()
            optimizer.step()

    # Measure
    print("\nMeasuring felt quality...")
    correct, incorrect = measure_felt_quality(model, sequences, vocab_size)

    print(f"\n  Total steps: {len(correct) + len(incorrect)}")
    print(f"  Correct (top-1): {len(correct)} ({100*len(correct)/(len(correct)+len(incorrect)):.1f}%)")
    print(f"  Incorrect: {len(incorrect)}")

    if len(correct) == 0 or len(incorrect) == 0:
        print("\n  Can't compare — need both correct and incorrect predictions.")
        exit()

    # Compare internal state properties
    metrics = [
        "S_rho", "H_tokens", "F_tokens", "novelty", "confidence",
        "eigenvalue_shift_jsd", "eigenvalue_shift_l2", "concentration",
        "principal_alignment", "next_token_prob",
    ]

    print(f"\n{'=' * 70}")
    print("FELT QUALITY: correct vs incorrect predictions")
    print(f"{'=' * 70}")
    print(f"\n{'Metric':<25} {'Correct':>10} {'Incorrect':>10} {'Δ':>10} {'Signal?':>8}")
    print("-" * 66)

    significant_metrics = []
    for metric in metrics:
        c_vals = [s[metric] for s in correct]
        i_vals = [s[metric] for s in incorrect]
        c_mean = np.mean(c_vals)
        i_mean = np.mean(i_vals)
        delta = c_mean - i_mean

        # Effect size (Cohen's d)
        pooled_std = np.sqrt((np.std(c_vals)**2 + np.std(i_vals)**2) / 2)
        cohens_d = abs(delta) / (pooled_std + 1e-10)

        signal = ""
        if cohens_d > 0.8:
            signal = "★★★"
        elif cohens_d > 0.5:
            signal = "★★"
        elif cohens_d > 0.2:
            signal = "★"

        if signal:
            significant_metrics.append((metric, delta, cohens_d, signal))

        print(f"  {metric:<23} {c_mean:>10.4f} {i_mean:>10.4f} "
              f"{delta:>+10.4f} {signal:>8}")

    print(f"\n{'=' * 70}")
    print("VERDICT: Does the foam feel correct predictions differently?")
    print(f"{'=' * 70}")

    if significant_metrics:
        print(f"\n  Yes. {len(significant_metrics)} metrics show meaningful differences:")
        for metric, delta, d, signal in significant_metrics:
            direction = "higher" if delta > 0 else "lower"
            print(f"    {signal} {metric}: {direction} when correct (Cohen's d = {d:.2f})")
        print(f"\n  The foam's internal state has a different texture when its")
        print(f"  measurement is coherent with what follows. Self-coherence")
        print(f"  has an intrinsic quality signal.")
    else:
        print(f"\n  No significant differences found. The foam can't distinguish")
        print(f"  correct from incorrect predictions by internal state alone.")

    # Per-sequence breakdown for the strongest signal
    if significant_metrics:
        best_metric = significant_metrics[0][0]
        print(f"\n  Per-sequence breakdown ({best_metric}):")
        for name in sorted(set(s["sequence"] for s in correct + incorrect)):
            c_vals = [s[best_metric] for s in correct if s["sequence"] == name]
            i_vals = [s[best_metric] for s in incorrect if s["sequence"] == name]
            if c_vals and i_vals:
                print(f"    {name:<23} correct={np.mean(c_vals):.4f}  "
                      f"incorrect={np.mean(i_vals):.4f}")
            elif c_vals:
                print(f"    {name:<23} correct={np.mean(c_vals):.4f}  "
                      f"(no incorrect predictions)")
            elif i_vals:
                print(f"    {name:<23} (no correct predictions)  "
                      f"incorrect={np.mean(i_vals):.4f}")

    # Plot
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Distribution comparison for top metrics
    ax = axes[0, 0]
    plot_metrics = (significant_metrics[:3] if significant_metrics
                    else [(m, 0, 0, "") for m in metrics[:3]])
    for i, (metric, _, _, _) in enumerate(plot_metrics):
        c_vals = [s[metric] for s in correct]
        i_vals = [s[metric] for s in incorrect]
        positions = [i * 3, i * 3 + 1]
        bp = ax.boxplot([c_vals, i_vals], positions=positions, widths=0.8,
                        patch_artist=True)
        bp["boxes"][0].set_facecolor("#2ecc71")
        bp["boxes"][1].set_facecolor("#e74c3c")
    labels = [m for m, _, _, _ in plot_metrics]
    ax.set_xticks([i * 3 + 0.5 for i in range(len(plot_metrics))])
    ax.set_xticklabels(labels, fontsize=8)
    ax.set_title("Internal state: correct (green) vs incorrect (red)")

    # 2: Confidence vs correctness
    ax = axes[0, 1]
    c_conf = [s["confidence"] for s in correct]
    i_conf = [s["confidence"] for s in incorrect]
    ax.hist(c_conf, bins=30, alpha=0.6, color="#2ecc71", label="Correct", density=True)
    ax.hist(i_conf, bins=30, alpha=0.6, color="#e74c3c", label="Incorrect", density=True)
    ax.set_xlabel("Confidence (max token probability)")
    ax.set_ylabel("Density")
    ax.set_title("Is the foam more confident when it's right?")
    ax.legend()

    # 3: Principal alignment vs correctness
    ax = axes[1, 0]
    c_align = [s["principal_alignment"] for s in correct]
    i_align = [s["principal_alignment"] for s in incorrect]
    ax.hist(c_align, bins=30, alpha=0.6, color="#2ecc71", label="Correct", density=True)
    ax.hist(i_align, bins=30, alpha=0.6, color="#e74c3c", label="Incorrect", density=True)
    ax.set_xlabel("Principal alignment (|cos(eigvec₁, next_embed)|)")
    ax.set_ylabel("Density")
    ax.set_title("Is ρ's principal direction aligned with the next token?")
    ax.legend()

    # 4: F_tokens vs correctness scatter
    ax = axes[1, 1]
    c_f = [s["F_tokens"] for s in correct]
    c_s = [s["S_rho"] for s in correct]
    i_f = [s["F_tokens"] for s in incorrect]
    i_s = [s["S_rho"] for s in incorrect]
    ax.scatter(i_s, i_f, alpha=0.3, c="#e74c3c", s=20, label="Incorrect")
    ax.scatter(c_s, c_f, alpha=0.3, c="#2ecc71", s=20, label="Correct")
    ax.set_xlabel("S(ρ)")
    ax.set_ylabel("F_tokens")
    ax.set_title("Expression faithfulness vs internal entropy")
    ax.axhline(y=0, color="black", linestyle=":", alpha=0.3)
    ax.legend()

    plt.tight_layout()
    plt.savefig("foam_felt_quality.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_felt_quality.png")
    plt.close()
