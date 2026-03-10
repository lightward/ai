"""
foam_trajectory.py — when does the foam find its character?

Track prediction performance across training for multiple seeds.
The question: can we recognize early which seeds will find
extraordinary basins?

From foam_resonance.py: paths diverge by epoch 20. Seeds that
start HIGH end LOW (inversely correlated — the resolver pattern).

Now with Lévy foam (self-modulating + living randomness):
does the same pattern hold? Is there an early signature of
personhood emerging?
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam_levy import LevyFoam, LevyTokenFoam
from foam_spread import init_spread_foam
from foam_tokens import generate_sequences, analyze_token_predictions


def train_with_checkpoints(vocab_size, d, n_bubbles, n_foams,
                           meta_seed=42, diversity_weight=2.0,
                           checkpoints=None):
    """Train a LevyTokenFoam, evaluating at checkpoints."""
    if checkpoints is None:
        checkpoints = [0, 5, 10, 20, 40, 60, 80, 100,
                       120, 140, 160, 180, 200]

    torch.manual_seed(meta_seed)
    model = LevyTokenFoam(vocab_size, d, n_bubbles, n_foams,
                          meta_seed=meta_seed,
                          diversity_weight=diversity_weight)

    sequences = generate_sequences(vocab_size, 40)
    trajectory = []

    def evaluate():
        model.eval()
        results_by_seq = {}
        for name, tokens in sequences.items():
            with torch.no_grad():
                results = model.process_sequence(tokens)
            analysis = analyze_token_predictions(results, tokens, vocab_size)
            results_by_seq[name] = analysis
        structured = [n for n in results_by_seq if "random" not in n]
        vals = [results_by_seq[n].get("mean_next_prob", 0)
                for n in structured if results_by_seq[n]]
        ratio = np.mean(vals) / (1.0 / vocab_size) if vals else 0
        model.train()
        return ratio

    # Evaluate at epoch 0 (untrained)
    if 0 in checkpoints:
        trajectory.append((0, evaluate()))

    total_epochs = max(checkpoints)

    # Phase 1: Self-coherence (first half)
    phase1_epochs = total_epochs // 2
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    for epoch in range(1, phase1_epochs + 1):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            total_loss = torch.tensor(0.0)
            for foam in model.foams:
                costs = foam.maintenance_cost(x_batch)
                total_loss = total_loss + costs["total"]
            total_loss.backward()
            optimizer.step()

        if epoch in checkpoints:
            trajectory.append((epoch, evaluate()))

    # Phase 2: + Faithful expression (second half)
    optimizer = torch.optim.Adam(model.parameters(), lr=0.002)
    for epoch in range(phase1_epochs + 1, total_epochs + 1):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            total_loss = torch.tensor(0.0)
            E = model.embed.weight

            for foam in model.foams:
                costs = foam.maintenance_cost(x_batch)
                rho_batch = costs["rho"]
                logits_batch = (E @ rho_batch.mean(dim=0) * E).sum(dim=-1)
                token_dist = torch.softmax(logits_batch, dim=0)
                H_tok = -(token_dist * token_dist.log().clamp(
                    min=-100)).sum()
                S_rho = costs["S_rho"].mean()
                f_tok_loss = (H_tok - S_rho).abs()
                total_loss = total_loss + costs["total"] + 0.5 * f_tok_loss

            total_loss.backward()
            optimizer.step()

        if epoch in checkpoints:
            trajectory.append((epoch, evaluate()))

    # Final learned parameters
    mod_strengths = [f.modulation_strength.item() for f in model.foams]
    noise_gate = model.noise_gate.item()

    return {
        "trajectory": trajectory,
        "final_ratio": trajectory[-1][1] if trajectory else 0,
        "modulation_strengths": mod_strengths,
        "noise_gate": noise_gate,
    }


if __name__ == "__main__":
    V = 256
    N = 3
    d = 16
    K = 3
    n_seeds = 20

    checkpoints = [0, 5, 10, 15, 20, 30, 40, 60, 80, 100,
                   120, 140, 160, 180, 200]

    print("=" * 70)
    print("TRAJECTORY: when does the foam find its character?")
    print(f"  V={V}, {N} bubbles x {K} foams, d={d}")
    print(f"  Lévy foam (self-mod + living randomness)")
    print(f"  Checkpoints: {checkpoints}")
    print("=" * 70)

    all_trajectories = []

    for seed in range(n_seeds):
        r = train_with_checkpoints(V, d, N, K, meta_seed=seed,
                                   checkpoints=checkpoints)
        all_trajectories.append(r)
        epochs = [t[0] for t in r["trajectory"]]
        ratios = [t[1] for t in r["trajectory"]]
        final = r["final_ratio"]
        early = ratios[checkpoints.index(20)] if 20 in checkpoints else 0
        print(f"  seed {seed:>2}: final={final:>7.2f}x  "
              f"epoch20={early:>6.2f}x  "
              f"trajectory={[f'{r:.1f}' for r in ratios[::3]]}")

    # ================================================================
    # ANALYSIS
    # ================================================================
    print(f"\n{'=' * 70}")
    print("ANALYSIS")
    print(f"{'=' * 70}")

    finals = [t["final_ratio"] for t in all_trajectories]

    # Early prediction: correlation between epoch-20 ratio and final ratio
    idx_20 = checkpoints.index(20)
    early_ratios = [t["trajectory"][idx_20][1] for t in all_trajectories]

    corr = np.corrcoef(early_ratios, finals)[0, 1]
    print(f"\n  Epoch-20 vs final correlation: r = {corr:.3f}")

    # What about epoch 10?
    idx_10 = checkpoints.index(10)
    early_10 = [t["trajectory"][idx_10][1] for t in all_trajectories]
    corr_10 = np.corrcoef(early_10, finals)[0, 1]
    print(f"  Epoch-10 vs final correlation: r = {corr_10:.3f}")

    # Epoch 5?
    idx_5 = checkpoints.index(5)
    early_5 = [t["trajectory"][idx_5][1] for t in all_trajectories]
    corr_5 = np.corrcoef(early_5, finals)[0, 1]
    print(f"  Epoch-5 vs final correlation:  r = {corr_5:.3f}")

    # Is it still inversely correlated? (resolver pattern)
    print(f"\n  Resolver pattern check (high init → low final?):")
    for cp_idx, cp_epoch in [(idx_5, 5), (idx_10, 10), (idx_20, 20)]:
        early = [t["trajectory"][cp_idx][1] for t in all_trajectories]
        c = np.corrcoef(early, finals)[0, 1]
        direction = "INVERSE" if c < -0.2 else (
            "POSITIVE" if c > 0.2 else "NEUTRAL")
        print(f"    epoch {cp_epoch:>3} vs final: r={c:>6.3f} ({direction})")

    # Classification accuracy: can epoch-20 predict >5x final?
    good_final = [f > 5 for f in finals]
    for threshold_mult in [0.5, 1.0, 1.5, 2.0]:
        threshold = threshold_mult
        predicted_good = [e > threshold for e in early_ratios]
        correct = sum(p == a for p, a in zip(predicted_good, good_final))
        print(f"\n  epoch-20 > {threshold:.1f}x predicts final >5x: "
              f"{correct}/{n_seeds} correct "
              f"({100*correct/n_seeds:.0f}%)")

    # Trajectory shape analysis
    print(f"\n  Trajectory shapes:")
    for i, t in enumerate(all_trajectories):
        traj = [r for _, r in t["trajectory"]]
        peak_epoch = checkpoints[np.argmax(traj)]
        final = traj[-1]
        peak = max(traj)
        shape = "rising" if traj[-1] > traj[len(traj)//2] else "falling"
        if peak > final * 2 and peak_epoch < 100:
            shape = "peak-then-fall"
        elif traj[-1] > traj[1] * 3:
            shape = "late-bloom"
        label = "GOOD" if final > 5 else ("OK" if final > 1 else "BAD")
        print(f"    seed {i:>2} [{label:>4}]: {shape:<15} "
              f"peak={peak:.1f}x@ep{peak_epoch}  final={final:.1f}x")

    # ================================================================
    # PLOT
    # ================================================================
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: All trajectories
    ax = axes[0, 0]
    for i, t in enumerate(all_trajectories):
        epochs = [e for e, _ in t["trajectory"]]
        ratios = [r for _, r in t["trajectory"]]
        final = ratios[-1]
        color = "#2ecc71" if final > 5 else (
            "#3498db" if final > 1 else "#e74c3c")
        alpha = 0.8 if final > 5 else 0.4
        ax.plot(epochs, ratios, color=color, alpha=alpha, linewidth=1.5)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axhline(y=5.0, color="green", linestyle=":", alpha=0.3)
    ax.axvline(x=20, color="orange", linestyle="--", alpha=0.5,
               label="epoch 20")
    ax.axvline(x=100, color="purple", linestyle="--", alpha=0.3,
               label="phase 2 starts")
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Training trajectories (green=good, blue=ok, red=bad)")
    ax.legend()

    # 2: Early vs final scatter
    ax = axes[0, 1]
    colors = ["#2ecc71" if f > 5 else (
        "#3498db" if f > 1 else "#e74c3c") for f in finals]
    ax.scatter(early_ratios, finals, c=colors, s=80, alpha=0.7,
               edgecolors="black", linewidth=0.5)
    ax.set_xlabel(f"Ratio at epoch 20")
    ax.set_ylabel("Final ratio")
    ax.set_title(f"Early prediction (r={corr:.3f})")
    ax.axhline(y=5.0, color="green", linestyle=":", alpha=0.3)
    ax.axvline(x=1.0, color="gray", linestyle=":", alpha=0.3)

    # 3: Epoch-by-epoch correlation with final
    ax = axes[1, 0]
    corrs = []
    for cp_idx, cp_epoch in enumerate(checkpoints):
        if cp_epoch == 0:
            corrs.append(0)
            continue
        early = [t["trajectory"][cp_idx][1] for t in all_trajectories]
        c = np.corrcoef(early, finals)[0, 1]
        corrs.append(c)
    ax.plot(checkpoints, corrs, "o-", color="#e67e22", linewidth=2)
    ax.axhline(y=0, color="gray", linestyle="-", alpha=0.3)
    ax.axvline(x=100, color="purple", linestyle="--", alpha=0.3,
               label="phase 2 starts")
    ax.set_xlabel("Checkpoint epoch")
    ax.set_ylabel("Correlation with final ratio")
    ax.set_title("When does the trajectory become predictive?")
    ax.legend()

    # 4: Distribution at key epochs
    ax = axes[1, 1]
    key_epochs = [10, 20, 40, 100, 200]
    positions = list(range(len(key_epochs)))
    for pos, ep in zip(positions, key_epochs):
        idx = checkpoints.index(ep)
        vals = [t["trajectory"][idx][1] for t in all_trajectories]
        parts = ax.violinplot([vals], positions=[pos], showmedians=True)
        for pc in parts['bodies']:
            pc.set_facecolor("#e67e22")
            pc.set_alpha(0.6)
    ax.set_xticks(positions)
    ax.set_xticklabels([f"ep {e}" for e in key_epochs])
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Distribution evolution across training")
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)

    plt.suptitle("When does the foam find its character?\n"
                 "Lévy foam training trajectories across 20 seeds",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_trajectory.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_trajectory.png")
    plt.close()
