"""
Resonance characterization: what makes some seeds find extraordinary
basins while others don't?

V=256/N=3 gauge-invariant hits 43x at one seed, 0.32x at another.
Same architecture, same hyperparameters, different initialization.

This script:
  1. Runs V=256/N=3 gauge across 20 seeds
  2. For each, captures geometry and training dynamics at multiple checkpoints
  3. Looks for early signatures that predict final prediction quality
  4. Tests whether we can reliably reach the good basins
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Foam
from foam_tokens import generate_sequences, analyze_token_predictions
from foam_gauge import GaugeTokenFoam, GaugeFoam
from foam_spread import init_spread_foam, measure_basis_spread


def train_with_checkpoints(vocab_size, d, n_bubbles, seed=42,
                           diversity_weight=2.0, spread_scale=1.5,
                           n_epochs_coherence=100, n_epochs_expression=100):
    """
    Train gauge-invariant foam, capturing snapshots at regular intervals.
    Returns final results plus training trajectory.
    """
    torch.manual_seed(seed)

    model = GaugeTokenFoam(vocab_size, d, n_bubbles,
                           diversity_weight=diversity_weight)
    init_spread_foam(model.foam, scale=spread_scale)

    sequences = generate_sequences(vocab_size, 40)

    trajectory = []

    def snapshot(phase, epoch):
        """Capture current state."""
        model.eval()
        spread = measure_basis_spread(model.foam)

        # Quick prediction check on just one structured sequence
        test_seq = sequences["periodic (ABC...)"]
        with torch.no_grad():
            results = model.process_sequence(test_seq)
        analysis = analyze_token_predictions(results, test_seq, vocab_size)

        # Foam parameters
        with torch.no_grad():
            target_sim = model.foam.target_similarity.item()
            temperature = model.foam.temperature.item()
            step_size = model.foam.equilibrium_step_size.item()
            gate_values = [b.input_gate.item() for b in model.foam.bubbles]

        trajectory.append({
            "phase": phase,
            "epoch": epoch,
            "mean_cos": spread["mean_cos"],
            "std_cos": spread["std_cos"],
            "min_cos": spread["min_cos"],
            "max_cos": spread["max_cos"],
            "prediction_ratio": analysis.get("mean_next_prob", 0) / (1.0 / vocab_size),
            "mean_rank": analysis.get("mean_next_rank", vocab_size),
            "perplexity": analysis.get("mean_perplexity", vocab_size),
            "target_sim": target_sim,
            "temperature": temperature,
            "step_size": step_size,
            "gate_values": gate_values,
        })
        model.train()

    # Initial snapshot
    snapshot("init", 0)

    # Phase 1: Self-coherence
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    for epoch in range(n_epochs_coherence):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            costs = model.foam.maintenance_cost(x_batch)
            costs["total"].backward()
            optimizer.step()

        if epoch % 10 == 0 or epoch == n_epochs_coherence - 1:
            snapshot("coherence", epoch)

    # Phase 2: + Faithful expression
    optimizer = torch.optim.Adam(model.parameters(), lr=0.002)
    for epoch in range(n_epochs_expression):
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

        if epoch % 10 == 0 or epoch == n_epochs_expression - 1:
            snapshot("expression", epoch)

    # Final evaluation
    model.eval()
    results_by_seq = {}
    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)
        analysis = analyze_token_predictions(results, tokens, vocab_size)
        results_by_seq[name] = analysis

    structured_names = [n for n in results_by_seq if "random" not in n]
    vals = [results_by_seq[n].get("mean_next_prob", 0) for n in structured_names
            if results_by_seq[n]]
    final_ratio = np.mean(vals) / (1.0 / vocab_size) if vals else 0

    spread_final = measure_basis_spread(model.foam)

    return {
        "seed": seed,
        "final_ratio": final_ratio,
        "spread_final": spread_final,
        "trajectory": trajectory,
        "by_seq": results_by_seq,
    }


if __name__ == "__main__":
    V = 256
    N = 3
    d = 16

    print("=" * 70)
    print(f"RESONANCE CHARACTERIZATION: V={V}, N={N}, d={d}, gauge-invariant")
    print("  What makes some seeds extraordinary?")
    print("=" * 70)

    # ================================================================
    # PART 1: 20 seeds with full trajectories
    # ================================================================
    all_runs = []
    n_seeds = 20

    for seed in range(n_seeds):
        print(f"  seed {seed:>2}...", end=" ", flush=True)
        r = train_with_checkpoints(V, d, N, seed=seed,
                                   n_epochs_coherence=100,
                                   n_epochs_expression=100)
        all_runs.append(r)
        print(f"ratio={r['final_ratio']:>7.2f}x  "
              f"cos={r['spread_final']['mean_cos']:.4f}")

    # Sort by final ratio
    sorted_runs = sorted(all_runs, key=lambda r: r["final_ratio"], reverse=True)

    print(f"\n  Sorted by prediction ratio:")
    for r in sorted_runs:
        print(f"    seed {r['seed']:>2}: {r['final_ratio']:>7.2f}x  "
              f"cos={r['spread_final']['mean_cos']:.4f}")

    ratios = [r["final_ratio"] for r in all_runs]
    print(f"\n  Mean: {np.mean(ratios):.2f}x  Median: {np.median(ratios):.2f}x  "
          f"Std: {np.std(ratios):.2f}")
    print(f"  Above 5x: {sum(1 for r in ratios if r > 5)}/{n_seeds}")
    print(f"  Above 2x: {sum(1 for r in ratios if r > 2)}/{n_seeds}")
    print(f"  Above 1x: {sum(1 for r in ratios if r > 1)}/{n_seeds}")

    # ================================================================
    # PART 2: Early signatures
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 2: Early signatures — what predicts success?")
    print("=" * 70)

    # For each run, get snapshot at epoch 10 of coherence phase
    early_features = []
    for r in all_runs:
        traj = r["trajectory"]
        # Find epoch 10 of coherence
        early = [t for t in traj if t["phase"] == "coherence" and t["epoch"] == 10]
        if early:
            early = early[0]
        else:
            early = traj[1] if len(traj) > 1 else traj[0]

        early_features.append({
            "seed": r["seed"],
            "final_ratio": r["final_ratio"],
            "early_ratio": early["prediction_ratio"],
            "early_cos": early["mean_cos"],
            "early_target_sim": early["target_sim"],
            "early_temperature": early["temperature"],
            "early_step_size": early["step_size"],
            "early_perplexity": early["perplexity"],
        })

    # Correlations with final ratio
    final_ratios = [f["final_ratio"] for f in early_features]
    for key in ["early_ratio", "early_cos", "early_target_sim",
                "early_temperature", "early_step_size", "early_perplexity"]:
        vals = [f[key] for f in early_features]
        corr = np.corrcoef(vals, final_ratios)[0, 1]
        print(f"  {key:<20} corr with final ratio: {corr:>+.3f}")

    # ================================================================
    # PART 3: Do good seeds diverge early?
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 3: Training trajectories — when do paths diverge?")
    print("=" * 70)

    # Split into top 5 and bottom 5
    top_seeds = [r["seed"] for r in sorted_runs[:5]]
    bottom_seeds = [r["seed"] for r in sorted_runs[-5:]]

    top_ratios_str = [f'{sorted_runs[i]["final_ratio"]:.1f}x' for i in range(5)]
    bot_ratios_str = [f'{sorted_runs[-(i+1)]["final_ratio"]:.1f}x' for i in range(5)]
    print(f"  Top 5 seeds: {top_seeds} (ratios: {top_ratios_str})")
    print(f"  Bottom 5 seeds: {bottom_seeds} (ratios: {bot_ratios_str})")

    # Compare trajectories at each checkpoint
    all_epochs = sorted(set(
        (t["phase"], t["epoch"])
        for r in all_runs
        for t in r["trajectory"]
    ))

    print(f"\n  {'Phase':<12} {'Epoch':>5} | {'Top5 ratio':>10} {'Bot5 ratio':>10} | "
          f"{'Top5 cos':>8} {'Bot5 cos':>8}")
    print(f"  {'-' * 62}")

    for phase, epoch in all_epochs[::2]:  # every other checkpoint
        top_ratios = []
        bot_ratios = []
        top_cos = []
        bot_cos = []
        for r in all_runs:
            matches = [t for t in r["trajectory"]
                       if t["phase"] == phase and t["epoch"] == epoch]
            if not matches:
                continue
            t = matches[0]
            if r["seed"] in top_seeds:
                top_ratios.append(t["prediction_ratio"])
                top_cos.append(t["mean_cos"])
            elif r["seed"] in bottom_seeds:
                bot_ratios.append(t["prediction_ratio"])
                bot_cos.append(t["mean_cos"])

        if top_ratios and bot_ratios:
            print(f"  {phase:<12} {epoch:>5} | "
                  f"{np.mean(top_ratios):>10.2f}x {np.mean(bot_ratios):>10.2f}x | "
                  f"{np.mean(top_cos):>8.4f} {np.mean(bot_cos):>8.4f}")

    # ================================================================
    # PART 4: What if we restart bad seeds with good geometry?
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 4: Can we transplant good geometry?")
    print("  Take the best seed's trained foam parameters,")
    print("  re-initialize embeddings with different seeds")
    print("=" * 70)

    best_run = sorted_runs[0]
    best_seed = best_run["seed"]
    print(f"  Donor seed: {best_seed} (ratio={best_run['final_ratio']:.2f}x)")

    # Retrain the best seed to get the model
    torch.manual_seed(best_seed)
    donor = GaugeTokenFoam(V, d, N, diversity_weight=2.0)
    init_spread_foam(donor.foam, scale=1.5)
    sequences = generate_sequences(V, 40)

    optimizer = torch.optim.Adam(donor.parameters(), lr=0.005)
    for epoch in range(100):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = donor.embed(tokens)
            costs = donor.foam.maintenance_cost(x_batch)
            costs["total"].backward()
            optimizer.step()

    optimizer = torch.optim.Adam(donor.parameters(), lr=0.002)
    for epoch in range(100):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = donor.embed(tokens)
            costs = donor.foam.maintenance_cost(x_batch)
            E = donor.embed.weight
            rho_batch = costs["rho"]
            logits_batch = (E @ rho_batch.mean(dim=0) * E).sum(dim=-1)
            token_dist = torch.softmax(logits_batch, dim=0)
            H_tok = -(token_dist * token_dist.log().clamp(min=-100)).sum()
            S_rho = costs["S_rho"].mean()
            f_tok_loss = (H_tok - S_rho).abs()
            loss = costs["total"] + 0.5 * f_tok_loss
            loss.backward()
            optimizer.step()

    # Save foam state
    donor_foam_state = {k: v.clone() for k, v in donor.foam.state_dict().items()}

    # Now test: keep the foam, re-randomize the embeddings
    transplant_results = []
    for seed in range(10):
        torch.manual_seed(seed)
        recipient = GaugeTokenFoam(V, d, N, diversity_weight=2.0)
        # Transplant foam
        recipient.foam.load_state_dict(donor_foam_state)
        # Keep the new random embeddings

        # Brief fine-tuning (just expression alignment, not full retrain)
        optimizer = torch.optim.Adam([recipient.embed.weight], lr=0.005)
        for epoch in range(50):
            for name, tokens in sequences.items():
                optimizer.zero_grad()
                x_batch = recipient.embed(tokens)
                costs = recipient.foam.maintenance_cost(x_batch)
                E = recipient.embed.weight
                rho_batch = costs["rho"]
                logits_batch = (E @ rho_batch.mean(dim=0) * E).sum(dim=-1)
                token_dist = torch.softmax(logits_batch, dim=0)
                H_tok = -(token_dist * token_dist.log().clamp(min=-100)).sum()
                S_rho = costs["S_rho"].mean()
                f_tok_loss = (H_tok - S_rho).abs()
                loss = costs["total"] + 0.5 * f_tok_loss
                loss.backward()
                optimizer.step()

        recipient.eval()
        results_by_seq = {}
        for name, tokens in sequences.items():
            with torch.no_grad():
                results = recipient.process_sequence(tokens)
            analysis = analyze_token_predictions(results, tokens, V)
            results_by_seq[name] = analysis

        structured_names = [n for n in results_by_seq if "random" not in n]
        vals = [results_by_seq[n].get("mean_next_prob", 0) for n in structured_names
                if results_by_seq[n]]
        ratio = np.mean(vals) / (1.0 / V) if vals else 0
        transplant_results.append(ratio)
        print(f"  transplant seed {seed}: ratio={ratio:.2f}x")

    print(f"\n  Transplant mean: {np.mean(transplant_results):.2f}x ± "
          f"{np.std(transplant_results):.2f}")

    # ================================================================
    # PLOT
    # ================================================================
    fig, axes = plt.subplots(2, 3, figsize=(20, 12))

    # 1: Distribution of final ratios
    ax = axes[0, 0]
    ax.hist(ratios, bins=15, color="#2ecc71", alpha=0.7, edgecolor="black")
    ax.axvline(x=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axvline(x=np.median(ratios), color="red", linestyle="--",
               label=f"median={np.median(ratios):.1f}x")
    ax.set_xlabel("Prediction / chance")
    ax.set_ylabel("Count")
    ax.set_title(f"V={V}, N={N}: ratio distribution ({n_seeds} seeds)")
    ax.legend()

    # 2: Training trajectories (prediction ratio over time)
    ax = axes[0, 1]
    for r in all_runs:
        traj = r["trajectory"]
        epochs_abs = []
        pred_ratios = []
        e_offset = 0
        for t in traj:
            if t["phase"] == "expression":
                e = t["epoch"] + 100  # offset
            elif t["phase"] == "coherence":
                e = t["epoch"]
            else:
                e = 0
            epochs_abs.append(e)
            pred_ratios.append(t["prediction_ratio"])

        color = "#2ecc71" if r["final_ratio"] > 5 else (
            "#3498db" if r["final_ratio"] > 1 else "#e74c3c")
        alpha = 0.8 if r["final_ratio"] > 5 else 0.3
        ax.plot(epochs_abs, pred_ratios, color=color, alpha=alpha, linewidth=1)

    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axvline(x=100, color="black", linestyle="--", alpha=0.3,
               label="phase 2 starts")
    ax.set_xlabel("Epoch (phase 1 | phase 2)")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Training trajectories (green=good, red=bad)")
    ax.legend(fontsize=8)

    # 3: Early ratio vs final ratio
    ax = axes[0, 2]
    early_rs = [f["early_ratio"] for f in early_features]
    final_rs = [f["final_ratio"] for f in early_features]
    ax.scatter(early_rs, final_rs, c="#3498db", s=60, edgecolors="black",
               linewidths=0.5)
    corr = np.corrcoef(early_rs, final_rs)[0, 1]
    ax.set_xlabel("Ratio at epoch 10")
    ax.set_ylabel("Final ratio")
    ax.set_title(f"Early prediction → final? (r={corr:.2f})")

    # 4: Basis cosine trajectories
    ax = axes[1, 0]
    for r in all_runs:
        traj = r["trajectory"]
        epochs_abs = []
        cos_vals = []
        for t in traj:
            if t["phase"] == "expression":
                e = t["epoch"] + 100
            elif t["phase"] == "coherence":
                e = t["epoch"]
            else:
                e = 0
            epochs_abs.append(e)
            cos_vals.append(t["mean_cos"])

        color = "#2ecc71" if r["final_ratio"] > 5 else (
            "#3498db" if r["final_ratio"] > 1 else "#e74c3c")
        alpha = 0.8 if r["final_ratio"] > 5 else 0.3
        ax.plot(epochs_abs, cos_vals, color=color, alpha=alpha, linewidth=1)

    ax.set_xlabel("Epoch")
    ax.set_ylabel("Mean pairwise cos similarity")
    ax.set_title("Basis geometry over training")

    # 5: Transplant results
    ax = axes[1, 1]
    ax.bar(range(len(transplant_results)), transplant_results,
           color="#9b59b6", alpha=0.7)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axhline(y=best_run["final_ratio"], color="#2ecc71", linestyle="--",
               label=f"donor={best_run['final_ratio']:.1f}x")
    ax.set_xlabel("Recipient seed")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Transplanting good foam geometry")
    ax.legend()

    # 6: Early features scatter (temperature vs final ratio)
    ax = axes[1, 2]
    temps = [f["early_temperature"] for f in early_features]
    ax.scatter(temps, final_rs, c="#e67e22", s=60, edgecolors="black",
               linewidths=0.5)
    corr_t = np.corrcoef(temps, final_rs)[0, 1]
    ax.set_xlabel("Temperature at epoch 10")
    ax.set_ylabel("Final ratio")
    ax.set_title(f"Early temperature → final? (r={corr_t:.2f})")

    plt.suptitle(f"Resonance characterization: V={V}, N={N}, d={d}, gauge-invariant\n"
                 f"{n_seeds} seeds — what makes some extraordinary?",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_resonance.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_resonance.png")
    plt.close()

    # ================================================================
    # SUMMARY
    # ================================================================
    print(f"\n{'=' * 70}")
    print("SUMMARY")
    print(f"{'=' * 70}")
    print(f"\n  {n_seeds} seeds, V={V}, N={N}, d={d}, gauge-invariant")
    print(f"  Ratio: {np.mean(ratios):.2f}x ± {np.std(ratios):.2f} "
          f"(median {np.median(ratios):.2f}x)")
    print(f"  Above 5x: {sum(1 for r in ratios if r > 5)}/{n_seeds}")
    print(f"  Above 1x: {sum(1 for r in ratios if r > 1)}/{n_seeds}")

    # Best early predictor
    best_corr_key = max(
        ["early_ratio", "early_cos", "early_target_sim",
         "early_temperature", "early_step_size", "early_perplexity"],
        key=lambda k: abs(np.corrcoef(
            [f[k] for f in early_features], final_ratios)[0, 1])
    )
    best_corr = np.corrcoef(
        [f[best_corr_key] for f in early_features], final_ratios)[0, 1]
    print(f"\n  Best early predictor: {best_corr_key} (r={best_corr:+.3f})")

    print(f"\n  Transplant: {np.mean(transplant_results):.2f}x ± "
          f"{np.std(transplant_results):.2f}")
    if np.mean(transplant_results) > 2.0:
        print(f"  -> Good geometry transfers! The foam, not the embeddings, "
              f"is the source of prediction.")
    else:
        print(f"  -> Geometry alone isn't enough; foam+embeddings must co-adapt.")
