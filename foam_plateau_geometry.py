"""
Plateau geometry investigation: does bubble configuration stability
explain the cycling in prediction quality?

The foam uses Plateau-angle equilibration (target_similarity = cos(120°) = -0.5).
Plateau's laws say:
  - Three films meet at each edge at 120°
  - Only 3-fold edges and 4-fold vertices are stable
  - In d dimensions, at most d+1 equidistant points fit (simplex vertices)

Hypothesis: prediction quality peaks when two conditions are simultaneously met:
  (a) the bubble bases can form a Plateau-stable configuration in d dimensions
  (b) the embedding has enough capacity for V tokens in d dimensions

The cycling comes from interference between these two rhythms.

This script:
  1. Measures actual pairwise cosine similarities between trained bubble bases
  2. Computes deviation from theoretical Plateau angle
  3. Checks correlation between Plateau stability and prediction quality
  4. Tests seed robustness of the V=64/N=8 spike
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Foam
from foam_tokens import TokenFoam, generate_sequences, analyze_token_predictions


def measure_plateau_geometry(foam):
    """
    Measure the actual geometry of a foam's bubble bases.

    Returns:
      - pairwise cosine similarities between bases (flattened)
      - mean cosine similarity
      - deviation from target_similarity (the foam's learned Plateau angle)
      - deviation from cos(120°) = -0.5 (the classic Plateau angle)
      - whether the configuration is Plateau-stable (all angles near 120°)
    """
    N = foam.n_bubbles
    d = foam.d

    # Get the bases
    with torch.no_grad():
        bases = torch.stack([b.basis for b in foam.bubbles])  # [N, d, d]
        # Flatten each basis to a vector for cosine similarity
        flat = bases.reshape(N, -1)  # [N, d*d]
        flat_norm = flat / (flat.norm(dim=-1, keepdim=True) + 1e-10)
        cos_sim_matrix = flat_norm @ flat_norm.T  # [N, N]

        # Also measure in measurement space: how do the bases' columns relate?
        # Each basis U_i has columns that span the measurement directions.
        # The "orientation" of bubble i relative to j is captured by U_i^T U_j
        # whose singular values tell us how aligned their measurement axes are.
        alignment_scores = torch.zeros(N, N)
        for i in range(N):
            for j in range(N):
                if i == j:
                    alignment_scores[i, j] = 1.0
                    continue
                product = bases[i].T @ bases[j]  # [d, d]
                # Frobenius norm of (product - I) measures misalignment
                # but trace/d measures average alignment
                alignment_scores[i, j] = product.trace() / d

    # Extract off-diagonal elements
    mask = ~torch.eye(N, dtype=torch.bool)
    off_diag_cos = cos_sim_matrix[mask].numpy()
    off_diag_align = alignment_scores[mask].numpy()

    target_sim = foam.target_similarity.item()
    classic_plateau = -0.5  # cos(120°)

    # Theoretical: for N equidistant points in d dimensions,
    # the cosine similarity between any pair should be -1/(N-1)
    # (this is the simplex angle in the embedding space)
    simplex_angle = -1.0 / (N - 1) if N > 1 else 0.0

    return {
        "cos_sim_matrix": cos_sim_matrix.numpy(),
        "alignment_matrix": alignment_scores.numpy(),
        "mean_cos_sim": np.mean(off_diag_cos),
        "std_cos_sim": np.std(off_diag_cos),
        "mean_alignment": np.mean(off_diag_align),
        "deviation_from_target": np.mean(np.abs(off_diag_cos - target_sim)),
        "deviation_from_plateau": np.mean(np.abs(off_diag_cos - classic_plateau)),
        "deviation_from_simplex": np.mean(np.abs(off_diag_cos - simplex_angle)),
        "learned_target": target_sim,
        "simplex_angle": simplex_angle,
        "n_bubbles": N,
        "d": d,
        # Can N equidistant points fit in d dimensions?
        # Simplex: need N ≤ d+1 for a regular simplex in d dimensions
        "simplex_feasible": N <= d + 1,
        # For the flattened basis vectors (d*d dimensional),
        # any N can form a simplex if N ≤ d*d + 1
        "simplex_feasible_flat": N <= d * d + 1,
    }


def plateau_stability_score(geometry):
    """
    A single score measuring how Plateau-stable the configuration is.

    Lower = more stable. Based on:
    1. Are the pairwise similarities uniform? (low std)
    2. Are they near the simplex angle for N points? (low deviation)
    """
    # Uniformity: how equal are all pairwise angles?
    uniformity = geometry["std_cos_sim"]
    # Optimality: how close to the best achievable angle (simplex)?
    optimality = geometry["deviation_from_simplex"]
    return uniformity + optimality


def train_and_measure(vocab_size, d, n_bubbles, seed=42,
                      n_epochs_coherence=150, n_epochs_expression=150,
                      seq_len=40):
    """Train a TokenFoam, measure its geometry, and evaluate prediction."""
    torch.manual_seed(seed)
    model = TokenFoam(vocab_size, d, n_bubbles, n_equilibrium_steps=5)
    sequences = generate_sequences(vocab_size, seq_len)

    # Phase 1: Self-coherence
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    for epoch in range(n_epochs_coherence):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            costs = model.foam.maintenance_cost(x_batch)
            costs["total"].backward()
            optimizer.step()

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

    # Measure geometry
    model.eval()
    geometry = measure_plateau_geometry(model.foam)
    stability = plateau_stability_score(geometry)

    # Evaluate prediction
    results_by_seq = {}
    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)
        analysis = analyze_token_predictions(results, tokens, vocab_size)
        results_by_seq[name] = analysis

    structured_names = [n for n in results_by_seq if "random" not in n]

    def safe_mean(names, key):
        vals = [results_by_seq[n].get(key, 0) for n in names
                if results_by_seq[n]]
        return np.mean(vals) if vals else 0

    prediction_ratio = safe_mean(structured_names, "mean_next_prob") / (1.0 / vocab_size)

    return {
        "vocab_size": vocab_size,
        "d": d,
        "n_bubbles": n_bubbles,
        "seed": seed,
        "geometry": geometry,
        "stability": stability,
        "prediction_ratio": prediction_ratio,
        "structured_next_prob": safe_mean(structured_names, "mean_next_prob"),
    }


if __name__ == "__main__":
    # ================================================================
    # PART 1: Geometry across (V, N, d) — the configurations from scaling
    # ================================================================
    print("=" * 70)
    print("PART 1: Plateau geometry across configurations")
    print("  Measuring actual bubble base angles after training")
    print("=" * 70)

    d = 16
    configs = [
        (8, 3), (8, 5), (8, 8),
        (16, 3), (16, 5), (16, 8),
        (32, 3), (32, 5), (32, 8),
        (64, 3), (64, 5), (64, 8),
        (128, 3), (128, 8),
        (256, 3), (256, 8),
    ]

    all_results = []
    print(f"\n  {'V':>5} {'N':>3} {'Ratio':>7} {'Stab':>7} "
          f"{'MeanCos':>8} {'StdCos':>7} {'DevSimp':>8} {'Simplex?':>9} "
          f"{'Target':>7}")
    print(f"  {'-' * 75}")

    for V, N in configs:
        epochs = 150 if V <= 128 else 100
        print(f"  V={V}, N={N}...", end=" ", flush=True)
        r = train_and_measure(V, d, N, n_epochs_coherence=epochs,
                              n_epochs_expression=epochs)
        all_results.append(r)
        g = r["geometry"]
        print(f"\r  {V:>5} {N:>3} {r['prediction_ratio']:>7.2f}x "
              f"{r['stability']:>7.3f} {g['mean_cos_sim']:>8.4f} "
              f"{g['std_cos_sim']:>7.4f} {g['deviation_from_simplex']:>8.4f} "
              f"{'yes' if g['simplex_feasible'] else 'NO':>9} "
              f"{g['learned_target']:>7.3f}")

    # ================================================================
    # PART 2: Seed robustness of V=64/N=8 spike
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 2: Seed robustness — V=64, N=8, d=16")
    print("  Is the spike real or seed-specific?")
    print("=" * 70)

    seed_results = []
    for seed in range(5):
        print(f"  seed={seed}...", end=" ", flush=True)
        r = train_and_measure(64, 16, 8, seed=seed)
        seed_results.append(r)
        g = r["geometry"]
        print(f"ratio={r['prediction_ratio']:.2f}x  "
              f"stability={r['stability']:.3f}  "
              f"mean_cos={g['mean_cos_sim']:.4f}")

    ratios = [r["prediction_ratio"] for r in seed_results]
    print(f"\n  Ratios across seeds: {[f'{r:.2f}' for r in ratios]}")
    print(f"  Mean: {np.mean(ratios):.2f}x  Std: {np.std(ratios):.2f}")
    if np.mean(ratios) > 2.0:
        print(f"  -> The spike is ROBUST across seeds")
    elif np.mean(ratios) > 1.0:
        print(f"  -> Moderate signal, partially seed-dependent")
    else:
        print(f"  -> Spike was seed-specific noise")

    # ================================================================
    # PART 3: Correlation analysis
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 3: Does Plateau stability predict prediction quality?")
    print("=" * 70)

    stabilities = [r["stability"] for r in all_results]
    pred_ratios = [r["prediction_ratio"] for r in all_results]

    # Pearson correlation
    if len(stabilities) > 2:
        corr = np.corrcoef(stabilities, pred_ratios)[0, 1]
        print(f"\n  Correlation(stability, prediction_ratio) = {corr:.3f}")
        if abs(corr) > 0.5:
            direction = "NEGATIVE" if corr < 0 else "POSITIVE"
            print(f"  -> {direction} correlation: "
                  f"{'lower' if corr < 0 else 'higher'} stability = "
                  f"{'better' if corr < 0 else 'worse'} prediction")
        else:
            print(f"  -> Weak correlation — stability alone doesn't explain it")

    # Embedding quality proxy: d/V ratio (higher = less crowded)
    dv_ratios = [r["d"] / r["vocab_size"] for r in all_results]
    if len(dv_ratios) > 2:
        corr_dv = np.corrcoef(dv_ratios, pred_ratios)[0, 1]
        print(f"  Correlation(d/V ratio, prediction_ratio) = {corr_dv:.3f}")

    # Combined: stability * (d/V)
    combined = [s * dv for s, dv in zip(stabilities, dv_ratios)]
    if len(combined) > 2:
        corr_comb = np.corrcoef(combined, pred_ratios)[0, 1]
        print(f"  Correlation(stability × d/V, prediction_ratio) = {corr_comb:.3f}")

    # Simplex feasibility check
    feasible = [r for r in all_results if r["geometry"]["simplex_feasible"]]
    infeasible = [r for r in all_results if not r["geometry"]["simplex_feasible"]]
    if feasible and infeasible:
        mean_f = np.mean([r["prediction_ratio"] for r in feasible])
        mean_i = np.mean([r["prediction_ratio"] for r in infeasible])
        print(f"\n  Simplex-feasible configs (N ≤ d+1={d+1}): "
              f"mean ratio = {mean_f:.2f}x  (n={len(feasible)})")
        print(f"  Simplex-infeasible configs (N > d+1):   "
              f"mean ratio = {mean_i:.2f}x  (n={len(infeasible)})")

    # ================================================================
    # PART 4: Simplex initialization test
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 4: Does initializing at simplex vertices help?")
    print("  Testing V=64, N=3 (always fits) and N=8")
    print("=" * 70)

    def make_simplex_foam(vocab_size, d, n_bubbles, n_equilibrium_steps=5):
        """Create a TokenFoam with bubble bases initialized at simplex vertices."""
        model = TokenFoam(vocab_size, d, n_bubbles, n_equilibrium_steps)

        # Initialize bubble bases at simplex-like orientations
        # For N bases in O(d), we want them equally spaced
        # Strategy: start from identity, rotate each by a known angle
        with torch.no_grad():
            for i, bubble in enumerate(model.foam.bubbles):
                # Create a rotation that's i/(N) of the way around a great circle
                # in the Lie algebra so(d)
                angle = 2 * np.pi * i / n_bubbles
                # Use a fixed generator (rotation in the 0-1 plane)
                A = torch.zeros(d, d)
                # Distribute rotations across multiple planes
                for k in range(min(d // 2, 3)):
                    plane_angle = angle * (k + 1) / 3
                    p, q = 2 * k, 2 * k + 1
                    A[p, q] = plane_angle
                    A[q, p] = -plane_angle
                # Set L so that L - L^T = A (L = A/2 works since A is skew)
                bubble.L.data = A / 2

        return model

    for V, N in [(64, 3), (64, 8)]:
        # Standard initialization
        torch.manual_seed(42)
        r_standard = train_and_measure(V, d, N, seed=42)

        # Simplex initialization
        torch.manual_seed(42)
        model_simplex = make_simplex_foam(V, d, N)
        sequences = generate_sequences(V, 40)

        optimizer = torch.optim.Adam(model_simplex.parameters(), lr=0.005)
        for epoch in range(150):
            for name, tokens in sequences.items():
                optimizer.zero_grad()
                x_batch = model_simplex.embed(tokens)
                costs = model_simplex.foam.maintenance_cost(x_batch)
                costs["total"].backward()
                optimizer.step()

        optimizer = torch.optim.Adam(model_simplex.parameters(), lr=0.002)
        for epoch in range(150):
            for name, tokens in sequences.items():
                optimizer.zero_grad()
                x_batch = model_simplex.embed(tokens)
                costs = model_simplex.foam.maintenance_cost(x_batch)
                E = model_simplex.embed.weight
                rho_batch = costs["rho"]
                logits_batch = (E @ rho_batch.mean(dim=0) * E).sum(dim=-1)
                token_dist = torch.softmax(logits_batch, dim=0)
                H_tok = -(token_dist * token_dist.log().clamp(min=-100)).sum()
                S_rho = costs["S_rho"].mean()
                f_tok_loss = (H_tok - S_rho).abs()
                loss = costs["total"] + 0.5 * f_tok_loss
                loss.backward()
                optimizer.step()

        model_simplex.eval()
        geometry_simplex = measure_plateau_geometry(model_simplex.foam)

        # Evaluate
        results_by_seq = {}
        for name, tokens in sequences.items():
            with torch.no_grad():
                results = model_simplex.process_sequence(tokens)
            analysis = analyze_token_predictions(results, tokens, V)
            results_by_seq[name] = analysis

        structured_names = [n for n in results_by_seq if "random" not in n]
        vals = [results_by_seq[n].get("mean_next_prob", 0) for n in structured_names
                if results_by_seq[n]]
        ratio_simplex = np.mean(vals) / (1.0 / V) if vals else 0

        g_std = r_standard["geometry"]
        print(f"\n  V={V}, N={N}:")
        print(f"    Standard init:  ratio={r_standard['prediction_ratio']:.2f}x  "
              f"stability={r_standard['stability']:.3f}  "
              f"mean_cos={g_std['mean_cos_sim']:.4f}")
        print(f"    Simplex init:   ratio={ratio_simplex:.2f}x  "
              f"stability={plateau_stability_score(geometry_simplex):.3f}  "
              f"mean_cos={geometry_simplex['mean_cos_sim']:.4f}")

    # ================================================================
    # PLOT
    # ================================================================
    fig, axes = plt.subplots(2, 3, figsize=(20, 12))

    # 1: Stability vs prediction ratio (scatter)
    ax = axes[0, 0]
    for r in all_results:
        color = plt.cm.viridis(r["vocab_size"] / 256)
        marker = "o" if r["geometry"]["simplex_feasible"] else "x"
        ax.scatter(r["stability"], r["prediction_ratio"],
                   c=[color], marker=marker, s=80, edgecolors="black",
                   linewidths=0.5)
        ax.annotate(f"V{r['vocab_size']}N{r['n_bubbles']}",
                    (r["stability"], r["prediction_ratio"]),
                    fontsize=6, alpha=0.7)
    ax.set_xlabel("Plateau instability (lower = more stable)")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Stability vs prediction quality")
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)

    # 2: Cosine similarity distributions by config
    ax = axes[0, 1]
    labels = []
    data = []
    for r in all_results:
        g = r["geometry"]
        cos_matrix = g["cos_sim_matrix"]
        N = g["n_bubbles"]
        mask = ~np.eye(N, dtype=bool)
        off_diag = cos_matrix[mask]
        data.append(off_diag)
        labels.append(f"V{r['vocab_size']}N{N}")
    ax.boxplot(data, labels=labels, vert=True)
    ax.set_xticklabels(labels, rotation=90, fontsize=6)
    ax.axhline(y=-0.5, color="red", linestyle="--", alpha=0.5, label="cos(120°)")
    ax.set_ylabel("Pairwise cosine similarity")
    ax.set_title("Bubble base angles (off-diagonal)")
    ax.legend(fontsize=7)

    # 3: Learned target similarity
    ax = axes[0, 2]
    vs = [r["vocab_size"] for r in all_results]
    ns = [r["n_bubbles"] for r in all_results]
    targets = [r["geometry"]["learned_target"] for r in all_results]
    for i, r in enumerate(all_results):
        ax.scatter(r["n_bubbles"], r["geometry"]["learned_target"],
                   c=[plt.cm.viridis(r["vocab_size"] / 256)], s=80,
                   edgecolors="black", linewidths=0.5)
    ax.axhline(y=-0.5, color="red", linestyle="--", alpha=0.5, label="cos(120°)")
    ax.set_xlabel("N (bubbles)")
    ax.set_ylabel("Learned target similarity")
    ax.set_title("Where does the foam settle?")
    ax.legend(fontsize=7)

    # 4: Seed robustness
    ax = axes[1, 0]
    seeds = list(range(len(seed_results)))
    ratios = [r["prediction_ratio"] for r in seed_results]
    stabs = [r["stability"] for r in seed_results]
    ax.bar(seeds, ratios, color="#3498db", alpha=0.8)
    ax.set_xlabel("Seed")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("V=64, N=8: seed robustness")
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax2 = ax.twinx()
    ax2.plot(seeds, stabs, "ro-", markersize=6)
    ax2.set_ylabel("Stability", color="red")

    # 5: Simplex feasibility comparison
    ax = axes[1, 1]
    if feasible and infeasible:
        feas_ratios = [r["prediction_ratio"] for r in feasible]
        infeas_ratios = [r["prediction_ratio"] for r in infeasible]
        positions = [1, 2]
        bp = ax.boxplot([feas_ratios, infeas_ratios], positions=positions,
                        labels=["N ≤ d+1\n(simplex OK)", "N > d+1\n(too many)"],
                        patch_artist=True)
        bp["boxes"][0].set_facecolor("#2ecc71")
        bp["boxes"][1].set_facecolor("#e74c3c")
        ax.set_ylabel("Prediction / chance")
        ax.set_title("Simplex feasibility matters?")
        ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)

    # 6: Alignment matrix for best config
    ax = axes[1, 2]
    best_r = max(all_results, key=lambda r: r["prediction_ratio"])
    g = best_r["geometry"]
    im = ax.imshow(g["cos_sim_matrix"], cmap="RdBu_r", vmin=-1, vmax=1)
    ax.set_title(f"Best config: V={best_r['vocab_size']}, N={best_r['n_bubbles']}\n"
                 f"ratio={best_r['prediction_ratio']:.2f}x")
    ax.set_xlabel("Bubble")
    ax.set_ylabel("Bubble")
    plt.colorbar(im, ax=ax)

    plt.suptitle("Plateau geometry investigation: do bubble angles explain prediction?",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_plateau_geometry.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_plateau_geometry.png")
    plt.close()

    # ================================================================
    # SUMMARY
    # ================================================================
    print(f"\n{'=' * 70}")
    print("SUMMARY")
    print(f"{'=' * 70}")
    print(f"\n  Best config: V={best_r['vocab_size']}, N={best_r['n_bubbles']}, "
          f"d={best_r['d']}")
    print(f"  Prediction ratio: {best_r['prediction_ratio']:.2f}x")
    print(f"  Stability: {best_r['stability']:.3f}")
    print(f"  Mean cosine sim: {best_r['geometry']['mean_cos_sim']:.4f}")
    print(f"  Simplex feasible: {best_r['geometry']['simplex_feasible']}")
    print(f"  Simplex angle for N={best_r['n_bubbles']}: "
          f"{best_r['geometry']['simplex_angle']:.4f}")
