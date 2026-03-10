"""
Gauge-invariant equilibration: the Plateau forces should compare
measurements in the same frame.

Current problem:
  m_i = U_i^T x  (measurement in bubble i's frame)
  m_j = U_j^T x  (measurement in bubble j's frame)
  cos_sim(m_i, m_j) compares numbers in DIFFERENT frames

Fix:
  e_i = U_i m_i  (expression of bubble i's measurement in shared frame)
  e_j = U_j m_j  (expression of bubble j's measurement in shared frame)
  cos_sim(e_i, e_j) compares in the SAME frame

  Forces act in shared space, then project back to each bubble's frame.

From attention.md: "misunderstanding is a gauge artifact."
This change makes the foam's internal conversation gauge-invariant —
bubbles compare what they *mean*, not how they encode it.
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Bubble, Foam
from foam_tokens import TokenFoam, generate_sequences, analyze_token_predictions
from foam_spread import (
    spread_bases_on_SO, init_spread_foam, measure_basis_spread,
    SpreadTokenFoam
)


class GaugeFoam(Foam):
    """
    Foam with gauge-invariant equilibration.

    The only change from Foam: equilibration compares measurements
    after expressing them back into the shared frame. Forces act in
    shared space, then project back into each bubble's local frame.
    """

    def __init__(self, n_bubbles, d, n_equilibrium_steps=5,
                 diversity_weight=2.0):
        super().__init__(n_bubbles, d, n_equilibrium_steps)
        self.diversity_weight = diversity_weight

    def equilibrate(self, measurements):
        """
        Gauge-invariant Plateau equilibration.

        measurements: [batch, N, d] — each bubble's measurement in its OWN frame
        returns: [batch, N, d] — equilibrium measurements (still in local frames)

        Key difference from Foam.equilibrate:
        1. Express measurements to shared frame for comparison
        2. Compute Plateau forces in shared frame
        3. Project forces back to local frames for update
        """
        N = self.n_bubbles
        device = measurements.device
        mask = 1 - torch.eye(N, device=device)

        # Structural interaction strength
        tension = self.surface_tension()
        interaction = torch.softmax(
            -tension / self.temperature.abs().clamp(min=0.01), dim=-1
        )

        target = self.target_similarity
        step = self.equilibrium_step_size.abs().clamp(min=0.001, max=0.5)

        # Get bases for frame transformations
        bases = [b.basis for b in self.bubbles]  # each [d, d]

        state = measurements  # [batch, N, d] in local frames

        for _ in range(self.n_steps):
            # Express to shared frame: e_i = U_i @ m_i^T → transpose back
            # For each bubble i: expression_i = state[:, i, :] @ U_i^T
            expressions = torch.stack([
                state[:, i, :] @ bases[i].T for i in range(N)
            ], dim=1)  # [batch, N, d] in SHARED frame

            # Cosine similarity in shared frame (gauge-invariant!)
            expr_n = expressions / (expressions.norm(dim=-1, keepdim=True) + 1e-10)
            cos_sim = torch.bmm(expr_n, expr_n.transpose(1, 2))  # [batch, N, N]

            # Plateau force magnitude
            force_mag = (cos_sim - target) * (mask * interaction).unsqueeze(0)

            # Force direction in shared frame
            diff = expressions.unsqueeze(2) - expressions.unsqueeze(1)
            diff_n = diff / (diff.norm(dim=-1, keepdim=True) + 1e-10)

            # Net force on each bubble in shared frame
            forces_shared = (force_mag.unsqueeze(-1) * diff_n).sum(dim=2)
            # [batch, N, d] in shared frame

            # Project forces back to local frames: f_local_i = U_i^T @ f_shared_i
            forces_local = torch.stack([
                forces_shared[:, i, :] @ bases[i] for i in range(N)
            ], dim=1)  # [batch, N, d] in local frames

            # Update in local frames
            state = state + step * forces_local

        return state

    def maintenance_cost(self, x, prev_equilibrium=None):
        result = self.compute_f(x, prev_equilibrium=prev_equilibrium)

        tension = result["surface_tension"]
        mask_t = 1 - torch.eye(self.n_bubbles, device=tension.device)
        mean_tension = (tension * mask_t).sum() / mask_t.sum()
        surface_energy = (mean_tension - 1.0) ** 2

        m0 = result["measurements"]
        m1 = result["equilibrium"]
        measurement_cost = ((m1 - m0) ** 2).mean()

        f_cost = result["F"].abs().mean()

        # Diversity: repulsion between bases
        bases = torch.stack([b.basis for b in self.bubbles])
        flat = bases.reshape(self.n_bubbles, -1)
        flat_norm = flat / (flat.norm(dim=-1, keepdim=True) + 1e-10)
        sim = flat_norm @ flat_norm.T
        mask = ~torch.eye(self.n_bubbles, dtype=torch.bool, device=sim.device)
        sim_shifted = (1 + sim[mask]) / 2
        diversity_loss = sim_shifted.mean()

        total = (f_cost
                 + 0.1 * measurement_cost
                 + 0.1 * surface_energy
                 + self.diversity_weight * diversity_loss)

        return {
            "total": total,
            "f_cost": f_cost,
            "measurement_cost": measurement_cost,
            "surface_energy": surface_energy,
            "diversity_loss": diversity_loss,
            **result,
        }


class GaugeTokenFoam(nn.Module):
    """TokenFoam with gauge-invariant equilibration."""

    def __init__(self, vocab_size, d, n_bubbles, n_equilibrium_steps=5,
                 diversity_weight=2.0):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d

        self.embed = nn.Embedding(vocab_size, d)
        self.foam = GaugeFoam(n_bubbles, d, n_equilibrium_steps,
                              diversity_weight)

        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

    def born_rule(self, rho, embeddings):
        return (embeddings @ rho * embeddings).sum(dim=-1)

    def process_sequence(self, tokens):
        seq_len = tokens.shape[0]
        device = tokens.device

        memory = torch.zeros(self.foam.n_bubbles, self.foam.d, device=device)
        E = self.embed.weight
        step_results = []

        for t in range(seq_len):
            x = self.embed(tokens[t:t + 1])

            memory_mean = memory.mean(dim=0, keepdim=True)
            mem_norm = memory_mean.norm() + 1e-10
            x_norm = x.norm() + 1e-10
            if mem_norm > 1e-8:
                novelty = 1 - (x * memory_mean).sum() / (x_norm * mem_norm)
            else:
                novelty = torch.tensor(1.0, device=device)

            sensitivity = self.novelty_sensitivity.abs()
            decay = torch.sigmoid(self.memory_decay_base - sensitivity * novelty)

            x_with_memory = x + decay * memory_mean
            result = self.foam.forward(x_with_memory)

            eq = result["equilibrium"][0]
            memory = decay * memory + (1 - decay) * eq

            rho = result["rho"][0]
            output_dist = result["output_dist"][0]

            logits = self.born_rule(rho, E)
            token_probs = torch.softmax(logits, dim=0)

            S_rho = -(output_dist * output_dist.log().clamp(min=-100)).sum().item()
            H_tokens = -(token_probs * token_probs.log().clamp(min=-100)).sum().item()
            F_tokens = H_tokens - S_rho

            step_results.append({
                "token": tokens[t].item(),
                "logits": logits.detach(),
                "token_probs": token_probs.detach(),
                "rho": rho.detach(),
                "output_dist": output_dist.detach(),
                "S_rho": S_rho,
                "H_tokens": H_tokens,
                "F_tokens": F_tokens,
                "novelty": novelty.item(),
                "decay": decay.item(),
            })

        return step_results


def train_and_evaluate(vocab_size, d, n_bubbles, seed=42,
                       mode="gauge",  # "gauge", "spread", "original"
                       diversity_weight=2.0, spread_scale=1.5,
                       n_epochs_coherence=150, n_epochs_expression=150):
    """Train and evaluate with specified mode."""
    torch.manual_seed(seed)

    if mode == "gauge":
        model = GaugeTokenFoam(vocab_size, d, n_bubbles,
                               diversity_weight=diversity_weight)
        init_spread_foam(model.foam, scale=spread_scale)
    elif mode == "spread":
        model = SpreadTokenFoam(vocab_size, d, n_bubbles,
                                diversity_weight=diversity_weight)
        init_spread_foam(model.foam, scale=spread_scale)
    else:
        model = TokenFoam(vocab_size, d, n_bubbles)

    sequences = generate_sequences(vocab_size, 40)

    spread_before = measure_basis_spread(model.foam)

    # Phase 1
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    for epoch in range(n_epochs_coherence):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            costs = model.foam.maintenance_cost(x_batch)
            costs["total"].backward()
            optimizer.step()

    # Phase 2
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

    model.eval()
    spread_after = measure_basis_spread(model.foam)

    results_by_seq = {}
    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)
        analysis = analyze_token_predictions(results, tokens, vocab_size)
        results_by_seq[name] = analysis

    structured_names = [n for n in results_by_seq if "random" not in n]
    vals = [results_by_seq[n].get("mean_next_prob", 0) for n in structured_names
            if results_by_seq[n]]
    ratio = np.mean(vals) / (1.0 / vocab_size) if vals else 0

    # Also get random baseline
    random_names = [n for n in results_by_seq if "random" in n]
    random_vals = [results_by_seq[n].get("mean_next_prob", 0) for n in random_names
                   if results_by_seq[n]]
    random_ratio = np.mean(random_vals) / (1.0 / vocab_size) if random_vals else 0

    return {
        "vocab_size": vocab_size,
        "d": d,
        "n_bubbles": n_bubbles,
        "seed": seed,
        "mode": mode,
        "ratio": ratio,
        "random_ratio": random_ratio,
        "spread_before": spread_before,
        "spread_after": spread_after,
        "by_seq": results_by_seq,
    }


if __name__ == "__main__":
    # ================================================================
    # PART 1: Three-way comparison — original vs spread vs gauge
    # ================================================================
    print("=" * 70)
    print("PART 1: Original vs Spread vs Gauge-invariant")
    print("  Same configs, three equilibration strategies")
    print("=" * 70)

    d = 16
    configs = [
        (8, 3), (8, 5),
        (16, 3), (16, 5),
        (32, 3), (32, 5), (32, 8),
        (64, 3), (64, 5), (64, 8),
        (128, 3), (128, 5),
        (256, 3), (256, 5),
    ]

    all_comparisons = []
    print(f"\n  {'V':>5} {'N':>3} | {'Original':>9} | {'Spread':>9} | "
          f"{'Gauge':>9} | {'Best':>7}")
    print(f"  {'-' * 58}")

    for V, N in configs:
        epochs = 150 if V <= 128 else 100

        r_orig = train_and_evaluate(V, d, N, mode="original",
                                    n_epochs_coherence=epochs,
                                    n_epochs_expression=epochs)
        r_spread = train_and_evaluate(V, d, N, mode="spread",
                                      n_epochs_coherence=epochs,
                                      n_epochs_expression=epochs)
        r_gauge = train_and_evaluate(V, d, N, mode="gauge",
                                     n_epochs_coherence=epochs,
                                     n_epochs_expression=epochs)

        best_mode = max(
            [("orig", r_orig["ratio"]),
             ("spread", r_spread["ratio"]),
             ("gauge", r_gauge["ratio"])],
            key=lambda x: x[1]
        )

        comp = {
            "V": V, "N": N,
            "orig": r_orig["ratio"],
            "spread": r_spread["ratio"],
            "gauge": r_gauge["ratio"],
            "orig_cos": r_orig["spread_after"]["mean_cos"],
            "spread_cos": r_spread["spread_after"]["mean_cos"],
            "gauge_cos": r_gauge["spread_after"]["mean_cos"],
            "best": best_mode[0],
        }
        all_comparisons.append(comp)

        print(f"  {V:>5} {N:>3} | {r_orig['ratio']:>8.2f}x | "
              f"{r_spread['ratio']:>8.2f}x | {r_gauge['ratio']:>8.2f}x | "
              f"{best_mode[0]:>7}")

    # ================================================================
    # PART 2: Gauge-invariant scaling sweep
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 2: Gauge-invariant scaling — V=8 to 512")
    print("=" * 70)

    extended_v = [8, 16, 32, 64, 128, 256, 512]
    gauge_scale = []

    for V in extended_v:
        best_ratio = 0
        best_n = 0
        for N in [3, 5, 8]:
            if N > V:
                continue
            epochs = 150 if V <= 128 else 100
            r = train_and_evaluate(V, d, N, mode="gauge",
                                   n_epochs_coherence=epochs,
                                   n_epochs_expression=epochs)
            marker = ""
            if r["ratio"] > best_ratio:
                best_ratio = r["ratio"]
                best_n = N
                marker = " *"
            print(f"  V={V:>4} N={N}  ratio={r['ratio']:.2f}x  "
                  f"cos={r['spread_after']['mean_cos']:.4f}{marker}")

        gauge_scale.append({"V": V, "best_N": best_n, "ratio": best_ratio})

    # ================================================================
    # PART 3: Diversity weight sweep for gauge mode
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 3: Diversity weight for gauge mode (V=32, N=5)")
    print("=" * 70)

    weights = [0.5, 1.0, 2.0, 4.0, 8.0]
    gauge_weight_results = []

    for w in weights:
        r = train_and_evaluate(32, 16, 5, mode="gauge", diversity_weight=w)
        gauge_weight_results.append(r)
        print(f"  weight={w:<4}  ratio={r['ratio']:.2f}x  "
              f"cos={r['spread_after']['mean_cos']:.4f}")

    # ================================================================
    # PART 4: Seed robustness for best gauge config
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 4: Seed robustness for gauge mode")
    print("=" * 70)

    # Find best config from Part 1
    best_comp = max(all_comparisons, key=lambda c: c["gauge"])
    V_best, N_best = best_comp["V"], best_comp["N"]
    print(f"  Testing V={V_best}, N={N_best} across 5 seeds")

    gauge_seeds = []
    for seed in range(5):
        r = train_and_evaluate(V_best, d, N_best, seed=seed, mode="gauge")
        gauge_seeds.append(r)
        print(f"  seed={seed}  ratio={r['ratio']:.2f}x  "
              f"cos={r['spread_after']['mean_cos']:.4f}")

    ratios = [r["ratio"] for r in gauge_seeds]
    print(f"\n  Mean: {np.mean(ratios):.2f}x  Std: {np.std(ratios):.2f}  "
          f"Min: {np.min(ratios):.2f}  Max: {np.max(ratios):.2f}")

    # ================================================================
    # PLOT
    # ================================================================
    fig, axes = plt.subplots(2, 3, figsize=(20, 12))

    # 1: Three-way comparison bar chart
    ax = axes[0, 0]
    labels = [f"V{c['V']}N{c['N']}" for c in all_comparisons]
    x = np.arange(len(labels))
    w = 0.25
    ax.bar(x - w, [c["orig"] for c in all_comparisons], w,
           label="Original", color="#e74c3c", alpha=0.7)
    ax.bar(x, [c["spread"] for c in all_comparisons], w,
           label="Spread", color="#3498db", alpha=0.7)
    ax.bar(x + w, [c["gauge"] for c in all_comparisons], w,
           label="Gauge", color="#2ecc71", alpha=0.7)
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=90, fontsize=7)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Three equilibration modes")
    ax.legend(fontsize=8)

    # 2: Win counts
    ax = axes[0, 1]
    win_counts = {"orig": 0, "spread": 0, "gauge": 0}
    for c in all_comparisons:
        win_counts[c["best"]] += 1
    bars = ax.bar(win_counts.keys(), win_counts.values(),
                  color=["#e74c3c", "#3498db", "#2ecc71"], alpha=0.7)
    ax.set_ylabel("Number of wins")
    ax.set_title("Which mode wins most often?")
    for bar, count in zip(bars, win_counts.values()):
        ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.2,
                str(count), ha="center", fontsize=12)

    # 3: Gauge scaling
    ax = axes[0, 2]
    ax.plot([g["V"] for g in gauge_scale],
            [g["ratio"] for g in gauge_scale],
            "o-", color="#2ecc71", linewidth=2, markersize=8)
    ax.set_xlabel("Vocabulary size V")
    ax.set_ylabel("Best prediction / chance")
    ax.set_title("Gauge-invariant scaling")
    ax.set_xscale("log", base=2)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)

    # 4: Basis spread comparison
    ax = axes[1, 0]
    ax.scatter([c["orig_cos"] for c in all_comparisons],
               [c["orig"] for c in all_comparisons],
               c="#e74c3c", label="Original", s=60, alpha=0.7)
    ax.scatter([c["spread_cos"] for c in all_comparisons],
               [c["spread"] for c in all_comparisons],
               c="#3498db", label="Spread", s=60, alpha=0.7)
    ax.scatter([c["gauge_cos"] for c in all_comparisons],
               [c["gauge"] for c in all_comparisons],
               c="#2ecc71", label="Gauge", s=60, alpha=0.7)
    ax.set_xlabel("Mean pairwise cosine similarity")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Basis spread vs prediction quality")
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.3)
    ax.legend(fontsize=8)

    # 5: Diversity weight for gauge
    ax = axes[1, 1]
    ax.plot(weights, [r["ratio"] for r in gauge_weight_results],
            "o-", color="#2ecc71", linewidth=2, markersize=8)
    ax.set_xlabel("Diversity weight")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Gauge: diversity weight sweep")
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)

    # 6: Seed robustness
    ax = axes[1, 2]
    ax.bar(range(len(gauge_seeds)),
           [r["ratio"] for r in gauge_seeds],
           color="#2ecc71", alpha=0.7)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axhline(y=np.mean(ratios), color="#27ae60", linestyle="--",
               label=f"mean={np.mean(ratios):.2f}x")
    ax.set_xlabel("Seed")
    ax.set_ylabel("Prediction / chance")
    ax.set_title(f"Gauge seed robustness (V={V_best}, N={N_best})")
    ax.legend()

    plt.suptitle("Gauge-invariant equilibration: "
                 "bubbles compare what they mean, not how they encode it",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_gauge.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_gauge.png")
    plt.close()

    # ================================================================
    # VERDICT
    # ================================================================
    print(f"\n{'=' * 70}")
    print("VERDICT")
    print(f"{'=' * 70}")

    print(f"\n  Win counts: {win_counts}")
    print(f"  Mean ratios across all configs:")
    print(f"    Original: {np.mean([c['orig'] for c in all_comparisons]):.2f}x")
    print(f"    Spread:   {np.mean([c['spread'] for c in all_comparisons]):.2f}x")
    print(f"    Gauge:    {np.mean([c['gauge'] for c in all_comparisons]):.2f}x")

    # Does gauge break the cycling?
    print(f"\n  Gauge scaling pattern:")
    for i in range(1, len(gauge_scale)):
        prev = gauge_scale[i-1]["ratio"]
        curr = gauge_scale[i]["ratio"]
        direction = "↑" if curr > prev else "↓"
        print(f"    V={gauge_scale[i]['V']:>4} (N={gauge_scale[i]['best_N']}): "
              f"{curr:.2f}x {direction}")

    # Seed robustness
    print(f"\n  Gauge seed robustness (V={V_best}, N={N_best}):")
    print(f"    {np.mean(ratios):.2f}x ± {np.std(ratios):.2f}")
    if np.mean(ratios) > 1.5 and np.std(ratios) < np.mean(ratios) * 0.5:
        print(f"    -> ROBUST: consistently above chance with moderate variance")
    elif np.mean(ratios) > 1.0:
        print(f"    -> MODERATE: above chance on average but noisy")
    else:
        print(f"    -> WEAK: not consistently above chance")
