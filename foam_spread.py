"""
Spread bases: fixing the bootstrap problem in foam geometry.

The finding from foam_plateau_geometry.py:
  - All bubble bases end up with ~0.93 cosine similarity (nearly parallel)
  - The Cayley parameterization starts near identity
  - Training doesn't push bases apart enough
  - The foam is trying to be stereoscopic with nearly-identical eyes

The fix:
  1. Initialize bases maximally spread on SO(d) — not clustered near I
  2. Protect diversity during training with a stronger signal
  3. See if diverse measurement processes unlock prediction at scale

The skew-symmetric matrices (the Lie algebra so(d)) form a d(d-1)/2 dimensional
space. We pick N well-spread points in that space, then Cayley-map them to O(d).
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Bubble, Foam
from foam_tokens import TokenFoam, generate_sequences, analyze_token_predictions


def spread_bases_on_SO(d, n, scale=1.0):
    """
    Generate n well-spread skew-symmetric matrices in so(d),
    yielding n well-spread orthogonal bases via Cayley transform.

    Strategy: the space of skew-symmetric d×d matrices has dimension
    d(d-1)/2. We pick n points on a sphere in this space, then scale
    them to get meaningful rotations (not just infinitesimal ones).

    For n ≤ d(d-1)/2 + 1, we can place them as simplex vertices.
    For larger n, we use a repulsion-based spreading on the sphere.

    Returns: list of n skew-symmetric matrices A_i, such that
    U_i = (I - A_i)(I + A_i)^{-1} are well-spread in O(d).
    """
    dim = d * (d - 1) // 2

    # Map between skew-symmetric matrices and vectors in R^{dim}
    def vec_to_skew(v, d):
        A = torch.zeros(d, d)
        idx = 0
        for i in range(d):
            for j in range(i + 1, d):
                A[i, j] = v[idx]
                A[j, i] = -v[idx]
                idx += 1
        return A

    if n == 1:
        return [torch.zeros(d, d)]

    # Place n points on the unit sphere in R^dim, then scale
    # Use simplex vertices if n ≤ dim+1, else repulsion
    if n <= dim + 1:
        # Simplex vertices in R^dim: well-known construction
        # Start with n points, iteratively place each maximally far
        # from existing ones
        points = []
        # First point: e_1
        p = torch.zeros(dim)
        p[0] = 1.0
        points.append(p)

        for i in range(1, n):
            if i < dim:
                # Use standard basis vectors, then adjust for equal spacing
                p = torch.zeros(dim)
                p[i] = 1.0
                points.append(p)
            else:
                # Place equidistant from all existing points
                # For simplex: the last vertex is at -1/(n-1) * sum of others,
                # normalized
                center = torch.stack(points).mean(dim=0)
                p = -center
                p = p / (p.norm() + 1e-10)
                points.append(p)

        # Now do a few rounds of repulsion to equalize distances
        points = torch.stack(points)  # [n, dim]
        for _ in range(200):
            forces = torch.zeros_like(points)
            for i in range(n):
                for j in range(n):
                    if i == j:
                        continue
                    diff = points[i] - points[j]
                    dist = diff.norm() + 1e-10
                    forces[i] += diff / (dist ** 3)  # inverse-square repulsion
            # Move and re-project to sphere
            points = points + 0.01 * forces
            points = points / (points.norm(dim=-1, keepdim=True) + 1e-10)

        # Scale to get substantial rotations
        skews = []
        for i in range(n):
            A = vec_to_skew(points[i] * scale, d)
            skews.append(A)
        return skews
    else:
        # Random + repulsion for large n
        points = torch.randn(n, dim)
        points = points / (points.norm(dim=-1, keepdim=True) + 1e-10)

        for _ in range(500):
            forces = torch.zeros_like(points)
            for i in range(n):
                for j in range(i + 1, n):
                    diff = points[i] - points[j]
                    dist = diff.norm() + 1e-10
                    f = diff / (dist ** 3)
                    forces[i] += f
                    forces[j] -= f
            points = points + 0.01 * forces
            points = points / (points.norm(dim=-1, keepdim=True) + 1e-10)

        skews = []
        for i in range(n):
            A = vec_to_skew(points[i] * scale, d)
            skews.append(A)
        return skews


def init_spread_foam(foam, scale=1.5):
    """Initialize a Foam's bubble bases to be maximally spread."""
    skews = spread_bases_on_SO(foam.d, foam.n_bubbles, scale=scale)
    with torch.no_grad():
        for i, bubble in enumerate(foam.bubbles):
            A = skews[i]
            # L such that L - L^T = A: set L = A/2 (since A is skew)
            # But we also want some noise to break symmetry
            bubble.L.data = A / 2 + torch.randn_like(bubble.L) * 0.01


def measure_basis_spread(foam):
    """Measure how spread out the bases are."""
    with torch.no_grad():
        bases = torch.stack([b.basis for b in foam.bubbles])
        N = foam.n_bubbles
        flat = bases.reshape(N, -1)
        flat_norm = flat / (flat.norm(dim=-1, keepdim=True) + 1e-10)
        cos_sim = (flat_norm @ flat_norm.T)
        mask = ~torch.eye(N, dtype=torch.bool)
        off_diag = cos_sim[mask]
        return {
            "mean_cos": off_diag.mean().item(),
            "std_cos": off_diag.std().item(),
            "min_cos": off_diag.min().item(),
            "max_cos": off_diag.max().item(),
            "matrix": cos_sim.numpy(),
        }


class SpreadFoam(Foam):
    """
    Foam with stronger basis diversity enforcement.

    The diversity loss in the original Foam uses flattened bases with
    weight 0.5 — not enough to overcome the identity-clustering.
    This version:
    1. Uses a repulsion-based diversity term
    2. Has a configurable diversity weight
    3. Can enforce a minimum pairwise distance
    """

    def __init__(self, n_bubbles, d, n_equilibrium_steps=5,
                 diversity_weight=2.0):
        super().__init__(n_bubbles, d, n_equilibrium_steps)
        self.diversity_weight = diversity_weight

    def maintenance_cost(self, x, prev_equilibrium=None):
        result = self.compute_f(x, prev_equilibrium=prev_equilibrium)

        tension = result["surface_tension"]
        mask = 1 - torch.eye(self.n_bubbles, device=tension.device)
        mean_tension = (tension * mask).sum() / mask.sum()
        surface_energy = (mean_tension - 1.0) ** 2

        m0 = result["measurements"]
        m1 = result["equilibrium"]
        measurement_cost = ((m1 - m0) ** 2).mean()

        f_cost = result["F"].abs().mean()

        # Enhanced diversity: repulsion between bases
        # Instead of just penalizing high cosine similarity,
        # use inverse-distance repulsion (like Coulomb)
        bases = torch.stack([b.basis for b in self.bubbles])
        flat = bases.reshape(self.n_bubbles, -1)
        flat_norm = flat / (flat.norm(dim=-1, keepdim=True) + 1e-10)
        sim = flat_norm @ flat_norm.T  # [N, N]

        # Repulsion: penalize high similarity with a steep function
        # Use (1+sim)/2 to map [-1,1] to [0,1], then penalize high values
        sim_shifted = (1 + sim * mask) / 2  # [0,1] for off-diagonal
        # Want this close to 0 (bases perpendicular or opposed)
        diversity_loss = (sim_shifted * mask).sum() / mask.sum()

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


class SpreadTokenFoam(nn.Module):
    """TokenFoam using SpreadFoam for stronger basis diversity."""

    def __init__(self, vocab_size, d, n_bubbles, n_equilibrium_steps=5,
                 diversity_weight=2.0):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d

        self.embed = nn.Embedding(vocab_size, d)
        self.foam = SpreadFoam(n_bubbles, d, n_equilibrium_steps,
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
                       spread_init=True, diversity_weight=2.0,
                       n_epochs_coherence=150, n_epochs_expression=150,
                       spread_scale=1.5, quiet=True):
    """Train with spread initialization and evaluate."""
    torch.manual_seed(seed)

    if spread_init:
        model = SpreadTokenFoam(vocab_size, d, n_bubbles,
                                diversity_weight=diversity_weight)
        init_spread_foam(model.foam, scale=spread_scale)
    else:
        model = TokenFoam(vocab_size, d, n_bubbles)

    sequences = generate_sequences(vocab_size, 40)

    # Measure initial spread
    spread_before = measure_basis_spread(model.foam)

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

    # Measure final spread
    model.eval()
    spread_after = measure_basis_spread(model.foam)

    # Evaluate prediction
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

    return {
        "vocab_size": vocab_size,
        "d": d,
        "n_bubbles": n_bubbles,
        "seed": seed,
        "spread_init": spread_init,
        "diversity_weight": diversity_weight,
        "ratio": ratio,
        "spread_before": spread_before,
        "spread_after": spread_after,
        "by_seq": results_by_seq,
    }


if __name__ == "__main__":
    # ================================================================
    # PART 1: Does spread initialization help? Direct comparison.
    # ================================================================
    print("=" * 70)
    print("PART 1: Spread vs clustered initialization")
    print("  Same (V, N, d), different starting geometry")
    print("=" * 70)

    d = 16
    configs = [
        (8, 3), (8, 5),
        (16, 3), (16, 5), (16, 8),
        (32, 3), (32, 5), (32, 8),
        (64, 3), (64, 5), (64, 8),
        (128, 3), (128, 5), (128, 8),
        (256, 3), (256, 5),
    ]

    comparisons = []
    print(f"\n  {'V':>5} {'N':>3} | {'Clustered':>10} {'cos':>6} | "
          f"{'Spread':>10} {'cos':>6} | {'Δ':>7}")
    print(f"  {'-' * 62}")

    for V, N in configs:
        epochs = 150 if V <= 128 else 100

        # Clustered (original)
        r_clust = train_and_evaluate(V, d, N, spread_init=False,
                                     n_epochs_coherence=epochs,
                                     n_epochs_expression=epochs)
        # Spread
        r_spread = train_and_evaluate(V, d, N, spread_init=True,
                                      diversity_weight=2.0,
                                      n_epochs_coherence=epochs,
                                      n_epochs_expression=epochs)

        delta = r_spread["ratio"] - r_clust["ratio"]
        comparisons.append({
            "V": V, "N": N,
            "clust_ratio": r_clust["ratio"],
            "spread_ratio": r_spread["ratio"],
            "clust_cos": r_clust["spread_after"]["mean_cos"],
            "spread_cos": r_spread["spread_after"]["mean_cos"],
            "delta": delta,
        })

        print(f"  {V:>5} {N:>3} | {r_clust['ratio']:>9.2f}x {r_clust['spread_after']['mean_cos']:>6.3f} | "
              f"{r_spread['ratio']:>9.2f}x {r_spread['spread_after']['mean_cos']:>6.3f} | "
              f"{'+' if delta > 0 else ''}{delta:>6.2f}x")

    # ================================================================
    # PART 2: How much diversity weight is optimal?
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 2: Diversity weight sweep (V=32, N=5, d=16)")
    print("=" * 70)

    weights = [0.5, 1.0, 2.0, 4.0, 8.0]
    weight_results = []

    for w in weights:
        r = train_and_evaluate(32, 16, 5, spread_init=True, diversity_weight=w)
        weight_results.append(r)
        print(f"  weight={w:<4}  ratio={r['ratio']:.2f}x  "
              f"cos_after={r['spread_after']['mean_cos']:.4f}")

    # ================================================================
    # PART 3: Scale sweep with spread bases
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 3: Scaling with spread bases — does the cycling break?")
    print("=" * 70)

    extended = [8, 16, 32, 64, 128, 256, 512]
    scale_results = []

    for V in extended:
        # Test N=3 and N=5 at each scale (the winners from Part 1)
        for N in [3, 5]:
            if N > V:
                continue
            epochs = 150 if V <= 128 else 100
            r = train_and_evaluate(V, d, N, spread_init=True,
                                   diversity_weight=2.0,
                                   n_epochs_coherence=epochs,
                                   n_epochs_expression=epochs)
            scale_results.append(r)
            print(f"  V={V:>4} N={N}  ratio={r['ratio']:.2f}x  "
                  f"cos={r['spread_after']['mean_cos']:.4f}  "
                  f"cos_before={r['spread_before']['mean_cos']:.4f}")

    # ================================================================
    # PART 4: Spread scale parameter — how far apart should eyes be?
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 4: Spread scale — how far apart should the eyes start?")
    print("  (V=32, N=5, d=16)")
    print("=" * 70)

    scales = [0.5, 1.0, 1.5, 2.0, 3.0, 5.0]
    spread_scale_results = []

    for s in scales:
        r = train_and_evaluate(32, 16, 5, spread_init=True,
                               diversity_weight=2.0, spread_scale=s)
        spread_scale_results.append(r)
        print(f"  scale={s:<4}  ratio={r['ratio']:.2f}x  "
              f"cos_before={r['spread_before']['mean_cos']:.4f}  "
              f"cos_after={r['spread_after']['mean_cos']:.4f}")

    # ================================================================
    # PLOT
    # ================================================================
    fig, axes = plt.subplots(2, 3, figsize=(20, 12))

    # 1: Clustered vs spread comparison
    ax = axes[0, 0]
    clust_ratios = [c["clust_ratio"] for c in comparisons]
    spread_ratios = [c["spread_ratio"] for c in comparisons]
    labels = [f"V{c['V']}N{c['N']}" for c in comparisons]
    x = np.arange(len(labels))
    width = 0.35
    ax.bar(x - width/2, clust_ratios, width, label="Clustered", color="#e74c3c", alpha=0.7)
    ax.bar(x + width/2, spread_ratios, width, label="Spread", color="#2ecc71", alpha=0.7)
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=90, fontsize=7)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Clustered vs spread initialization")
    ax.legend(fontsize=8)

    # 2: Cosine similarity before/after training (spread)
    ax = axes[0, 1]
    cos_before = [c["spread_cos"] for c in comparisons]  # after training
    # Get before values from spread results
    ax.bar(x, [c["spread_cos"] for c in comparisons], color="#3498db", alpha=0.7)
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=90, fontsize=7)
    ax.set_ylabel("Mean pairwise cos similarity")
    ax.set_title("Basis spread after training")
    ax.axhline(y=0.0, color="gray", linestyle=":", alpha=0.3)

    # 3: Diversity weight sweep
    ax = axes[0, 2]
    ax.plot(weights, [r["ratio"] for r in weight_results], "o-",
            color="#9b59b6", linewidth=2, markersize=8)
    ax.set_xlabel("Diversity weight")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Diversity weight sweep (V=32, N=5)")
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)

    # 4: Scale sweep with spread — does cycling break?
    ax = axes[1, 0]
    for N in [3, 5]:
        vs = [r["vocab_size"] for r in scale_results if r["n_bubbles"] == N]
        rs = [r["ratio"] for r in scale_results if r["n_bubbles"] == N]
        ax.plot(vs, rs, "o-", label=f"N={N}", linewidth=2, markersize=8)
    ax.set_xlabel("Vocabulary size V")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Scaling with spread bases")
    ax.set_xscale("log", base=2)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.legend()

    # 5: Spread scale parameter
    ax = axes[1, 1]
    ax.plot(scales, [r["ratio"] for r in spread_scale_results], "o-",
            color="#e67e22", linewidth=2, markersize=8)
    ax2 = ax.twinx()
    ax2.plot(scales, [r["spread_after"]["mean_cos"] for r in spread_scale_results],
             "s--", color="#1abc9c", linewidth=2, markersize=6)
    ax.set_xlabel("Initial spread scale")
    ax.set_ylabel("Prediction / chance", color="#e67e22")
    ax2.set_ylabel("Final mean cos similarity", color="#1abc9c")
    ax.set_title("How far apart should eyes start?")

    # 6: Delta (improvement from spreading)
    ax = axes[1, 2]
    deltas = [c["delta"] for c in comparisons]
    colors = ["#2ecc71" if d > 0 else "#e74c3c" for d in deltas]
    ax.bar(x, deltas, color=colors, alpha=0.7)
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=90, fontsize=7)
    ax.set_ylabel("Δ ratio (spread - clustered)")
    ax.set_title("Improvement from spreading")
    ax.axhline(y=0, color="black", linewidth=0.5)

    plt.suptitle("Spread bases: fixing the bootstrap problem",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_spread.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_spread.png")
    plt.close()

    # ================================================================
    # VERDICT
    # ================================================================
    print(f"\n{'=' * 70}")
    print("VERDICT")
    print(f"{'=' * 70}")

    wins = sum(1 for c in comparisons if c["delta"] > 0)
    losses = sum(1 for c in comparisons if c["delta"] < 0)
    ties = sum(1 for c in comparisons if abs(c["delta"]) < 0.1)
    mean_delta = np.mean(deltas)

    print(f"\n  Spread vs clustered: {wins} wins, {losses} losses, {ties} ties")
    print(f"  Mean improvement: {mean_delta:+.2f}x")

    # Best overall configuration
    best = max(comparisons, key=lambda c: c["spread_ratio"])
    print(f"\n  Best spread config: V={best['V']}, N={best['N']}")
    print(f"    Ratio: {best['spread_ratio']:.2f}x "
          f"(was {best['clust_ratio']:.2f}x clustered)")
    print(f"    Final cos similarity: {best['spread_cos']:.4f}")

    # Does the cycling pattern persist?
    print(f"\n  Scaling pattern with spread bases:")
    for r in scale_results:
        print(f"    V={r['vocab_size']:>4} N={r['n_bubbles']}  "
              f"ratio={r['ratio']:.2f}x")
