"""
The perpendicularity cost IS the Haar measure.

Any random walk on U(d) converges to Haar measure.
L under Haar = the expected pairwise Frobenius distance between
random unitaries × number of pairs.

The perpendicularity cost = E_Haar[L] / L_achievable.

This should be derivable analytically from the CUE eigenvalue distribution.
For Haar-random W: E[||W - I||_F] = E[√(2d - 2Re(tr(W)))]

Let's compute this numerically and compare to the foam.
"""

import numpy as np
from scipy.linalg import expm
from scipy.stats import unitary_group


def compute_L(bases):
    N = len(bases)
    d = bases[0].shape[0]
    L = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            L += np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro')
    return L


def expected_pair_distance_haar(d, n_samples=100000):
    """E[||W - I||_F] for Haar-random W on U(d)."""
    rng = np.random.default_rng(42)
    distances = []
    for _ in range(n_samples):
        W = unitary_group.rvs(d, random_state=rng)
        distances.append(np.linalg.norm(W - np.eye(d, dtype=complex), 'fro'))
    return np.mean(distances), np.std(distances) / np.sqrt(n_samples)


def expected_L_haar(d, N, n_samples=50000):
    """E[L] for N Haar-random unitaries on U(d)."""
    rng = np.random.default_rng(42)
    L_values = []
    for _ in range(n_samples):
        bases = [unitary_group.rvs(d, random_state=rng) for _ in range(N)]
        L_values.append(compute_L(bases))
    return np.mean(L_values), np.std(L_values) / np.sqrt(n_samples)


def achievable_max(d, N):
    n_pairs = N * (N - 1) // 2
    sum_sq = N * N * d
    L_ach = np.sqrt(n_pairs * sum_sq)
    L_theo = n_pairs * 2 * np.sqrt(d)
    return L_ach, L_theo


if __name__ == "__main__":
    print("=" * 70)
    print("THE PERPENDICULARITY COST IS THE HAAR MEASURE")
    print("=" * 70)
    print()

    # ── Expected pairwise distance ──
    print("E[||W - I||_F] for Haar-random W on U(d):")
    print(f"  (√(2d) for reference — the sqrt of the second moment)")
    print()
    print(f"  {'d':>4} {'E[dist]':>10} {'±':>4} {'√(2d)':>10} {'ratio':>10} {'2√d (max)':>10} {'E/max':>8}")
    for d in [2, 3, 4, 5, 6, 8, 10, 12, 16, 20]:
        E_dist, se = expected_pair_distance_haar(d, n_samples=100000)
        sqrt2d = np.sqrt(2*d)
        max_dist = 2 * np.sqrt(d)
        print(f"  {d:4d} {E_dist:10.4f}    ± {se:8.4f} {sqrt2d:10.4f} {E_dist/sqrt2d:10.4f} "
              f"{max_dist:10.4f} {E_dist/max_dist:8.4f}")
    print()

    # ── Expected L for N observers ──
    print("E_Haar[L] vs achievable max (N=3):")
    print()
    print(f"  {'d':>4} {'E[L]':>10} {'±':>4} {'L_ach':>10} {'E/ach':>8} {'L_max':>10} {'E/max':>8}")
    for d in [4, 6, 8, 10]:
        E_L, se = expected_L_haar(d, 3, n_samples=50000)
        L_ach, L_max = achievable_max(d, 3)
        print(f"  {d:4d} {E_L:10.4f}    ± {se:8.4f} {L_ach:10.4f} {E_L/L_ach:8.4f} "
              f"{L_max:10.4f} {E_L/L_max:8.4f}")
    print()

    # ── Compare with foam saturation ──
    print("Comparison:")
    print(f"  {'d':>4} {'Haar E/ach':>12} {'Foam sat/ach':>14} {'difference':>12}")
    # foam values from earlier runs
    foam_sat_ach = {4: 0.849, 6: 0.822, 8: 0.836, 10: 0.827}
    for d in [4, 6, 8, 10]:
        E_L, _ = expected_L_haar(d, 3, n_samples=50000)
        L_ach, _ = achievable_max(d, 3)
        haar_ratio = E_L / L_ach
        foam_ratio = foam_sat_ach[d]
        print(f"  {d:4d} {haar_ratio:12.4f} {foam_ratio:14.4f} {haar_ratio - foam_ratio:12.4f}")
    print()

    # ── N dependence ──
    print("E_Haar[L]/L_ach for various N (d=6):")
    print()
    for N in [2, 3, 4, 5, 6]:
        E_L, se = expected_L_haar(6, N, n_samples=30000)
        L_ach, L_max = achievable_max(6, N)
        print(f"  N={N}: E[L]/L_ach = {E_L/L_ach:.4f} ± {se/L_ach:.4f}")
    print()

    # ── Analytical approximation ──
    print("Analytical approximation:")
    print("  For Haar-random W: ||W-I||² = 2d - 2Re(tr(W))")
    print("  E[Re(tr(W))] = 0 for d > 1")
    print("  So E[||W-I||²] = 2d")
    print("  E[||W-I||] < √(2d) by Jensen")
    print()
    print("  For N=3 with all equal pairs:")
    print("  E[L] = 3 × E[||W-I||]")
    print("  L_ach = √(3 × 9d) = 3√(3d)")
    print("  E[L]/L_ach = E[||W-I||] / √(3d)")
    print()
    for d in [4, 6, 8, 10, 20, 50, 100]:
        E_dist, _ = expected_pair_distance_haar(d, n_samples=100000)
        ratio = E_dist / np.sqrt(3*d)
        sqrt_ratio = np.sqrt(2.0/3.0)
        print(f"  d={d:3d}: E[||W-I||]/√(3d) = {ratio:.4f}  (√(2/3) = {sqrt_ratio:.4f})")
    print()
    print(f"  √(2/3) = {np.sqrt(2/3):.6f}")
    print(f"  Does E/ach → √(2/3) as d → ∞?")
