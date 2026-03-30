"""
Cross-test: what determines the L saturation level?

Observed: L saturates at ~72% of theoretical max across d and N.
Questions:
  1. Does the ratio depend on eps (write scale)? If yes → dynamical. If no → geometric.
  2. Does it depend on d, N, number of slices?
  3. What's the algebraic fixed point?

Also: the theoretical max assumes all pairs at distance 2√d, which is
geometrically impossible for N ≥ 3. The ACHIEVABLE max is lower.
By Cauchy-Schwarz + the constraint Σ Re(tr(U_i†U_j)) ≥ -Nd/2 (from ||Σ U_i||² ≥ 0),
the achievable max of Σ D_ij² = N²d, giving Σ D_ij ≤ N√(C(N,2)) · √(N²d / C(N,2))...
Let's just compute it numerically.
"""

import numpy as np
from foam import cayley, skew_hermitian, random_unitary, compute_L


def write_single(basis, P, v, bases_all, idx, N, eps):
    """Centroid-based stabilization write (test-specific rule)."""
    m = np.real(P @ (v @ basis))
    m_norm = np.linalg.norm(m)
    if m_norm < 1e-12:
        return basis.copy()
    all_m = []
    for k in range(len(bases_all)):
        mk = np.real(P @ (v @ bases_all[k]))
        mk_n = np.linalg.norm(mk)
        all_m.append(mk / mk_n if mk_n > 1e-12 else mk)
    others = [all_m[k] for k in range(len(all_m)) if k != idx]
    if not others:
        return basis.copy()
    centroid = np.mean(others, axis=0)
    target = m / m_norm - centroid
    t_norm = np.linalg.norm(target)
    if t_norm > 1e-12:
        target = target / t_norm
    j2 = target * m_norm
    d_vec = j2 - m
    d_norm = np.linalg.norm(d_vec)
    if d_norm < 1e-12:
        return basis.copy()
    d_hat = d_vec / d_norm
    m_hat = m / m_norm
    d_full = P.T @ d_hat
    m_full = P.T @ m_hat
    dL = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
    dL = skew_hermitian(dL)
    return basis @ cayley(dL)


def run_to_saturation(d, N, eps, n_steps, n_slices=1, rng_seed=42):
    """Run foam and return saturation level as fraction of theoretical max."""
    rng = np.random.default_rng(rng_seed)
    bases = [random_unitary(d, rng) for _ in range(N)]

    slices = []
    for _ in range(n_slices):
        Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
        slices.append(Q[:, :3].T)

    input_rng = np.random.default_rng(rng_seed + 1000)
    n_pairs = N * (N - 1) // 2
    L_max = n_pairs * 2 * np.sqrt(d)

    # run to saturation
    L_history = []
    for t in range(n_steps):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)
        P = slices[t % n_slices]
        for i in range(N):
            bases[i] = write_single(bases[i], P, v, bases, i, N, eps)
        L_history.append(compute_L(bases))

    # saturation level = mean of last 20%
    tail = L_history[int(0.8 * n_steps):]
    L_sat = np.mean(tail)
    L_std = np.std(tail)

    return L_sat, L_max, L_sat / L_max, L_std


def achievable_max(d, N):
    """Compute achievable max of Σ D_ij by optimization.
    Place N unitaries to maximize total pairwise Frobenius distance.
    Use: L² ≤ C(N,2) · Σ D_ij², and Σ D_ij² ≤ N²d (from ||Σ U_i||² ≥ 0).
    Equality when all D_ij are equal AND Σ U_i = 0."""
    n_pairs = N * (N - 1) // 2
    # when Σ U_i = 0: Σ_{i<j} Re(tr(U_i† U_j)) = -Nd/2
    # so Σ D_ij² = n_pairs * 2d - 2*(-Nd/2) = n_pairs*2d + Nd = N(N-1)d + Nd = N²d
    sum_sq = N * N * d
    # by Cauchy-Schwarz: (Σ D_ij)² ≤ n_pairs · Σ D_ij²
    L_achievable = np.sqrt(n_pairs * sum_sq)
    L_theoretical = n_pairs * 2 * np.sqrt(d)
    return L_achievable, L_theoretical, L_achievable / L_theoretical


# ============================================================
# Sweep 1: eps dependence (is saturation level dynamical or geometric?)
# ============================================================

def sweep_eps():
    print("Sweep 1: eps dependence")
    print("=" * 60)
    d, N, n_steps = 6, 3, 2000

    print(f"  d={d}, N={N}, steps={n_steps}")
    print(f"  {'eps':>8} {'L_sat':>8} {'L_max':>8} {'ratio':>8} {'std':>8}")
    for eps in [0.01, 0.03, 0.05, 0.1, 0.2, 0.5]:
        L_sat, L_max, ratio, std = run_to_saturation(d, N, eps, n_steps)
        print(f"  {eps:8.3f} {L_sat:8.3f} {L_max:8.3f} {ratio:8.3f} {std:8.4f}")
    print()


# ============================================================
# Sweep 2: d dependence
# ============================================================

def sweep_d():
    print("Sweep 2: d dependence (N=3)")
    print("=" * 60)
    N = 3
    eps = 0.1

    print(f"  {'d':>4} {'L_sat':>8} {'L_max':>8} {'ratio':>8} {'ach_max':>8} {'ach_ratio':>10} {'sat/ach':>8}")
    for d in [3, 4, 5, 6, 8, 10, 12]:
        n_steps = 3000
        L_sat, L_max, ratio, std = run_to_saturation(d, N, eps, n_steps)
        L_ach, _, ach_ratio = achievable_max(d, N)
        print(f"  {d:4d} {L_sat:8.3f} {L_max:8.3f} {ratio:8.3f} {L_ach:8.3f} {ach_ratio:10.3f} {L_sat/L_ach:8.3f}")
    print()


# ============================================================
# Sweep 3: N dependence
# ============================================================

def sweep_N():
    print("Sweep 3: N dependence (d=6)")
    print("=" * 60)
    d = 6
    eps = 0.1

    print(f"  {'N':>4} {'L_sat':>8} {'L_max':>8} {'ratio':>8} {'ach_max':>8} {'sat/ach':>8}")
    for N in [2, 3, 4, 5, 6]:
        n_steps = 3000
        L_sat, L_max, ratio, std = run_to_saturation(d, N, eps, n_steps)
        L_ach, _, _ = achievable_max(d, N)
        print(f"  {N:4d} {L_sat:8.3f} {L_max:8.3f} {ratio:8.3f} {L_ach:8.3f} {L_sat/L_ach:8.3f}")
    print()


# ============================================================
# Sweep 4: number of slices
# ============================================================

def sweep_slices():
    print("Sweep 4: number of slices (d=8, N=4)")
    print("=" * 60)
    d, N = 8, 4
    eps = 0.1
    n_steps = 2000

    print(f"  {'slices':>6} {'L_sat':>8} {'L_max':>8} {'ratio':>8}")
    for n_slices in [1, 2, 3, 4]:
        L_sat, L_max, ratio, std = run_to_saturation(d, N, eps, n_steps, n_slices=n_slices)
        print(f"  {n_slices:6d} {L_sat:8.3f} {L_max:8.3f} {ratio:8.3f}")
    print()


# ============================================================
# Algebraic analysis: the achievable bound
# ============================================================

def analyze_achievable():
    print("Algebraic: achievable max vs theoretical max")
    print("=" * 60)
    print(f"  The theoretical max assumes all C(N,2) pairs at distance 2sqrt(d).")
    print(f"  This is impossible for N >= 3 (if U1†U2 = -I and U1†U3 = -I, then U2†U3 = I).")
    print(f"  The achievable max (from Cauchy-Schwarz + ||Σ Ui||² ≥ 0):")
    print()
    print(f"  {'d':>4} {'N':>4} {'L_theo':>8} {'L_ach':>8} {'ach/theo':>9}")
    for d in [4, 6, 8, 10]:
        for N in [3, 4, 5]:
            L_ach, L_theo, ratio = achievable_max(d, N)
            print(f"  {d:4d} {N:4d} {L_theo:8.3f} {L_ach:8.3f} {ratio:9.3f}")
    print()
    print("  The achievable max is ~82-87% of theoretical. The foam saturates at ~72%.")
    print("  The gap between achievable and actual saturation is the cost of")
    print("  the perpendicularity constraint: writes can't reach all configurations.")
    print()


if __name__ == "__main__":
    analyze_achievable()
    sweep_eps()
    sweep_d()
    sweep_N()
    sweep_slices()
