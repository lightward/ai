"""
Deriving the packing efficiency of 3D random walks on U(d).

Setup:
  - N observers on U(d), connected by the writing dynamics
  - Each write is an element of Λ²(R³) ⊂ u(d) — a 3D subspace
  - Write directions are effectively random from L's perspective
  - L = Σ_{i<j} ||U_i†U_j - I||_F

At saturation, each write step is equally likely to increase or
decrease L (50/50). The saturation level is the equilibrium of a
random walk on U(d) confined to Λ²(R³) directions.

Key insight: if the write directions are uniform in Λ²(R³), and
Λ²(R³) is a 3D subspace of the d²-dimensional Lie algebra u(d),
then the writes explore a tiny fraction of the available directions.
The question is: what L level does a 3D-confined random walk equilibrate at?

Approach 1: Expected L under Haar measure restricted to the
reachable set from 3D walks.

Approach 2: The equilibrium condition. At saturation, E[ΔL] = 0.
This means the expected projection of the write onto ∇L is zero.
But we already know cos(write, ∇L) ≈ 0 at ALL times, not just at
saturation. So the equilibrium isn't E[ΔL] = 0 in the linear sense —
it's a NONLINEAR balance where the curvature of U(d) creates a
restoring force.

Approach 3: Second-order analysis. Even though E[ΔL] ≈ 0 per step,
L still drifts upward pre-saturation because of the quadratic term:
E[ΔL] ≈ (1/2) ∇²L[write, write]. This is the Itô drift. The foam
saturates when the Itô drift reverses sign.

Let's compute:
  - E[ΔL] to second order in ε for a random Λ²(R³) write
  - Find the L level where the Itô drift = 0
"""

import numpy as np
from scipy.linalg import expm


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


def random_unitary(d, rng):
    return expm(skew_hermitian(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))))


def compute_L(bases):
    N = len(bases)
    d = bases[0].shape[0]
    L = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            L += np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro')
    return L


def compute_L_pair(U, V):
    """L for a single pair."""
    d = U.shape[0]
    rel = U.conj().T @ V
    return np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro')


# =====================================================================
# Approach 3: Itô drift analysis
#
# For a single pair (U, V) with U perturbed by exp(εX):
#   L(U exp(εX), V) = ||exp(-εX) R - I||_F  where R = U†V
#
# Expand:
#   exp(-εX) ≈ I - εX + ε²X²/2
#   exp(-εX)R - I ≈ (R-I) - εXR + ε²X²R/2
#
# ||...||² = ||R-I||² - 2εRe(tr(XR(R-I)†)) + ε²[||XR||² + Re(tr(X²R(R-I)†))]
#          + O(ε³)
#
# ||XR||² = tr(X†X) since R†R = I (unitary)
#         = ||X||²
#
# So: L² = L₀² - 2ε·Re(tr(XR(R-I)†)) + ε²[||X||² + Re(tr(X²R(R-I)†))]
#
# And: L = L₀ · √(1 + stuff/L₀²)
#      ≈ L₀ + stuff/(2L₀) - stuff²/(8L₀³) + ...
#
# First order in ε:
#   ΔL ≈ -Re(tr(XR(R-I)†)) / L₀
#   E[ΔL] = 0 if E_X[Re(tr(XR(R-I)†))] = 0 for X uniform in Λ²(R³)
#
# Second order in ε (the Itô drift):
#   E[ΔL]₂ ≈ ε²/(2L₀) · E[||X||² + Re(tr(X²R(R-I)†))]
#           - ε²/(2L₀³) · E[(Re(tr(XR(R-I)†)))²]
#
# The first term is positive (diffusion adds energy).
# The third term is negative (curvature correction).
# Saturation: when these balance.
# =====================================================================

def ito_drift_empirical(bases, P, eps, n_samples=1000, rng_seed=None):
    """Compute the expected ΔL and its components for random Λ²(R³) writes.

    For each random input v:
    - Compute the write X for each observer
    - Compute ΔL exactly (by applying the write)
    - Also compute the first and second order Taylor terms
    """
    rng = np.random.default_rng(rng_seed)
    N = len(bases)
    d = bases[0].shape[0]

    dL_values = []
    first_order = []
    second_order = []
    write_norms = []

    for _ in range(n_samples):
        v = rng.standard_normal(d)
        v /= np.linalg.norm(v)

        # measure
        all_m = []
        all_m_hat = []
        for k in range(N):
            mk = np.real(P @ (v @ bases[k]))
            n = np.linalg.norm(mk)
            all_m.append(mk)
            all_m_hat.append(mk / n if n > 1e-12 else mk)

        # compute writes
        writes = []
        for i in range(N):
            m = all_m[i]
            m_norm = np.linalg.norm(m)
            if m_norm < 1e-12:
                writes.append(np.zeros((d, d), dtype=complex))
                continue
            m_hat = m / m_norm
            others = [all_m_hat[k] for k in range(N) if k != i]
            centroid = np.mean(others, axis=0)
            target = m_hat - centroid
            t_norm = np.linalg.norm(target)
            if t_norm > 1e-12:
                target = target / t_norm
            j2 = target * m_norm
            d_vec = j2 - m
            d_norm = np.linalg.norm(d_vec)
            if d_norm < 1e-12:
                writes.append(np.zeros((d, d), dtype=complex))
                continue
            d_hat = d_vec / d_norm
            d_full = P.T @ d_hat
            m_full = P.T @ m_hat
            dL_mat = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
            dL_mat = skew_hermitian(dL_mat)
            writes.append(dL_mat)

        # exact ΔL
        L_before = compute_L(bases)
        new_bases = []
        for i in range(N):
            new_bases.append(bases[i] @ cayley(writes[i]))
        L_after = compute_L(new_bases)
        dL_exact = L_after - L_before
        dL_values.append(dL_exact)

        # write norms
        total_write_norm = sum(np.linalg.norm(w, 'fro')**2 for w in writes)
        write_norms.append(total_write_norm)

        # first order: for each pair (i,j), -Re(tr(X_i R_ij (R_ij - I)†)) / L_ij
        fo = 0.0
        for i in range(N):
            for j in range(i+1, N):
                R = bases[i].conj().T @ bases[j]
                diff = R - np.eye(d, dtype=complex)
                L_ij = np.linalg.norm(diff, 'fro')
                if L_ij < 1e-15:
                    continue
                # perturbation of U_i → U_i @ exp(X_i)
                # L_ij' = ||exp(-X_i)R_ij - I|| ≈ ||(R_ij - X_i R_ij) - I||
                # first order: -Re(tr(X_i R_ij diff†)) / L_ij
                fo -= np.real(np.trace(writes[i] @ R @ diff.conj().T)) / L_ij
                # perturbation of U_j → U_j @ exp(X_j)
                # L_ij' = ||R_ij exp(X_j) - I|| ≈ ||(R_ij + R_ij X_j) - I||
                # first order: Re(tr(R_ij X_j diff†)) / L_ij
                fo += np.real(np.trace(R @ writes[j] @ diff.conj().T)) / L_ij
        first_order.append(fo)

    return (np.array(dL_values), np.array(first_order),
            np.array(write_norms))


def measure_ito_drift_vs_L(d, N, eps, n_steps, rng_seed=42):
    """Run foam and at each step compute E[ΔL] and E[ΔL²].

    The Itô drift = E[ΔL] per step. At saturation this should be ≈ 0.
    The key: track how the drift transitions from positive to zero
    and whether we can identify the L level where it crosses zero.
    """
    rng = np.random.default_rng(rng_seed)
    bases = [random_unitary(d, rng) for _ in range(N)]

    Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
    P = Q[:, :3].T

    input_rng = np.random.default_rng(rng_seed + 1000)

    L_history = []
    dL_history = []

    L_prev = compute_L(bases)

    for t in range(n_steps):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)

        all_m = []
        all_m_hat = []
        for k in range(N):
            mk = np.real(P @ (v @ bases[k]))
            n = np.linalg.norm(mk)
            all_m.append(mk)
            all_m_hat.append(mk / n if n > 1e-12 else mk)

        for i in range(N):
            m = all_m[i]
            m_norm = np.linalg.norm(m)
            if m_norm < 1e-12:
                continue
            m_hat = m / m_norm
            others = [all_m_hat[k] for k in range(N) if k != i]
            centroid = np.mean(others, axis=0)
            target = m_hat - centroid
            t_norm = np.linalg.norm(target)
            if t_norm > 1e-12:
                target = target / t_norm
            j2 = target * m_norm
            d_vec = j2 - m
            d_norm = np.linalg.norm(d_vec)
            if d_norm < 1e-12:
                continue
            d_hat = d_vec / d_norm
            d_full = P.T @ d_hat
            m_full = P.T @ m_hat
            dL = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
            dL = skew_hermitian(dL)
            bases[i] = bases[i] @ cayley(dL)

        L_new = compute_L(bases)
        dL_val = L_new - L_prev
        L_history.append(L_new)
        dL_history.append(dL_val)
        L_prev = L_new

    return np.array(L_history), np.array(dL_history)


def find_drift_zero(L_history, dL_history, n_bins=20):
    """Bin ΔL by L level and find where E[ΔL] crosses zero."""
    L = np.array(L_history)
    dL = np.array(dL_history)

    # only use data after initial transient
    start = len(L) // 10
    L = L[start:]
    dL = dL[start:]

    bins = np.linspace(L.min(), L.max(), n_bins + 1)
    bin_centers = []
    bin_means = []
    bin_stds = []
    bin_counts = []

    for k in range(n_bins):
        mask = (L >= bins[k]) & (L < bins[k+1])
        if np.sum(mask) < 10:
            continue
        bin_centers.append((bins[k] + bins[k+1]) / 2)
        bin_means.append(np.mean(dL[mask]))
        bin_stds.append(np.std(dL[mask]) / np.sqrt(np.sum(mask)))
        bin_counts.append(np.sum(mask))

    return np.array(bin_centers), np.array(bin_means), np.array(bin_stds), np.array(bin_counts)


if __name__ == "__main__":
    print("=" * 70)
    print("PACKING EFFICIENCY DERIVATION — ITÔ DRIFT ANALYSIS")
    print("=" * 70)
    print()

    # ── Test 1: Drift vs L level ──
    print("Test 1: E[ΔL] as a function of L level (d=6, N=3)")
    print("-" * 50)
    print("  If E[ΔL] > 0 below saturation and < 0 above,")
    print("  the zero-crossing IS the saturation level.")
    print()

    for d_val in [4, 6, 8]:
        L_h, dL_h = measure_ito_drift_vs_L(d=d_val, N=3, eps=0.1, n_steps=10000)
        centers, means, stds, counts = find_drift_zero(L_h, dL_h, n_bins=15)

        L_max = 3 * 2 * np.sqrt(d_val)

        print(f"  d={d_val} (L_max={L_max:.2f}):")
        print(f"    {'L':>8} {'E[ΔL]':>12} {'±':>4} {'stderr':>10} {'n':>6}")
        for c, m, s, n in zip(centers, means, stds, counts):
            marker = " <-- zero" if abs(m) < 2*s and n > 50 else ""
            print(f"    {c:8.3f} {m:12.6f}    ± {s:10.6f} {n:6d}{marker}")
        print()

    # ── Test 2: At saturation, what is E[ΔL²] / E[write_norm²]? ──
    print("Test 2: Diffusion coefficient at saturation")
    print("-" * 50)
    print("  E[ΔL²] per step, normalized by write energy")
    print()

    for d_val in [4, 6, 8]:
        L_h, dL_h = measure_ito_drift_vs_L(d=d_val, N=3, eps=0.1, n_steps=10000)
        # use tail
        tail = int(0.7 * len(L_h))
        dL_tail = dL_h[tail:]
        L_sat = np.mean(L_h[tail:])
        L_max = 3 * 2 * np.sqrt(d_val)

        diffusion = np.mean(dL_tail**2)
        mean_dL = np.mean(dL_tail)
        print(f"  d={d_val}:")
        print(f"    L_sat = {L_sat:.4f}, L_sat/L_max = {L_sat/L_max:.4f}")
        print(f"    E[ΔL] at sat = {mean_dL:.6f}")
        print(f"    E[ΔL²] at sat = {diffusion:.8f}")
        print(f"    √(E[ΔL²]) = {np.sqrt(diffusion):.6f}")
    print()

    # ── Test 3: The critical question — can we predict L_sat? ──
    print("Test 3: Can we predict the saturation level from Λ²(R³)?")
    print("-" * 50)
    print()
    print("  The writes span Λ²(R³) = 3D of u(d).")
    print("  dim(u(d)) = d².")
    print("  The 'coverage fraction' of the Lie algebra is 3/d².")
    print()
    for d_val in [4, 6, 8, 10]:
        lie_dim = d_val**2
        write_dim = 3
        coverage = write_dim / lie_dim

        L_h, _ = measure_ito_drift_vs_L(d=d_val, N=3, eps=0.1, n_steps=5000)
        L_sat = np.mean(L_h[int(0.7*len(L_h)):])
        L_max = 3 * 2 * np.sqrt(d_val)
        sat_ratio = L_sat / L_max

        # achievable max
        n_pairs = 3
        sum_sq = 9 * d_val
        L_ach = np.sqrt(n_pairs * sum_sq)
        ach_ratio = L_ach / L_max
        sat_ach = L_sat / L_ach

        print(f"  d={d_val}: dim_u(d)={lie_dim:3d}  3/d²={coverage:.4f}  "
              f"L_sat/L_max={sat_ratio:.4f}  L_sat/L_ach={sat_ach:.4f}  "
              f"ach/max={ach_ratio:.4f}")
    print()

    # ── Test 4: Random walk on U(d) with TRULY random Λ²(R³) directions ──
    print("Test 4: Pure random walk in Λ²(R³) — no foam dynamics")
    print("-" * 50)
    print("  Apply random Λ²(R³) writes to N unitaries (no stabilization)")
    print("  Does L still saturate? At what level?")
    print()

    for d_val in [4, 6, 8]:
        rng = np.random.default_rng(42)
        N = 3
        bases = [random_unitary(d_val, rng) for _ in range(N)]

        Q = np.linalg.qr(rng.standard_normal((d_val, 3)))[0]
        P = Q[:, :3].T  # 3 x d

        eps = 0.1
        L_history = []

        for t in range(5000):
            for i in range(N):
                # random direction in Λ²(R³): pick two random vectors in R³,
                # lift to R^d via P.T, take wedge product
                a = rng.standard_normal(3)
                a /= np.linalg.norm(a)
                b = rng.standard_normal(3)
                b /= np.linalg.norm(b)
                a_full = P.T @ a
                b_full = P.T @ b
                X = eps * (np.outer(a_full, b_full.conj()) - np.outer(b_full, a_full.conj()))
                X = skew_hermitian(X)
                bases[i] = bases[i] @ cayley(X)

            L_history.append(compute_L(bases))

        L_sat = np.mean(L_history[int(0.7*len(L_history)):])
        L_max = 3 * 2 * np.sqrt(d_val)
        n_pairs = 3
        L_ach = np.sqrt(n_pairs * 9 * d_val)

        print(f"  d={d_val}: L_sat={L_sat:.3f}  L_sat/L_max={L_sat/L_max:.4f}  "
              f"L_sat/L_ach={L_sat/L_ach:.4f}")
    print()

    # ── Test 5: Random walk with FULL u(d) directions ──
    print("Test 5: Random walk in full u(d) — no 3D bottleneck")
    print("-" * 50)
    print("  If the 3D bottleneck causes the gap, removing it should raise L_sat")
    print()

    for d_val in [4, 6, 8]:
        rng = np.random.default_rng(42)
        N = 3
        bases = [random_unitary(d_val, rng) for _ in range(N)]
        eps = 0.1
        L_history = []

        for t in range(5000):
            for i in range(N):
                # random direction in full u(d)
                X = rng.standard_normal((d_val, d_val)) + 1j * rng.standard_normal((d_val, d_val))
                X = skew_hermitian(X)
                X = eps * X / np.linalg.norm(X, 'fro')
                bases[i] = bases[i] @ cayley(X)

            L_history.append(compute_L(bases))

        L_sat = np.mean(L_history[int(0.7*len(L_history)):])
        L_max = 3 * 2 * np.sqrt(d_val)
        n_pairs = 3
        L_ach = np.sqrt(n_pairs * 9 * d_val)

        print(f"  d={d_val}: L_sat={L_sat:.3f}  L_sat/L_max={L_sat/L_max:.4f}  "
              f"L_sat/L_ach={L_sat/L_ach:.4f}")
    print()

    print("=" * 70)
    print("KEY COMPARISON")
    print("  Foam dynamics:    L_sat/L_ach ≈ 0.83 (the perpendicularity cost)")
    print("  Random Λ²(R³):   L_sat/L_ach = ???")
    print("  Random u(d):     L_sat/L_ach = ???")
    print()
    print("  If random Λ²(R³) ≈ foam ≈ 0.83, the cost is purely geometric")
    print("  If random u(d) > random Λ²(R³) ≈ foam, the 3D bottleneck is the cause")
    print("  If random u(d) ≈ random Λ²(R³), the bottleneck doesn't matter")
    print("=" * 70)
