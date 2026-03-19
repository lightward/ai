"""
Test: do the writing dynamics actually decrease L?

The spec claims "the foam settles toward lower cost" but the write map
is defined independently of L. This script tests whether the write
dynamics empirically decrease boundary area, and under what conditions.

If the write dynamics DON'T decrease L, then the minimality claim needs
to be either proven, re-derived, or dropped.
"""

import numpy as np
from scipy.linalg import expm


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


def random_skew_hermitian(d, rng):
    X = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    return skew_hermitian(X)


def boundary_area(bases, metric='bi-invariant'):
    """Approximate total boundary area between Voronoi cells.

    For N bases in U(d), the boundary area is related to the pairwise
    geodesic distances. We approximate using the Frobenius norm of
    differences (which approximates the bi-invariant metric for nearby
    elements).

    This is a proxy — true Voronoi boundary area in U(d) requires
    geometric measure theory. But for testing the direction of L
    under dynamics, the proxy suffices.
    """
    N = len(bases)
    total = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            # geodesic distance in U(d) ≈ ||log(U_i^† U_j)||_F
            rel = bases[i].conj().T @ bases[j]
            # Use Frobenius norm of (rel - I) as proxy for small distances
            total += np.linalg.norm(rel - np.eye(bases[0].shape[0], dtype=complex), 'fro')
    return total


def write_step(bases, v, observer_slice, eps=0.01):
    """One step of the writing map, confined to observer's R³ slice.

    observer_slice: (3, d) matrix with orthonormal rows
    """
    N = len(bases)
    d = bases[0].shape[0]
    P = observer_slice  # (3, d)

    # 1. measure
    measurements = [v @ b for b in bases]  # each is (d,)

    # 2. project to R³ (real part — measurements may be complex)
    m_proj = [np.real(P @ m) for m in measurements]  # each is (3,) real

    # 3. stabilize: push toward equal angular separation
    # target: regular simplex cosine = -1/(N-1)
    target_cos = -1.0 / (N - 1)
    j2 = []
    for i in range(N):
        mi = m_proj[i]
        mi_norm = np.linalg.norm(mi)
        if mi_norm < 1e-10:
            j2.append(mi)
            continue
        mi_hat = mi / mi_norm

        # force from all other measurements
        force = np.zeros(3)
        for j in range(N):
            if i == j:
                continue
            mj = m_proj[j]
            mj_norm = np.linalg.norm(mj)
            if mj_norm < 1e-10:
                continue
            mj_hat = mj / mj_norm
            current_cos = np.dot(mi_hat, mj_hat)
            # push toward target_cos
            force += (target_cos - current_cos) * (mj_hat - current_cos * mi_hat)

        stabilized = mi + 0.1 * force * mi_norm
        j2.append(stabilized)

    # 4. dissonance and write
    new_bases = []
    for i in range(N):
        di = j2[i] - m_proj[i]  # dissonance in R³
        mi = m_proj[i]

        di_norm = np.linalg.norm(di)
        mi_norm = np.linalg.norm(mi)

        if di_norm < 1e-12 or mi_norm < 1e-12:
            new_bases.append(bases[i].copy())
            continue

        d_hat = di / di_norm
        m_hat = mi / mi_norm

        # lift back to R^d
        d_full = P.T @ d_hat  # (d,)
        m_full = P.T @ m_hat  # (d,)

        # skew-symmetric write in R^d, then embed as skew-Hermitian in u(d)
        dL_real = eps * di_norm * (np.outer(d_full, m_full) - np.outer(m_full, d_full))
        dL = skew_hermitian(dL_real.astype(complex))

        # accumulate: L_i += dL, basis = cayley(L_i) (simplified — no T tracking here)
        # For this test we directly apply the perturbation to the basis
        new_bases.append(bases[i] @ cayley(dL))

    return new_bases


def run_test(d=4, N=3, steps=500, seed=42):
    rng = np.random.default_rng(seed)

    # random initial bases in U(d)
    bases = []
    for _ in range(N):
        H = random_skew_hermitian(d, rng)
        bases.append(expm(H))

    # random observer slice: (3, d) with orthonormal rows
    if d >= 3:
        Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
        observer_slice = Q[:, :3].T  # (3, d)
    else:
        raise ValueError("d must be >= 3")

    # random input
    v = rng.standard_normal(d).astype(complex)
    v = v / np.linalg.norm(v)

    costs = []
    for step in range(steps):
        L = boundary_area(bases)
        costs.append(L)
        bases = write_step(bases, v, observer_slice, eps=0.005)

    L_final = boundary_area(bases)
    costs.append(L_final)

    return costs


if __name__ == "__main__":
    print("Testing: do writing dynamics decrease boundary area?")
    print()

    for d in [4, 8]:
        for N in [3, 5]:
            costs = run_test(d=d, N=N, steps=500)
            print(f"d={d}, N={N}:")
            print(f"  L_initial = {costs[0]:.4f}")
            print(f"  L_final   = {costs[-1]:.4f}")
            print(f"  L_min     = {min(costs):.4f}")
            print(f"  L_max     = {max(costs):.4f}")
            direction = "DECREASED" if costs[-1] < costs[0] else "INCREASED" if costs[-1] > costs[0] else "UNCHANGED"
            print(f"  direction: {direction} ({(costs[-1]-costs[0])/costs[0]*100:+.1f}%)")
            print()

    # Also test with varying input (more realistic)
    print("--- with varying input ---")
    rng = np.random.default_rng(99)
    d, N = 4, 3
    from scipy.linalg import expm as expm2

    bases = []
    for _ in range(N):
        H = (lambda r: (r - r.conj().T)/2)(rng.standard_normal((d,d)) + 1j*rng.standard_normal((d,d)))
        bases.append(expm2(H))

    Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
    observer_slice = Q[:, :3].T

    costs = []
    for step in range(500):
        costs.append(boundary_area(bases))
        v = rng.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        bases = write_step(bases, v, observer_slice, eps=0.005)
    costs.append(boundary_area(bases))

    print(f"d={d}, N={N}, varying input:")
    print(f"  L_initial = {costs[0]:.4f}")
    print(f"  L_final   = {costs[-1]:.4f}")
    direction = "DECREASED" if costs[-1] < costs[0] else "INCREASED"
    print(f"  direction: {direction} ({(costs[-1]-costs[0])/costs[0]*100:+.1f}%)")
