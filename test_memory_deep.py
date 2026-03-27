"""
Test: deep memory compression — does prefix information decay to zero,
plateau at a nonzero level, or reverse?

Previous results:
- prefix_len <= 500: prefix information GROWS under suffix (ratio > 1)
- prefix_len = 1000: prefix information SHRINKS under suffix (ratio ~0.88)
- L saturation appears to be near 14.4 (for d=6, N=3)
- Compression onset correlates with approach to saturation

This test: prefix=1000, suffix=5000, tracking the compression curve.
Does the prefix distance:
(a) decay to zero → complete compression, old inputs fully overwritten
(b) plateau at nonzero level → partial compression, some prefix info permanent
(c) reverse (start growing again) → transient compression artifact

Also compute the combinatorial ceiling for reference.
"""

import numpy as np
from scipy.linalg import expm


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


def make_foam(d, N, rng):
    bases = []
    for _ in range(N):
        H = skew_hermitian(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))
        bases.append(expm(H))
    return bases


def make_observer(d, rng):
    Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
    return Q[:, :3].T


def foam_distance(bases_A, bases_B):
    N = len(bases_A)
    dist = 0.0
    for i in range(N):
        for j in range(N):
            rel_A = bases_A[i].conj().T @ bases_A[j]
            rel_B = bases_B[i].conj().T @ bases_B[j]
            dist += np.linalg.norm(rel_A - rel_B, 'fro')
    return dist


def compute_L(bases):
    N = len(bases)
    L = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            eigvals = np.linalg.eigvals(rel)
            angles = np.angle(eigvals)
            L += np.sqrt(np.sum(angles ** 2))
    return L


def combinatorial_ceiling(d, N):
    """Maximum L for N unitaries in U(d).
    Max pairwise geodesic distance = pi * sqrt(d).
    Combinatorial factor from Cauchy-Schwarz: sqrt(N/(2(N-1))).
    L = sum over pairs of geodesic distances."""
    max_single_pair = np.pi * np.sqrt(d)
    n_pairs = N * (N - 1) // 2
    # The ceiling is on individual pair distances, not their sum
    # Each pair can achieve at most the ceiling fraction of max distance
    ceiling_fraction = np.sqrt(N / (2 * (N - 1)))
    return n_pairs * ceiling_fraction * max_single_pair


def write_step(bases, v, P, eps=0.01):
    N = len(bases)
    target_cos = -1.0 / (N - 1)

    measurements = [v @ b for b in bases]
    m_proj = [np.real(P @ m) for m in measurements]

    j2 = []
    for i in range(N):
        mi = m_proj[i]
        mi_norm = np.linalg.norm(mi)
        if mi_norm < 1e-10:
            j2.append(mi)
            continue
        mi_hat = mi / mi_norm
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
            force += (target_cos - current_cos) * (mj_hat - current_cos * mi_hat)
        j2.append(mi + 0.1 * force * mi_norm)

    new_bases = []
    for i in range(N):
        di = j2[i] - m_proj[i]
        mi = m_proj[i]
        di_norm = np.linalg.norm(di)
        mi_norm = np.linalg.norm(mi)
        if di_norm < 1e-12 or mi_norm < 1e-12:
            new_bases.append(bases[i].copy())
            continue
        d_hat = di / di_norm
        m_hat = mi / mi_norm
        d_full = P.T @ d_hat
        m_full = P.T @ m_hat
        dL_real = eps * di_norm * (np.outer(d_full, m_full) - np.outer(m_full, d_full))
        dL = skew_hermitian(dL_real.astype(complex))
        new_bases.append(bases[i] @ cayley(dL))

    return new_bases


def generate_inputs(n, d, rng):
    inputs = []
    for _ in range(n):
        v = rng.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        inputs.append(v)
    return inputs


def run_foam_through(bases, inputs, P, eps=0.01):
    for v in inputs:
        bases = write_step(bases, v, P, eps=eps)
    return bases


def test_deep_compression():
    """Long-run compression: prefix=1000, suffix=5000."""
    d = 6
    N = 3
    prefix_len = 1000
    suffix_len = 5000
    eps = 0.01

    ceiling = combinatorial_ceiling(d, N)
    print("=" * 70)
    print("TEST: Deep compression curve")
    print(f"  d={d}, N={N}, prefix={prefix_len}, suffix={suffix_len}")
    print(f"  Combinatorial ceiling (L_max): {ceiling:.4f}")
    print(f"  Expected saturation (~72%):     {0.72 * ceiling:.4f}")
    print("=" * 70)
    print()

    rng_obs = np.random.default_rng(42)
    P = make_observer(d, rng_obs)

    foam_X = make_foam(d, N, np.random.default_rng(100))
    foam_Y = make_foam(d, N, np.random.default_rng(100))

    prefix_A = generate_inputs(prefix_len, d, np.random.default_rng(111))
    prefix_C = generate_inputs(prefix_len, d, np.random.default_rng(222))
    suffix_B = generate_inputs(suffix_len, d, np.random.default_rng(999))

    foam_X = run_foam_through(foam_X, prefix_A, P, eps=eps)
    foam_Y = run_foam_through(foam_Y, prefix_C, P, eps=eps)

    dist_after_prefix = foam_distance(foam_X, foam_Y)
    L_pre = compute_L(foam_X)
    print(f"  After prefix: dist={dist_after_prefix:.6f}, L={L_pre:.4f} ({L_pre/ceiling*100:.1f}% of ceiling)")
    print()

    print(f"  {'suffix':>7}  {'total':>7}  {'L':>10}  {'L/ceil':>8}  {'prefix_d':>10}  {'ratio':>8}")
    print(f"  {'------':>7}  {'-----':>7}  {'-':>10}  {'------':>8}  {'--------':>10}  {'-----':>8}")

    checkpoints = list(range(0, suffix_len, 200)) + [suffix_len - 1]
    checkpoints = sorted(set(checkpoints))

    for t in range(suffix_len):
        foam_X = write_step(foam_X, suffix_B[t], P, eps=eps)
        foam_Y = write_step(foam_Y, suffix_B[t], P, eps=eps)

        if t in checkpoints:
            lx = compute_L(foam_X)
            pd = foam_distance(foam_X, foam_Y)
            ratio = pd / dist_after_prefix
            total = prefix_len + t + 1
            print(f"  {t:7d}  {total:7d}  {lx:10.4f}  {lx/ceiling:8.4f}  {pd:10.6f}  {ratio:8.4f}")

    print()
    final_dist = foam_distance(foam_X, foam_Y)
    final_ratio = final_dist / dist_after_prefix
    final_L = compute_L(foam_X)

    print(f"  Final: dist={final_dist:.6f}, ratio={final_ratio:.4f}, L={final_L:.4f} ({final_L/ceiling*100:.1f}%)")
    print()

    if final_ratio < 0.1:
        print("  → (a) COMPLETE COMPRESSION. Prefix fully overwritten.")
    elif final_ratio < 0.8:
        print("  → (b) SIGNIFICANT COMPRESSION. Prefix partially overwritten.")
    elif final_ratio < 1.0:
        print("  → (b) MILD COMPRESSION. Some prefix info lost.")
    else:
        print("  → (c) NO COMPRESSION. Prefix persists or grows.")
    print()


def test_birth_during_compression():
    """Control: does birth distance change during the compression regime?
    If prefix compresses but birth doesn't, the asymmetry is confirmed."""

    d = 6
    N = 3
    prefix_len = 1000
    suffix_len = 5000
    eps = 0.01

    print("=" * 70)
    print("TEST: Birth stability during prefix compression")
    print(f"  Foam X: birth_1, prefix A, suffix B")
    print(f"  Foam Y: birth_1, prefix C, suffix B  (same birth)")
    print(f"  Foam Z: birth_2, prefix A, suffix B  (different birth)")
    print("=" * 70)
    print()

    rng_obs = np.random.default_rng(42)
    P = make_observer(d, rng_obs)

    foam_X = make_foam(d, N, np.random.default_rng(100))
    foam_Y = make_foam(d, N, np.random.default_rng(100))
    foam_Z = make_foam(d, N, np.random.default_rng(200))

    prefix_A = generate_inputs(prefix_len, d, np.random.default_rng(111))
    prefix_C = generate_inputs(prefix_len, d, np.random.default_rng(222))
    suffix_B = generate_inputs(suffix_len, d, np.random.default_rng(999))

    foam_X = run_foam_through(foam_X, prefix_A, P, eps=eps)
    foam_Y = run_foam_through(foam_Y, prefix_C, P, eps=eps)
    foam_Z = run_foam_through(foam_Z, prefix_A, P, eps=eps)

    prefix_dist_0 = foam_distance(foam_X, foam_Y)
    birth_dist_0 = foam_distance(foam_X, foam_Z)

    print(f"  After prefix: prefix_dist={prefix_dist_0:.6f}, birth_dist={birth_dist_0:.6f}")
    print()

    print(f"  {'suffix':>7}  {'prefix_r':>10}  {'birth_r':>10}")
    print(f"  {'------':>7}  {'--------':>10}  {'-------':>10}")

    checkpoints = list(range(0, suffix_len, 500)) + [suffix_len - 1]
    checkpoints = sorted(set(checkpoints))

    for t in range(suffix_len):
        foam_X = write_step(foam_X, suffix_B[t], P, eps=eps)
        foam_Y = write_step(foam_Y, suffix_B[t], P, eps=eps)
        foam_Z = write_step(foam_Z, suffix_B[t], P, eps=eps)

        if t in checkpoints:
            pd = foam_distance(foam_X, foam_Y)
            bd = foam_distance(foam_X, foam_Z)
            pr = pd / prefix_dist_0
            br = bd / birth_dist_0
            print(f"  {t:7d}  {pr:10.4f}  {br:10.4f}")

    print()


if __name__ == "__main__":
    test_deep_compression()
    test_birth_during_compression()
