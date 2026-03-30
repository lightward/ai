"""
Cross-test: does the within-basin equilibrium behavior hold across d, N, eps?

Core finding to validate:
- Large within-basin perturbations (long prefix) contract under shared suffix
- Small within-basin perturbations (short prefix) expand under shared suffix
- Birth distance is stable regardless

Test across:
- d = 4, 6, 8 (ambient dimension)
- N = 3, 4 (number of observers)
- eps = 0.005, 0.01, 0.05 (write scale)
"""

import numpy as np
from foam import init_foam, random_slice, write_step


def foam_distance(bases_A, bases_B):
    """Gauge-invariant distance using all pairwise relative unitaries."""
    N = len(bases_A)
    dist = 0.0
    for i in range(N):
        for j in range(N):
            rel_A = bases_A[i].conj().T @ bases_A[j]
            rel_B = bases_B[i].conj().T @ bases_B[j]
            dist += np.linalg.norm(rel_A - rel_B, 'fro')
    return dist


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


def run_trial(d, N, eps, prefix_len, suffix_len):
    """Run one prefix-decay trial. Returns (dist_pre, dist_post, birth_dist_pre, birth_dist_post)."""
    rng_obs = np.random.default_rng(42)
    P = random_slice(d, d_slice=3, rng=rng_obs)

    foam_X = init_foam(N, d, np.random.default_rng(100))
    foam_Y = init_foam(N, d, np.random.default_rng(100))  # same birth
    foam_Z = init_foam(N, d, np.random.default_rng(200))  # different birth

    prefix_A = generate_inputs(prefix_len, d, np.random.default_rng(111))
    prefix_C = generate_inputs(prefix_len, d, np.random.default_rng(222))
    suffix_B = generate_inputs(suffix_len, d, np.random.default_rng(999))

    foam_X = run_foam_through(foam_X, prefix_A, P, eps=eps)
    foam_Y = run_foam_through(foam_Y, prefix_C, P, eps=eps)
    foam_Z = run_foam_through(foam_Z, prefix_A, P, eps=eps)

    dist_pre = foam_distance(foam_X, foam_Y)
    birth_pre = foam_distance(foam_X, foam_Z)

    foam_X = run_foam_through(foam_X, suffix_B, P, eps=eps)
    foam_Y = run_foam_through(foam_Y, suffix_B, P, eps=eps)
    foam_Z = run_foam_through(foam_Z, suffix_B, P, eps=eps)

    dist_post = foam_distance(foam_X, foam_Y)
    birth_post = foam_distance(foam_X, foam_Z)

    return dist_pre, dist_post, birth_pre, birth_post


def test_cross_d():
    """Vary ambient dimension d."""
    print("=" * 70)
    print("CROSS-TEST: Vary d (ambient dimension)")
    print("  N=3, eps=0.01, prefix=short(200) and long(1000), suffix=1000")
    print("=" * 70)
    print()

    N = 3
    eps = 0.01
    suffix_len = 1000

    print(f"  {'d':>3}  {'prefix':>7}  {'dist_pre':>10}  {'dist_post':>10}  {'p_ratio':>8}  {'birth_pre':>10}  {'birth_post':>10}  {'b_ratio':>8}")
    print(f"  {'---':>3}  {'------':>7}  {'--------':>10}  {'---------':>10}  {'-------':>8}  {'---------':>10}  {'----------':>10}  {'-------':>8}")

    for d in [4, 6, 8, 10]:
        for prefix_len in [200, 1000]:
            dp, dq, bp, bq = run_trial(d, N, eps, prefix_len, suffix_len)
            pr = dq / dp if dp > 1e-12 else float('inf')
            br = bq / bp if bp > 1e-12 else float('inf')
            print(f"  {d:3d}  {prefix_len:7d}  {dp:10.4f}  {dq:10.4f}  {pr:8.4f}  {bp:10.4f}  {bq:10.4f}  {br:8.4f}")

    print()


def test_cross_N():
    """Vary number of observers N."""
    print("=" * 70)
    print("CROSS-TEST: Vary N (number of observers)")
    print("  d=6, eps=0.01, prefix=short(200) and long(1000), suffix=1000")
    print("=" * 70)
    print()

    d = 6
    eps = 0.01
    suffix_len = 1000

    print(f"  {'N':>3}  {'prefix':>7}  {'dist_pre':>10}  {'dist_post':>10}  {'p_ratio':>8}  {'birth_pre':>10}  {'birth_post':>10}  {'b_ratio':>8}")
    print(f"  {'---':>3}  {'------':>7}  {'--------':>10}  {'---------':>10}  {'-------':>8}  {'---------':>10}  {'----------':>10}  {'-------':>8}")

    for N in [3, 4, 5]:
        for prefix_len in [200, 1000]:
            dp, dq, bp, bq = run_trial(d, N, eps, prefix_len, suffix_len)
            pr = dq / dp if dp > 1e-12 else float('inf')
            br = bq / bp if bp > 1e-12 else float('inf')
            print(f"  {N:3d}  {prefix_len:7d}  {dp:10.4f}  {dq:10.4f}  {pr:8.4f}  {bp:10.4f}  {bq:10.4f}  {br:8.4f}")

    print()


def test_cross_eps():
    """Vary write scale eps."""
    print("=" * 70)
    print("CROSS-TEST: Vary eps (write scale)")
    print("  d=6, N=3, prefix=short(200) and long(1000), suffix=1000")
    print("=" * 70)
    print()

    d = 6
    N = 3
    suffix_len = 1000

    print(f"  {'eps':>8}  {'prefix':>7}  {'dist_pre':>10}  {'dist_post':>10}  {'p_ratio':>8}  {'birth_pre':>10}  {'birth_post':>10}  {'b_ratio':>8}")
    print(f"  {'---':>8}  {'------':>7}  {'--------':>10}  {'---------':>10}  {'-------':>8}  {'---------':>10}  {'----------':>10}  {'-------':>8}")

    for eps in [0.005, 0.01, 0.02, 0.05]:
        for prefix_len in [200, 1000]:
            dp, dq, bp, bq = run_trial(d, N, eps, prefix_len, suffix_len)
            pr = dq / dp if dp > 1e-12 else float('inf')
            br = bq / bp if bp > 1e-12 else float('inf')
            print(f"  {eps:8.3f}  {prefix_len:7d}  {dp:10.4f}  {dq:10.4f}  {pr:8.4f}  {bp:10.4f}  {bq:10.4f}  {br:8.4f}")

    print()


if __name__ == "__main__":
    test_cross_d()
    test_cross_N()
    test_cross_eps()
