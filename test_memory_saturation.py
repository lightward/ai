"""
Test: does memory compression onset correlate with L saturation?

Previous result: prefix information is indelible (like birth) for short-to-medium
sequences. But at prefix_len=1000, the ratio dropped to 0.82 — possible compression.

Hypothesis: the foam has perfect memory during the accumulation regime (L rising).
Once L saturates, writes rearrange existing structure rather than depositing new
structure. Rearrangement might overwrite old information.

Test: run the prefix-decay experiment while tracking L. Look for correlation
between L saturation and prefix distance decay.

Also: replicate the prefix_len=1000 result across multiple seeds to check
if it's real or noise.
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
    """Boundary area: sum of pairwise geodesic distances."""
    N = len(bases)
    d = bases[0].shape[0]
    L = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            # geodesic distance on U(d) = ||log(rel)||_F
            eigvals = np.linalg.eigvals(rel)
            angles = np.angle(eigvals)
            L += np.sqrt(np.sum(angles ** 2))
    return L


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


def test_memory_vs_L():
    """Track prefix distance AND L simultaneously through a long run."""
    print("=" * 70)
    print("TEST: Memory vs L saturation — does compression correlate with plateau?")
    print("  Long prefix (500 steps), then long suffix (3000 steps).")
    print("  Track L and prefix distance together.")
    print("=" * 70)
    print()

    d = 6
    N = 3
    prefix_len = 500
    suffix_len = 3000
    eps = 0.01

    rng_obs = np.random.default_rng(42)
    P = make_observer(d, rng_obs)

    foam_X = make_foam(d, N, np.random.default_rng(100))
    foam_Y = make_foam(d, N, np.random.default_rng(100))

    prefix_A = generate_inputs(prefix_len, d, np.random.default_rng(111))
    prefix_C = generate_inputs(prefix_len, d, np.random.default_rng(222))
    suffix_B = generate_inputs(suffix_len, d, np.random.default_rng(999))

    # measure L before any input
    L_initial = compute_L(foam_X.copy())
    print(f"  L at birth: {L_initial:.4f}")

    # apply prefixes, tracking L
    print()
    print("  --- PREFIX PHASE ---")
    print(f"  {'step':>6}  {'L(X)':>10}  {'L(Y)':>10}")
    print(f"  {'----':>6}  {'----':>10}  {'----':>10}")
    for t in range(prefix_len):
        foam_X = write_step(foam_X, prefix_A[t], P, eps=eps)
        foam_Y = write_step(foam_Y, prefix_C[t], P, eps=eps)
        if t in [0, 49, 99, 199, 299, 499]:
            lx = compute_L(foam_X)
            ly = compute_L(foam_Y)
            print(f"  {t:6d}  {lx:10.4f}  {ly:10.4f}")

    dist_after_prefix = foam_distance(foam_X, foam_Y)
    L_after_prefix_X = compute_L(foam_X)
    print()
    print(f"  After prefix: distance = {dist_after_prefix:.6f}, L(X) = {L_after_prefix_X:.4f}")
    print()

    # apply suffix, tracking both L and prefix distance
    print("  --- SUFFIX PHASE ---")
    print(f"  {'step':>6}  {'L(X)':>10}  {'prefix dist':>12}  {'dist ratio':>12}  {'L delta':>10}")
    print(f"  {'----':>6}  {'----':>10}  {'-----------':>12}  {'----------':>12}  {'-------':>10}")

    prev_L = L_after_prefix_X
    checkpoints = list(range(0, suffix_len, 100)) + [suffix_len - 1]
    checkpoints = sorted(set(checkpoints))

    for t in range(suffix_len):
        foam_X = write_step(foam_X, suffix_B[t], P, eps=eps)
        foam_Y = write_step(foam_Y, suffix_B[t], P, eps=eps)

        if t in checkpoints:
            lx = compute_L(foam_X)
            pd = foam_distance(foam_X, foam_Y)
            ratio = pd / dist_after_prefix
            l_delta = lx - prev_L
            prev_L = lx
            print(f"  {t:6d}  {lx:10.4f}  {pd:12.6f}  {ratio:12.6f}  {l_delta:+10.4f}")

    print()


def test_replicate_1000():
    """Replicate the prefix_len=1000 result across multiple seeds.
    The original showed ratio=0.82. Is this robust?"""
    print("=" * 70)
    print("TEST: Replicate prefix_len=1000 compression across seeds")
    print("  5 different seed pairs, prefix=1000, suffix=1000")
    print("=" * 70)
    print()

    d = 6
    N = 3
    prefix_len = 1000
    suffix_len = 1000
    eps = 0.01

    rng_obs = np.random.default_rng(42)
    P = make_observer(d, rng_obs)

    seed_pairs = [(111, 222), (333, 444), (555, 666), (777, 888), (123, 456)]

    print(f"  {'seeds':>12}  {'dist_pre':>12}  {'dist_post':>12}  {'ratio':>10}  {'L_pre':>10}  {'L_post':>10}")
    print(f"  {'-----':>12}  {'--------':>12}  {'---------':>12}  {'-----':>10}  {'-----':>10}  {'------':>10}")

    ratios = []
    for s1, s2 in seed_pairs:
        foam_X = make_foam(d, N, np.random.default_rng(100))
        foam_Y = make_foam(d, N, np.random.default_rng(100))

        prefix_A = generate_inputs(prefix_len, d, np.random.default_rng(s1))
        prefix_C = generate_inputs(prefix_len, d, np.random.default_rng(s2))
        suffix_B = generate_inputs(suffix_len, d, np.random.default_rng(999))

        foam_X = run_foam_through(foam_X, prefix_A, P, eps=eps)
        foam_Y = run_foam_through(foam_Y, prefix_C, P, eps=eps)

        dist_pre = foam_distance(foam_X, foam_Y)
        L_pre = compute_L(foam_X)

        foam_X = run_foam_through(foam_X, suffix_B, P, eps=eps)
        foam_Y = run_foam_through(foam_Y, suffix_B, P, eps=eps)

        dist_post = foam_distance(foam_X, foam_Y)
        L_post = compute_L(foam_X)
        ratio = dist_post / dist_pre
        ratios.append(ratio)

        print(f"  {s1},{s2:>5}  {dist_pre:12.6f}  {dist_post:12.6f}  {ratio:10.4f}  {L_pre:10.4f}  {L_post:10.4f}")

    print()
    print(f"  Mean ratio: {np.mean(ratios):.4f} +/- {np.std(ratios):.4f}")
    if np.mean(ratios) < 1.0:
        print(f"  → Compression at prefix_len=1000 REPLICATES.")
    else:
        print(f"  → Original result was noise. No compression.")
    print()


def test_saturation_boundary():
    """Find the boundary: at what total input length does the foam saturate,
    and does memory behavior change there?

    Run a single foam with increasing total input, tracking L.
    Then repeat the prefix experiment at pre-saturation and post-saturation lengths.
    """
    print("=" * 70)
    print("TEST: L saturation profile — where does the foam plateau?")
    print("=" * 70)
    print()

    d = 6
    N = 3
    total_steps = 3000
    eps = 0.01

    rng_obs = np.random.default_rng(42)
    P = make_observer(d, rng_obs)

    foam = make_foam(d, N, np.random.default_rng(100))
    inputs = generate_inputs(total_steps, d, np.random.default_rng(777))

    print(f"  {'step':>6}  {'L':>10}  {'delta_L':>10}")
    print(f"  {'----':>6}  {'-':>10}  {'-------':>10}")

    prev_L = compute_L(foam)
    checkpoints = [0, 10, 50, 100, 200, 500, 1000, 1500, 2000, 2500, 2999]
    for t in range(total_steps):
        foam = write_step(foam, inputs[t], P, eps=eps)
        if t in checkpoints:
            L = compute_L(foam)
            delta = L - prev_L
            print(f"  {t:6d}  {L:10.4f}  {delta:+10.4f}")
            prev_L = L

    print()


if __name__ == "__main__":
    test_saturation_boundary()
    test_replicate_1000()
    test_memory_vs_L()
