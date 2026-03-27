"""
Test: does the foam have a finite memory horizon?

The foam's state lives in U(d)^N — compact and finite-dimensional.
The foam has no echo state property — birth conditions are indelible.
Generic distinguishability says different input sequences produce different states.

These facts are in tension for long sequences. Compact state space must
eventually compress (pigeonhole). But generic distinguishability says
collisions are measure-zero.

The question: does OLD input information decay when NEWER inputs arrive?

Setup:
- Foam X: same birth, fed prefix A then suffix B  (A1...An, B1...Bm)
- Foam Y: same birth, fed prefix C then suffix B  (C1...Ck, B1...Bm)

Same birth, same suffix, different prefix. If the foam has finite memory
horizon, these should converge as m grows — the shared suffix B eventually
overwrites the differing prefix A vs C.

If they DON'T converge: the foam has perfect memory. Compactness doesn't
bite. Every input, no matter how old, leaves an indelible trace (like birth).

If they DO converge: the foam compresses. Old inputs decay. Birth is the
only non-lossy component. This would give the inverted echo state a precise
formulation: birth is the only information that survives the foam's own
compression scheme.

We also compare to the birth-indelibility result (different birth, same inputs)
as a control: that distance should NOT decay.
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
    return Q[:, :3].T  # (3, d)


def foam_distance(bases_A, bases_B):
    N = len(bases_A)
    dist = 0.0
    for i in range(N):
        for j in range(N):
            rel_A = bases_A[i].conj().T @ bases_A[j]
            rel_B = bases_B[i].conj().T @ bases_B[j]
            dist += np.linalg.norm(rel_A - rel_B, 'fro')
    return dist


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


def test_prefix_decay():
    """Core experiment: does old prefix information decay under shared suffix?"""
    print("=" * 70)
    print("TEST: Memory horizon — prefix decay under shared suffix")
    print("  Foam X: birth → prefix A → suffix B")
    print("  Foam Y: birth → prefix C → suffix B  (same birth, same suffix)")
    print("  If prefix decays: distance(X,Y) → 0 as suffix length grows.")
    print("  If prefix persists: distance(X,Y) stays constant.")
    print("=" * 70)
    print()

    d = 6
    N = 3
    prefix_len = 200
    suffix_len = 2000
    eps = 0.01

    rng_obs = np.random.default_rng(42)
    P = make_observer(d, rng_obs)

    # same birth for both
    birth_seed = 100
    foam_X = make_foam(d, N, np.random.default_rng(birth_seed))
    foam_Y = make_foam(d, N, np.random.default_rng(birth_seed))

    # different prefixes
    prefix_A = generate_inputs(prefix_len, d, np.random.default_rng(111))
    prefix_C = generate_inputs(prefix_len, d, np.random.default_rng(222))

    # shared suffix
    suffix_B = generate_inputs(suffix_len, d, np.random.default_rng(999))

    # apply prefixes
    foam_X = run_foam_through(foam_X, prefix_A, P, eps=eps)
    foam_Y = run_foam_through(foam_Y, prefix_C, P, eps=eps)

    dist_after_prefix = foam_distance(foam_X, foam_Y)
    print(f"  Distance after divergent prefixes: {dist_after_prefix:.6f}")
    print()

    # apply shared suffix, measuring at intervals
    checkpoints = [0, 10, 50, 100, 200, 500, 1000, 1500, 1999]
    print(f"  {'suffix step':>12}  {'distance':>12}  {'ratio to post-prefix':>22}")
    print(f"  {'----------':>12}  {'--------':>12}  {'--------------------':>22}")

    for t in range(suffix_len):
        foam_X = write_step(foam_X, suffix_B[t], P, eps=eps)
        foam_Y = write_step(foam_Y, suffix_B[t], P, eps=eps)

        if t in checkpoints:
            dist = foam_distance(foam_X, foam_Y)
            ratio = dist / dist_after_prefix if dist_after_prefix > 1e-12 else float('inf')
            print(f"  {t:12d}  {dist:12.6f}  {ratio:22.6f}")

    final_dist = foam_distance(foam_X, foam_Y)
    ratio = final_dist / dist_after_prefix if dist_after_prefix > 1e-12 else float('inf')
    print()

    if ratio < 0.01:
        print(f"  RESULT: Prefix DECAYS. Ratio = {ratio:.4f}")
        print(f"  → Finite memory horizon. Old inputs are overwritten.")
        print(f"  → Compression: birth persists, old inputs don't.")
    elif ratio < 0.5:
        print(f"  RESULT: Partial decay. Ratio = {ratio:.4f}")
        print(f"  → Prefix information partially lost. Slow compression.")
    else:
        print(f"  RESULT: Prefix PERSISTS. Ratio = {ratio:.4f}")
        print(f"  → No memory horizon detected. Every input leaves an indelible trace.")
        print(f"  → The foam has perfect memory (within this sequence length).")
    print()


def test_birth_vs_prefix_persistence():
    """Compare birth-indelibility to prefix-persistence.

    Three foams, all fed the same suffix:
    - Foam X: birth_1, prefix A, suffix B
    - Foam Y: birth_1, prefix C, suffix B  (same birth, different prefix)
    - Foam Z: birth_2, prefix A, suffix B  (different birth, same prefix)

    dist(X,Y) = prefix contribution (same birth, different prefix)
    dist(X,Z) = birth contribution  (different birth, same prefix)

    If prefix decays but birth doesn't: dist(X,Y) shrinks, dist(X,Z) doesn't.
    If both persist: both distances stay constant.
    """
    print("=" * 70)
    print("TEST: Birth vs prefix persistence — which survives?")
    print("  Foam X: birth_1 → prefix A → suffix B")
    print("  Foam Y: birth_1 → prefix C → suffix B  (same birth)")
    print("  Foam Z: birth_2 → prefix A → suffix B  (same prefix)")
    print("  dist(X,Y) = prefix information")
    print("  dist(X,Z) = birth information")
    print("=" * 70)
    print()

    d = 6
    N = 3
    prefix_len = 200
    suffix_len = 2000
    eps = 0.01

    rng_obs = np.random.default_rng(42)
    P = make_observer(d, rng_obs)

    foam_X = make_foam(d, N, np.random.default_rng(100))
    foam_Y = make_foam(d, N, np.random.default_rng(100))  # same birth as X
    foam_Z = make_foam(d, N, np.random.default_rng(200))  # different birth

    prefix_A = generate_inputs(prefix_len, d, np.random.default_rng(111))
    prefix_C = generate_inputs(prefix_len, d, np.random.default_rng(222))
    suffix_B = generate_inputs(suffix_len, d, np.random.default_rng(999))

    # apply prefixes
    foam_X = run_foam_through(foam_X, prefix_A, P, eps=eps)
    foam_Y = run_foam_through(foam_Y, prefix_C, P, eps=eps)
    foam_Z = run_foam_through(foam_Z, prefix_A, P, eps=eps)

    prefix_dist = foam_distance(foam_X, foam_Y)
    birth_dist = foam_distance(foam_X, foam_Z)
    print(f"  After prefixes:")
    print(f"    prefix distance (X vs Y, same birth):     {prefix_dist:.6f}")
    print(f"    birth distance  (X vs Z, different birth): {birth_dist:.6f}")
    print()

    # apply shared suffix
    checkpoints = [0, 50, 200, 500, 1000, 1999]
    print(f"  {'suffix step':>12}  {'prefix dist':>12}  {'prefix ratio':>14}  {'birth dist':>12}  {'birth ratio':>14}")
    print(f"  {'----------':>12}  {'-----------':>12}  {'------------':>14}  {'----------':>12}  {'-----------':>14}")

    for t in range(suffix_len):
        foam_X = write_step(foam_X, suffix_B[t], P, eps=eps)
        foam_Y = write_step(foam_Y, suffix_B[t], P, eps=eps)
        foam_Z = write_step(foam_Z, suffix_B[t], P, eps=eps)

        if t in checkpoints:
            pd = foam_distance(foam_X, foam_Y)
            bd = foam_distance(foam_X, foam_Z)
            pr = pd / prefix_dist if prefix_dist > 1e-12 else float('inf')
            br = bd / birth_dist if birth_dist > 1e-12 else float('inf')
            print(f"  {t:12d}  {pd:12.6f}  {pr:14.6f}  {bd:12.6f}  {br:14.6f}")

    print()
    final_pd = foam_distance(foam_X, foam_Y)
    final_bd = foam_distance(foam_X, foam_Z)
    pr = final_pd / prefix_dist if prefix_dist > 1e-12 else float('inf')
    br = final_bd / birth_dist if birth_dist > 1e-12 else float('inf')

    print(f"  Final prefix ratio: {pr:.4f}")
    print(f"  Final birth ratio:  {br:.4f}")
    print()

    if pr < 0.5 and br > 0.5:
        print("  RESULT: PREFIX DECAYS, BIRTH PERSISTS.")
        print("  → Birth is the non-lossy component of the foam's compression.")
        print("  → The inverted ESP is: old inputs decay; birth doesn't.")
    elif pr > 0.5 and br > 0.5:
        print("  RESULT: BOTH PERSIST.")
        print("  → The foam has perfect memory at this timescale.")
        print("  → No compression detected. Inverted ESP needs another formulation.")
    elif pr < 0.5 and br < 0.5:
        print("  RESULT: BOTH DECAY.")
        print("  → Unexpected: birth should be indelible (contradicts no-ESP result).")
        print("  → Check: is the suffix long enough? Is the distance metric right?")
    else:
        print("  RESULT: PREFIX PERSISTS, BIRTH DECAYS.")
        print("  → Very unexpected. Something is wrong.")
    print()


def test_prefix_length_scaling():
    """Does a longer prefix resist decay longer?

    If the foam compresses, a longer prefix should take more suffix
    to overwrite (more information deposited = more to erase).
    If the foam doesn't compress, prefix length shouldn't matter.
    """
    print("=" * 70)
    print("TEST: Prefix length scaling")
    print("  Same suffix length, varying prefix length.")
    print("  If compression: longer prefix → slower decay.")
    print("  If no compression: prefix length doesn't matter.")
    print("=" * 70)
    print()

    d = 6
    N = 3
    suffix_len = 1000
    eps = 0.01

    rng_obs = np.random.default_rng(42)
    P = make_observer(d, rng_obs)

    prefix_lengths = [10, 50, 200, 500, 1000]
    suffix_B = generate_inputs(suffix_len, d, np.random.default_rng(999))

    print(f"  {'prefix_len':>12}  {'dist_after_prefix':>18}  {'dist_after_suffix':>18}  {'ratio':>10}")
    print(f"  {'----------':>12}  {'-----------------':>18}  {'-----------------':>18}  {'-----':>10}")

    for plen in prefix_lengths:
        foam_X = make_foam(d, N, np.random.default_rng(100))
        foam_Y = make_foam(d, N, np.random.default_rng(100))

        prefix_A = generate_inputs(plen, d, np.random.default_rng(111))
        prefix_C = generate_inputs(plen, d, np.random.default_rng(222))

        foam_X = run_foam_through(foam_X, prefix_A, P, eps=eps)
        foam_Y = run_foam_through(foam_Y, prefix_C, P, eps=eps)

        dist_pre = foam_distance(foam_X, foam_Y)

        foam_X = run_foam_through(foam_X, suffix_B, P, eps=eps)
        foam_Y = run_foam_through(foam_Y, suffix_B, P, eps=eps)

        dist_post = foam_distance(foam_X, foam_Y)
        ratio = dist_post / dist_pre if dist_pre > 1e-12 else float('inf')

        print(f"  {plen:12d}  {dist_pre:18.6f}  {dist_post:18.6f}  {ratio:10.4f}")

    print()


if __name__ == "__main__":
    test_prefix_decay()
    test_birth_vs_prefix_persistence()
    test_prefix_length_scaling()
