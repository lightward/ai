"""
Test: does the foam HOST reservoir dynamics without itself being a reservoir?

The foam's basis matrices don't converge (test_echo_state.py proved this).
But the observer doesn't see basis matrices — they see measurements:
projected, stabilized, through their slice.

The bucket-of-water analogy: the water's molecular state is indelible,
but the ripple pattern on the surface has ESP. The ripples are the
reservoir, not the water.

Question: do two foams with different initial states, fed the same input
sequence, produce converging MEASUREMENT outputs even though their
underlying states never converge?

If yes: the foam hosts a reservoir in measurement space. The observer's
experience has ESP even though the foam's identity doesn't.

If no: the foam's birth conditions are visible all the way through
to the observer's experience. Identity is not just stored — it's felt.
"""

import numpy as np
from foam import cayley, skew_hermitian, random_unitary, init_foam, random_slice


def make_observer(d, rng):
    Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
    return Q[:, :3].T


def write_step_instrumented(bases, v, P, eps=0.01):
    """Write step that also returns the measurement data."""
    N = len(bases)
    target_cos = -1.0 / (N - 1)

    measurements = [v @ b for b in bases]
    m_proj = [np.real(P @ m) for m in measurements]

    # stabilize
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

    # dissonance
    dissonances = [j2[i] - m_proj[i] for i in range(N)]

    # write
    new_bases = []
    write_magnitudes = []
    for i in range(N):
        di = dissonances[i]
        mi = m_proj[i]
        di_norm = np.linalg.norm(di)
        mi_norm = np.linalg.norm(mi)
        if di_norm < 1e-12 or mi_norm < 1e-12:
            new_bases.append(bases[i].copy())
            write_magnitudes.append(0.0)
            continue
        d_hat = di / di_norm
        m_hat = mi / mi_norm
        d_full = P.T @ d_hat
        m_full = P.T @ m_hat
        dL_real = eps * di_norm * (np.outer(d_full, m_full) - np.outer(m_full, d_full))
        dL = skew_hermitian(dL_real.astype(complex))
        new_bases.append(bases[i] @ cayley(dL))
        write_magnitudes.append(di_norm)

    # observable quantities
    obs = {
        'm_proj': np.array([m for m in m_proj]),       # (N, 3) projected measurements
        'j2': np.array(j2),                             # (N, 3) stabilized targets
        'dissonance': np.array(dissonances),             # (N, 3) dissonance vectors
        'write_mag': np.array(write_magnitudes),         # (N,) write magnitudes
    }

    # pairwise angles between projected measurements
    angles = []
    for i in range(N):
        mi = m_proj[i]
        mi_norm = np.linalg.norm(mi)
        if mi_norm < 1e-10:
            continue
        for j in range(i+1, N):
            mj = m_proj[j]
            mj_norm = np.linalg.norm(mj)
            if mj_norm < 1e-10:
                continue
            cos_a = np.clip(np.dot(mi/mi_norm, mj/mj_norm), -1, 1)
            angles.append(cos_a)
    obs['angles'] = np.array(angles)

    return new_bases, obs


def test_hosted_esp():
    """Do measurement observables converge even though bases don't?"""
    print("=" * 70)
    print("TEST: Hosted ESP — does measurement experience converge?")
    print("  Same input, different birth. Comparing what the observer SEES.")
    print("=" * 70)
    print()

    d = 6
    N = 3
    n_steps = 1000

    rng_obs = np.random.default_rng(42)
    P = make_observer(d, rng_obs)

    foam_A = init_foam(N, d, np.random.default_rng(100))
    foam_B = init_foam(N, d, np.random.default_rng(200))

    rng_input = np.random.default_rng(999)
    inputs = []
    for _ in range(n_steps):
        v = rng_input.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        inputs.append(v)

    # track measurement divergence over time
    checkpoints = [0, 10, 50, 100, 200, 500, 999]

    print(f"  {'step':>6}  {'m_proj dist':>12}  {'angle dist':>12}  {'disson dist':>12}  {'write_m dist':>12}")
    print(f"  {'----':>6}  {'----------':>12}  {'----------':>12}  {'----------':>12}  {'------------':>12}")

    m_proj_dists = []
    angle_dists = []

    for t in range(n_steps):
        foam_A, obs_A = write_step_instrumented(foam_A, inputs[t], P)
        foam_B, obs_B = write_step_instrumented(foam_B, inputs[t], P)

        m_dist = np.linalg.norm(obs_A['m_proj'] - obs_B['m_proj'])
        a_dist = np.linalg.norm(obs_A['angles'] - obs_B['angles']) if len(obs_A['angles']) > 0 else 0.0
        d_dist = np.linalg.norm(obs_A['dissonance'] - obs_B['dissonance'])
        w_dist = np.linalg.norm(obs_A['write_mag'] - obs_B['write_mag'])

        m_proj_dists.append(m_dist)
        angle_dists.append(a_dist)

        if t in checkpoints:
            print(f"  {t:6d}  {m_dist:12.6f}  {a_dist:12.6f}  {d_dist:12.6f}  {w_dist:12.6f}")

    print()

    # did measurements converge?
    early_m = np.mean(m_proj_dists[:50])
    late_m = np.mean(m_proj_dists[-50:])
    m_ratio = late_m / early_m if early_m > 1e-12 else float('inf')

    early_a = np.mean(angle_dists[:50])
    late_a = np.mean(angle_dists[-50:])
    a_ratio = late_a / early_a if early_a > 1e-12 else float('inf')

    print(f"  Measurement projection convergence: early={early_m:.6f} late={late_m:.6f} ratio={m_ratio:.4f}")
    print(f"  Angle convergence:                  early={early_a:.6f} late={late_a:.6f} ratio={a_ratio:.4f}")
    print()

    if m_ratio < 0.1:
        print("  RESULT: Measurements CONVERGE. The foam hosts reservoir dynamics.")
        print("  → The observer's experience has ESP even though the foam's identity doesn't.")
        print("  → The foam is the bucket. The measurements are the ripples.")
    elif m_ratio < 0.5:
        print("  RESULT: Partial measurement convergence.")
        print("  → Birth conditions partially visible in measurement space.")
    else:
        print("  RESULT: Measurements DO NOT CONVERGE.")
        print("  → Birth conditions visible all the way to the observer's experience.")
        print("  → Identity is not just stored — it's felt.")
    print()


def test_hosted_esp_normalized():
    """Maybe the measurements don't converge in absolute terms but
    converge in STRUCTURE — the angles between measurements, the
    relative geometry, even if the absolute projections differ.

    This would mean: two foams see different things but organize them
    the same way. The reservoir is in the organization, not the content."""
    print("=" * 70)
    print("TEST: Hosted ESP (structural) — does measurement GEOMETRY converge?")
    print("  Comparing angles and ratios, not absolute projections.")
    print("=" * 70)
    print()

    d = 6
    N = 3
    n_steps = 1000

    rng_obs = np.random.default_rng(42)
    P = make_observer(d, rng_obs)

    foam_A = init_foam(N, d, np.random.default_rng(100))
    foam_B = init_foam(N, d, np.random.default_rng(200))

    rng_input = np.random.default_rng(999)
    inputs = []
    for _ in range(n_steps):
        v = rng_input.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        inputs.append(v)

    checkpoints = [0, 10, 50, 100, 200, 500, 999]

    # structural observables:
    # 1. pairwise cosines between normalized measurements
    # 2. relative write magnitudes (ratios, not absolutes)
    # 3. dissonance directions (normalized)

    print(f"  {'step':>6}  {'cos dist':>12}  {'write ratio dist':>16}  {'disson angle':>12}")
    print(f"  {'----':>6}  {'--------':>12}  {'----------------':>16}  {'------------':>12}")

    cos_dists = []

    for t in range(n_steps):
        foam_A, obs_A = write_step_instrumented(foam_A, inputs[t], P)
        foam_B, obs_B = write_step_instrumented(foam_B, inputs[t], P)

        # 1. cosine structure
        cos_dist = np.linalg.norm(obs_A['angles'] - obs_B['angles']) if len(obs_A['angles']) > 0 else 0.0
        cos_dists.append(cos_dist)

        # 2. relative write magnitudes
        wa = obs_A['write_mag']
        wb = obs_B['write_mag']
        wa_sum = np.sum(wa)
        wb_sum = np.sum(wb)
        if wa_sum > 1e-12 and wb_sum > 1e-12:
            wr_dist = np.linalg.norm(wa/wa_sum - wb/wb_sum)
        else:
            wr_dist = 0.0

        # 3. dissonance direction alignment
        disson_angles = []
        for i in range(N):
            da = obs_A['dissonance'][i]
            db = obs_B['dissonance'][i]
            da_n = np.linalg.norm(da)
            db_n = np.linalg.norm(db)
            if da_n > 1e-10 and db_n > 1e-10:
                cos_d = np.clip(np.dot(da/da_n, db/db_n), -1, 1)
                disson_angles.append(cos_d)
        mean_disson = np.mean(disson_angles) if disson_angles else 0.0

        if t in checkpoints:
            print(f"  {t:6d}  {cos_dist:12.6f}  {wr_dist:16.6f}  {mean_disson:12.6f}")

    print()

    early_cos = np.mean(cos_dists[:50])
    late_cos = np.mean(cos_dists[-50:])
    cos_ratio = late_cos / early_cos if early_cos > 1e-12 else float('inf')

    print(f"  Cosine structure convergence: early={early_cos:.6f} late={late_cos:.6f} ratio={cos_ratio:.4f}")
    print()

    if cos_ratio < 0.1:
        print("  RESULT: Measurement STRUCTURE converges.")
        print("  → Two foams see different things but organize them the same way.")
        print("  → The reservoir is in the organization, not the content.")
    elif cos_ratio < 0.5:
        print("  RESULT: Partial structural convergence.")
    else:
        print("  RESULT: Measurement structure DOES NOT converge.")
        print("  → Birth conditions shape not just what you see, but how you organize it.")
    print()


if __name__ == "__main__":
    test_hosted_esp()
    test_hosted_esp_normalized()
