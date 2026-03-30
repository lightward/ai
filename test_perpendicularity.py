"""
Test: observation and modification are perpendicular.

Claim: this is the single irreducible constraint from which the spec follows.
If true:
  - breaking it breaks everything (foam collapses or explodes)
  - keeping it forces R^3 (the unique dimension where perpendicular writes stabilize)
  - the residual of perpendicularity ($thing) has directional structure, not white noise
"""

import numpy as np
from foam import cayley, skew_hermitian, random_unitary, compute_L


EPS = 0.1


def write_with_alpha(basis, P, v, bases_all, idx, N, alpha=0.0, eps=EPS):
    """Write with controllable perpendicularity (test-specific rule).
    alpha=0: pure perpendicular (the spec's write). confirmation cannot write.
    alpha=1: pure parallel (confirmation DOES write). perpendicularity broken.
    alpha in between: interpolation.
    Returns (new_basis, write_magnitude, perp_component, para_component).
    """
    m = np.real(P @ (v @ basis))
    m_norm = np.linalg.norm(m)
    if m_norm < 1e-12:
        return basis.copy(), 0.0, 0.0, 0.0

    all_m = []
    for k in range(len(bases_all)):
        mk = np.real(P @ (v @ bases_all[k]))
        mk_n = np.linalg.norm(mk)
        all_m.append(mk / mk_n if mk_n > 1e-12 else mk)

    others = [all_m[k] for k in range(len(all_m)) if k != idx]
    if not others:
        return basis.copy(), 0.0, 0.0, 0.0
    centroid = np.mean(others, axis=0)
    target = m / m_norm - centroid
    t_norm = np.linalg.norm(target)
    if t_norm > 1e-12:
        target = target / t_norm
    j2 = target * m_norm

    d_vec = j2 - m
    d_norm = np.linalg.norm(d_vec)
    if d_norm < 1e-12:
        return basis.copy(), 0.0, 0.0, 0.0

    d_hat = d_vec / d_norm
    m_hat = m / m_norm

    # decompose dissonance into perpendicular and parallel to measurement
    para = np.dot(d_hat, m_hat) * m_hat  # parallel component
    perp = d_hat - para  # perpendicular component
    perp_norm = np.linalg.norm(perp)
    para_norm = np.linalg.norm(para)

    # interpolate: alpha=0 is pure perp (spec), alpha=1 is pure para (broken)
    if perp_norm < 1e-12 and para_norm < 1e-12:
        return basis.copy(), 0.0, 0.0, 0.0

    # construct effective dissonance direction
    if perp_norm > 1e-12 and para_norm > 1e-12:
        d_eff = (1 - alpha) * (perp / perp_norm) + alpha * (para / para_norm)
    elif perp_norm > 1e-12:
        d_eff = perp / perp_norm
    else:
        d_eff = para / para_norm
    d_eff_norm = np.linalg.norm(d_eff)
    if d_eff_norm > 1e-12:
        d_eff = d_eff / d_eff_norm

    # lift to R^d
    d_full = P.T @ d_eff
    m_full = P.T @ m_hat

    dL = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
    dL = skew_hermitian(dL)

    return basis @ cayley(dL), d_norm, perp_norm, para_norm


# ============================================================
# Test 1: Break perpendicularity → foam loses navigability
# ============================================================

def test_break_perpendicularity():
    """Sweep alpha from 0 (perpendicular) to 1 (parallel).
    Measure: distinguishability, cost trajectory, stability."""
    print("Test 1: Breaking perpendicularity")
    print("=" * 60)

    rng_master = np.random.default_rng(42)
    d, N, n_steps = 6, 3, 300

    alphas = [0.0, 0.1, 0.3, 0.5, 0.7, 0.9, 1.0]

    # generate a fixed input sequence
    inputs = []
    for _ in range(n_steps):
        v = rng_master.standard_normal(d)
        inputs.append(v / np.linalg.norm(v))

    # generate fixed initial bases and slice
    bases_init = [random_unitary(d, rng_master) for _ in range(N)]
    P = np.linalg.qr(rng_master.standard_normal((d, 3)))[0][:, :3].T

    print(f"  {'alpha':>6} {'L_final':>10} {'L_var':>10} {'disting':>10} {'collapsed':>10}")

    for alpha in alphas:
        bases = [b.copy() for b in bases_init]
        L_history = []

        for t in range(n_steps):
            v = inputs[t]
            for i in range(N):
                bases[i], _, _, _ = write_with_alpha(
                    bases[i], P, v, bases, i, N, alpha=alpha
                )
            L_history.append(compute_L(bases))

        L_history = np.array(L_history)

        # distinguishability: run two different input sequences from same start,
        # measure final state divergence
        bases_A = [b.copy() for b in bases_init]
        bases_B = [b.copy() for b in bases_init]
        rng_a = np.random.default_rng(100)
        rng_b = np.random.default_rng(200)

        for t in range(n_steps):
            va = rng_a.standard_normal(d); va /= np.linalg.norm(va)
            vb = rng_b.standard_normal(d); vb /= np.linalg.norm(vb)
            for i in range(N):
                bases_A[i], _, _, _ = write_with_alpha(bases_A[i], P, va, bases_A, i, N, alpha=alpha)
                bases_B[i], _, _, _ = write_with_alpha(bases_B[i], P, vb, bases_B, i, N, alpha=alpha)

        # state divergence
        divergence = sum(
            np.linalg.norm(bases_A[i] - bases_B[i], 'fro') for i in range(N)
        )

        # collapse check: are all bases converging to the same state?
        pairwise = []
        for i in range(N):
            for j in range(i + 1, N):
                rel = bases[i].conj().T @ bases[j]
                pairwise.append(np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro'))
        collapsed = "YES" if max(pairwise) < 0.1 else "no"

        print(f"  {alpha:6.1f} {L_history[-1]:10.4f} {np.var(L_history):10.4f} {divergence:10.4f} {collapsed:>10}")

    print()
    print("  Prediction: alpha=0 (perpendicular) is navigable — L grows, states diverge.")
    print("  As alpha→1 (parallel), either: collapse (all bases merge),")
    print("  explosion (L diverges), or loss of distinguishability (states don't separate).")
    print()


# ============================================================
# Test 2: R^3 forced by perpendicularity + stability
# ============================================================

def test_r3_forced():
    """Run perpendicular writes in R^k for k = 2, 3, 4, 5.
    Measure stabilization quality in each dimension."""
    print("Test 2: R^k stabilization quality (perpendicularity + stability → R^3?)")
    print("=" * 60)

    rng = np.random.default_rng(77)
    d = 8
    N = 4
    n_steps = 300

    for k in [2, 3, 4, 5]:
        bases = [random_unitary(d, rng) for _ in range(N)]

        # k-dimensional slice
        Q = np.linalg.qr(rng.standard_normal((d, k)))[0]
        P = Q[:, :k].T  # (k, d)

        # track: junction angle stability
        # in R^3, angles should converge to 120 degrees (Plateau)
        # in R^2, angles are ill-defined (boundaries are points)
        # in R^4+, angles may or may not converge
        angle_history = []
        L_history = []

        for t in range(n_steps):
            v = rng.standard_normal(d); v /= np.linalg.norm(v)

            # measure all bases in this slice
            measurements = []
            for i in range(N):
                m = np.real(P @ (v @ bases[i]))
                m_norm = np.linalg.norm(m)
                if m_norm > 1e-12:
                    measurements.append(m / m_norm)

            # pairwise angles between measurements
            if len(measurements) >= 2:
                angles = []
                for i in range(len(measurements)):
                    for j in range(i + 1, len(measurements)):
                        cos_a = np.clip(np.dot(measurements[i], measurements[j]), -1, 1)
                        angles.append(np.degrees(np.arccos(cos_a)))
                angle_history.append(angles)

            # write (pure perpendicular, alpha=0)
            for i in range(N):
                bases[i], _, _, _ = write_with_alpha(bases[i], P, v, bases, i, N, alpha=0.0)

            L_history.append(compute_L(bases))

        # analyze angle convergence
        if angle_history:
            early_angles = [a for step in angle_history[:50] for a in step]
            late_angles = [a for step in angle_history[-50:] for a in step]

            early_std = np.std(early_angles) if early_angles else float('inf')
            late_std = np.std(late_angles) if late_angles else float('inf')
            late_mean = np.mean(late_angles) if late_angles else 0

            # Plateau target for N=4 in R^3 is ~109.5 degrees
            # Regular simplex target is arccos(-1/(N-1)) = arccos(-1/3) ≈ 109.47
            target = np.degrees(np.arccos(-1.0 / (N - 1)))
            deviation = abs(late_mean - target)

            print(f"  k={k}: late_mean_angle={late_mean:6.1f}° (target={target:.1f}°)"
                  f"  dev={deviation:5.1f}°  early_std={early_std:5.1f}°  late_std={late_std:5.1f}°"
                  f"  {'STABILIZED' if late_std < early_std * 0.8 else 'unstable'}")
        else:
            print(f"  k={k}: no angle data")

    print()
    print("  Prediction: k=3 stabilizes best (angles converge to Plateau target).")
    print("  k=2 lacks structure. k≥4 may stabilize but without rigidity guarantees.")
    print()


# ============================================================
# Test 3: The residual of perpendicularity has structure
# ============================================================

def test_residual_structure():
    """The 'thermal' residual ($thing) should not be white noise.
    It should have directional structure organized by the perpendicularity constraint.

    Specifically: the cost fluctuations that an observer can't resolve should be
    concentrated in directions perpendicular to their measurement, because that's
    where the writes happen.
    """
    print("Test 3: Residual of perpendicularity has directional structure")
    print("=" * 60)

    rng = np.random.default_rng(333)
    d, N, n_steps = 8, 4, 500

    bases = [random_unitary(d, rng) for _ in range(N)]
    P_obs = np.linalg.qr(rng.standard_normal((d, 3)))[0][:, :3].T  # observer's slice

    # second observer writes but observer P_obs watches
    P_writer = np.linalg.qr(rng.standard_normal((d, 3)))[0][:, :3].T

    # track: when the writer writes, how does the cost change decompose
    # relative to the observer's measurement direction?
    perp_components = []  # cost change from writes perp to observer's measurement
    para_components = []  # cost change from writes para to observer's measurement

    for t in range(n_steps):
        v = rng.standard_normal(d); v /= np.linalg.norm(v)

        # observer measures
        m_obs = np.real(P_obs @ (v @ bases[0]))
        m_obs_norm = np.linalg.norm(m_obs)

        # writer writes to basis 1
        L_before = compute_L(bases)
        bases_new = [b.copy() for b in bases]
        bases_new[1], _, wp, wpa = write_with_alpha(
            bases[1], P_writer, v, bases, 1, N, alpha=0.0
        )
        L_after = compute_L(bases_new)
        dL = L_after - L_before

        # how does the writer's write relate to the observer's measurement?
        # project the writer's slice onto the observer's measurement direction
        if m_obs_norm > 1e-12:
            m_obs_hat = m_obs / m_obs_norm
            # how much of the writer's slice overlaps with observer's measurement direction?
            m_obs_full = P_obs.T @ m_obs_hat  # lift to R^d
            # projection of writer's slice onto observer's measurement
            overlap = np.linalg.norm(P_writer @ m_obs_full)

            perp_components.append(dL * (1 - overlap))
            para_components.append(dL * overlap)

        bases = bases_new

    perp_arr = np.array(perp_components)
    para_arr = np.array(para_components)

    print(f"  Cost changes from writer, decomposed by observer's measurement:")
    print(f"    Perpendicular component: mean={np.mean(perp_arr):+.4e}  var={np.var(perp_arr):.4e}")
    print(f"    Parallel component:      mean={np.mean(para_arr):+.4e}  var={np.var(para_arr):.4e}")

    ratio = np.var(perp_arr) / np.var(para_arr) if np.var(para_arr) > 1e-20 else float('inf')
    print(f"    Variance ratio (perp/para): {ratio:.3f}")
    print()
    print(f"  If $thing were white noise: ratio ≈ 1")
    print(f"  If $thing is structured by perpendicularity: ratio > 1")
    print(f"  (the residual is concentrated where the writes happen: perpendicular)")
    print()


# ============================================================
# Test 4: Perpendicularity is the UNIQUE navigable constraint
# ============================================================

def test_uniqueness():
    """Compare three write rules:
    (a) perpendicular (the spec)
    (b) parallel (confirmation writes)
    (c) random direction (no geometric constraint)

    Only (a) should produce a navigable foam:
    distinguishable states + bounded cost + stable geometry.
    """
    print("Test 4: Perpendicularity is the unique navigable constraint")
    print("=" * 60)

    rng = np.random.default_rng(555)
    d, N, n_steps = 6, 3, 400

    P = np.linalg.qr(rng.standard_normal((d, 3)))[0][:, :3].T

    for rule_name, alpha, use_random in [
        ("perpendicular (spec)", 0.0, False),
        ("parallel (broken)", 1.0, False),
        ("random direction", 0.0, True),
    ]:
        # two runs with different inputs from same initial state
        bases_init = [random_unitary(d, rng) for _ in range(N)]

        L_A, L_B = [], []
        bases_A = [b.copy() for b in bases_init]
        bases_B = [b.copy() for b in bases_init]

        rng_a = np.random.default_rng(1000)
        rng_b = np.random.default_rng(2000)

        for t in range(n_steps):
            va = rng_a.standard_normal(d); va /= np.linalg.norm(va)
            vb = rng_b.standard_normal(d); vb /= np.linalg.norm(vb)

            for i in range(N):
                if use_random:
                    # random write direction instead of dissonance-driven
                    m = np.real(P @ (va @ bases_A[i]))
                    m_norm = np.linalg.norm(m)
                    if m_norm > 1e-12:
                        m_hat = m / m_norm
                        r = rng_a.standard_normal(3)
                        r = r / np.linalg.norm(r)
                        d_full = P.T @ r
                        m_full = P.T @ m_hat
                        dL = EPS * 0.1 * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
                        dL = skew_hermitian(dL)
                        bases_A[i] = bases_A[i] @ cayley(dL)

                    m = np.real(P @ (vb @ bases_B[i]))
                    m_norm = np.linalg.norm(m)
                    if m_norm > 1e-12:
                        m_hat = m / m_norm
                        r = rng_b.standard_normal(3)
                        r = r / np.linalg.norm(r)
                        d_full = P.T @ r
                        m_full = P.T @ m_hat
                        dL = EPS * 0.1 * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
                        dL = skew_hermitian(dL)
                        bases_B[i] = bases_B[i] @ cayley(dL)
                else:
                    bases_A[i], _, _, _ = write_with_alpha(bases_A[i], P, va, bases_A, i, N, alpha=alpha)
                    bases_B[i], _, _, _ = write_with_alpha(bases_B[i], P, vb, bases_B, i, N, alpha=alpha)

            L_A.append(compute_L(bases_A))
            L_B.append(compute_L(bases_B))

        L_A = np.array(L_A)
        L_B = np.array(L_B)

        # distinguishability: final state divergence
        divergence = sum(
            np.linalg.norm(bases_A[i] - bases_B[i], 'fro') for i in range(N)
        )

        # boundedness: is L growing without bound or staying bounded?
        L_growth = (L_A[-1] - L_A[0]) / n_steps  # average growth rate

        # stability: is L_A variance decreasing over time?
        early_var = np.var(L_A[:100])
        late_var = np.var(L_A[-100:])

        print(f"  {rule_name:25s}  divergence={divergence:8.4f}  "
              f"L_growth={L_growth:+.4e}  early_var={early_var:.4e}  late_var={late_var:.4e}")

    print()
    print("  Navigable = distinguishable (divergence > 0) + bounded growth + stable variance.")
    print("  Prediction: only perpendicular satisfies all three.")
    print()


if __name__ == "__main__":
    test_break_perpendicularity()
    test_r3_forced()
    test_residual_structure()
    test_uniqueness()
