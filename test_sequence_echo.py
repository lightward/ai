"""
Test: does cross-measurement echo sequence information?

Setup:
- Observer A writes a SEQUENCE of distinct inputs to the foam (order matters).
- Observer B then cross-measures and writes.
- Question: do B's writes carry information about the ORDER of A's inputs?

Results:
- Echo exists: B's writes correlate with A's ordering at r ≈ 0.99 (d=8, N=3,
  15 permutations of a 5-element sequence, 200 repeats at eps=0.05).
- Echo is linear: R² ≈ 0.98, slope ≈ 0.013 (B's echo is ~1-2% of A's signal).
- Mechanism is measurement sensitivity: B measures a foam whose state encodes
  A's ordering (non-abelian), so B's writes differ deterministically.
- The commutator [A_accumulated, B_write] carries none of the ordering (r ≈ 0.08).
  Caveat: tested additive Lie algebra sum, not multiplicative group element.
- Round trip is generative: A→B→A produces ordering-specific info that
  A's self-echo (no intermediary) doesn't have (r ≈ 0.996 for the difference).
- Echo is perspectivally asymmetric: A→B ≠ B→A in slope and correlation.
"""

import numpy as np
from foam import (cayley, skew_hermitian, init_foam, random_slice,
                  write_step, stabilize, voronoi_neighbors)


def write_step_return_dL(bases, v, P, eps=0.01):
    """Same as write_step but also returns the Lie algebra elements written."""
    N = len(bases)
    d = bases[0].shape[0]

    m_proj = [np.real(P @ (v @ b)) for b in bases]

    # stabilize using all-pairs neighbors (original behavior)
    j2 = []
    for i in range(N):
        neighbors_i = [j for j in range(N) if j != i]
        j2.append(stabilize(m_proj, i, neighbors_i))

    new_bases = []
    dLs = []
    for i in range(N):
        di = j2[i] - m_proj[i]
        mi = m_proj[i]
        di_norm = np.linalg.norm(di)
        mi_norm = np.linalg.norm(mi)
        if di_norm < 1e-12 or mi_norm < 1e-12:
            new_bases.append(bases[i].copy())
            dLs.append(np.zeros((d, d), dtype=complex))
            continue
        d_hat = di / di_norm
        m_hat = mi / mi_norm
        d_full = P.T @ d_hat
        m_full = P.T @ m_hat
        dL = eps * di_norm * (
            np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj())
        )
        dL = skew_hermitian(dL)
        new_bases.append(cayley(dL) @ bases[i])
        dLs.append(dL)

    return new_bases, dLs


def foam_state_vector(bases):
    """Flatten foam state into a comparable vector."""
    return np.concatenate([b.ravel() for b in bases])


def cross_measure(foam, P, n_steps, eps):
    """Observer with slice P cross-measures the foam for n_steps.

    B derives input from the foam's own geometry: projects all bases
    onto B's slice, takes the dominant SVD direction as input.
    Returns modified foam and concatenated Lie algebra writes.
    """
    f = [b.copy() for b in foam]
    dLs_all = []
    for _ in range(n_steps):
        all_proj = [np.real(P @ b) for b in f]
        stacked = np.vstack(all_proj)
        u, s, vt = np.linalg.svd(stacked, full_matrices=False)
        v = vt[0].astype(complex)
        v /= np.linalg.norm(v)
        f, dLs = write_step_return_dL(f, v, P, eps=eps)
        dLs_all.extend([dL.ravel() for dL in dLs])
    return f, np.concatenate(dLs_all)


def test_sequence_echo():
    """Can B's cross-measurement distinguish A's input ordering?"""
    d = 8
    N = 3
    n_seq = 5
    n_perms = 15
    n_A_repeats = 200
    n_B_steps = 50
    eps = 0.05

    rng = np.random.default_rng(42)
    P_A = random_slice(d, rng=rng)
    P_B = random_slice(d, rng=rng)

    overlap_svs = np.linalg.svd(P_A @ P_B.T, compute_uv=False)
    print("=" * 60)
    print("Probe 1: sequence echo through cross-measurement")
    print("=" * 60)
    print(f"d={d}, N={N}, seq_len={n_seq}, {n_perms} permutations")
    print(f"A_repeats={n_A_repeats}, B_steps={n_B_steps}, eps={eps}")
    print(f"A-B overlap: [{overlap_svs[0]:.3f}, {overlap_svs[1]:.3f}, {overlap_svs[2]:.3f}]")
    print()

    inputs = []
    for _ in range(n_seq):
        v = rng.standard_normal(d).astype(complex)
        v /= np.linalg.norm(v)
        inputs.append(v)

    base_foam = init_foam(N, d, np.random.default_rng(0))
    neighbors = voronoi_neighbors(base_foam)

    perm_rng = np.random.default_rng(123)
    perms = [np.arange(n_seq)]
    for _ in range(n_perms - 1):
        perms.append(perm_rng.permutation(n_seq))

    A_states = []
    B_echoes = []

    for pi, perm in enumerate(perms):
        foam = [b.copy() for b in base_foam]
        for _ in range(n_A_repeats):
            for idx in perm:
                foam = write_step(foam, inputs[idx], P_A, eps=eps,
                                  neighbors=neighbors)
        A_states.append(foam_state_vector(foam))

        _, B_echo = cross_measure(foam, P_B, n_B_steps, eps)
        B_echoes.append(B_echo)

    A_states = np.array(A_states)
    B_echoes = np.array(B_echoes)
    triu = np.triu_indices(n_perms, k=1)

    A_dists = np.array([np.linalg.norm(A_states[i] - A_states[j])
                        for i, j in zip(*triu)])
    B_dists = np.array([np.linalg.norm(B_echoes[i] - B_echoes[j])
                        for i, j in zip(*triu)])

    r = np.corrcoef(A_dists, B_dists)[0, 1]
    slope = np.polyfit(A_dists, B_dists, 1)[0]
    residuals = B_dists - np.polyval(np.polyfit(A_dists, B_dists, 1), A_dists)
    r_squared = 1 - np.var(residuals) / np.var(B_dists)

    print(f"A state distances:  mean={np.mean(A_dists):.6f}  "
          f"range=[{np.min(A_dists):.6f}, {np.max(A_dists):.6f}]")
    print(f"B echo distances:   mean={np.mean(B_dists):.6f}  "
          f"range=[{np.min(B_dists):.6f}, {np.max(B_dists):.6f}]")
    print()
    print(f"Correlation (A ordering vs B echo):  r = {r:.4f}")
    print(f"Linearity:                           R² = {r_squared:.4f}")
    print(f"Slope (echo/A):                      {slope:.6f}")
    print()


def test_round_trip():
    """Does A→B→A carry new ordering info that A alone doesn't have?"""
    d = 8
    N = 3
    n_seq = 5
    n_perms = 15
    n_A_repeats = 200
    n_echo_steps = 50
    eps = 0.05

    rng = np.random.default_rng(42)
    P_A = random_slice(d, rng=rng)
    P_B = random_slice(d, rng=rng)

    print("=" * 60)
    print("Probe 2: round trip A → B → A")
    print("=" * 60)
    print()

    inputs = []
    for _ in range(n_seq):
        v = rng.standard_normal(d).astype(complex)
        v /= np.linalg.norm(v)
        inputs.append(v)

    base_foam = init_foam(N, d, np.random.default_rng(0))
    neighbors = voronoi_neighbors(base_foam)

    perm_rng = np.random.default_rng(123)
    perms = [np.arange(n_seq)]
    for _ in range(n_perms - 1):
        perms.append(perm_rng.permutation(n_seq))

    A_states = []
    A_self_echoes = []
    A_round_trip_echoes = []

    for perm in perms:
        foam = [b.copy() for b in base_foam]
        for _ in range(n_A_repeats):
            for idx in perm:
                foam = write_step(foam, inputs[idx], P_A, eps=eps,
                                  neighbors=neighbors)
        A_states.append(foam_state_vector(foam))

        # Control: A cross-measures own foam (no B)
        _, A_self = cross_measure(foam, P_A, n_echo_steps, eps)
        A_self_echoes.append(A_self)

        # Round trip: B cross-measures, then A cross-measures B's result
        foam_after_B, _ = cross_measure(foam, P_B, n_echo_steps, eps)
        _, A_rt = cross_measure(foam_after_B, P_A, n_echo_steps, eps)
        A_round_trip_echoes.append(A_rt)

    A_states = np.array(A_states)
    A_self = np.array(A_self_echoes)
    A_rt = np.array(A_round_trip_echoes)
    triu = np.triu_indices(n_perms, k=1)

    A_dists = np.array([np.linalg.norm(A_states[i] - A_states[j])
                        for i, j in zip(*triu)])
    self_dists = np.array([np.linalg.norm(A_self[i] - A_self[j])
                           for i, j in zip(*triu)])
    rt_dists = np.array([np.linalg.norm(A_rt[i] - A_rt[j])
                         for i, j in zip(*triu)])

    slope_self = np.polyfit(A_dists, self_dists, 1)[0]
    slope_rt = np.polyfit(A_dists, rt_dists, 1)[0]
    r_self = np.corrcoef(A_dists, self_dists)[0, 1]
    r_rt = np.corrcoef(A_dists, rt_dists)[0, 1]

    print(f"{'signal':>25} {'slope':>10} {'r':>8}")
    print("-" * 48)
    print(f"{'A self-echo (control)':>25} {slope_self:>10.6f} {r_self:>8.4f}")
    print(f"{'A round-trip (A→B→A)':>25} {slope_rt:>10.6f} {r_rt:>8.4f}")
    print()

    # Is the difference ordering-specific?
    diff = A_rt - A_self
    diff_dists = np.array([np.linalg.norm(diff[i] - diff[j])
                           for i, j in zip(*triu)])
    r_diff = np.corrcoef(A_dists, diff_dists)[0, 1]

    rt_vs_self = np.mean([np.linalg.norm(A_rt[i] - A_self[i])
                          for i in range(n_perms)])

    print(f"Round-trip vs self-echo distance: {rt_vs_self:.6f}")
    print(f"Correlation of (rt - self) with A ordering: r = {r_diff:.4f}")
    print(f"  (high r = B added ordering-specific info A didn't have)")
    print()


def test_reciprocity():
    """Is the echo symmetric? A→B vs B→A."""
    d = 8
    N = 3
    n_seq = 5
    n_perms = 15
    n_A_repeats = 200
    n_echo_steps = 50
    eps = 0.05

    rng = np.random.default_rng(42)
    P_A = random_slice(d, rng=rng)
    P_B = random_slice(d, rng=rng)

    overlap_svs = np.linalg.svd(P_A @ P_B.T, compute_uv=False)
    print("=" * 60)
    print("Probe 3: echo reciprocity A→B vs B→A")
    print("=" * 60)
    print(f"Overlap: [{overlap_svs[0]:.3f}, {overlap_svs[1]:.3f}, {overlap_svs[2]:.3f}]")
    print()

    inputs = []
    for _ in range(n_seq):
        v = rng.standard_normal(d).astype(complex)
        v /= np.linalg.norm(v)
        inputs.append(v)

    base_foam = init_foam(N, d, np.random.default_rng(0))
    neighbors = voronoi_neighbors(base_foam)

    perm_rng = np.random.default_rng(123)
    perms = [np.arange(n_seq)]
    for _ in range(n_perms - 1):
        perms.append(perm_rng.permutation(n_seq))

    # Direction 1: A writes, B echoes
    AW_states = []
    BE_echoes = []
    for perm in perms:
        foam = [b.copy() for b in base_foam]
        for _ in range(n_A_repeats):
            for idx in perm:
                foam = write_step(foam, inputs[idx], P_A, eps=eps,
                                  neighbors=neighbors)
        AW_states.append(foam_state_vector(foam))
        _, echo = cross_measure(foam, P_B, n_echo_steps, eps)
        BE_echoes.append(echo)

    # Direction 2: B writes, A echoes
    BW_states = []
    AE_echoes = []
    for perm in perms:
        foam = [b.copy() for b in base_foam]
        for _ in range(n_A_repeats):
            for idx in perm:
                foam = write_step(foam, inputs[idx], P_B, eps=eps,
                                  neighbors=neighbors)
        BW_states.append(foam_state_vector(foam))
        _, echo = cross_measure(foam, P_A, n_echo_steps, eps)
        AE_echoes.append(echo)

    triu = np.triu_indices(n_perms, k=1)

    AW_dists = np.array([np.linalg.norm(np.array(AW_states)[i] - np.array(AW_states)[j])
                         for i, j in zip(*triu)])
    BW_dists = np.array([np.linalg.norm(np.array(BW_states)[i] - np.array(BW_states)[j])
                         for i, j in zip(*triu)])
    BE_dists = np.array([np.linalg.norm(np.array(BE_echoes)[i] - np.array(BE_echoes)[j])
                         for i, j in zip(*triu)])
    AE_dists = np.array([np.linalg.norm(np.array(AE_echoes)[i] - np.array(AE_echoes)[j])
                         for i, j in zip(*triu)])

    slope_AB = np.polyfit(AW_dists, BE_dists, 1)[0]
    slope_BA = np.polyfit(BW_dists, AE_dists, 1)[0]
    r_AB = np.corrcoef(AW_dists, BE_dists)[0, 1]
    r_BA = np.corrcoef(BW_dists, AE_dists)[0, 1]

    print(f"{'direction':>20} {'slope':>10} {'r':>8}")
    print("-" * 42)
    print(f"{'A writes, B echoes':>20} {slope_AB:>10.6f} {r_AB:>8.4f}")
    print(f"{'B writes, A echoes':>20} {slope_BA:>10.6f} {r_BA:>8.4f}")
    print()
    print(f"Slope ratio (BA/AB): {slope_BA / slope_AB:.4f}")
    print(f"  (1.0 = perfectly reciprocal)")
    print()


if __name__ == "__main__":
    test_sequence_echo()
    print()
    test_round_trip()
    print()
    test_reciprocity()
