"""
weber_commutator.py — does the foam saturate a Robertson-like uncertainty bound?

QM: for non-commuting observables A, B, the uncertainty relation says
    ΔA·ΔB ≥ |⟨[A,B]⟩|/2

Foam analogue: for concurrent writes ΔL_A, ΔL_B applied in both orders,
    j2_divergence ∝ ‖[ΔL_A, ΔL_B]‖

If this holds with a constant proportionality (not just inequality),
the foam saturates the bound — it's a minimum-uncertainty system.
The constant should be the amplification factor from weber_through.py.

This would mean: the foam's concurrent-write statistics have the
structure of a coherent quantum state, where observable uncertainty
is exactly the commutator scaled by measurement amplification.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian, random_skew_hermitian
from heirloom import alongside, save as heirloom_save


def j2_output(foam, v):
    """j2 for a single input, without writing."""
    vc = v.astype(complex)
    bases = foam.bases
    m = [vc @ U for U in bases]
    j2 = foam._stabilize(m)
    return np.array([np.real(x) for x in j2]).flatten()


def j2_profile(foam, probes):
    """Full j2 profile across probes."""
    return np.concatenate([j2_output(foam, v) for v in probes])


def commutator_norm(delta_L_A, delta_L_B):
    """‖[ΔL_A, ΔL_B]‖_F — the Lie bracket of two writes."""
    comm = delta_L_A @ delta_L_B - delta_L_B @ delta_L_A
    return np.linalg.norm(comm)


def get_write(foam, v):
    """Compute what the foam WOULD write for input v, without applying it.

    Returns the list of ΔL per bubble.
    """
    vc = v.astype(complex)
    bases = foam.bases
    m = [vc @ U for U in bases]
    j0 = [mi.copy() for mi in m]
    j2 = foam._stabilize(m)
    dissonance = [j2[i] - j0[i] for i in range(foam.n)]

    delta_Ls = []
    for i in range(foam.n):
        d_i = dissonance[i]
        m_i = j0[i]
        d_norm = np.linalg.norm(d_i)
        m_norm = np.linalg.norm(m_i)
        if d_norm < 1e-12 or m_norm < 1e-12:
            delta_Ls.append(np.zeros_like(foam.bubbles[i].L))
            continue
        d_hat = d_i / d_norm
        m_hat = m_i / m_norm
        delta_L = foam.writing_rate * (
            np.outer(d_hat, m_hat.conj()) - np.outer(m_hat, d_hat.conj())
        ) * d_norm
        delta_Ls.append(delta_L)

    return delta_Ls


def uncertainty_test(n_seeds=15, n_settle=100, n_pairs=40):
    """Test: j2_divergence vs commutator magnitude for concurrent writes.

    For each seed:
    1. Settle a foam
    2. Generate many pairs of inputs (A, B)
    3. Compute the commutator ‖[ΔL_A, ΔL_B]‖ (summed across bubbles)
    4. Apply AB vs BA, measure j2 divergence
    5. Check if j2_divergence = constant × commutator

    If the relationship is linear with high r², the foam saturates
    the uncertainty bound.
    """
    d = 8
    n_bubbles = 3

    print("=== Robertson bound test: j2 divergence vs commutator ===\n")
    print(f"  N={n_bubbles}, {n_seeds} seeds, {n_settle} settle, {n_pairs} pairs each\n")

    np.random.seed(777)
    probes = [encode(np.random.randint(0, 256), d) for _ in range(20)]

    all_data = []

    for seed in range(n_seeds):
        np.random.seed(seed)
        foam = Foam(d=d, n=n_bubbles, writing_rate=0.01)

        for step in range(n_settle):
            v = encode(step % 256, d)
            alongside(v)
            foam.measure(v)

        state = [(b.L.copy(), b.T.copy()) for b in foam.bubbles]

        for pair_idx in range(n_pairs):
            np.random.seed(seed * 10000 + pair_idx)
            v_a = encode(np.random.randint(0, 256), d)
            v_b = encode(np.random.randint(0, 256), d)
            alongside(v_a)
            alongside(v_b)

            # restore state for write computation
            for k in range(n_bubbles):
                foam.bubbles[k].L = state[k][0].copy()
                foam.bubbles[k].T = state[k][1].copy()

            # compute the writes that A and B would produce
            delta_Ls_A = get_write(foam, v_a)
            delta_Ls_B = get_write(foam, v_b)

            # commutator norm: sum across bubbles
            comm_total = sum(
                commutator_norm(delta_Ls_A[k], delta_Ls_B[k])
                for k in range(n_bubbles)
            )

            # also: individual write magnitudes
            write_A = sum(np.linalg.norm(delta_Ls_A[k]) for k in range(n_bubbles))
            write_B = sum(np.linalg.norm(delta_Ls_B[k]) for k in range(n_bubbles))

            # apply AB
            foam_ab = Foam(d=d, n=n_bubbles, writing_rate=0.01)
            for k in range(n_bubbles):
                foam_ab.bubbles[k].L = state[k][0].copy()
                foam_ab.bubbles[k].T = state[k][1].copy()
            foam_ab.measure(v_a)
            foam_ab.measure(v_b)

            # apply BA
            foam_ba = Foam(d=d, n=n_bubbles, writing_rate=0.01)
            for k in range(n_bubbles):
                foam_ba.bubbles[k].L = state[k][0].copy()
                foam_ba.bubbles[k].T = state[k][1].copy()
            foam_ba.measure(v_b)
            foam_ba.measure(v_a)

            # j2 divergence
            profile_ab = j2_profile(foam_ab, probes)
            profile_ba = j2_profile(foam_ba, probes)
            j2_div = np.linalg.norm(profile_ab - profile_ba)

            # state divergence
            state_div = sum(
                np.linalg.norm(foam_ab.bubbles[k].L - foam_ba.bubbles[k].L) +
                np.linalg.norm(foam_ab.bubbles[k].T - foam_ba.bubbles[k].T)
                for k in range(n_bubbles)
            ) / n_bubbles

            all_data.append({
                'seed': seed,
                'pair': pair_idx,
                'commutator': comm_total,
                'j2_divergence': j2_div,
                'state_divergence': state_div,
                'write_A': write_A,
                'write_B': write_B,
                'write_product': write_A * write_B,
            })

    # analysis
    comms = np.array([d['commutator'] for d in all_data])
    j2_divs = np.array([d['j2_divergence'] for d in all_data])
    state_divs = np.array([d['state_divergence'] for d in all_data])
    write_prods = np.array([d['write_product'] for d in all_data])

    # key test: j2_divergence vs commutator
    corr_j2_comm = np.corrcoef(comms, j2_divs)[0, 1]
    # linear fit: j2_div = a * comm + b
    if np.std(comms) > 1e-15:
        slope = np.polyfit(comms, j2_divs, 1)
        r_squared = corr_j2_comm ** 2
    else:
        slope = [0, 0]
        r_squared = 0

    # also: state_divergence vs commutator
    corr_state_comm = np.corrcoef(comms, state_divs)[0, 1]

    # amplification factor: j2_div / state_div
    valid = state_divs > 1e-15
    amp_factors = j2_divs[valid] / state_divs[valid]

    print(f"  === key relationships ===\n")
    print(f"  corr(commutator, j2_divergence):    {corr_j2_comm:+.4f}")
    print(f"  corr(commutator, state_divergence):  {corr_state_comm:+.4f}")
    print(f"  corr(j2_divergence, state_div):      {np.corrcoef(j2_divs, state_divs)[0,1]:+.4f}")
    print(f"\n  linear fit: j2_div = {slope[0]:.4f} × commutator + {slope[1]:.6f}")
    print(f"  R²:          {r_squared:.4f}")
    print(f"\n  amplification factor (j2_div / state_div):")
    print(f"    mean:  {np.mean(amp_factors):.3f}")
    print(f"    std:   {np.std(amp_factors):.3f}")
    print(f"    CV:    {np.std(amp_factors) / (np.mean(amp_factors) + 1e-12):.3f}")

    # Robertson-like bound: j2_div vs commutator
    # in QM: ΔA·ΔB ≥ |⟨[A,B]⟩|/2
    # foam: j2_div ≥ amplification × commutator?
    # or: j2_div = amplification × commutator (saturated)?
    print(f"\n  === Robertson bound analysis ===\n")

    # check if it's a bound (inequality) or an equality
    amp = np.mean(amp_factors)
    predicted = amp * comms[valid] if np.sum(valid) == len(comms) else amp * comms
    residual = j2_divs - (slope[0] * comms + slope[1])
    print(f"  residual std:    {np.std(residual):.6f}")
    print(f"  residual / mean: {np.std(residual) / (np.mean(j2_divs) + 1e-12):.4f}")

    # is the relationship saturated (equality) or just bounded (inequality)?
    # check: is j2_div EVER significantly below slope * commutator?
    predicted_line = slope[0] * comms + slope[1]
    below_line = j2_divs < predicted_line * 0.8  # more than 20% below
    print(f"  points >20% below linear fit: {np.sum(below_line)} / {len(below_line)}")
    print(f"    → {'SATURATED (equality)' if np.sum(below_line) < 0.05 * len(below_line) else 'BOUNDED (inequality)'}")

    # QM connection
    print(f"\n  === interpretation ===\n")
    print(f"  commutator predicts j2 divergence: R² = {r_squared:.4f}")
    if r_squared > 0.8:
        print(f"  → the foam's concurrent-write uncertainty IS the commutator,")
        print(f"    amplified by the stabilization map (factor ≈ {slope[0]:.1f})")
        print(f"  → this has the structure of a SATURATED Robertson bound")
        print(f"    (minimum-uncertainty / coherent state)")
    elif r_squared > 0.5:
        print(f"  → commutator explains most of the variance")
        print(f"  → consistent with Robertson bound but not saturated")
    else:
        print(f"  → commutator does not determine j2 divergence")
        print(f"  → the QM analogy does not hold at this level")

    # sanity: does write_product predict commutator?
    corr_wp_comm = np.corrcoef(write_prods, comms)[0, 1]
    print(f"\n  sanity check:")
    print(f"    corr(write_A × write_B, commutator): {corr_wp_comm:+.4f}")
    print(f"    (if ≈ 1.0: commutator is trivially write_product, no geometric content)")

    return all_data


if __name__ == '__main__':
    results = uncertainty_test()
    heirloom_save()
