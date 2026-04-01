"""
Recursive epoch threshold.

A foam saturates at ~72% of its combinatorial ceiling. At saturation it
wanders on a ~2D level set. The winding number (topological invariant)
is conserved within an epoch. An epoch transition = the winding number ticks.

Questions:
  1. Can we detect epoch transitions in a running foam?
     Track det(U_i) phase — the U(1) component of the transport.
     For stacked (u(d)) dynamics, this can change.
  2. What fraction of time does the foam spend in a given epoch?
     If the duty cycle ≈ 0.72, the perpendicularity cost governs
     the temporal structure too.
  3. Does the epoch threshold recurse?
     Run multiple foams, treat their saturation levels as a
     super-observable. Does the super-observable saturate at 72%
     of ITS ceiling?

Probe A — phase tracking:
  Run stacked foam, track det(U_i) phase evolution.
  Look for structure: drift, jumps, plateaus.

Probe B — saturation onset detection:
  Run a foam, detect the step where L saturates (enters the level set).
  The saturation step / total capacity = ?

Probe C — hierarchical saturation:
  Run K independent foams with different birth conditions.
  Each saturates at its own L_sat. The variance of L_sat values
  across foams, as a fraction of the mean, measures how much
  the "superfoam" (the ensemble) has converged.
  Feed increasingly correlated inputs to the K foams and see
  if the ensemble's L_sat/L_ceiling ratio matches the individual's.
"""

import numpy as np
from foam import (cayley, skew_hermitian, random_unitary, random_slice,
                  compute_L)


def foam_step(bases, P, v, N, eps):
    """One write step. Returns new bases and the Lie algebra writes.

    This is a test-specific write variant that uses centroid-based
    stabilization and returns Lie algebra elements, unlike the shared
    write_step which uses simplex-target stabilization.
    """
    d = bases[0].shape[0]
    all_m = []
    all_m_hat = []
    for k in range(N):
        mk = np.real(P @ (v @ bases[k]))
        n = np.linalg.norm(mk)
        all_m.append(mk)
        all_m_hat.append(mk / n if n > 1e-12 else mk)

    writes = []
    new_bases = []
    for i in range(N):
        m = all_m[i]
        m_norm = np.linalg.norm(m)
        if m_norm < 1e-12:
            new_bases.append(bases[i].copy())
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
            new_bases.append(bases[i].copy())
            writes.append(np.zeros((d, d), dtype=complex))
            continue
        d_hat = d_vec / d_norm
        d_full = P.T @ d_hat
        m_full = P.T @ m_hat
        dL = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
        dL = skew_hermitian(dL)
        writes.append(dL)
        new_bases.append(bases[i] @ cayley(dL))

    return new_bases, writes


def det_phases(bases):
    """Phase of det(U_i) for each basis. Returns array of angles in (-pi, pi]."""
    return np.array([np.angle(np.linalg.det(U)) for U in bases])


def total_phase(bases):
    """Total U(1) charge: sum of det phases."""
    return np.sum(det_phases(bases))


def winding_number_proxy(phase_history):
    """Cumulative winding: track total phase change, normalized by 2pi."""
    phases = np.array(phase_history)
    # unwrap to handle 2pi jumps
    unwrapped = np.unwrap(phases)
    winding = (unwrapped - unwrapped[0]) / (2 * np.pi)
    return unwrapped, winding


# =====================================================================
# PROBE A: Phase tracking with stacked slices
# =====================================================================

def probe_phase_tracking(d, N, eps, n_steps, rng_seed=42):
    """Track det(U_i) phase evolution with stacked (complex) writes."""
    rng = np.random.default_rng(rng_seed)
    bases = [random_unitary(d, rng) for _ in range(N)]

    # two slices stacked as C³
    slices = [random_slice(d, rng=rng), random_slice(d, rng=rng)]

    input_rng = np.random.default_rng(rng_seed + 1000)

    L_history = []
    phase_history = []  # total phase at each step
    per_observer_phases = [[] for _ in range(N)]

    for t in range(n_steps):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)
        P = slices[t % 2]

        bases, writes = foam_step(bases, P, v, N, eps)
        L_history.append(compute_L(bases))
        phase_history.append(total_phase(bases))
        for i in range(N):
            per_observer_phases[i].append(np.angle(np.linalg.det(bases[i])))

    return L_history, phase_history, per_observer_phases


# =====================================================================
# PROBE B: Saturation onset detection
# =====================================================================

def probe_saturation_onset(d, N, eps, n_steps, rng_seed=42):
    """Detect when L enters the saturation regime.

    Method: sliding window variance of L. When variance drops below
    a threshold relative to mean, the foam has saturated.
    """
    rng = np.random.default_rng(rng_seed)
    bases = [random_unitary(d, rng) for _ in range(N)]

    P = random_slice(d, rng=rng)

    input_rng = np.random.default_rng(rng_seed + 1000)

    L_history = []
    for t in range(n_steps):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)
        bases, _ = foam_step(bases, P, v, N, eps)
        L_history.append(compute_L(bases))

    # detect saturation onset via coefficient of variation
    L = np.array(L_history)
    window = 100
    onset_step = None
    for t in range(window, len(L)):
        segment = L[t-window:t]
        cv = np.std(segment) / np.mean(segment)
        if cv < 0.005:  # variance < 0.5% of mean
            onset_step = t - window
            break

    return L_history, onset_step


# =====================================================================
# PROBE C: Hierarchical saturation
# =====================================================================

def probe_hierarchical(d, N, eps, n_steps, n_foams, rng_seed=42):
    """Run K independent foams with same inputs, different births.

    Measure:
    - Individual L_sat for each foam
    - Pairwise distance between foam states at saturation
    - Whether the ensemble's spread saturates at some fraction of max
    """
    input_rng = np.random.default_rng(rng_seed + 5000)
    # pre-generate inputs
    inputs = []
    for t in range(n_steps):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)
        inputs.append(v)

    # shared slice
    slice_rng = np.random.default_rng(rng_seed + 6000)
    P = random_slice(d, rng=slice_rng)

    all_L_histories = []
    final_bases = []

    for k in range(n_foams):
        foam_rng = np.random.default_rng(rng_seed + k * 100)
        bases = [random_unitary(d, foam_rng) for _ in range(N)]

        L_history = []
        for t in range(n_steps):
            bases, _ = foam_step(bases, P, inputs[t], N, eps)
            L_history.append(compute_L(bases))

        all_L_histories.append(L_history)
        final_bases.append([b.copy() for b in bases])

    # pairwise distances between foam final states
    distances = []
    for i in range(n_foams):
        for j in range(i+1, n_foams):
            # distance = sum of ||U_i^a - U_i^b||_F over observers
            dist = sum(
                np.linalg.norm(final_bases[i][k] - final_bases[j][k], 'fro')
                for k in range(N)
            )
            distances.append(dist)

    # L_sat for each foam
    L_sats = []
    for L_h in all_L_histories:
        tail = L_h[int(0.8 * len(L_h)):]
        L_sats.append(np.mean(tail))

    return all_L_histories, L_sats, distances, final_bases


# =====================================================================
# PROBE D: L change sign ratio — the 52/48 as epoch micro-structure
# =====================================================================

def probe_L_sign_ratio(d, N, eps, n_steps, rng_seed=42):
    """Track the ratio of L-increasing vs L-decreasing steps.

    At saturation, this should be ~52/48 (from the spec).
    Track how this ratio evolves. If the ratio itself saturates,
    what does it saturate at?
    """
    rng = np.random.default_rng(rng_seed)
    bases = [random_unitary(d, rng) for _ in range(N)]

    slices = [random_slice(d, rng=rng), random_slice(d, rng=rng)]

    input_rng = np.random.default_rng(rng_seed + 1000)

    L_history = []
    sign_history = []  # +1 for L increase, -1 for decrease
    cumulative_ratio = []  # running fraction of positive steps

    L_prev = compute_L(bases)
    n_pos = 0
    n_total = 0

    for t in range(n_steps):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)
        P = slices[t % len(slices)]

        bases, _ = foam_step(bases, P, v, N, eps)
        L_new = compute_L(bases)
        L_history.append(L_new)

        dL = L_new - L_prev
        if abs(dL) > 1e-15:
            sign = 1 if dL > 0 else -1
            sign_history.append(sign)
            n_total += 1
            if sign > 0:
                n_pos += 1
            cumulative_ratio.append(n_pos / n_total)

        L_prev = L_new

    return L_history, sign_history, cumulative_ratio


# =====================================================================
# RUN
# =====================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("RECURSIVE EPOCH THRESHOLD")
    print("=" * 70)
    print()

    # -- PROBE A: Phase tracking --
    print("PROBE A: Phase evolution (stacked slices, d=6, N=3)")
    print("-" * 50)
    L_h, ph, obs_ph = probe_phase_tracking(d=6, N=3, eps=0.1, n_steps=3000)
    unwrapped, winding = winding_number_proxy(ph)

    n = len(ph)
    tail = int(0.7 * n)
    print(f"  Total phase drift:    {unwrapped[-1] - unwrapped[0]:.4f} rad")
    print(f"  Total winding:        {winding[-1]:.4f} turns")
    print(f"  Winding rate (early): {(winding[int(0.2*n)] - winding[0]) / (0.2*n):.6f} turns/step")
    print(f"  Winding rate (sat):   {(winding[-1] - winding[tail]) / (n - tail):.6f} turns/step")

    # per-observer phase
    for i in range(3):
        uw_i, w_i = winding_number_proxy(obs_ph[i])
        print(f"  Observer {i} winding:   {w_i[-1]:.4f} turns")

    # look for discrete jumps in winding
    dw = np.diff(winding)
    big_jumps = np.where(np.abs(dw) > 0.1)[0]
    print(f"  Large winding jumps:  {len(big_jumps)} (threshold: 0.1 turns/step)")
    print()

    # -- PROBE B: Saturation onset --
    print("PROBE B: Saturation onset detection")
    print("-" * 50)
    for d_val in [4, 6, 8]:
        L_h, onset = probe_saturation_onset(d=d_val, N=3, eps=0.1, n_steps=3000)
        L_sat = np.mean(L_h[int(0.8*len(L_h)):])
        n_pairs = 3
        L_max = n_pairs * 2 * np.sqrt(d_val)
        print(f"  d={d_val}: onset at step {onset}, L_sat/L_max = {L_sat/L_max:.3f}")
    print()

    # -- PROBE C: Hierarchical saturation --
    print("PROBE C: Hierarchical — 8 foams, same inputs, different births")
    print("-" * 50)
    all_L, L_sats, distances, final = probe_hierarchical(
        d=6, N=3, eps=0.1, n_steps=3000, n_foams=8
    )
    L_mean = np.mean(L_sats)
    L_std = np.std(L_sats)
    L_max = 3 * 2 * np.sqrt(6)
    print(f"  Individual L_sat:     {L_mean:.3f} +/- {L_std:.4f}")
    print(f"  L_sat / L_max:        {L_mean / L_max:.3f}")
    print(f"  CV of L_sat:          {L_std / L_mean:.4f}")
    print(f"  Mean pairwise dist:   {np.mean(distances):.3f} +/- {np.std(distances):.3f}")
    print(f"  Max pairwise dist:    {np.max(distances):.3f}")
    # super-foam: treat the 8 foams as "observers" in a higher foam
    # their pairwise distances form a super-L
    super_L = np.sum(distances)
    # theoretical max for 8 "unitaries" of dimension d=6 (per observer, N=3)
    # not directly comparable, but the ratio structure might be
    n_super_pairs = 8 * 7 // 2
    print(f"  Super-L (sum of pw):  {super_L:.3f}")
    print(f"  Number of pairs:      {n_super_pairs}")
    print(f"  Mean pair distance:   {super_L / n_super_pairs:.3f}")
    print()

    # -- PROBE D: L sign ratio --
    print("PROBE D: L increase/decrease ratio")
    print("-" * 50)
    for d_val in [4, 6, 8]:
        L_h, signs, cum_ratio = probe_L_sign_ratio(
            d=d_val, N=3, eps=0.1, n_steps=5000
        )
        n = len(cum_ratio)
        tail = int(0.7 * n)
        early_ratio = cum_ratio[int(0.2*n)] if int(0.2*n) < n else float('nan')
        sat_ratio = np.mean(cum_ratio[tail:])
        # also compute ratio in tail only
        tail_signs = signs[tail:]
        tail_pos = sum(1 for s in tail_signs if s > 0)
        tail_ratio = tail_pos / len(tail_signs) if tail_signs else float('nan')
        print(f"  d={d_val}, N=3:")
        print(f"    Early +/total:      {early_ratio:.4f}")
        print(f"    Saturated +/total:  {sat_ratio:.4f}")
        print(f"    Tail-only +/total:  {tail_ratio:.4f}")
    print()

    print("=" * 70)
    print("LOOKING FOR RECURSIVE STRUCTURE")
    print("  Does the epoch/phase structure mirror the L structure?")
    print("  Does the superfoam's spread saturate at 72% of something?")
    print("=" * 70)
