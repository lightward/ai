"""
inhabitation_structural.py — recursive inhabitation via structural coupling,
not feedback loops.

Previous test (inhabitation_plateau.py) used feedback: inner foam generates
input → feeds to outer bubble → outer feeds back. Result: worse than single-level.

This test: the inner foam IS the bubble's internal structure. The inner foam's
state directly modulates the bubble's L-T decomposition. The inner foam
co-settles with the outer foam's cross-measurement rather than feeding input.

The hypothesis:
- Feedback inhabitation destabilizes (confirmed: 22% worse)
- Structural coupling inhabitation co-settles (the recursive health prescription:
  "stabilize inner IN PRESENCE of outer dynamics")
- The difference IS the second inversion: you can't stabilize from outside
  without becoming inside. Your measurement is the perturbation. Structural
  coupling avoids this because the inner foam doesn't measure the outer —
  it IS the outer.

Tests:
1. STRUCTURAL COUPLING: inner foam's aggregate state becomes the bubble's
   effective basis. Inner cross-measurement runs alongside outer cross-measurement.

2. FEEDBACK vs STRUCTURAL: direct comparison on matched foams.

3. THE STABILIZATION PARADOX: one foam tries to "help" another by measuring it.
   Does the helper's measurement create the instability it's trying to fix?
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, encode, cayley, skew_hermitian, random_skew_hermitian
from heirloom import alongside, report, save

np.random.seed(42)


def junction_angles(foam):
    """Measure angles between all pairs of bases."""
    bases = foam.bases
    angles = []
    for i in range(foam.n):
        for j in range(i + 1, foam.n):
            R = bases[i].conj().T @ bases[j]
            try:
                log_R = logm(R)
                angle = np.linalg.norm(log_R) / np.sqrt(2)
                angles.append(angle)
            except Exception:
                angles.append(np.nan)
    return np.array(angles)


def junction_regularity(angles):
    """CV of junction angles. Lower = more regular."""
    angles = angles[~np.isnan(angles)]
    if len(angles) < 2:
        return np.nan, np.nan
    return np.std(angles) / (np.mean(angles) + 1e-15), np.mean(angles)


def cross_measure(foam, n_rounds=1):
    """Cross-measurement: bubbles measure each other."""
    for _ in range(n_rounds):
        for i in range(foam.n):
            for j in range(foam.n):
                if i != j:
                    bj = foam.bubbles[j].basis
                    v = np.real(bj[0, :])
                    v = v / (np.linalg.norm(v) + 1e-12)
                    foam.measure(v)
                    alongside(v)


def state_vector(foam):
    """Flatten L and T into a single real vector."""
    parts = []
    for b in foam.bubbles:
        parts.append(b.L.flatten().view(float))
        parts.append(b.T.flatten().view(float))
    return np.concatenate(parts)


# ============================================================
# TEST 1: Structural coupling
# ============================================================
print("=" * 60)
print("TEST 1: Structural coupling — inner foam IS the bubble")
print("=" * 60)

d, n = 8, 3
n_seeds = 15
n_steps = 100
n_settle = 50

structural_cv = []
structural_cost = []
structural_angles = []

feedback_cv = []
feedback_cost = []
feedback_angles = []

plain_cv = []
plain_cost = []

for seed in range(n_seeds):
    np.random.seed(seed * 100 + 42)

    # --- STRUCTURAL COUPLING ---
    # outer foam
    foam_struct = Foam(d, n)
    # inner foams: one per outer bubble
    inner_foams = [Foam(d, n) for _ in range(n)]

    for step in range(n_steps):
        # inner foams cross-measure (their own internal dynamics)
        for inner in inner_foams:
            for i in range(inner.n):
                for j in range(inner.n):
                    if i != j:
                        bj = inner.bubbles[j].basis
                        v = np.real(bj[0, :])
                        v = v / (np.linalg.norm(v) + 1e-12)
                        inner.measure(v)

        # structural coupling: inner foam's aggregate state modulates
        # the outer bubble's L. the inner foam doesn't feed input —
        # it directly shapes the basis.
        for i in range(n):
            inner = inner_foams[i]
            # aggregate inner state: mean of inner bubble generators
            inner_aggregate_L = np.mean([b.L for b in inner.bubbles], axis=0)
            # blend: outer bubble's L moves toward inner aggregate
            # this is co-settling, not overwriting
            blend_rate = 0.01
            delta = skew_hermitian(inner_aggregate_L - foam_struct.bubbles[i].L)
            foam_struct.bubbles[i].L = skew_hermitian(
                foam_struct.bubbles[i].L + blend_rate * delta
            )

        # outer foam cross-measures (its own relaxation dynamics)
        for i in range(foam_struct.n):
            for j in range(foam_struct.n):
                if i != j:
                    bj = foam_struct.bubbles[j].basis
                    v = np.real(bj[0, :])
                    v = v / (np.linalg.norm(v) + 1e-12)
                    foam_struct.measure(v)
                    alongside(v)

        # outer state feeds back to inner: inner foam sees the
        # outer bubble it's inhabiting (co-settling, bidirectional)
        for i in range(n):
            outer_L = foam_struct.bubbles[i].L
            inner = inner_foams[i]
            for ib in inner.bubbles:
                delta = skew_hermitian(outer_L - ib.L)
                ib.L = skew_hermitian(ib.L + blend_rate * delta)

    # let outer settle
    cross_measure(foam_struct, n_rounds=n_settle)

    ang = junction_angles(foam_struct)
    cv, mean_a = junction_regularity(ang)
    structural_cv.append(cv)
    structural_cost.append(foam_struct.boundary_cost())
    structural_angles.append(mean_a)

    # --- FEEDBACK (from previous experiment, reimplemented) ---
    np.random.seed(seed * 100 + 42)
    foam_fb = Foam(d, n)
    inner_foams_fb = [Foam(d, n) for _ in range(n)]

    for step in range(n_steps):
        for i in range(n):
            inner = inner_foams_fb[i]
            # inner self-measures
            inner_basis = inner.bubbles[0].basis
            v_inner = np.real(inner_basis[0, :])
            v_inner = v_inner / (np.linalg.norm(v_inner) + 1e-12)
            inner.measure(v_inner)

            # inner readout → outer input (feedback)
            readout = np.real(inner.readout(v_inner))
            readout = readout / (np.linalg.norm(readout) + 1e-12)
            foam_fb.measure(readout)

            # outer → inner feedback
            outer_basis = foam_fb.bubbles[i].basis
            v_outer = np.real(outer_basis[0, :])
            v_outer = v_outer / (np.linalg.norm(v_outer) + 1e-12)
            inner.measure(v_outer)

    cross_measure(foam_fb, n_rounds=n_settle)

    ang = junction_angles(foam_fb)
    cv, mean_a = junction_regularity(ang)
    feedback_cv.append(cv)
    feedback_cost.append(foam_fb.boundary_cost())
    feedback_angles.append(mean_a)

    # --- PLAIN (no inhabitation, just cross-measurement) ---
    np.random.seed(seed * 100 + 42)
    foam_plain = Foam(d, n)
    cross_measure(foam_plain, n_rounds=n_steps + n_settle)

    ang = junction_angles(foam_plain)
    cv, _ = junction_regularity(ang)
    plain_cv.append(cv)
    plain_cost.append(foam_plain.boundary_cost())

print(f"\nJunction regularity (CV, lower = more regular):")
print(f"  Structural coupling: {np.mean(structural_cv):.6f} ± {np.std(structural_cv):.6f}")
print(f"  Feedback loop:       {np.mean(feedback_cv):.6f} ± {np.std(feedback_cv):.6f}")
print(f"  Plain (cross-only):  {np.mean(plain_cv):.6f} ± {np.std(plain_cv):.6f}")

print(f"\nBoundary cost (lower = more settled):")
print(f"  Structural coupling: {np.mean(structural_cost):.4f} ± {np.std(structural_cost):.4f}")
print(f"  Feedback loop:       {np.mean(feedback_cost):.4f} ± {np.std(feedback_cost):.4f}")
print(f"  Plain (cross-only):  {np.mean(plain_cost):.4f} ± {np.std(plain_cost):.4f}")

print(f"\nMean junction angle:")
print(f"  Structural coupling: {np.mean(structural_angles):.4f} ± {np.std(structural_angles):.4f}")
print(f"  Feedback loop:       {np.mean(feedback_angles):.4f} ± {np.std(feedback_angles):.4f}")


# ============================================================
# TEST 2: The stabilization paradox
# ============================================================
print("\n" + "=" * 60)
print("TEST 2: The stabilization paradox")
print("=" * 60)
print("Does trying to stabilize another foam create instability?")

n_seeds_par = 12
n_steps_par = 80

# scenario: foam A is settling. foam B tries to "help" by measuring A.
# does B's measurement help or hurt A's settling?

helped_cost_trajectory = []
solo_cost_trajectory = []
mutual_cost_trajectory = []

for seed in range(n_seeds_par):
    np.random.seed(seed * 700 + 3)

    # --- SOLO: foam A settles on its own via cross-measurement ---
    foam_solo = Foam(d, n)
    # give it some initial structure
    for _ in range(20):
        v = np.random.randn(d)
        v /= np.linalg.norm(v)
        foam_solo.measure(v)

    solo_costs = []
    for step in range(n_steps_par):
        cross_measure(foam_solo, n_rounds=1)
        solo_costs.append(foam_solo.boundary_cost())
    solo_cost_trajectory.append(solo_costs)

    # --- HELPED: foam A settles while foam B measures it ---
    np.random.seed(seed * 700 + 3)
    foam_helped = Foam(d, n)
    foam_helper = Foam(d, n)
    for _ in range(20):
        v = np.random.randn(d)
        v /= np.linalg.norm(v)
        foam_helped.measure(v)

    helped_costs = []
    for step in range(n_steps_par):
        # A cross-measures (self-settling)
        cross_measure(foam_helped, n_rounds=1)

        # B measures A: reads A's bases and feeds them as input to A
        # this is "trying to help" — providing external measurement
        for i in range(foam_helped.n):
            ba = foam_helped.bubbles[i].basis
            v = np.real(ba[0, :])
            v = v / (np.linalg.norm(v) + 1e-12)
            foam_helped.measure(v)
            alongside(v)

        helped_costs.append(foam_helped.boundary_cost())
    helped_cost_trajectory.append(helped_costs)

    # --- MUTUAL: both foams measure each other ---
    np.random.seed(seed * 700 + 3)
    foam_m1 = Foam(d, n)
    foam_m2 = Foam(d, n)
    for _ in range(20):
        v = np.random.randn(d)
        v /= np.linalg.norm(v)
        foam_m1.measure(v)

    mutual_costs = []
    for step in range(n_steps_par):
        cross_measure(foam_m1, n_rounds=1)
        cross_measure(foam_m2, n_rounds=1)

        # mutual measurement: each reads the other
        for i in range(foam_m1.n):
            b1 = foam_m1.bubbles[i].basis
            v1 = np.real(b1[0, :])
            v1 = v1 / (np.linalg.norm(v1) + 1e-12)
            foam_m2.measure(v1)

            b2 = foam_m2.bubbles[i].basis
            v2 = np.real(b2[0, :])
            v2 = v2 / (np.linalg.norm(v2) + 1e-12)
            foam_m1.measure(v2)
            alongside(v2)

        mutual_costs.append(foam_m1.boundary_cost())
    mutual_cost_trajectory.append(mutual_costs)

solo_arr = np.array(solo_cost_trajectory)
helped_arr = np.array(helped_cost_trajectory)
mutual_arr = np.array(mutual_cost_trajectory)

print(f"\nBoundary cost trajectory ({n_seeds_par} seeds):")
print(f"\n  Solo (self-settling):")
print(f"    start: {solo_arr[:, 0].mean():.4f}")
print(f"    end:   {solo_arr[:, -1].mean():.4f}")
print(f"    Δ:     {(solo_arr[:, -1] - solo_arr[:, 0]).mean():.4f}")

print(f"\n  Helped (B measures A while A settles):")
print(f"    start: {helped_arr[:, 0].mean():.4f}")
print(f"    end:   {helped_arr[:, -1].mean():.4f}")
print(f"    Δ:     {(helped_arr[:, -1] - helped_arr[:, 0]).mean():.4f}")

print(f"\n  Mutual (both measure each other):")
print(f"    start: {mutual_arr[:, 0].mean():.4f}")
print(f"    end:   {mutual_arr[:, -1].mean():.4f}")
print(f"    Δ:     {(mutual_arr[:, -1] - mutual_arr[:, 0]).mean():.4f}")

# settling rate: how fast does cost decrease?
solo_rate = np.mean(np.diff(solo_arr, axis=1), axis=1)
helped_rate = np.mean(np.diff(helped_arr, axis=1), axis=1)
mutual_rate = np.mean(np.diff(mutual_arr, axis=1), axis=1)

print(f"\n  Mean settling rate (negative = settling):")
print(f"    Solo:   {solo_rate.mean():.6f}")
print(f"    Helped: {helped_rate.mean():.6f}")
print(f"    Mutual: {mutual_rate.mean():.6f}")

# regularity at the end
solo_end_cv = []
helped_end_cv = []
mutual_end_cv = []

# we need to re-run just to get final junction angles...
# actually let's just report the cost results, they tell the story

print("\n" + "=" * 60)
print("SUMMARY")
print("=" * 60)
print("""
Test 1 — Structural vs Feedback:
  If structural coupling co-settles: lower CV and cost than feedback.
  If structural coupling is just a different kind of perturbation: similar or worse.

Test 2 — Stabilization paradox:
  If measurement-as-help creates instability:
    helped foam settles SLOWER than solo foam.
  If mutual measurement is different from one-way help:
    mutual may settle differently from helped.

  The paradox: your measurement is your inhabitation is the departure
  from Plateau you're trying to fix. You can't measure someone toward
  rest without being their weather.
""")

report()
save()
