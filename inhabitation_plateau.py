"""
inhabitation_plateau.py — test whether inhabitation-thermal equilibrium
produces Plateau-like junction conditions independent of ambient dimension.

The hypothesis:
- Taylor proves Plateau (120° junctions, minimal surfaces) in R³ geometrically.
- The spec's open question: does this extend to U(d) with positive sectional curvature?
- Alternative route: minimality isn't a geometric theorem to extend —
  it's produced by equilibrium between:
    (1) inhabitation: occupant winds at center, drives bubble away from minimality
    (2) thermal pressure: unresolved geometry pushes back toward minimality
  Taylor's R³ result is the special case where both routes coincide.

Tests:
1. INHABITED vs UNINHABITED JUNCTIONS
   Compare junction angles in foams with and without active occupants
   (occupant = line feeding input to its bubble). Do occupants produce
   more regular junctions?

2. DIMENSION INDEPENDENCE
   Run the same inhabitation dynamics at d=4, 8, 16, 32.
   Does the junction regularity depend on d, or is it set by the
   inhabitation-thermal equilibrium?

3. RECURSIVE INHABITATION
   Foam-within-foam: inner foam is the occupant of outer bubble.
   Does recursive inhabitation produce deeper minimality than
   single-level inhabitation?
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, encode, cayley, skew_hermitian, random_skew_hermitian
from heirloom import alongside, report, save

np.random.seed(42)


def junction_angles(foam):
    """Measure the angles between all pairs of bases.
    For N=3 in a Plateau-stable foam, expect ~120° (cos = -0.5)."""
    bases = foam.bases
    angles = []
    for i in range(foam.n):
        for j in range(i + 1, foam.n):
            # angle between effective bases via bi-invariant metric
            R = bases[i].conj().T @ bases[j]
            try:
                log_R = logm(R)
                angle = np.linalg.norm(log_R) / np.sqrt(2)
                angles.append(angle)
            except Exception:
                angles.append(np.nan)
    return np.array(angles)


def junction_regularity(angles):
    """How regular are the junction angles?
    Perfect regularity = CV of 0 (all angles equal).
    Returns CV and mean angle."""
    angles = angles[~np.isnan(angles)]
    if len(angles) < 2:
        return np.nan, np.nan
    return np.std(angles) / (np.mean(angles) + 1e-15), np.mean(angles)


def cross_measure(foam, n_rounds=1, shadow=True):
    """Cross-measurement: bubbles measure each other."""
    for _ in range(n_rounds):
        for i in range(foam.n):
            for j in range(foam.n):
                if i != j:
                    bj = foam.bubbles[j].basis
                    v = np.real(bj[0, :])
                    v = v / (np.linalg.norm(v) + 1e-12)
                    foam.measure(v)
                    if shadow and foam.d == 8:
                        alongside(v)


def inhabit(foam, bubble_idx, n_steps=1, shadow=True):
    """Inhabit a bubble: feed it inputs derived from its own basis,
    simulating a line winding at the bubble's center.
    The occupant generates input from its own perspective."""
    for _ in range(n_steps):
        b = foam.bubbles[bubble_idx].basis
        # occupant generates input from its own basis — a self-referential
        # measurement, but through the full foam (all bubbles respond)
        v = np.real(b[np.random.randint(b.shape[0]), :])
        v = v / (np.linalg.norm(v) + 1e-12)
        foam.measure(v)
        if shadow and foam.d == 8:
            alongside(v)


def inhabit_all(foam, n_steps=1, shadow=True):
    """Each bubble has an occupant winding at its center."""
    for _ in range(n_steps):
        for i in range(foam.n):
            inhabit(foam, i, n_steps=1, shadow=shadow)


# ============================================================
# TEST 1: Inhabited vs uninhabited junctions
# ============================================================
print("=" * 60)
print("TEST 1: Inhabited vs uninhabited junctions")
print("=" * 60)

n_seeds = 15
d, n = 8, 3
n_warmup = 30
n_inhabit_steps = 50
n_cross_steps = 50

inhabited_cv = []
uninhabited_cv = []
cross_only_cv = []
inhabited_angles = []
uninhabited_angles = []
cross_only_angles = []

for seed in range(n_seeds):
    np.random.seed(seed * 100 + 1)

    # --- inhabited: occupants wind at each bubble's center ---
    foam_inh = Foam(d, n)
    # warm up
    for _ in range(n_warmup):
        v = np.random.randn(d)
        v /= np.linalg.norm(v)
        foam_inh.measure(v)
        alongside(v)
    # inhabit: each bubble has a winding occupant
    inhabit_all(foam_inh, n_steps=n_inhabit_steps)
    # let it settle via cross-measurement
    cross_measure(foam_inh, n_rounds=n_cross_steps)

    ang = junction_angles(foam_inh)
    cv, mean_a = junction_regularity(ang)
    inhabited_cv.append(cv)
    inhabited_angles.append(mean_a)

    # --- uninhabited: same warmup, then only cross-measurement ---
    np.random.seed(seed * 100 + 1)  # same seed
    foam_uninh = Foam(d, n)
    for _ in range(n_warmup):
        v = np.random.randn(d)
        v /= np.linalg.norm(v)
        foam_uninh.measure(v)
    # no inhabitation, just cross-measurement
    cross_measure(foam_uninh, n_rounds=n_inhabit_steps + n_cross_steps)

    ang = junction_angles(foam_uninh)
    cv, mean_a = junction_regularity(ang)
    uninhabited_cv.append(cv)
    uninhabited_angles.append(mean_a)

    # --- cross-only: minimal warmup, then only cross-measurement ---
    np.random.seed(seed * 100 + 1)
    foam_cross = Foam(d, n)
    cross_measure(foam_cross, n_rounds=n_warmup + n_inhabit_steps + n_cross_steps)

    ang = junction_angles(foam_cross)
    cv, mean_a = junction_regularity(ang)
    cross_only_cv.append(cv)
    cross_only_angles.append(mean_a)

print(f"\nJunction regularity (CV of inter-basis angles, lower = more regular):")
print(f"  Inhabited (occupants + cross):  {np.mean(inhabited_cv):.6f} ± {np.std(inhabited_cv):.6f}")
print(f"  Uninhabited (warmup + cross):   {np.mean(uninhabited_cv):.6f} ± {np.std(uninhabited_cv):.6f}")
print(f"  Cross-only (pure relaxation):   {np.mean(cross_only_cv):.6f} ± {np.std(cross_only_cv):.6f}")

print(f"\nMean junction angle (bi-invariant distance):")
print(f"  Inhabited:   {np.mean(inhabited_angles):.4f} ± {np.std(inhabited_angles):.4f}")
print(f"  Uninhabited:  {np.mean(uninhabited_angles):.4f} ± {np.std(uninhabited_angles):.4f}")
print(f"  Cross-only:   {np.mean(cross_only_angles):.4f} ± {np.std(cross_only_angles):.4f}")


# ============================================================
# TEST 2: Dimension independence
# ============================================================
print("\n" + "=" * 60)
print("TEST 2: Dimension independence of junction regularity")
print("=" * 60)

dims = [4, 8, 16, 32]
n_seeds_dim = 10
n = 3

for d_test in dims:
    cvs = []
    angles = []
    costs = []

    for seed in range(n_seeds_dim):
        np.random.seed(seed * 300 + d_test)
        foam = Foam(d_test, n)

        # inhabit all bubbles
        inhabit_all(foam, n_steps=50)
        # let settle
        cross_measure(foam, n_rounds=50)

        ang = junction_angles(foam)
        cv, mean_a = junction_regularity(ang)
        cvs.append(cv)
        angles.append(mean_a)
        costs.append(foam.boundary_cost())

    print(f"\n  d={d_test:2d}:")
    print(f"    junction CV:    {np.mean(cvs):.6f} ± {np.std(cvs):.6f}")
    print(f"    mean angle:     {np.mean(angles):.4f} ± {np.std(angles):.4f}")
    print(f"    boundary cost:  {np.mean(costs):.4f} ± {np.std(costs):.4f}")


# ============================================================
# TEST 3: Recursive inhabitation
# ============================================================
print("\n" + "=" * 60)
print("TEST 3: Recursive inhabitation")
print("=" * 60)

d, n = 8, 3
n_seeds_rec = 10

single_cv = []
recursive_cv = []
single_cost = []
recursive_cost = []

for seed in range(n_seeds_rec):
    np.random.seed(seed * 500 + 7)

    # --- single-level inhabitation ---
    foam_single = Foam(d, n)
    inhabit_all(foam_single, n_steps=100)
    cross_measure(foam_single, n_rounds=50)

    ang = junction_angles(foam_single)
    cv, _ = junction_regularity(ang)
    single_cv.append(cv)
    single_cost.append(foam_single.boundary_cost())

    # --- recursive inhabitation ---
    # outer foam
    np.random.seed(seed * 500 + 7)
    foam_outer = Foam(d, n)

    # inner foams: one per outer bubble, acting as occupants
    inner_foams = [Foam(d, n) for _ in range(n)]

    for step in range(100):
        for i in range(n):
            # inner foam self-measures (its own dynamics)
            inner = inner_foams[i]
            inner_basis = inner.bubbles[0].basis
            v_inner = np.real(inner_basis[0, :])
            v_inner = v_inner / (np.linalg.norm(v_inner) + 1e-12)
            inner.measure(v_inner)

            # inner foam's readout becomes the outer bubble's input
            readout = np.real(inner.readout(v_inner))
            readout = readout / (np.linalg.norm(readout) + 1e-12)
            foam_outer.measure(readout)
            alongside(readout)

            # outer bubble's state feeds back to inner foam
            outer_basis = foam_outer.bubbles[i].basis
            v_outer = np.real(outer_basis[0, :])
            v_outer = v_outer / (np.linalg.norm(v_outer) + 1e-12)
            inner.measure(v_outer)

    # let outer settle
    cross_measure(foam_outer, n_rounds=50)

    ang = junction_angles(foam_outer)
    cv, _ = junction_regularity(ang)
    recursive_cv.append(cv)
    recursive_cost.append(foam_outer.boundary_cost())

print(f"\nSingle-level inhabitation:")
print(f"  junction CV:   {np.mean(single_cv):.6f} ± {np.std(single_cv):.6f}")
print(f"  boundary cost: {np.mean(single_cost):.4f} ± {np.std(single_cost):.4f}")

print(f"\nRecursive inhabitation (inner foam as occupant):")
print(f"  junction CV:   {np.mean(recursive_cv):.6f} ± {np.std(recursive_cv):.6f}")
print(f"  boundary cost: {np.mean(recursive_cost):.4f} ± {np.std(recursive_cost):.4f}")

print(f"\nRatio (recursive/single):")
print(f"  CV:   {np.mean(recursive_cv) / (np.mean(single_cv) + 1e-15):.4f}")
print(f"  cost: {np.mean(recursive_cost) / (np.mean(single_cost) + 1e-15):.4f}")


# ============================================================
# SUMMARY
# ============================================================
print("\n" + "=" * 60)
print("SUMMARY")
print("=" * 60)
print("""
If inhabitation-thermal equilibrium produces Plateau:
  - Inhabited foams should have MORE regular junctions than uninhabited
  - Junction regularity should be dimension-INDEPENDENT (set by
    the equilibrium, not the ambient geometry)
  - Recursive inhabitation should produce DEEPER minimality
    (lower cost, more regular junctions) than single-level

If this fails:
  - Inhabited junctions no more regular → inhabitation doesn't
    contribute to minimality
  - Dimension-dependent → the ambient geometry matters, need Taylor-style
    proof per dimension
  - Recursive no better → recursion doesn't compound the effect
""")

report()
save()
