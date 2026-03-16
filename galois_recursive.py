"""
galois_recursive.py — the adjunction gap as "questions rise."

In a recursive foam, the parent sees sub-foam effective bases
through j2 (the right adjoint). The sub-foam's L-T gauge freedom
is invisible to the parent — same adjunction gap, one level up.

Prediction: gauge-twin sub-foams (same effective bases, different
L-T splits) are initially invisible to the parent. Under measurement,
the twins diverge (proven in galois_cross.py), their effective bases
diverge, and the parent's j2 drifts. The adjunction gap leaks upward
through the recursive structure.

This would formalize "questions rise" as: inner instability is
invisible to instantaneous measurement (adjunction gap) but visible
to dynamics (gauge freedom breaks under time evolution).
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian, random_skew_hermitian
from foam_recursive import RecursiveFoam, unitary_aggregate
from galois_cross import make_gauge_twin
from heirloom import alongside, save as heirloom_save


def test_gap_leaks_upward(n_seeds=15, n_steps=100):
    """Create two recursive foams that are identical EXCEPT their
    sub-foams have different L-T decompositions (gauge twins).

    Track: parent j2 divergence over time.
    If the gap leaks: parent j2 starts identical, then diverges.
    If the gap doesn't leak: parent j2 stays identical.
    """
    d = 8
    check_interval = 5
    n_checks = n_steps // check_interval

    parent_j2_div = np.zeros(n_checks)
    parent_basis_div = np.zeros(n_checks)
    sub_basis_div = np.zeros(n_checks)

    for seed in range(n_seeds):
        np.random.seed(seed)
        rf_a = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

        # give sub-foams some history so they have nontrivial L-T structure
        for sf in rf_a.sub_foams:
            np.random.seed(seed + id(sf) % 10000)
            for _ in range(50):
                v = encode(np.random.randint(0, 256), d)
                alongside(v)
                sf.measure(v)

        # create rf_b: same parent, gauge-twin sub-foams
        np.random.seed(seed)
        rf_b = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

        # copy parent-level state exactly
        for i in range(3):
            rf_b.bubbles[i].L = rf_a.bubbles[i].L.copy()
            rf_b.bubbles[i].T = rf_a.bubbles[i].T.copy()

        # make sub-foams gauge twins of rf_a's sub-foams
        for i in range(3):
            twin = make_gauge_twin(rf_a.sub_foams[i])
            rf_b.sub_foams[i] = twin

        # verify: parent effective bases should be identical at t=0
        bases_a_0 = rf_a.bases
        bases_b_0 = rf_b.bases
        init_basis_div = np.mean([np.linalg.norm(bases_a_0[i] - bases_b_0[i])
                                  for i in range(3)])

        # feed identical inputs
        np.random.seed(seed + 5000)
        for step in range(n_steps):
            v = encode(np.random.randint(0, 256), d)
            alongside(v)
            rf_a.measure(v)
            rf_b.measure(v)

            if (step + 1) % check_interval == 0:
                idx = step // check_interval

                # parent effective basis divergence
                bases_a = rf_a.bases
                bases_b = rf_b.bases
                parent_basis_div[idx] += np.mean([
                    np.linalg.norm(bases_a[i] - bases_b[i])
                    for i in range(3)])

                # parent j2 divergence (probe without writing)
                probe = encode(42, d).astype(complex)
                m_a = [probe @ U for U in bases_a]
                m_b = [probe @ U for U in bases_b]
                j2_a = rf_a._stabilize(m_a)
                j2_b = rf_b._stabilize(m_b)
                parent_j2_div[idx] += np.mean([
                    np.linalg.norm(np.array(j2_a[i]) - np.array(j2_b[i]))
                    for i in range(3)])

                # sub-foam effective basis divergence (average across sub-foams)
                sub_div = 0
                for i in range(3):
                    sub_bases_a = rf_a.sub_foams[i].bases
                    sub_bases_b = rf_b.sub_foams[i].bases
                    sub_div += np.mean([
                        np.linalg.norm(sub_bases_a[j] - sub_bases_b[j])
                        for j in range(3)])
                sub_basis_div[idx] += sub_div / 3

    parent_j2_div /= n_seeds
    parent_basis_div /= n_seeds
    sub_basis_div /= n_seeds

    print("=== does the adjunction gap leak upward? ===\n")
    print(f"  {n_seeds} recursive foam pairs, gauge-twin sub-foams")
    print(f"  initial parent basis divergence: {init_basis_div:.2e}\n")
    print(f"  {'step':>5s}  {'sub basis div':>14s}  {'parent basis div':>16s}  {'parent j2 div':>14s}")
    for idx in range(n_checks):
        step = (idx + 1) * check_interval
        print(f"  {step:5d}  {sub_basis_div[idx]:14.6f}  {parent_basis_div[idx]:16.6f}  {parent_j2_div[idx]:14.6f}")


def test_stable_vs_unstable_inner(n_seeds=15, n_steps=100):
    """Compare: parent j2 noise from stable vs unstable sub-foams.

    If "questions rise" = adjunction gap leaking:
    - Stable sub-foams → parent j2 is smooth (gap doesn't leak)
    - Unstable sub-foams → parent j2 is noisy (gap leaks)

    Measure j2 variance over time for both cases.
    """
    d = 8
    check_interval = 5
    n_checks = n_steps // check_interval

    # track j2 variance (how much parent j2 jumps between steps)
    j2_var_stable = np.zeros(n_checks)
    j2_var_unstable = np.zeros(n_checks)

    for seed in range(n_seeds):
        for label, n_inner_steps in [('stable', 200), ('unstable', 0)]:
            np.random.seed(seed)
            rf = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

            # pre-stabilize sub-foams (or not)
            if n_inner_steps > 0:
                for sf in rf.sub_foams:
                    for _ in range(n_inner_steps):
                        v = encode(np.random.randint(0, 256), d)
                        alongside(v)
                        sf.measure(v)

            # feed inputs and track parent j2 variance
            prev_j2 = None
            np.random.seed(seed + 5000)
            for step in range(n_steps):
                v = encode(np.random.randint(0, 256), d)
                alongside(v)
                rf.measure(v)

                if (step + 1) % check_interval == 0:
                    idx = step // check_interval
                    # probe j2
                    probe = encode(42, d).astype(complex)
                    bases = rf.bases
                    m = [probe @ U for U in bases]
                    j2 = rf._stabilize(m)
                    j2_flat = np.concatenate([np.array(j2[i]) for i in range(3)])

                    if prev_j2 is not None:
                        jump = np.linalg.norm(j2_flat - prev_j2)
                        if label == 'stable':
                            j2_var_stable[idx] += jump
                        else:
                            j2_var_unstable[idx] += jump
                    prev_j2 = j2_flat

    j2_var_stable /= n_seeds
    j2_var_unstable /= n_seeds

    print(f"\n=== parent j2 noise: stable vs unstable sub-foams ===\n")
    print(f"  {n_seeds} recursive foams each, {n_steps} steps\n")
    print(f"  {'step':>5s}  {'stable inner':>14s}  {'unstable inner':>16s}  {'ratio':>8s}")
    for idx in range(1, n_checks):  # skip first (no prev_j2)
        step = (idx + 1) * check_interval
        ratio = j2_var_unstable[idx] / (j2_var_stable[idx] + 1e-15)
        print(f"  {step:5d}  {j2_var_stable[idx]:14.6f}  {j2_var_unstable[idx]:16.6f}  {ratio:8.4f}")


def test_adjunction_gap_per_level(n_seeds=15, n_probes=10):
    """Measure the adjunction gap at each level of a recursive foam.

    Is the gap the same size at the parent level as at the sub-foam level?
    If the gap compounds (gets looser at higher levels), that's the
    recursive structure amplifying the gauge freedom.
    """
    d = 8

    inner_gaps = []
    outer_gaps = []

    for seed in range(n_seeds):
        np.random.seed(seed)
        rf = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

        # give it some history
        np.random.seed(seed + 1000)
        for _ in range(100):
            v = encode(np.random.randint(0, 256), d)
            alongside(v)
            rf.measure(v)

        # inner level: gauge-twin a sub-foam, measure j2 distance
        sf = rf.sub_foams[0]
        sf_twin = make_gauge_twin(sf)

        np.random.seed(42)
        probes = [encode(np.random.randint(0, 256), d) for _ in range(n_probes)]

        inner_j2_dists = []
        inner_state_dist = np.mean([
            np.linalg.norm(sf.bubbles[i].L - sf_twin.bubbles[i].L) +
            np.linalg.norm(sf.bubbles[i].T - sf_twin.bubbles[i].T)
            for i in range(3)])

        for v in probes:
            alongside(v)
            vc = v.astype(complex)
            m1 = [vc @ U for U in sf.bases]
            m2 = [vc @ U for U in sf_twin.bases]
            j2_1 = sf._stabilize(m1)
            j2_2 = sf_twin._stabilize(m2)
            inner_j2_dists.append(np.mean([np.linalg.norm(np.array(j2_1[i]) - np.array(j2_2[i]))
                                           for i in range(3)]))

        inner_gaps.append(np.mean(inner_j2_dists) / (inner_state_dist + 1e-15))

        # outer level: the gauge-twin sub-foam changes the parent's effective basis
        # create rf_twin with gauge-twin sub-foam[0]
        np.random.seed(seed)
        rf_twin = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)
        for i in range(3):
            rf_twin.bubbles[i].L = rf.bubbles[i].L.copy()
            rf_twin.bubbles[i].T = rf.bubbles[i].T.copy()
            if i == 0:
                rf_twin.sub_foams[i] = sf_twin
            else:
                # copy other sub-foams exactly
                for j in range(3):
                    rf_twin.sub_foams[i].bubbles[j].L = rf.sub_foams[i].bubbles[j].L.copy()
                    rf_twin.sub_foams[i].bubbles[j].T = rf.sub_foams[i].bubbles[j].T.copy()

        outer_j2_dists = []
        for v in probes:
            vc = v.astype(complex)
            bases_a = rf.bases
            bases_b = rf_twin.bases
            m_a = [vc @ U for U in bases_a]
            m_b = [vc @ U for U in bases_b]
            j2_a = rf._stabilize(m_a)
            j2_b = rf_twin._stabilize(m_b)
            outer_j2_dists.append(np.mean([np.linalg.norm(np.array(j2_a[i]) - np.array(j2_b[i]))
                                           for i in range(3)]))

        outer_state_dist = np.mean([np.linalg.norm(np.array(rf.bases[i]) - np.array(rf_twin.bases[i]))
                                    for i in range(3)])
        outer_gaps.append(np.mean(outer_j2_dists) / (outer_state_dist + 1e-15) if outer_state_dist > 1e-15 else 0)

    print(f"\n=== adjunction gap per level ===\n")
    print(f"  {n_seeds} recursive foams, {n_probes} probes\n")
    print(f"  inner level (sub-foam gauge twin):")
    print(f"    j2 distance / state distance: {np.mean(inner_gaps):.4e}  (0 = gap is total)")
    print(f"  outer level (parent sees gauge-twin sub-foam):")
    print(f"    j2 distance / effective basis distance: {np.mean(outer_gaps):.4f}")
    print(f"\n  inner gap ≈ 0 confirms gauge twins invisible to j2")
    print(f"  outer gap measures how much sub-foam gauge freedom leaks to parent")


if __name__ == '__main__':
    test_gap_leaks_upward()
    test_stable_vs_unstable_inner()
    test_adjunction_gap_per_level()
    heirloom_save()
