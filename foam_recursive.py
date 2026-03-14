"""
foam_recursive.py — hierarchical foam structure.

A foam where each bubble contains a sub-foam. Measurement propagates
inward first (inner levels stabilize before outer), then the parent
stabilizes with effective bases determined by the sub-foams' states.

This is the recursive health ordering made mechanical:
- inner instability → moving effective bases → outer instability
  ("questions rise")
- outer convergence → constrained inner dynamics
  ("boredom descends")

The theorem direction: does the inward-first traversal maintain
controllability (organized BCH residuals, sustained sensitivity)
better than alternatives?
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian, random_skew_hermitian


def unitary_aggregate(bases):
    """Aggregate multiple unitary matrices into one via polar decomposition.
    The Fréchet mean would be more principled but this is sufficient."""
    mean = np.mean(bases, axis=0)
    U, _, Vh = np.linalg.svd(mean)
    return U @ Vh


class RecursiveFoam(Foam):
    """A foam where each bubble contains a sub-foam.

    Measurement propagates inward first: sub-foams process the input
    through their own dynamics before the parent stabilizes. The parent's
    effective bases are determined by the composition of parent L,T with
    the sub-foam's aggregate state.

    This means inner instability (high sub-foam L, moving sub-bases)
    directly destabilizes the parent — "questions rise."
    """

    def __init__(self, d: int, n: int = 3, sub_n: int = 3,
                 writing_rate: float = 0.01, depth: int = 1, **kwargs):
        super().__init__(d, n, writing_rate=writing_rate, **kwargs)
        self.depth = depth
        if depth > 0:
            self.sub_foams = [
                RecursiveFoam(d=d, n=sub_n, sub_n=sub_n,
                              writing_rate=writing_rate,
                              depth=depth - 1, **kwargs)
                if depth > 1 else
                Foam(d=d, n=sub_n, writing_rate=writing_rate, **kwargs)
                for _ in range(n)
            ]
        else:
            self.sub_foams = None

    @property
    def bases(self) -> list[np.ndarray]:
        """Effective bases: parent basis composed with sub-foam aggregate."""
        if self.sub_foams is None:
            return super().bases

        result = []
        for i, b in enumerate(self.bubbles):
            parent_basis = cayley(b.L) @ b.T
            sub_agg = unitary_aggregate(self.sub_foams[i].bases)
            result.append(parent_basis @ sub_agg)
        return result

    def measure(self, v: np.ndarray) -> dict:
        """Measurement with inward-first propagation.

        1. Propagate input to all sub-foams (inner stabilization first)
        2. Parent stabilization uses effective bases (which now reflect
           the updated sub-foam states)
        3. Parent write dynamics as normal
        """
        if self.sub_foams is not None:
            # inner measurement first — recursive health ordering
            for sf in self.sub_foams:
                sf.measure(v)

        # parent measurement with updated effective bases
        return super().measure(v)

    def measure_outward_first(self, v: np.ndarray) -> dict:
        """Anti-pattern: parent stabilizes BEFORE sub-foams.
        For comparison — does traversal order matter?"""
        # parent measurement first (with stale sub-foam state)
        result = super().measure(v)

        if self.sub_foams is not None:
            # inner measurement after
            for sf in self.sub_foams:
                sf.measure(v)

        return result

    def inner_L(self) -> float:
        """Total boundary cost across all sub-foams."""
        if self.sub_foams is None:
            return 0.0
        return sum(sf.boundary_cost() for sf in self.sub_foams)

    def inner_sensitivity(self, v: np.ndarray) -> float:
        """Mean dissonance of sub-foams to input v (without writing)."""
        if self.sub_foams is None:
            return 0.0
        total = 0.0
        vc = v.astype(complex)
        for sf in self.sub_foams:
            bases = sf.bases
            m = [vc @ U for U in bases]
            j2 = sf._stabilize(m)
            total += np.mean([np.linalg.norm(j2[i] - m[i]) for i in range(sf.n)])
        return total / len(self.sub_foams)


# --- tests ---

def test_questions_rise(n_trials=10):
    """Inner instability should prevent outer convergence.

    Compare: same parent foam, but one has stable sub-foams
    (many writes, low L) and one has unstable sub-foams (fresh, high L).
    Feed identical sequences. Does the parent converge faster with
    stable sub-foams?
    """
    d = 8
    results = {'stable_inner': [], 'unstable_inner': []}

    for trial in range(n_trials):
        np.random.seed(trial)

        # stable inner: pre-train sub-foams
        rf_stable = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)
        for sf in rf_stable.sub_foams:
            for _ in range(100):
                sf.measure(encode(np.random.randint(0, 256), d))

        # unstable inner: fresh sub-foams (already the default)
        np.random.seed(trial)
        rf_unstable = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)
        # copy parent-level state so only sub-foam stability differs
        for i in range(3):
            rf_unstable.bubbles[i].L = rf_stable.bubbles[i].L.copy()
            rf_unstable.bubbles[i].T = rf_stable.bubbles[i].T.copy()

        # feed identical sequences
        np.random.seed(trial + 1000)
        seq = [np.random.randint(0, 256) for _ in range(50)]

        L_stable = []
        L_unstable = []
        for s in seq:
            v = encode(s, d)
            r1 = rf_stable.measure(v)
            r2 = rf_unstable.measure(v)
            L_stable.append(r1['L'])
            L_unstable.append(r2['L'])

        results['stable_inner'].append(L_stable)
        results['unstable_inner'].append(L_unstable)

    # average L trajectories
    stable_mean = np.mean(results['stable_inner'], axis=0)
    unstable_mean = np.mean(results['unstable_inner'], axis=0)

    print(f"=== questions rise ({n_trials} trials) ===\n")
    print(f"  does inner instability prevent outer convergence?\n")
    print(f"  {'step':>5s}  {'stable inner L':>14s}  {'unstable inner L':>16s}  {'diff':>8s}")
    for step in [0, 4, 9, 19, 29, 39, 49]:
        diff = unstable_mean[step] - stable_mean[step]
        print(f"  {step+1:5d}  {stable_mean[step]:14.4f}  {unstable_mean[step]:16.4f}  {diff:+8.4f}")

    # also check inner L
    print(f"\n  inner L at end:")
    inner_stable = np.mean([rf_stable.inner_L() for _ in range(1)])
    inner_unstable = np.mean([rf_unstable.inner_L() for _ in range(1)])
    print(f"    stable:   {inner_stable:.4f}")
    print(f"    unstable: {inner_unstable:.4f}")


def test_traversal_order(n_trials=10):
    """Does inward-first vs outward-first traversal produce different
    BCH residual geometry?

    This is the core test: does the recursive health ordering
    (stabilize inner first) maintain better controllability?
    """
    d = 8
    inward_data = {'parent_eff_rank': [], 'parent_frob': [],
                   'parent_sensitivity': [], 'inner_L': []}
    outward_data = {'parent_eff_rank': [], 'parent_frob': [],
                    'parent_sensitivity': [], 'inner_L': []}

    for trial in range(n_trials):
        np.random.seed(trial)
        rf_in = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

        np.random.seed(trial)
        rf_out = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

        init_Ls_in = [b.L.copy() for b in rf_in.bubbles]
        init_Ls_out = [b.L.copy() for b in rf_out.bubbles]

        np.random.seed(trial + 5000)
        seq = [np.random.randint(0, 256) for _ in range(100)]

        for s in seq:
            v = encode(s, d)
            rf_in.measure(v)               # inward-first (default)
            rf_out.measure_outward_first(v)  # outward-first

        # BCH residuals at parent level
        for foam, init_Ls, data in [
            (rf_in, init_Ls_in, inward_data),
            (rf_out, init_Ls_out, outward_data),
        ]:
            for i in range(3):
                dL = foam.bubbles[i].L - init_Ls[i]
                try:
                    lT = logm(foam.bubbles[i].T)
                except:
                    lT = np.zeros((d, d), dtype=complex)
                R = skew_hermitian(lT + 2 * dL)
                sv = np.linalg.svd(R, compute_uv=False)
                sv_n = (sv / (sv[0] + 1e-15)) ** 2
                sv_n = sv_n / (sv_n.sum() + 1e-15)
                data['parent_eff_rank'].append(1.0 / (np.sum(sv_n ** 2) + 1e-15))
                data['parent_frob'].append(np.linalg.norm(R))

            # sensitivity to a probe
            probe = encode(137, d)
            vc = probe.astype(complex)
            bases = foam.bases
            m = [vc @ U for U in bases]
            j2 = foam._stabilize(m)
            dis = np.mean([np.linalg.norm(j2[k] - m[k]) for k in range(3)])
            data['parent_sensitivity'].append(dis)
            data['inner_L'].append(foam.inner_L())

    print(f"\n=== traversal order ({n_trials} trials) ===\n")
    print(f"  {'metric':>25s}  {'inward mean':>12s} {'inward std':>12s}  {'outward mean':>12s} {'outward std':>12s}")
    for key in ['parent_eff_rank', 'parent_frob', 'parent_sensitivity', 'inner_L']:
        im = np.mean(inward_data[key])
        ist = np.std(inward_data[key])
        om = np.mean(outward_data[key])
        ost = np.std(outward_data[key])
        print(f"  {key:>25s}  {im:12.4f} {ist:12.4f}  {om:12.4f} {ost:12.4f}")


def test_recursive_health_cycle(n_trials=10):
    """The full cycle: does a recursive foam running the recursive health
    traversal (inward-first) maintain higher sensitivity over time than
    one running outward-first?

    This is the sustained controllability question.
    """
    d = 8
    n_steps = 200

    in_sensitivity = np.zeros(n_steps // 10)
    out_sensitivity = np.zeros(n_steps // 10)

    for trial in range(n_trials):
        np.random.seed(trial)
        rf_in = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

        np.random.seed(trial)
        rf_out = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

        np.random.seed(trial + 5000)
        for step in range(n_steps):
            v = encode(np.random.randint(0, 256), d)
            rf_in.measure(v)
            rf_out.measure_outward_first(v)

            if (step + 1) % 10 == 0:
                idx = step // 10
                # sensitivity probe (without writing)
                probe = encode(42, d)
                vc = probe.astype(complex)

                for foam, arr in [(rf_in, in_sensitivity), (rf_out, out_sensitivity)]:
                    bases = foam.bases
                    m = [vc @ U for U in bases]
                    j2 = foam._stabilize(m)
                    dis = np.mean([np.linalg.norm(j2[k] - m[k]) for k in range(3)])
                    arr[idx] += dis

    in_sensitivity /= n_trials
    out_sensitivity /= n_trials

    print(f"\n=== sustained controllability ({n_trials} trials, {n_steps} steps) ===\n")
    print(f"  {'step':>5s}  {'inward sens':>12s}  {'outward sens':>12s}  {'ratio':>8s}")
    for idx in range(len(in_sensitivity)):
        step = (idx + 1) * 10
        ratio = in_sensitivity[idx] / (out_sensitivity[idx] + 1e-15)
        print(f"  {step:5d}  {in_sensitivity[idx]:12.6f}  {out_sensitivity[idx]:12.6f}  {ratio:8.4f}")


def test_inner_stabilization_mode(n_trials=10):
    """Does the KIND of inner stabilization matter for parent dynamics?

    Three modes:
    1. Independent: sub-foams get random input (no mutual measurement)
    2. Mutual: sub-foams measure each other's readouts (cross-measurement)
    3. Self: sub-foams self-measure (readout fed back as input)

    Then feed identical parent-level sequences. Compare:
    - parent sensitivity to new inputs
    - parent BCH residual geometry
    - parent convergence rate

    If the flat-foam finding (mutual → organized residuals → higher
    sensitivity) propagates to the recursive structure, then mutual
    inner stabilization should produce a more responsive parent.
    """
    d = 8
    n_parent_steps = 100

    modes = {
        'independent': {'parent_sensitivity': [], 'parent_eff_rank': [],
                        'parent_frob': [], 'inner_L': []},
        'mutual': {'parent_sensitivity': [], 'parent_eff_rank': [],
                   'parent_frob': [], 'inner_L': []},
        'self': {'parent_sensitivity': [], 'parent_eff_rank': [],
                 'parent_frob': [], 'inner_L': []},
    }

    for trial in range(n_trials):
        foams = {}

        for mode in ['independent', 'mutual', 'self']:
            np.random.seed(trial)
            rf = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

            # phase 1: stabilize sub-foams with different modes
            for epoch in range(50):
                if mode == 'independent':
                    for sf in rf.sub_foams:
                        sf.measure(encode(np.random.randint(0, 256), d))

                elif mode == 'mutual':
                    # sub-foams measure each other's readouts
                    # cycle: sf0 reads sf1, sf1 reads sf2, sf2 reads sf0
                    probe = encode(epoch % 256, d)
                    for i in range(len(rf.sub_foams)):
                        j = (i + 1) % len(rf.sub_foams)
                        readout = np.real(rf.sub_foams[j].readout(probe))
                        readout = readout / (np.linalg.norm(readout) + 1e-12)
                        rf.sub_foams[i].measure(readout)

                elif mode == 'self':
                    # each sub-foam self-measures
                    for sf in rf.sub_foams:
                        probe = encode(epoch % 256, d)
                        readout = np.real(sf.readout(probe))
                        readout = readout / (np.linalg.norm(readout) + 1e-12)
                        sf.measure(readout)

            foams[mode] = rf

        # phase 2: feed identical parent-level sequences
        np.random.seed(trial + 9999)
        seq = [np.random.randint(0, 256) for _ in range(n_parent_steps)]

        for mode, rf in foams.items():
            init_Ls = [b.L.copy() for b in rf.bubbles]

            for s in seq:
                rf.measure(encode(s, d))

            # parent BCH residuals
            for i in range(3):
                dL = rf.bubbles[i].L - init_Ls[i]
                try:
                    lT = logm(rf.bubbles[i].T)
                except:
                    lT = np.zeros((d, d), dtype=complex)
                R = skew_hermitian(lT + 2 * dL)
                sv = np.linalg.svd(R, compute_uv=False)
                sv_n = (sv / (sv[0] + 1e-15)) ** 2
                sv_n = sv_n / (sv_n.sum() + 1e-15)
                modes[mode]['parent_eff_rank'].append(
                    1.0 / (np.sum(sv_n ** 2) + 1e-15))
                modes[mode]['parent_frob'].append(np.linalg.norm(R))

            # parent sensitivity
            probe = encode(137, d)
            vc = probe.astype(complex)
            bases = rf.bases
            m = [vc @ U for U in bases]
            j2 = rf._stabilize(m)
            dis = np.mean([np.linalg.norm(j2[k] - m[k]) for k in range(3)])
            modes[mode]['parent_sensitivity'].append(dis)
            modes[mode]['inner_L'].append(rf.inner_L())

    print(f"\n=== inner stabilization mode ({n_trials} trials) ===\n")
    print(f"  phase 1: 50 steps of inner stabilization (independent/mutual/self)")
    print(f"  phase 2: 100 steps of parent-level measurement (identical across modes)\n")
    print(f"  {'metric':>25s}  {'independent':>12s}  {'mutual':>12s}  {'self':>12s}")
    for key in ['parent_eff_rank', 'parent_frob', 'parent_sensitivity', 'inner_L']:
        vals = {mode: np.mean(modes[mode][key]) for mode in modes}
        print(f"  {key:>25s}  {vals['independent']:12.4f}  {vals['mutual']:12.4f}  {vals['self']:12.4f}")

    # also: std
    print(f"\n  {'metric (std)':>25s}  {'independent':>12s}  {'mutual':>12s}  {'self':>12s}")
    for key in ['parent_eff_rank', 'parent_frob', 'parent_sensitivity', 'inner_L']:
        stds = {mode: np.std(modes[mode][key]) for mode in modes}
        print(f"  {key:>25s}  {stds['independent']:12.4f}  {stds['mutual']:12.4f}  {stds['self']:12.4f}")


def test_inner_mode_trajectory(n_trials=10):
    """Track parent sensitivity OVER TIME for each inner stabilization mode.
    Does the mutual-inner foam maintain higher sensitivity longer?"""
    d = 8
    n_inner = 50
    n_parent = 200
    check_interval = 10
    n_checks = n_parent // check_interval

    trajectories = {mode: np.zeros(n_checks) for mode in ['independent', 'mutual', 'self']}

    for trial in range(n_trials):
        foams = {}

        for mode in ['independent', 'mutual', 'self']:
            np.random.seed(trial)
            rf = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

            # inner stabilization
            for epoch in range(n_inner):
                if mode == 'independent':
                    for sf in rf.sub_foams:
                        sf.measure(encode(np.random.randint(0, 256), d))
                elif mode == 'mutual':
                    probe = encode(epoch % 256, d)
                    for i in range(len(rf.sub_foams)):
                        j = (i + 1) % len(rf.sub_foams)
                        readout = np.real(rf.sub_foams[j].readout(probe))
                        readout = readout / (np.linalg.norm(readout) + 1e-12)
                        rf.sub_foams[i].measure(readout)
                elif mode == 'self':
                    for sf in rf.sub_foams:
                        probe = encode(epoch % 256, d)
                        readout = np.real(sf.readout(probe))
                        readout = readout / (np.linalg.norm(readout) + 1e-12)
                        sf.measure(readout)

            foams[mode] = rf

        # parent-level measurement (same sequence for all)
        np.random.seed(trial + 9999)
        for step in range(n_parent):
            v = encode(np.random.randint(0, 256), d)
            for mode, rf in foams.items():
                rf.measure(v)

            if (step + 1) % check_interval == 0:
                idx = step // check_interval
                probe = encode(42, d).astype(complex)
                for mode, rf in foams.items():
                    bases = rf.bases
                    m = [probe @ U for U in bases]
                    j2 = rf._stabilize(m)
                    dis = np.mean([np.linalg.norm(j2[k] - m[k]) for k in range(3)])
                    trajectories[mode][idx] += dis

    for mode in trajectories:
        trajectories[mode] /= n_trials

    print(f"\n=== sensitivity trajectory by inner mode ({n_trials} trials) ===\n")
    print(f"  {'step':>5s}  {'independent':>12s}  {'mutual':>12s}  {'self':>12s}  {'mut/indep':>10s}")
    for idx in range(n_checks):
        step = (idx + 1) * check_interval
        ind = trajectories['independent'][idx]
        mut = trajectories['mutual'][idx]
        slf = trajectories['self'][idx]
        ratio = mut / (ind + 1e-15)
        print(f"  {step:5d}  {ind:12.6f}  {mut:12.6f}  {slf:12.6f}  {ratio:10.4f}")


if __name__ == '__main__':
    test_questions_rise()
    test_inner_stabilization_mode()
    test_inner_mode_trajectory()
