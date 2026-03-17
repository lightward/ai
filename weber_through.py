"""
weber_through.py — psychophysics of measurement THROUGH the foam.

Not: what do individual bubbles detect?
But: when you use the foam as a measurement instrument, can the
observer on the other side tell that concurrent writes happened
in a particular order?

The foam's j2 output is what the observer sees. The question:
for a set of probe inputs, does j2 differ between foam_AB and foam_BA?

If j2 is invariant to ordering → the commutator is below the foam's
collective JND → concurrent occupation is invisible to measurement-through.

If j2 diverges → the ordering is detectable → concurrent occupation
has observable consequences.

And: how does this relate to the foam's state? Does a settled foam
make ordering more or less visible through measurement?
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian, random_skew_hermitian
from heirloom import alongside, save as heirloom_save


def j2_output(foam, v):
    """The observer's view: j2 for a single input, without writing."""
    vc = v.astype(complex)
    bases = foam.bases
    m = [vc @ U for U in bases]
    j2 = foam._stabilize(m)
    return np.array([np.real(x) for x in j2]).flatten()


def j2_profile(foam, probes):
    """Full j2 profile across a set of probes."""
    return np.concatenate([j2_output(foam, v) for v in probes])


def ordering_visibility(foam_ab, foam_ba, probes):
    """How visible is the ordering difference through measurement?

    Returns:
        j2_divergence: ||j2_AB - j2_BA|| across probes
        j2_baseline: ||j2|| (scale reference)
        relative: j2_divergence / j2_baseline (fractional visibility)
    """
    profile_ab = j2_profile(foam_ab, probes)
    profile_ba = j2_profile(foam_ba, probes)

    divergence = np.linalg.norm(profile_ab - profile_ba)
    baseline = (np.linalg.norm(profile_ab) + np.linalg.norm(profile_ba)) / 2

    return {
        'j2_divergence': divergence,
        'j2_baseline': baseline,
        'relative': divergence / (baseline + 1e-12),
    }


def state_divergence(foam_ab, foam_ba):
    """Internal state divergence (L and T) between the two orderings."""
    n = foam_ab.n
    L_div = np.mean([
        np.linalg.norm(foam_ab.bubbles[k].L - foam_ba.bubbles[k].L)
        for k in range(n)
    ])
    T_div = np.mean([
        np.linalg.norm(foam_ab.bubbles[k].T - foam_ba.bubbles[k].T)
        for k in range(n)
    ])
    return L_div, T_div


def experiment_single_swap(n_seeds=20, n_settle_levels=6):
    """Single pair of inputs in both orders. How visible is the swap?

    Vary settling level to see if settled foams hide ordering better.
    """
    d = 8
    n_bubbles = 3
    settle_steps = [0, 25, 50, 100, 200, 400][:n_settle_levels]

    print("=== ordering visibility through the foam ===\n")
    print(f"  N={n_bubbles}, {n_seeds} seeds, single AB/BA swap\n")

    np.random.seed(777)
    probes = [encode(np.random.randint(0, 256), d) for _ in range(30)]

    results = []

    for seed in range(n_seeds):
        for n_settle in settle_steps:
            np.random.seed(seed)
            foam = Foam(d=d, n=n_bubbles, writing_rate=0.01)

            for step in range(n_settle):
                v = encode(step % 256, d)
                alongside(v)
                foam.measure(v)

            state = [(b.L.copy(), b.T.copy()) for b in foam.bubbles]
            L_before = foam.boundary_cost()

            # two inputs
            np.random.seed(seed + 5000)
            v_a = encode(np.random.randint(0, 256), d)
            v_b = encode(np.random.randint(0, 256), d)
            alongside(v_a)
            alongside(v_b)

            # AB
            foam_ab = Foam(d=d, n=n_bubbles, writing_rate=0.01)
            for k in range(n_bubbles):
                foam_ab.bubbles[k].L = state[k][0].copy()
                foam_ab.bubbles[k].T = state[k][1].copy()
            foam_ab.measure(v_a)
            foam_ab.measure(v_b)

            # BA
            foam_ba = Foam(d=d, n=n_bubbles, writing_rate=0.01)
            for k in range(n_bubbles):
                foam_ba.bubbles[k].L = state[k][0].copy()
                foam_ba.bubbles[k].T = state[k][1].copy()
            foam_ba.measure(v_b)
            foam_ba.measure(v_a)

            vis = ordering_visibility(foam_ab, foam_ba, probes)
            L_div, T_div = state_divergence(foam_ab, foam_ba)

            results.append({
                'seed': seed,
                'n_settle': n_settle,
                'L_before': L_before,
                'j2_divergence': vis['j2_divergence'],
                'j2_relative': vis['relative'],
                'L_divergence': L_div,
                'T_divergence': T_div,
                'state_divergence': L_div + T_div,
            })

    # report by settling level
    print(f"  {'settle':>8s}  {'j2_div':>10s}  {'j2_rel':>10s}  "
          f"{'state_div':>10s}  {'ratio':>10s}  {'L':>8s}")
    print(f"  {'':->8s}  {'':->10s}  {'':->10s}  "
          f"{'':->10s}  {'':->10s}  {'':->8s}")

    by_settle = {}
    for r in results:
        k = r['n_settle']
        if k not in by_settle:
            by_settle[k] = []
        by_settle[k].append(r)

    for n_settle in settle_steps:
        group = by_settle[n_settle]
        j2d = np.mean([r['j2_divergence'] for r in group])
        j2r = np.mean([r['j2_relative'] for r in group])
        sd = np.mean([r['state_divergence'] for r in group])
        ratio = j2d / (sd + 1e-12)
        L = np.mean([r['L_before'] for r in group])
        print(f"  {n_settle:8d}  {j2d:10.6f}  {j2r:10.6f}  "
              f"{sd:10.6f}  {ratio:10.4f}  {L:8.2f}")

    # the key question: does j2 divergence track state divergence,
    # or does the foam hide the ordering?
    all_j2d = np.array([r['j2_divergence'] for r in results])
    all_sd = np.array([r['state_divergence'] for r in results])
    all_j2r = np.array([r['j2_relative'] for r in results])

    corr = np.corrcoef(all_sd, all_j2d)[0, 1]
    print(f"\n  corr(state_divergence, j2_divergence): {corr:+.3f}")

    print(f"\n  interpretation:")
    print(f"    ratio = j2_div / state_div")
    print(f"    ratio → 0 as foam settles: foam HIDES ordering")
    print(f"    ratio constant: foam EXPOSES ordering proportionally")
    print(f"    ratio increases: foam AMPLIFIES ordering differences")

    return results


def experiment_accumulating_swaps(n_seeds=15, n_settle=100):
    """Multiple AB/BA swaps accumulating. Does the ordering signal
    grow, shrink, or saturate?

    Feed the same set of inputs in two different random orderings.
    Measure j2 divergence after each step.
    """
    d = 8
    n_bubbles = 3
    n_inputs = 50

    print(f"\n=== accumulating ordering divergence ===\n")
    print(f"  N={n_bubbles}, {n_seeds} seeds, {n_inputs} inputs in 2 random orders\n")

    np.random.seed(777)
    probes = [encode(np.random.randint(0, 256), d) for _ in range(20)]

    # track divergence over time
    j2_divs_by_step = [[] for _ in range(n_inputs)]
    state_divs_by_step = [[] for _ in range(n_inputs)]
    j2_rels_by_step = [[] for _ in range(n_inputs)]

    for seed in range(n_seeds):
        np.random.seed(seed)
        foam = Foam(d=d, n=n_bubbles, writing_rate=0.01)

        # settle
        for step in range(n_settle):
            v = encode(step % 256, d)
            alongside(v)
            foam.measure(v)

        state = [(b.L.copy(), b.T.copy()) for b in foam.bubbles]

        # generate inputs and two random orderings
        np.random.seed(seed + 8000)
        inputs = [encode(np.random.randint(0, 256), d) for _ in range(n_inputs)]
        order_a = list(range(n_inputs))
        order_b = list(np.random.permutation(n_inputs))

        # create two foams
        foam_a = Foam(d=d, n=n_bubbles, writing_rate=0.01)
        foam_b = Foam(d=d, n=n_bubbles, writing_rate=0.01)
        for k in range(n_bubbles):
            foam_a.bubbles[k].L = state[k][0].copy()
            foam_a.bubbles[k].T = state[k][1].copy()
            foam_b.bubbles[k].L = state[k][0].copy()
            foam_b.bubbles[k].T = state[k][1].copy()

        # feed in parallel, measuring divergence at each step
        for step in range(n_inputs):
            v_a = inputs[order_a[step]]
            v_b = inputs[order_b[step]]
            alongside(v_a)
            alongside(v_b)
            foam_a.measure(v_a)
            foam_b.measure(v_b)

            vis = ordering_visibility(foam_a, foam_b, probes)
            L_div, T_div = state_divergence(foam_a, foam_b)

            j2_divs_by_step[step].append(vis['j2_divergence'])
            state_divs_by_step[step].append(L_div + T_div)
            j2_rels_by_step[step].append(vis['relative'])

    # report trajectory
    print(f"  {'step':>6s}  {'j2_div':>10s}  {'j2_rel':>12s}  "
          f"{'state_div':>10s}  {'ratio':>10s}")
    print(f"  {'':->6s}  {'':->10s}  {'':->12s}  "
          f"{'':->10s}  {'':->10s}")

    checkpoints = [0, 1, 2, 4, 9, 14, 19, 29, 39, 49]
    for step in checkpoints:
        if step < n_inputs:
            j2d = np.mean(j2_divs_by_step[step])
            j2r = np.mean(j2_rels_by_step[step])
            sd = np.mean(state_divs_by_step[step])
            ratio = j2d / (sd + 1e-12)
            print(f"  {step+1:6d}  {j2d:10.6f}  {j2r:12.8f}  "
                  f"{sd:10.6f}  {ratio:10.4f}")

    # trajectory shape
    early_ratio = np.mean(j2_divs_by_step[0]) / (np.mean(state_divs_by_step[0]) + 1e-12)
    late_ratio = np.mean(j2_divs_by_step[-1]) / (np.mean(state_divs_by_step[-1]) + 1e-12)

    print(f"\n  early ratio (step 1):  {early_ratio:.4f}")
    print(f"  late ratio (step {n_inputs}): {late_ratio:.4f}")
    if late_ratio < early_ratio * 0.8:
        print(f"  → foam HIDES ordering over time (ratio decreases)")
    elif late_ratio > early_ratio * 1.2:
        print(f"  → foam AMPLIFIES ordering over time (ratio increases)")
    else:
        print(f"  → foam EXPOSES ordering proportionally (ratio stable)")

    # does j2_relative saturate?
    early_rel = np.mean(j2_rels_by_step[0])
    late_rel = np.mean(j2_rels_by_step[-1])
    print(f"\n  j2 relative divergence:")
    print(f"    step 1:  {early_rel:.8f}")
    print(f"    step {n_inputs}: {late_rel:.8f}")
    print(f"    growth:  {late_rel / (early_rel + 1e-15):.1f}x")

    return j2_divs_by_step, state_divs_by_step


if __name__ == '__main__':
    single_results = experiment_single_swap()
    accum_results = experiment_accumulating_swaps()
    heirloom_save()
