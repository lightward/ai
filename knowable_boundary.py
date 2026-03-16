"""
knowable_boundary.py — where does the knowable live?

Cell birth at the "knowable" position (near-perturbation, scale=0.01)
produced 2.8x sensitivity increase vs 1.9x for random (session 10).
But what's the optimal perturbation scale?

At scale=0: clone (deadlocks, 0.67x)
At scale→∞: effectively random (1.9x)
Somewhere in between: the peak

The peak is where the new bubble creates maximum dissonance that the
adjunction can see — close enough that j2 can't easily separate it
from an existing bubble, forcing fine-grained Plateau reorganization.

The knowable boundary is the adjunction gap's sweet spot.
"""

import numpy as np
from foam import Foam, Bubble, encode, skew_hermitian, random_skew_hermitian
from heirloom import alongside, save as heirloom_save


def sensitivity(foam, n_probe=50, seed=999):
    """Mean dissonance to random probes (without writing)."""
    np.random.seed(seed)
    total = 0.0
    for _ in range(n_probe):
        v = encode(np.random.randint(0, 256), foam.d)
        alongside(v)
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        total += np.mean([np.linalg.norm(j2[i] - m[i]) for i in range(foam.n)])
    return total / n_probe


def add_bubble_at_scale(foam, scale, reference_idx=0):
    """Add a bubble at a specific perturbation scale from an existing bubble."""
    b = Bubble(foam.d)
    ref = foam.bubbles[reference_idx]
    b.L = ref.L.copy() + random_skew_hermitian(foam.d, scale=scale)
    b.T = ref.T.copy()
    foam.bubbles.append(b)
    foam.n += 1
    return foam


def sweep_scale(n_seeds=20, n_settle=200):
    """Sweep perturbation scale and measure sensitivity after cell birth."""
    d = 8
    scales = [0.0, 0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1.0, 3.0, 10.0]

    results = {s: [] for s in scales}
    baseline_sens = []

    for seed in range(n_seeds):
        # settle a foam
        np.random.seed(seed)
        base_foam = Foam(d=d, n=3, writing_rate=0.01)
        for step in range(n_settle):
            v = encode(step % 256, d)
            alongside(v)
            readout = np.real(base_foam.readout(v))
            readout = readout / (np.linalg.norm(readout) + 1e-12)
            base_foam.measure(readout)

        settled = [(b.L.copy(), b.T.copy()) for b in base_foam.bubbles]
        baseline_sens.append(sensitivity(base_foam))

        for scale in scales:
            foam = Foam(d=d, n=3, writing_rate=0.01)
            for i in range(3):
                foam.bubbles[i].L = settled[i][0].copy()
                foam.bubbles[i].T = settled[i][1].copy()

            np.random.seed(seed + 3000)
            add_bubble_at_scale(foam, scale)
            results[scale].append(sensitivity(foam))

    print("=== knowable boundary sweep ===\n")
    print(f"  {n_seeds} seeds, {n_settle} self-measurement steps to settle\n")
    base = np.mean(baseline_sens)
    print(f"  baseline (no birth): {base:.4f}\n")
    print(f"  {'scale':>10s}  {'sensitivity':>12s}  {'ratio':>8s}  {'std':>8s}")
    for scale in scales:
        m = np.mean(results[scale])
        s = np.std(results[scale])
        ratio = m / base
        print(f"  {scale:10.3f}  {m:12.4f}  {ratio:8.2f}x  {s:8.4f}")

    # find the peak
    means = [np.mean(results[s]) for s in scales]
    peak_idx = np.argmax(means)
    print(f"\n  peak at scale={scales[peak_idx]:.3f} ({means[peak_idx]/base:.2f}x)")


def fine_sweep(n_seeds=20, n_settle=200):
    """Fine-grained sweep around the peak identified in sweep_scale."""
    d = 8
    # based on coarse sweep, the peak should be near scale=0.01-0.03
    scales = [0.003, 0.005, 0.007, 0.01, 0.015, 0.02, 0.03, 0.05, 0.07, 0.1]

    results = {s: [] for s in scales}
    baseline_sens = []

    for seed in range(n_seeds):
        np.random.seed(seed)
        base_foam = Foam(d=d, n=3, writing_rate=0.01)
        for step in range(n_settle):
            v = encode(step % 256, d)
            alongside(v)
            readout = np.real(base_foam.readout(v))
            readout = readout / (np.linalg.norm(readout) + 1e-12)
            base_foam.measure(readout)

        settled = [(b.L.copy(), b.T.copy()) for b in base_foam.bubbles]
        baseline_sens.append(sensitivity(base_foam))

        for scale in scales:
            foam = Foam(d=d, n=3, writing_rate=0.01)
            for i in range(3):
                foam.bubbles[i].L = settled[i][0].copy()
                foam.bubbles[i].T = settled[i][1].copy()

            np.random.seed(seed + 3000)
            add_bubble_at_scale(foam, scale)
            results[scale].append(sensitivity(foam))

    print("\n=== fine sweep around peak ===\n")
    base = np.mean(baseline_sens)
    print(f"  {'scale':>10s}  {'sensitivity':>12s}  {'ratio':>8s}  {'std':>8s}")
    for scale in scales:
        m = np.mean(results[scale])
        s = np.std(results[scale])
        ratio = m / base
        print(f"  {scale:10.4f}  {m:12.4f}  {ratio:8.2f}x  {s:8.4f}")

    means = [np.mean(results[s]) for s in scales]
    peak_idx = np.argmax(means)
    print(f"\n  peak at scale={scales[peak_idx]:.4f} ({means[peak_idx]/base:.2f}x)")


def characterize_peak(n_seeds=20, n_settle=200):
    """At the peak scale, what does the dissonance look like?

    Compare: the new bubble's distance to the reference bubble
    vs to the other bubbles. At the peak, the new bubble should be
    close enough to the reference to force Plateau reorganization
    but far enough to not be absorbed.
    """
    d = 8
    # use peak from coarse sweep
    peak_scale = 0.01  # will adjust if sweep says otherwise

    distances_to_ref = []
    distances_to_others = []
    inter_bubble_dists = []

    for seed in range(n_seeds):
        np.random.seed(seed)
        foam = Foam(d=d, n=3, writing_rate=0.01)
        for step in range(n_settle):
            v = encode(step % 256, d)
            alongside(v)
            readout = np.real(foam.readout(v))
            readout = readout / (np.linalg.norm(readout) + 1e-12)
            foam.measure(readout)

        # measure inter-bubble distances before birth
        bases = foam.bases
        for i in range(3):
            for j in range(i+1, 3):
                inter_bubble_dists.append(foam.bi_invariant_distance(bases[i], bases[j]))

        np.random.seed(seed + 3000)
        add_bubble_at_scale(foam, peak_scale, reference_idx=0)

        # distances from new bubble to all others
        new_basis = foam.bubbles[3].basis
        d_ref = foam.bi_invariant_distance(new_basis, foam.bubbles[0].basis)
        d_others = [foam.bi_invariant_distance(new_basis, foam.bubbles[i].basis)
                    for i in range(1, 3)]

        distances_to_ref.append(d_ref)
        distances_to_others.extend(d_others)

    mean_inter = np.mean(inter_bubble_dists)
    mean_to_ref = np.mean(distances_to_ref)
    mean_to_others = np.mean(distances_to_others)

    print(f"\n=== geometry at the peak (scale={peak_scale}) ===\n")
    print(f"  inter-bubble distance (settled): {mean_inter:.4f}")
    print(f"  new → reference bubble:          {mean_to_ref:.4f}  ({mean_to_ref/mean_inter:.2f}x inter-bubble)")
    print(f"  new → other bubbles:             {mean_to_others:.4f}  ({mean_to_others/mean_inter:.2f}x inter-bubble)")
    print(f"\n  (the knowable boundary is at ~{mean_to_ref/mean_inter:.0%} of the inter-bubble distance)")


if __name__ == '__main__':
    sweep_scale()
    fine_sweep()
    characterize_peak()
    heirloom_save()
