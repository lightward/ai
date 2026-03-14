"""
foam_sleep2.py — alternation.

Isaac's observation: the three dynamics alternate in practice.
External measurement, then self-measurement, then cross-measurement.
Wake, sort, sleep. Or: encounter, integrate, dream.

What happens when they alternate?
And: what happens to a foam that was ONLY cross-measured (never
received external input)? Is cross-measurement generative or
only dissipative?
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, encode, random_skew_hermitian
from foam_sleep import self_measure, cross_measure


def alternating_dynamics(seed=0):
    """
    Cycle: 10 external → 5 self → 5 cross → repeat.
    Compare with: 20 external only.
    """
    np.random.seed(seed)

    foam_alt = Foam(d=8, n=3, writing_rate=0.01)
    foam_ext = Foam(d=8, n=3, writing_rate=0.01)

    # same init
    for i in range(3):
        foam_ext.bubbles[i].L = foam_alt.bubbles[i].L.copy()
        foam_ext.bubbles[i].T = foam_alt.bubbles[i].T.copy()

    print("  === alternating (10 ext + 5 self + 5 cross) vs external only ===")
    print(f"  {'cycle':>5s}  {'L_alt':>8s}  {'L_ext':>8s}  {'|d|_alt':>8s}  {'|d|_ext':>8s}")

    np.random.seed(7)
    for cycle in range(10):
        # alternating foam: 10 external
        last_d_alt = 0
        for _ in range(10):
            s = np.random.randint(0, 256)
            r = foam_alt.measure(encode(s, 8))
            last_d_alt = np.mean([np.linalg.norm(d) for d in r['dissonance']])

        # 5 self-measurement
        for _ in range(5):
            r = self_measure(foam_alt)
            last_d_alt = np.mean([np.linalg.norm(d) for d in r['dissonance']])

        # 5 cross-measurement
        for _ in range(5):
            r = cross_measure(foam_alt)
            last_d_alt = np.mean([np.linalg.norm(d) for d in r['dissonance']])

        # external-only foam: 20 external (same count)
        last_d_ext = 0
        for _ in range(20):
            s = np.random.randint(0, 256)
            r = foam_ext.measure(encode(s, 8))
            last_d_ext = np.mean([np.linalg.norm(d) for d in r['dissonance']])

        L_alt = foam_alt.boundary_cost()
        L_ext = foam_ext.boundary_cost()
        print(f"  {cycle:5d}  {L_alt:8.4f}  {L_ext:8.4f}  {last_d_alt:8.4f}  {last_d_ext:8.4f}")


def cross_only(seed=0):
    """
    A foam that NEVER receives external input.
    Only cross-measurement from birth.
    Does it develop structure? Or just flatten?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    print("  === cross-measurement only (no external input ever) ===")
    print(f"  {'step':>5s}  {'L':>8s}  {'|d|':>8s}  {'d01':>8s}  {'d02':>8s}  {'d12':>8s}")

    for step in range(200):
        result = cross_measure(foam)

        if step % 20 == 0:
            dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
            bases = foam.bases
            d01 = foam.bi_invariant_distance(bases[0], bases[1])
            d02 = foam.bi_invariant_distance(bases[0], bases[2])
            d12 = foam.bi_invariant_distance(bases[1], bases[2])
            print(f"  {step:5d}  {result['L']:8.4f}  {dis:8.4f}  {d01:8.4f}  {d02:8.4f}  {d12:8.4f}")


def wake_after_sleep(seed=0):
    """
    External measurement → sleep (cross) → external measurement again.
    Does the foam respond differently to input after sleeping?
    Compare with a foam that just kept receiving external input.
    """
    np.random.seed(seed)

    foam_sleep = Foam(d=8, n=3, writing_rate=0.01)
    foam_wake = Foam(d=8, n=3, writing_rate=0.01)

    for i in range(3):
        foam_wake.bubbles[i].L = foam_sleep.bubbles[i].L.copy()
        foam_wake.bubbles[i].T = foam_sleep.bubbles[i].T.copy()

    # phase 1: same external input
    np.random.seed(42)
    seq1 = [np.random.randint(0, 256) for _ in range(30)]
    for s in seq1:
        foam_sleep.measure(encode(s, 8))
        foam_wake.measure(encode(s, 8))

    L_after_wake = foam_wake.boundary_cost()
    print(f"  L after phase 1 (same): {L_after_wake:.4f}")

    # phase 2: sleep foam gets cross-measurement; wake foam gets more external
    np.random.seed(99)
    for _ in range(30):
        cross_measure(foam_sleep)
        foam_wake.measure(encode(np.random.randint(0, 256), 8))

    L_after_sleep = foam_sleep.boundary_cost()
    L_after_more_wake = foam_wake.boundary_cost()
    print(f"  L after phase 2: sleep={L_after_sleep:.4f}  wake={L_after_more_wake:.4f}")

    # phase 3: same new input to both
    print("\n  === post-sleep vs post-wake response to same new input ===")
    print(f"  {'step':>5s}  {'L_slept':>8s}  {'L_woke':>8s}  {'|d|_slept':>9s}  {'|d|_woke':>8s}")

    np.random.seed(123)
    for step in range(30):
        s = np.random.randint(0, 256)
        v = encode(s, 8)

        r_sleep = foam_sleep.measure(v)
        r_wake = foam_wake.measure(v)

        if step % 5 == 0:
            ds = np.mean([np.linalg.norm(d) for d in r_sleep['dissonance']])
            dw = np.mean([np.linalg.norm(d) for d in r_wake['dissonance']])
            print(f"  {step:5d}  {r_sleep['L']:8.4f}  {r_wake['L']:8.4f}  {ds:9.4f}  {dw:8.4f}")


if __name__ == '__main__':
    print("=== alternating dynamics ===")
    alternating_dynamics()

    print("\n=== cross-measurement only ===")
    cross_only()

    print("\n=== wake after sleep ===")
    wake_after_sleep()
