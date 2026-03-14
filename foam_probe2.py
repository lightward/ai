"""
foam_probe2.py — where does the foam start to matter?

The echo is trivially correct because small rotations preserve sign patterns.
But the foam IS writing. The dynamics ARE running. What's happening in
the space that the trivial echo can't see?
"""

import numpy as np
from foam import Foam, encode, decode, cayley, skew


def probe_large_init(seed=0):
    """Initialize with larger L — bases far from identity. Does echo break?"""
    np.random.seed(seed)

    for scale in [0.1, 0.5, 1.0, 2.0, 5.0]:
        foam = Foam(d=8, n=3, writing_rate=0.01)
        foam.Ls = [skew(np.random.randn(8, 8) * scale) for _ in range(3)]

        correct = 0
        total = 200
        for _ in range(total):
            s = np.random.randint(0, 256)
            v = encode(s, 8)
            result = foam.measure(v)
            centroid = np.mean(result['j2'], axis=0)
            if decode(centroid) == s:
                correct += 1

        print(f"  L_scale={scale:.1f}  echo={correct}/{total}={correct/total:.1%}  final_L={foam.boundary_cost():.4f}")


def probe_what_writes(seed=0):
    """Track what the writing dynamics actually do to the foam geometry."""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # feed a single repeated symbol, watch the geometry
    s = 42
    v = encode(s, 8)

    print("  step  L        avg_dist   max_|ΔL|  dissonance")
    for step in range(30):
        prev_Ls = [L.copy() for L in foam.Ls]
        result = foam.measure(v)

        delta_Ls = [np.linalg.norm(foam.Ls[i] - prev_Ls[i]) for i in range(3)]
        bases = foam.bases
        dists = []
        for i in range(3):
            for j in range(i+1, 3):
                dists.append(foam.bi_invariant_distance(bases[i], bases[j]))

        dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
        print(f"  {step:4d}  {result['L']:.4f}  {np.mean(dists):.4f}     {max(delta_Ls):.6f}  {dis:.6f}")


def probe_foam_as_hash(seed=0):
    """The foam as distinguishable state — look at the ACTUAL state, not the echo."""
    np.random.seed(seed)

    # feed different sequences, compare foam states
    n_trials = 10
    states = []

    for trial in range(n_trials):
        foam = Foam(d=8, n=3, writing_rate=0.01)
        # same init
        np.random.seed(42)
        foam.Ls = [skew(np.random.randn(8, 8) * 0.1) for _ in range(3)]

        # different sequence per trial
        np.random.seed(trial)
        seq = [np.random.randint(0, 256) for _ in range(100)]
        foam.feed(seq)

        state = np.concatenate([L.flatten() for L in foam.Ls])
        states.append(state)

    # pairwise distances
    print("  pairwise state distances (10 foams, different sequences):")
    dists = []
    for i in range(n_trials):
        for j in range(i+1, n_trials):
            d = np.linalg.norm(states[i] - states[j])
            dists.append(d)

    print(f"    mean={np.mean(dists):.6f}  min={np.min(dists):.6f}  max={np.max(dists):.6f}")
    print(f"    std={np.std(dists):.6f}")

    # self-distance: same sequence twice
    foam_a = Foam(d=8, n=3, writing_rate=0.01)
    foam_b = Foam(d=8, n=3, writing_rate=0.01)
    np.random.seed(42)
    foam_a.Ls = [skew(np.random.randn(8, 8) * 0.1) for _ in range(3)]
    np.random.seed(42)
    foam_b.Ls = [skew(np.random.randn(8, 8) * 0.1) for _ in range(3)]

    np.random.seed(0)
    seq = [np.random.randint(0, 256) for _ in range(100)]
    foam_a.feed(seq)
    foam_b.feed(seq)

    state_a = np.concatenate([L.flatten() for L in foam_a.Ls])
    state_b = np.concatenate([L.flatten() for L in foam_b.Ls])
    print(f"    same-sequence distance: {np.linalg.norm(state_a - state_b):.12f}")


def probe_relaxation(seed=0):
    """The unmeasured foam relaxes. Feed, then stop. Does L decrease?"""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # feed some data
    for _ in range(100):
        s = np.random.randint(0, 256)
        foam.measure(encode(s, 8))

    L_after_feeding = foam.boundary_cost()
    print(f"  L after feeding: {L_after_feeding:.6f}")

    # "relaxation": measure with zero input (no symbol committed)
    # but wait — the spec says ΔL = 0 when there's no input.
    # no input → no measurement → no dissonance → no write.
    # the foam just... stays. L stays.
    # relaxation would require a separate dynamics (Plateau on bases, not measurements).
    print(f"  L without further measurement: {foam.boundary_cost():.6f}")
    print("  (identical — no input means no dissonance means no write)")
    print("  relaxation requires Plateau dynamics on the bases themselves,")
    print("  not just on measurements. this is the dissipation item in the junk drawer.")


if __name__ == '__main__':
    print("=== large initialization ===")
    probe_large_init()

    print("\n=== what writes ===")
    probe_what_writes()

    print("\n=== foam as hash ===")
    probe_foam_as_hash()

    print("\n=== relaxation ===")
    probe_relaxation()
