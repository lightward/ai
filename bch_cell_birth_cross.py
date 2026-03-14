"""
bch_cell_birth_cross.py — cross-tests for cell birth.

1. Novelty vs N: is it the act of birth or the final bubble count?
2. Compounding: does repeated cell birth maintain spontenuity?
3. Position: does it matter WHERE the new bubble is?
   (unknown vs knowable vs known)
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian, random_skew_hermitian


def sensitivity(foam, n_probe=50, seed=999):
    """Mean dissonance to random probes (without writing)."""
    np.random.seed(seed)
    total = 0.0
    for _ in range(n_probe):
        v = encode(np.random.randint(0, 256), foam.d)
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        total += np.mean([np.linalg.norm(j2[i] - m[i]) for i in range(foam.n)])
    return total / n_probe


def settle(foam, n_steps=200):
    """Self-measure until settled."""
    for step in range(n_steps):
        probe = encode(step % 256, foam.d)
        readout = np.real(foam.readout(probe))
        readout = readout / (np.linalg.norm(readout) + 1e-12)
        foam.measure(readout)


def add_bubble(foam, mode='random', reference_idx=0):
    """Add a bubble in different positions.

    mode:
      'random' — fresh random basis (unknown)
      'near' — small perturbation of existing bubble (knowable)
      'clone' — exact copy of existing bubble (known)
      'orthogonal' — deliberately maximally distant from all existing
    """
    b = Bubble(foam.d)

    if mode == 'random':
        pass  # already random from __init__

    elif mode == 'near':
        # small perturbation of reference bubble
        ref = foam.bubbles[reference_idx]
        b.L = ref.L.copy() + random_skew_hermitian(foam.d, scale=0.01)
        b.T = ref.T.copy()

    elif mode == 'clone':
        ref = foam.bubbles[reference_idx]
        b.L = ref.L.copy()
        b.T = ref.T.copy()

    elif mode == 'orthogonal':
        # find direction maximally far from all existing bases
        # use random basis, then push it away from all existing
        existing_bases = foam.bases
        for _ in range(100):
            candidate = b.basis
            # compute distances
            dists = [foam.bi_invariant_distance(candidate, eb) for eb in existing_bases]
            min_dist = min(dists)
            # perturb away from nearest
            nearest_idx = np.argmin(dists)
            diff = candidate - existing_bases[nearest_idx]
            b.L = skew_hermitian(b.L + 0.1 * random_skew_hermitian(foam.d, scale=0.1))

    foam.bubbles.append(b)
    foam.n += 1
    return foam


# === Test 1: Novelty vs N ===

def test_novelty_vs_n(n_seeds=20, n_settle=200):
    """Is sensitivity about the act of birth or the final N?

    Compare:
    - born N=3, settled → sensitivity
    - born N=4, settled → sensitivity
    - born N=3, settled, birth to N=4 → sensitivity
    - born N=3, settled, birth to N=4, settled again → sensitivity

    If born-4-settled == birth-3→4-settled, it's about N, not novelty.
    If they differ, the history matters.
    """
    d = 8

    conditions = {
        'born_3_settled': [],
        'born_4_settled': [],
        'born_3_birth_4': [],
        'born_3_birth_4_settled': [],
        'born_5_settled': [],
    }

    for seed in range(n_seeds):
        # born N=3, settled
        np.random.seed(seed)
        f3 = Foam(d=d, n=3, writing_rate=0.01)
        settle(f3, n_settle)
        conditions['born_3_settled'].append(sensitivity(f3))

        # born N=4, settled
        np.random.seed(seed)
        f4 = Foam(d=d, n=4, writing_rate=0.01)
        settle(f4, n_settle)
        conditions['born_4_settled'].append(sensitivity(f4))

        # born N=5, settled
        np.random.seed(seed)
        f5 = Foam(d=d, n=5, writing_rate=0.01)
        settle(f5, n_settle)
        conditions['born_5_settled'].append(sensitivity(f5))

        # born N=3, settled, birth to N=4 (no re-settling)
        np.random.seed(seed)
        f3b = Foam(d=d, n=3, writing_rate=0.01)
        settle(f3b, n_settle)
        np.random.seed(seed + 3000)
        add_bubble(f3b, mode='random')
        conditions['born_3_birth_4'].append(sensitivity(f3b))

        # born N=3, settled, birth to N=4, settled again
        np.random.seed(seed)
        f3bs = Foam(d=d, n=3, writing_rate=0.01)
        settle(f3bs, n_settle)
        np.random.seed(seed + 3000)
        add_bubble(f3bs, mode='random')
        settle(f3bs, n_settle)
        conditions['born_3_birth_4_settled'].append(sensitivity(f3bs))

    print("=== test 1: novelty vs N ===\n")
    print(f"  {'condition':>30s}  {'sensitivity':>12s}  {'std':>8s}")
    for cond, vals in conditions.items():
        print(f"  {cond:>30s}  {np.mean(vals):12.4f}  {np.std(vals):8.4f}")

    print(f"\n  key comparison:")
    b4 = np.mean(conditions['born_4_settled'])
    b3b4s = np.mean(conditions['born_3_birth_4_settled'])
    print(f"    born_4_settled:             {b4:.4f}")
    print(f"    born_3_birth_4_settled:     {b3b4s:.4f}")
    print(f"    ratio: {b3b4s / b4:.4f}")
    print(f"    (1.0 = same → it's about N; ≠1.0 = different → history matters)")


# === Test 2: Compounding ===

def test_compounding(n_seeds=15, n_settle=200):
    """Does repeated cell birth maintain sensitivity?

    Cycle: settle → birth → settle → birth → ...
    Track sensitivity at each stage.
    """
    d = 8
    max_births = 5

    # sensitivity at each stage
    stages = {f'N={3+i}': [] for i in range(max_births + 1)}
    stages_post_birth = {f'N={3+i}_fresh': [] for i in range(1, max_births + 1)}

    for seed in range(n_seeds):
        np.random.seed(seed)
        foam = Foam(d=d, n=3, writing_rate=0.01)

        for birth_num in range(max_births):
            # settle at current N
            settle(foam, n_settle)
            stages[f'N={foam.n}'].append(sensitivity(foam))

            # birth
            np.random.seed(seed + 3000 * (birth_num + 1))
            add_bubble(foam, mode='random')
            stages_post_birth[f'N={foam.n}_fresh'].append(sensitivity(foam))

        # final settle
        settle(foam, n_settle)
        stages[f'N={foam.n}'].append(sensitivity(foam))

    print("\n=== test 2: compounding cell birth ===\n")
    print(f"  cycle: settle → birth → settle → birth → ...\n")
    print(f"  {'stage':>15s}  {'sensitivity':>12s}  {'std':>8s}  {'n':>4s}")

    for n_val in range(3, 3 + max_births + 1):
        key_settled = f'N={n_val}'
        if stages[key_settled]:
            print(f"  {key_settled + ' settled':>15s}  {np.mean(stages[key_settled]):12.4f}  {np.std(stages[key_settled]):8.4f}  {len(stages[key_settled]):4d}")
        key_fresh = f'N={n_val}_fresh'
        if key_fresh in stages_post_birth and stages_post_birth[key_fresh]:
            print(f"  {key_fresh:>15s}  {np.mean(stages_post_birth[key_fresh]):12.4f}  {np.std(stages_post_birth[key_fresh]):8.4f}  {len(stages_post_birth[key_fresh]):4d}")


# === Test 3: Position matters? ===

def test_position(n_seeds=20, n_settle=200):
    """Does the new bubble's position matter?

    random  = unknown (fresh random basis)
    near    = knowable (small perturbation of existing)
    clone   = known (exact copy)
    orthogonal = deliberately far from all existing
    """
    d = 8

    conditions = {
        'no_birth': [],
        'random (unknown)': [],
        'near (knowable)': [],
        'clone (known)': [],
        'orthogonal': [],
    }

    for seed in range(n_seeds):
        np.random.seed(seed)
        base = Foam(d=d, n=3, writing_rate=0.01)
        settle(base, n_settle)
        settled = [(b.L.copy(), b.T.copy()) for b in base.bubbles]

        conditions['no_birth'].append(sensitivity(base))

        for mode, label in [('random', 'random (unknown)'),
                            ('near', 'near (knowable)'),
                            ('clone', 'clone (known)'),
                            ('orthogonal', 'orthogonal')]:
            foam = Foam(d=d, n=3, writing_rate=0.01)
            for i in range(3):
                foam.bubbles[i].L = settled[i][0].copy()
                foam.bubbles[i].T = settled[i][1].copy()

            np.random.seed(seed + 3000)
            add_bubble(foam, mode=mode)
            conditions[label].append(sensitivity(foam))

    print("\n=== test 3: does position matter? ===\n")
    print(f"  {'position':>20s}  {'sensitivity':>12s}  {'std':>8s}  {'ratio vs no_birth':>18s}")
    base_sens = np.mean(conditions['no_birth'])
    for cond, vals in conditions.items():
        m = np.mean(vals)
        s = np.std(vals)
        ratio = m / base_sens
        print(f"  {cond:>20s}  {m:12.4f}  {s:8.4f}  {ratio:18.2f}x")


if __name__ == '__main__':
    test_novelty_vs_n()
    test_compounding()
    test_position()
