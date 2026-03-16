"""
galois_recursive_cross.py — cross-tests for the recursive adjunction finding.

1. Is the noise-ratio inversion robust? (more seeds, different params)
2. Does partial contact (intermittent shared measurement) produce
   intermediate results between "fully independent" and "co-stabilized"?
"""

import numpy as np
from foam import Foam, encode
from foam_recursive import RecursiveFoam
from heirloom import alongside, save as heirloom_save


def parent_j2_noise(rf, n_steps=100, check_interval=5, seed_offset=5000):
    """Measure parent j2 jump magnitude over time."""
    d = rf.d
    n_checks = n_steps // check_interval
    jumps = np.zeros(n_checks)
    prev_j2 = None

    np.random.seed(seed_offset)
    for step in range(n_steps):
        v = encode(np.random.randint(0, 256), d)
        alongside(v)
        rf.measure(v)

        if (step + 1) % check_interval == 0:
            idx = step // check_interval
            probe = encode(42, d).astype(complex)
            bases = rf.bases
            m = [probe @ U for U in bases]
            j2 = rf._stabilize(m)
            j2_flat = np.concatenate([np.array(j2[i]) for i in range(3)])

            if prev_j2 is not None:
                jumps[idx] = np.linalg.norm(j2_flat - prev_j2)
            prev_j2 = j2_flat

    return jumps


def test_inversion_robustness(n_seeds=30, n_steps=150):
    """Test 1: Is the noise-ratio inversion robust across more seeds
    and a longer time horizon?"""
    d = 8
    check_interval = 5
    n_checks = n_steps // check_interval

    stable_noise = np.zeros(n_checks)
    unstable_noise = np.zeros(n_checks)

    for seed in range(n_seeds):
        for label, n_inner in [('stable', 200), ('unstable', 0)]:
            np.random.seed(seed)
            rf = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

            if n_inner > 0:
                for sf in rf.sub_foams:
                    for _ in range(n_inner):
                        v = encode(np.random.randint(0, 256), d)
                        alongside(v)
                        sf.measure(v)

            jumps = parent_j2_noise(rf, n_steps=n_steps,
                                    check_interval=check_interval,
                                    seed_offset=seed + 5000)
            if label == 'stable':
                stable_noise += jumps
            else:
                unstable_noise += jumps

    stable_noise /= n_seeds
    unstable_noise /= n_seeds

    print(f"=== test 1: noise-ratio inversion robustness ({n_seeds} seeds, {n_steps} steps) ===\n")
    print(f"  {'step':>5s}  {'stable':>10s}  {'unstable':>10s}  {'ratio':>8s}")
    for idx in range(1, n_checks):
        step = (idx + 1) * check_interval
        ratio = unstable_noise[idx] / (stable_noise[idx] + 1e-15)
        marker = " ←" if abs(ratio - 1.0) < 0.02 else ""
        print(f"  {step:5d}  {stable_noise[idx]:10.6f}  {unstable_noise[idx]:10.6f}  {ratio:8.4f}{marker}")

    # find crossover point
    for idx in range(1, n_checks):
        if unstable_noise[idx] < stable_noise[idx]:
            step = (idx + 1) * check_interval
            print(f"\n  crossover at step ~{step}: unstable becomes LESS noisy than stable")
            break
    else:
        print(f"\n  no crossover found in {n_steps} steps")


def test_partial_contact(n_seeds=20, n_steps=100):
    """Test 2: Does intermittent shared measurement produce intermediate results?

    Four conditions:
    - fully_independent: sub-foams get 200 independent writes, no parent contact
    - quarter_contact: 150 independent + 50 shared with parent
    - half_contact: 100 independent + 100 shared with parent
    - co_stabilized: 0 independent, sub-foams only see parent's measurement stream
    - fresh: no pre-stabilization at all
    """
    d = 8
    check_interval = 5
    n_checks = n_steps // check_interval

    conditions = {
        'fully_independent': {'noise': np.zeros(n_checks), 'inner_steps': 200, 'shared_steps': 0},
        'quarter_contact': {'noise': np.zeros(n_checks), 'inner_steps': 150, 'shared_steps': 50},
        'half_contact': {'noise': np.zeros(n_checks), 'inner_steps': 100, 'shared_steps': 100},
        'co_stabilized': {'noise': np.zeros(n_checks), 'inner_steps': 0, 'shared_steps': 200},
        'fresh': {'noise': np.zeros(n_checks), 'inner_steps': 0, 'shared_steps': 0},
    }

    for seed in range(n_seeds):
        for cond_name, cond in conditions.items():
            np.random.seed(seed)
            rf = RecursiveFoam(d=d, n=3, sub_n=3, writing_rate=0.01)

            # independent stabilization (sub-foams only, no parent)
            if cond['inner_steps'] > 0:
                for sf in rf.sub_foams:
                    np.random.seed(seed + id(sf) % 10000)
                    for _ in range(cond['inner_steps']):
                        v = encode(np.random.randint(0, 256), d)
                        alongside(v)
                        sf.measure(v)

            # shared stabilization (full recursive measurement)
            if cond['shared_steps'] > 0:
                np.random.seed(seed + 3000)
                for _ in range(cond['shared_steps']):
                    v = encode(np.random.randint(0, 256), d)
                    alongside(v)
                    rf.measure(v)

            # now measure parent noise
            jumps = parent_j2_noise(rf, n_steps=n_steps,
                                    check_interval=check_interval,
                                    seed_offset=seed + 7000)
            cond['noise'] += jumps

    for cond in conditions.values():
        cond['noise'] /= n_seeds

    print(f"\n=== test 2: partial contact ({n_seeds} seeds, {n_steps} steps) ===\n")
    print(f"  {'step':>5s}", end="")
    for name in conditions:
        print(f"  {name:>18s}", end="")
    print()

    for idx in range(1, n_checks):
        step = (idx + 1) * check_interval
        print(f"  {step:5d}", end="")
        for name, cond in conditions.items():
            print(f"  {cond['noise'][idx]:18.6f}", end="")
        print()

    # summary: average noise over last 10 checkpoints
    print(f"\n  average noise (last {10 * check_interval} steps):")
    for name, cond in conditions.items():
        avg = np.mean(cond['noise'][-10:])
        print(f"    {name:>20s}: {avg:.6f}")


if __name__ == '__main__':
    test_inversion_robustness()
    test_partial_contact()
    heirloom_save()
