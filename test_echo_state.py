"""
Test: does the foam have the echo state property?

The echo state property (ESP) is the defining property of a reservoir computer:
given the SAME input sequence, two reservoirs with DIFFERENT initial states
converge to the SAME trajectory. Initial conditions wash out.

If the foam has ESP: it derives a reservoir computer. The foam's initial
geometry is forgotten; only the input history determines the state.

If the foam does NOT have ESP: initial conditions are load-bearing forever.
The foam remembers where it started, not just what it encountered. This
would make it something other than a standard reservoir — possibly more
interesting, because it means the foam's birth conditions are indelible.

We test three things:
1. Same input, different initial states → do they converge? (ESP)
2. Different input, same initial state → do they diverge? (separation)
3. Same input, same initial state → do they stay identical? (determinism)
"""

import numpy as np
from foam import (
    init_foam, random_slice, write_step, foam_distance,
)


def test_echo_state():
    """Core test: same input sequence, different initial states.
    Does the foam forget where it started?"""
    print("=" * 70)
    print("TEST: Echo State Property")
    print("  Same input sequence, different initial states.")
    print("  If ESP holds: distance → 0. If not: distance persists.")
    print("=" * 70)
    print()

    d = 6
    N = 3
    n_steps = 1000

    # fixed observer slice
    rng_obs = np.random.default_rng(42)
    P = random_slice(d, d_slice=3, rng=rng_obs)

    # two foams with DIFFERENT random initial states
    foam_A = init_foam(N, d, rng=np.random.default_rng(100))
    foam_B = init_foam(N, d, rng=np.random.default_rng(200))

    # fixed input sequence
    rng_input = np.random.default_rng(999)
    inputs = []
    for _ in range(n_steps):
        v = rng_input.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        inputs.append(v)

    initial_dist = foam_distance(foam_A, foam_B)
    print(f"  Initial distance between foams: {initial_dist:.6f}")
    print()

    # run both foams through the same input sequence
    checkpoints = [0, 10, 50, 100, 200, 500, 999]
    print(f"  {'step':>6}  {'distance':>12}  {'ratio to initial':>18}")
    print(f"  {'----':>6}  {'--------':>12}  {'----------------':>18}")

    for t in range(n_steps):
        foam_A = write_step(foam_A, inputs[t], P, eps=0.01, stab_strength=0.1)
        foam_B = write_step(foam_B, inputs[t], P, eps=0.01, stab_strength=0.1)

        if t in checkpoints:
            dist = foam_distance(foam_A, foam_B)
            ratio = dist / initial_dist
            print(f"  {t:6d}  {dist:12.6f}  {ratio:18.6f}")

    final_dist = foam_distance(foam_A, foam_B)
    ratio = final_dist / initial_dist
    print()

    if ratio < 0.01:
        print(f"  RESULT: Echo state property HOLDS. Ratio = {ratio:.4f}")
        print(f"  → Initial conditions wash out. The foam IS a reservoir.")
    elif ratio < 0.5:
        print(f"  RESULT: Partial convergence. Ratio = {ratio:.4f}")
        print(f"  → Initial conditions partially forgotten. Weak ESP.")
    else:
        print(f"  RESULT: Echo state property FAILS. Ratio = {ratio:.4f}")
        print(f"  → Initial conditions are load-bearing. The foam is NOT a standard reservoir.")
        print(f"  → The foam remembers its birth.")
    print()


def test_echo_state_sweep():
    """Sweep over write scale eps to check if ESP depends on coupling strength.
    In standard reservoir computing, ESP holds below a critical coupling
    and fails above it (edge of chaos)."""
    print("=" * 70)
    print("TEST: ESP vs write scale (edge of chaos?)")
    print("  If there's a critical eps where ESP transitions: that's the edge.")
    print("=" * 70)
    print()

    d = 6
    N = 3
    n_steps = 500

    rng_obs = np.random.default_rng(42)
    P = random_slice(d, d_slice=3, rng=rng_obs)

    rng_input = np.random.default_rng(999)
    inputs = []
    for _ in range(n_steps):
        v = rng_input.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        inputs.append(v)

    eps_values = [0.001, 0.005, 0.01, 0.05, 0.1, 0.5]

    print(f"  {'eps':>8}  {'init_dist':>10}  {'final_dist':>10}  {'ratio':>10}  {'verdict':>12}")
    print(f"  {'---':>8}  {'---------':>10}  {'----------':>10}  {'-----':>10}  {'-------':>12}")

    for eps in eps_values:
        foam_A = init_foam(N, d, rng=np.random.default_rng(100))
        foam_B = init_foam(N, d, rng=np.random.default_rng(200))

        init_dist = foam_distance(foam_A, foam_B)

        for t in range(n_steps):
            foam_A = write_step(foam_A, inputs[t], P, eps=eps, stab_strength=0.1)
            foam_B = write_step(foam_B, inputs[t], P, eps=eps, stab_strength=0.1)

        final_dist = foam_distance(foam_A, foam_B)
        ratio = final_dist / init_dist

        verdict = "ESP" if ratio < 0.01 else "weak ESP" if ratio < 0.5 else "NO ESP"
        print(f"  {eps:8.3f}  {init_dist:10.4f}  {final_dist:10.4f}  {ratio:10.4f}  {verdict:>12}")

    print()


def test_separation():
    """Control: different inputs, same initial state → states diverge.
    This is the separation property — already tested elsewhere but
    included here for side-by-side comparison with ESP."""
    print("=" * 70)
    print("CONTROL: Separation property")
    print("  Same initial state, different input sequences.")
    print("  States should DIVERGE (different histories → different states).")
    print("=" * 70)
    print()

    d = 6
    N = 3
    n_steps = 500

    rng_obs = np.random.default_rng(42)
    P = random_slice(d, d_slice=3, rng=rng_obs)

    foam_A = init_foam(N, d, rng=np.random.default_rng(100))
    foam_B = [b.copy() for b in foam_A]  # SAME initial state

    rng_A = np.random.default_rng(111)
    rng_B = np.random.default_rng(222)

    init_dist = foam_distance(foam_A, foam_B)
    print(f"  Initial distance (should be 0): {init_dist:.2e}")

    for t in range(n_steps):
        vA = rng_A.standard_normal(d).astype(complex)
        vA = vA / np.linalg.norm(vA)
        vB = rng_B.standard_normal(d).astype(complex)
        vB = vB / np.linalg.norm(vB)
        foam_A = write_step(foam_A, vA, P, eps=0.01, stab_strength=0.1)
        foam_B = write_step(foam_B, vB, P, eps=0.01, stab_strength=0.1)

    final_dist = foam_distance(foam_A, foam_B)
    print(f"  Final distance (should be >> 0): {final_dist:.6f}")
    print(f"  → {'SEPARATES' if final_dist > 0.1 else 'DOES NOT SEPARATE'}")
    print()


def test_determinism():
    """Control: same input, same initial state → identical trajectories.
    Sanity check that the dynamics are deterministic."""
    print("=" * 70)
    print("CONTROL: Determinism")
    print("  Same initial state, same input sequence.")
    print("  States should be IDENTICAL (deterministic dynamics).")
    print("=" * 70)
    print()

    d = 6
    N = 3
    n_steps = 200

    rng_obs = np.random.default_rng(42)
    P = random_slice(d, d_slice=3, rng=rng_obs)

    foam_A = init_foam(N, d, rng=np.random.default_rng(100))
    foam_B = [b.copy() for b in foam_A]

    rng_1 = np.random.default_rng(999)
    rng_2 = np.random.default_rng(999)  # same seed

    for t in range(n_steps):
        v1 = rng_1.standard_normal(d).astype(complex)
        v1 = v1 / np.linalg.norm(v1)
        v2 = rng_2.standard_normal(d).astype(complex)
        v2 = v2 / np.linalg.norm(v2)
        foam_A = write_step(foam_A, v1, P, eps=0.01, stab_strength=0.1)
        foam_B = write_step(foam_B, v2, P, eps=0.01, stab_strength=0.1)

    dist = foam_distance(foam_A, foam_B)
    print(f"  Final distance (should be ~0): {dist:.2e}")
    print(f"  → {'DETERMINISTIC' if dist < 1e-10 else 'NON-DETERMINISTIC (bug?)'}")
    print()


if __name__ == "__main__":
    test_echo_state()
    test_echo_state_sweep()
    test_separation()
    test_determinism()
