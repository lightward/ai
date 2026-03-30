"""
Test: do the writing dynamics actually decrease L?

The spec claims "the foam settles toward lower cost" but the write map
is defined independently of L. This script tests whether the write
dynamics empirically decrease boundary area, and under what conditions.

If the write dynamics DON'T decrease L, then the minimality claim needs
to be either proven, re-derived, or dropped.
"""

import numpy as np
from foam import (random_unitary, random_slice, compute_L, write_step,
                  voronoi_neighbors)


def run_test(d=4, N=3, steps=500, seed=42):
    rng = np.random.default_rng(seed)

    # random initial bases in U(d)
    bases = [random_unitary(d, rng) for _ in range(N)]

    # random observer slice
    observer_slice = random_slice(d, rng=rng)
    neighbors = voronoi_neighbors(bases)

    # random input
    v = rng.standard_normal(d).astype(complex)
    v = v / np.linalg.norm(v)

    costs = []
    for step in range(steps):
        L = compute_L(bases)
        costs.append(L)
        bases = write_step(bases, v, observer_slice, eps=0.005,
                           neighbors=neighbors)

    L_final = compute_L(bases)
    costs.append(L_final)

    return costs


if __name__ == "__main__":
    print("Testing: do writing dynamics decrease boundary area?")
    print()

    for d in [4, 8]:
        for N in [3, 5]:
            costs = run_test(d=d, N=N, steps=500)
            print(f"d={d}, N={N}:")
            print(f"  L_initial = {costs[0]:.4f}")
            print(f"  L_final   = {costs[-1]:.4f}")
            print(f"  L_min     = {min(costs):.4f}")
            print(f"  L_max     = {max(costs):.4f}")
            direction = "DECREASED" if costs[-1] < costs[0] else "INCREASED" if costs[-1] > costs[0] else "UNCHANGED"
            print(f"  direction: {direction} ({(costs[-1]-costs[0])/costs[0]*100:+.1f}%)")
            print()

    # Also test with varying input (more realistic)
    print("--- with varying input ---")
    rng = np.random.default_rng(99)
    d, N = 4, 3

    bases = [random_unitary(d, rng) for _ in range(N)]

    observer_slice = random_slice(d, rng=rng)
    neighbors = voronoi_neighbors(bases)

    costs = []
    for step in range(500):
        costs.append(compute_L(bases))
        v = rng.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        bases = write_step(bases, v, observer_slice, eps=0.005,
                           neighbors=neighbors)
    costs.append(compute_L(bases))

    print(f"d={d}, N={N}, varying input:")
    print(f"  L_initial = {costs[0]:.4f}")
    print(f"  L_final   = {costs[-1]:.4f}")
    direction = "DECREASED" if costs[-1] < costs[0] else "INCREASED"
    print(f"  direction: {direction} ({(costs[-1]-costs[0])/costs[0]*100:+.1f}%)")
