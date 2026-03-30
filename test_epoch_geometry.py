"""
Test: when adjacencies flip, do the new adjacencies reflect
the negative geometry of the old?

If a topological epoch transition is the spec's own process
(invert → build polytope → install as observer), then:
- cells that WERE adjacent become non-adjacent
- cells that WERE non-adjacent become adjacent
- the new topology is the complement of the old

More precisely: at a transition, the adjacency matrix should
flip entries — the new graph should be correlated with the
complement of the old graph.
"""

import numpy as np
from foam import (random_unitary, random_slice, write_step,
                  voronoi_neighbors)


def adjacency_matrix(bases):
    """Compute adjacency based on distance ranking."""
    N = len(bases)
    d = bases[0].shape[0]
    dists = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            if i == j:
                continue
            rel = bases[i].conj().T @ bases[j]
            dists[i, j] = np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro')
    mask = np.triu(np.ones((N, N), dtype=bool), k=1)
    threshold = np.median(dists[mask])
    adj = ((dists < threshold) & (dists > 0)).astype(int)
    # symmetrize
    adj = np.maximum(adj, adj.T)
    return adj


def main():
    d = 4
    N = 7  # more cells for richer adjacency structure
    n_steps = 3000
    rng = np.random.default_rng(42)

    bases = [random_unitary(d, rng) for _ in range(N)]

    n_observers = 3
    observers = [random_slice(d, rng=rng) for _ in range(n_observers)]

    neighbors = voronoi_neighbors(bases)

    # track adjacency over time
    prev_adj = adjacency_matrix(bases)
    transitions = []  # (step, old_adj, new_adj)

    for step in range(n_steps):
        obs_idx = rng.integers(n_observers)
        v = rng.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        bases = write_step(bases, v, observers[obs_idx], eps=0.05,
                           neighbors=neighbors)

        adj = adjacency_matrix(bases)
        if not np.array_equal(adj, prev_adj):
            transitions.append((step, prev_adj.copy(), adj.copy()))
            prev_adj = adj.copy()
        else:
            prev_adj = adj

    print(f"d={d}, N={N}, observers={n_observers}")
    print(f"Total transitions: {len(transitions)}")
    print()

    if not transitions:
        print("No transitions found.")
        return

    # For each transition, check: does the new adjacency correlate
    # with the complement of the old?
    complement_correlations = []
    continuity_correlations = []

    mask = np.triu(np.ones((N, N), dtype=bool), k=1)

    for step, old_adj, new_adj in transitions:
        old_flat = old_adj[mask].flatten()
        new_flat = new_adj[mask].flatten()
        complement_flat = (1 - old_flat)

        # correlation with complement (negative geometry hypothesis)
        if np.std(new_flat) > 0 and np.std(complement_flat) > 0:
            comp_corr = np.corrcoef(new_flat, complement_flat)[0, 1]
        else:
            comp_corr = 0

        # correlation with old (continuity — mostly the same)
        if np.std(new_flat) > 0 and np.std(old_flat) > 0:
            cont_corr = np.corrcoef(new_flat, old_flat)[0, 1]
        else:
            cont_corr = 0

        complement_correlations.append(comp_corr)
        continuity_correlations.append(cont_corr)

    comp_arr = np.array(complement_correlations)
    cont_arr = np.array(continuity_correlations)

    print("Transition analysis:")
    print(f"  correlation(new, old):        mean={cont_arr.mean():.3f}, std={cont_arr.std():.3f}")
    print(f"  correlation(new, complement): mean={comp_arr.mean():.3f}, std={comp_arr.std():.3f}")
    print()

    # Count how many edges actually flip per transition
    flips_per_transition = []
    for step, old_adj, new_adj in transitions:
        diff = np.abs(old_adj - new_adj)[mask]
        flips_per_transition.append(diff.sum())

    flips_arr = np.array(flips_per_transition)
    total_edges = mask.sum()
    print(f"Edges per transition: mean={flips_arr.mean():.1f}, "
          f"max={flips_arr.max()}, total possible={total_edges}")
    print()

    # Are transitions local (few edges) or global (many edges)?
    if flips_arr.mean() < total_edges * 0.3:
        print("Transitions are LOCAL: few edges flip per transition.")
        print("The topology reorganizes incrementally, not catastrophically.")
    else:
        print("Transitions are GLOBAL: many edges flip per transition.")
        print("The topology reorganizes in bulk — epoch-like.")

    # Check for transition clustering
    steps = [t[0] for t in transitions]
    gaps = np.diff(steps)
    print(f"\nTransition timing:")
    print(f"  mean gap: {gaps.mean():.1f} steps")
    print(f"  min gap:  {gaps.min()} steps")
    print(f"  max gap:  {gaps.max()} steps")
    print(f"  clustered (>50% within 10 steps of another): "
          f"{sum(1 for g in gaps if g <= 10) / len(gaps) * 100:.0f}%")


if __name__ == "__main__":
    main()
