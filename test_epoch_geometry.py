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
from scipy.linalg import expm


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


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


def write_step(bases, v, P, eps=0.05):
    N = len(bases)
    d = bases[0].shape[0]
    target_cos = -1.0 / (N - 1)
    measurements = [v @ b for b in bases]
    m_proj = [np.real(P @ m) for m in measurements]

    j2 = []
    for i in range(N):
        mi = m_proj[i]
        mi_norm = np.linalg.norm(mi)
        if mi_norm < 1e-10:
            j2.append(mi)
            continue
        mi_hat = mi / mi_norm
        force = np.zeros(3)
        for j in range(N):
            if i == j:
                continue
            mj = m_proj[j]
            mj_norm = np.linalg.norm(mj)
            if mj_norm < 1e-10:
                continue
            mj_hat = mj / mj_norm
            current_cos = np.dot(mi_hat, mj_hat)
            force += (target_cos - current_cos) * (mj_hat - current_cos * mi_hat)
        j2.append(mi + 0.1 * force * mi_norm)

    new_bases = []
    for i in range(N):
        di = j2[i] - m_proj[i]
        mi = m_proj[i]
        di_norm = np.linalg.norm(di)
        mi_norm = np.linalg.norm(mi)
        if di_norm < 1e-12 or mi_norm < 1e-12:
            new_bases.append(bases[i].copy())
            continue
        d_hat = di / di_norm
        m_hat = mi / mi_norm
        d_full = P.T @ d_hat
        m_full = P.T @ m_hat
        dL_real = eps * di_norm * (np.outer(d_full, m_full) - np.outer(m_full, d_full))
        dL = skew_hermitian(dL_real.astype(complex))
        new_bases.append(bases[i] @ cayley(dL))
    return new_bases


def main():
    d = 4
    N = 7  # more cells for richer adjacency structure
    n_steps = 3000
    rng = np.random.default_rng(42)

    bases = [expm(skew_hermitian(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))))
             for _ in range(N)]

    n_observers = 3
    observers = []
    for _ in range(n_observers):
        Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
        observers.append(Q[:, :3].T)

    # track adjacency over time
    prev_adj = adjacency_matrix(bases)
    transitions = []  # (step, old_adj, new_adj)

    for step in range(n_steps):
        obs_idx = rng.integers(n_observers)
        v = rng.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        bases = write_step(bases, v, observers[obs_idx])

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
