"""
Test: what happens when L approaches its bound?

U(d) is compact, so L (boundary area) is bounded. As measurement
deposits structure, L increases. At some point, Voronoi adjacencies
must flip — the topology changes.

Questions:
1. Can we actually reach the saturation regime?
2. What does the topology change look like?
3. Does the new topology reflect the negative geometry of the old?
"""

import numpy as np
from scipy.linalg import expm


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


def boundary_area(bases):
    N = len(bases)
    d = bases[0].shape[0]
    total = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            total += np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro')
    return total


def voronoi_adjacency(bases):
    """Which cells are adjacent? (simplified: all pairs within threshold)"""
    N = len(bases)
    d = bases[0].shape[0]
    dists = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            rel = bases[i].conj().T @ bases[j]
            dists[i, j] = np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro')
    # adjacency: pairs closer than median distance
    mask = np.triu(np.ones((N, N), dtype=bool), k=1)
    threshold = np.median(dists[mask])
    adj = (dists < threshold) & mask
    return adj, dists


def write_step(bases, v, P, eps=0.05):
    """Single write step with larger epsilon to accelerate dynamics."""
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


def theoretical_L_bound(d, N):
    """Upper bound on L = sum of pairwise distances.

    Maximum pairwise distance in U(d) under Frobenius norm of (U-I):
    max ||U - I||_F = max over unitary U. The farthest unitary from I
    is -I (eigenvalues all -1), with ||(-I) - I||_F = 2*sqrt(d).

    Upper bound on L: N*(N-1)/2 * 2*sqrt(d)
    """
    max_dist = 2 * np.sqrt(d)
    n_pairs = N * (N - 1) // 2
    return n_pairs * max_dist


def main():
    d = 4
    N = 5
    n_steps = 5000
    rng = np.random.default_rng(42)

    bases = [expm(skew_hermitian(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))))
             for _ in range(N)]

    # multiple observers writing from different slices
    n_observers = 3
    observers = []
    for _ in range(n_observers):
        Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
        observers.append(Q[:, :3].T)

    L_bound = theoretical_L_bound(d, N)
    print(f"d={d}, N={N}, observers={n_observers}")
    print(f"Theoretical L upper bound: {L_bound:.2f}")
    print()

    costs = []
    adjacency_changes = []
    prev_adj = None

    for step in range(n_steps):
        L = boundary_area(bases)
        costs.append(L)

        # check adjacency
        adj, _ = voronoi_adjacency(bases)
        if prev_adj is not None:
            changed = np.any(adj != prev_adj)
            if changed:
                adjacency_changes.append((step, L))
        prev_adj = adj.copy()

        # write from a random observer with a random input
        obs_idx = rng.integers(n_observers)
        v = rng.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        bases = write_step(bases, v, observers[obs_idx], eps=0.05)

        if step % 1000 == 0:
            pct_of_bound = L / L_bound * 100
            print(f"  step {step:5d}: L = {L:.4f} ({pct_of_bound:.1f}% of bound)")

    L_final = boundary_area(bases)
    costs.append(L_final)

    print()
    print(f"Final L: {L_final:.4f} ({L_final/L_bound*100:.1f}% of bound)")
    print(f"L range: [{min(costs):.4f}, {max(costs):.4f}]")
    print(f"Adjacency changes: {len(adjacency_changes)}")

    if adjacency_changes:
        print("\nEpoch transitions (adjacency flips):")
        for step, L_at in adjacency_changes[:20]:
            print(f"  step {step}: L = {L_at:.4f} ({L_at/L_bound*100:.1f}% of bound)")
        if len(adjacency_changes) > 20:
            print(f"  ... and {len(adjacency_changes) - 20} more")

    # Check: does L plateau?
    last_quarter = costs[3*len(costs)//4:]
    first_quarter = costs[:len(costs)//4]
    print(f"\nL growth rate:")
    print(f"  first quarter mean:  {np.mean(first_quarter):.4f}")
    print(f"  last quarter mean:   {np.mean(last_quarter):.4f}")
    print(f"  ratio: {np.mean(last_quarter)/np.mean(first_quarter):.4f}")


if __name__ == "__main__":
    main()
