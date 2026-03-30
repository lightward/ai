"""
foam.py — the writing map.

shared implementation for all tests. stabilization is local
(see spec: ground, the stabilization contract). R³ + Taylor
is the default (d_slice=3, k ≤ 4).

for N << d² (the tested regime), all pairs are Voronoi neighbors
on U(d) — concentration of measure makes random unitaries roughly
equidistant, so N points can't create non-trivial Voronoi structure
on a d²-dimensional manifold. local stabilization gives the same
result as global in this regime. the distinction matters at N
comparable to d², where adjacency becomes non-trivial and flips
are possible.
"""

import numpy as np
from scipy.linalg import expm


# --- core operations ---

def cayley(A):
    """Cayley transform: (I - A)(I + A)^{-1}."""
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    """Project to skew-Hermitian."""
    return (A - A.conj().T) / 2


def random_unitary(d, rng=None):
    """Random unitary via expm of random skew-Hermitian."""
    if rng is None:
        rng = np.random.default_rng()
    A = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    return expm(skew_hermitian(A))


def random_slice(d, d_slice=3, rng=None):
    """Random d_slice-dimensional slice (orthonormal rows in R^d)."""
    if rng is None:
        rng = np.random.default_rng()
    A = rng.standard_normal((d_slice, d))
    Q, _ = np.linalg.qr(A.T)
    return Q.T[:d_slice]


# --- geometry ---

def pairwise_distances(bases):
    """Frobenius distances: d(U_i, U_j) = ||U_i†U_j - I||_F."""
    N = len(bases)
    d = bases[0].shape[0]
    I = np.eye(d, dtype=complex)
    dist = np.zeros((N, N))
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            dist[i, j] = dist[j, i] = np.linalg.norm(rel - I, 'fro')
    return dist


def voronoi_neighbors(bases, n_samples=5000, rng=None):
    """Voronoi adjacency on U(d) under Frobenius distance.

    Returns list of lists: neighbors[i] = [j1, j2, ...].

    For N << d² (typical), all pairs are adjacent — returns the
    complete graph without sampling. For larger N, determines
    adjacency by sampling random unitaries and recording which
    pairs appear as nearest/second-nearest.
    """
    N = len(bases)
    d = bases[0].shape[0]

    # for small N relative to manifold dimension, all pairs are neighbors
    if N <= d * d // 4:
        return [[j for j in range(N) if j != i] for i in range(N)]

    # for larger N, sample to determine adjacency
    if rng is None:
        rng = np.random.default_rng()
    I_d = np.eye(d, dtype=complex)

    adj = set()
    for _ in range(n_samples):
        U = random_unitary(d, rng)
        dists = [np.linalg.norm(U.conj().T @ bases[k] - I_d, 'fro')
                 for k in range(N)]
        idx = np.argsort(dists)
        pair = (min(idx[0], idx[1]), max(idx[0], idx[1]))
        adj.add(pair)

    neighbors = [[] for _ in range(N)]
    for i, j in adj:
        neighbors[i].append(j)
        neighbors[j].append(i)
    return neighbors


def compute_L(bases):
    """Boundary area: L = sum_{i<j} ||U_i†U_j - I||_F."""
    N = len(bases)
    d = bases[0].shape[0]
    I = np.eye(d, dtype=complex)
    L = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            L += np.linalg.norm(bases[i].conj().T @ bases[j] - I, 'fro')
    return L


def foam_distance(bases_A, bases_B):
    """Gauge-invariant distance between two foam states.

    Uses relative distances (each basis relative to the first)
    to cancel global gauge.
    """
    N = len(bases_A)
    total = 0.0
    for i in range(N):
        rel_A = bases_A[0].conj().T @ bases_A[i]
        rel_B = bases_B[0].conj().T @ bases_B[i]
        total += np.linalg.norm(rel_A - rel_B, 'fro')
    return total


# --- the writing map ---

def stabilize(m_proj, observer_idx, neighbor_indices, stab_strength=0.1):
    """Local stabilization: push toward regular simplex with Voronoi neighbors.

    k = len(neighbor_indices) + 1 (neighbors + self).
    target cosine = -1/(k-1).
    returns j2 for the observer.
    """
    mi = m_proj[observer_idx]
    mi_norm = np.linalg.norm(mi)
    if mi_norm < 1e-12:
        return mi.copy()
    mi_hat = mi / mi_norm

    k = len(neighbor_indices) + 1
    target_cos = -1.0 / (k - 1) if k > 1 else 0.0

    force = np.zeros_like(mi)
    for j in neighbor_indices:
        mj = m_proj[j]
        mj_norm = np.linalg.norm(mj)
        if mj_norm < 1e-12:
            continue
        mj_hat = mj / mj_norm
        current_cos = np.dot(mi_hat, mj_hat)
        force += (target_cos - current_cos) * (mj_hat - current_cos * mi_hat)

    return mi + stab_strength * force * mi_norm


def write_single(bases, v, P, observer_idx, neighbors=None, eps=0.01,
                 stab_strength=0.1):
    """One observer writes. Returns updated copy of that basis.

    bases: list of N unitary matrices
    v: input vector (unit vector in R^d)
    P: observer's slice (d_slice x d real matrix)
    observer_idx: which basis is writing
    neighbors: pre-computed neighbor list (voronoi_neighbors output)
    """
    if neighbors is None:
        neighbors = voronoi_neighbors(bases)

    # 1. measure
    m_proj = [np.real(P @ (v @ b)) for b in bases]

    i = observer_idx
    mi = m_proj[i]
    mi_norm = np.linalg.norm(mi)
    if mi_norm < 1e-12:
        return bases[i].copy()

    # 2. stabilize (local)
    j2 = stabilize(m_proj, i, neighbors[i], stab_strength)

    # 3. dissonance
    d_vec = j2 - mi
    d_norm = np.linalg.norm(d_vec)
    if d_norm < 1e-12:
        return bases[i].copy()

    d_hat = d_vec / d_norm
    m_hat = mi / mi_norm

    # lift to R^d
    d_full = P.T @ d_hat
    m_full = P.T @ m_hat

    # 4. write (perpendicular: wedge product)
    dL = eps * d_norm * (
        np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj())
    )
    dL = skew_hermitian(dL)

    return cayley(dL) @ bases[i]


def write_step(bases, v, P, eps=0.01, neighbors=None, stab_strength=0.1):
    """Full writing map: all observers write sequentially.

    Sequential per spec (causal ordering: each write changes the foam,
    next observer measures the changed state).

    Returns new list of bases.
    """
    N = len(bases)
    new_bases = [b.copy() for b in bases]

    if neighbors is None:
        neighbors = voronoi_neighbors(new_bases)

    for i in range(N):
        new_bases[i] = write_single(new_bases, v, P, i, neighbors, eps,
                                    stab_strength)

    return new_bases


def init_foam(N, d, rng=None):
    """Initialize N random unitary bases in U(d)."""
    if rng is None:
        rng = np.random.default_rng()
    return [random_unitary(d, rng) for _ in range(N)]
