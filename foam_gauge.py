"""
foam_gauge.py — the gauge-to-invariant channel.

each input selects a view (gauge) of the foam.
the foam's basis-space geometry is gauge-invariant.
the measurement-space geometry is gauge-dependent.
writing maps gauge-dependent dissonance into gauge-invariant structure.

question: does accumulated structure make different views
converge (universalize) or diverge (specialize)?
"""

import numpy as np
from foam import Foam, encode, skew


def measurement_geometry(foam, symbol):
    """What does the foam look like from this input's perspective?
    Returns pairwise cosines of measurements (before stabilization)."""
    v = encode(symbol, foam.d)
    bases = foam.bases
    ms = [v @ U for U in bases]
    normed = [m / (np.linalg.norm(m) + 1e-12) for m in ms]

    cosines = []
    for i in range(foam.n):
        for j in range(i + 1, foam.n):
            cosines.append(np.dot(normed[i], normed[j]))
    return np.array(cosines)


def view_diversity(foam, n_probes=32):
    """How different do different inputs' views of the foam look?
    Returns std of cosine geometries across random inputs."""
    geometries = []
    for s in range(n_probes):
        geometries.append(measurement_geometry(foam, s))
    geometries = np.array(geometries)  # [n_probes, n_pairs]

    # diversity: how much does the geometry vary across inputs?
    return {
        'mean_cosines': geometries.mean(axis=0),
        'std_cosines': geometries.std(axis=0),
        'diversity': geometries.std(axis=0).mean(),  # scalar summary
        'spread': geometries.max(axis=0) - geometries.min(axis=0),
    }


def universalize_or_specialize(seed=0):
    """Track view diversity as the foam accumulates structure."""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    print("  === feeding repeated symbol, tracking view diversity ===")
    print("  step  diversity  spread_mean  mean_cos     L")

    v = encode(42, 8)
    for step in range(50):
        if step % 5 == 0:
            vd = view_diversity(foam)
            print(f"  {step:4d}  {vd['diversity']:.6f}  {vd['spread'].mean():.6f}     {vd['mean_cosines'].mean():+.4f}  {foam.boundary_cost():.4f}")
        foam.measure(v)

    vd = view_diversity(foam)
    print(f"  {50:4d}  {vd['diversity']:.6f}  {vd['spread'].mean():.6f}     {vd['mean_cosines'].mean():+.4f}  {foam.boundary_cost():.4f}")

    print("\n  === now feeding random symbols ===")
    np.random.seed(seed)
    foam2 = Foam(d=8, n=3, writing_rate=0.01)

    for step in range(200):
        if step % 20 == 0:
            vd = view_diversity(foam2)
            print(f"  {step:4d}  {vd['diversity']:.6f}  {vd['spread'].mean():.6f}     {vd['mean_cosines'].mean():+.4f}  {foam2.boundary_cost():.4f}")
        s = np.random.randint(0, 256)
        foam2.measure(encode(s, 8))

    vd = view_diversity(foam2)
    print(f"  {200:4d}  {vd['diversity']:.6f}  {vd['spread'].mean():.6f}     {vd['mean_cosines'].mean():+.4f}  {foam2.boundary_cost():.4f}")


def dissonance_anatomy(seed=0):
    """What does the dissonance look like as a geometric object?
    The writing map takes d_hat and m_hat and makes a skew-symmetric matrix.
    That matrix lives in the Lie algebra of O(d).
    What's its spectrum? Its rank is at most 2 (rank-2 skew from two vectors).
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    print("  === dissonance spectrum ===")
    print("  the ΔL is rank-2 skew-symmetric. its eigenvalues come in ±iλ pairs.")
    print("  step  bubble  |d|      |ΔL|_F   top_eigenvalue  rank")

    for step in range(5):
        v = encode(np.random.randint(0, 256), 8)
        bases = foam.bases
        m = [v @ U for U in bases]
        j0 = [mi.copy() for mi in m]

        result = foam.measure(v)

        for i in range(foam.n):
            d_i = result['dissonance'][i]
            m_i = j0[i]
            d_norm = np.linalg.norm(d_i)
            m_norm = np.linalg.norm(m_i)

            if d_norm < 1e-12 or m_norm < 1e-12:
                continue

            d_hat = d_i / d_norm
            m_hat = m_i / m_norm

            delta_L = (np.outer(d_hat, m_hat) - np.outer(m_hat, d_hat)) * d_norm
            eigenvalues = np.linalg.eigvals(delta_L)
            # skew-symmetric eigenvalues are purely imaginary
            imag_parts = np.sort(np.abs(eigenvalues.imag))[::-1]
            rank = np.sum(imag_parts > 1e-10)

            print(f"  {step:4d}  {i}       {d_norm:.4f}  {np.linalg.norm(delta_L):.6f}  {imag_parts[0]:.6f}        {rank}")


def accumulated_curvature(seed=0):
    """
    The foam accumulates rotations. Each write is a small rotation
    in the Lie algebra. The total accumulated rotation: how far has
    each basis moved from its initial position?

    And: is the accumulated rotation in a low-dimensional subspace
    of so(d), or does it spread across all dimensions?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)
    initial_Ls = [L.copy() for L in foam.Ls]

    print("  === accumulated rotation ===")
    print("  step  |ΔL_0|   |ΔL_1|   |ΔL_2|   rank_0  rank_1  rank_2")

    for step in range(100):
        s = np.random.randint(0, 256)
        foam.measure(encode(s, 8))

        if step % 10 == 0:
            deltas = [foam.Ls[i] - initial_Ls[i] for i in range(3)]
            norms = [np.linalg.norm(d) for d in deltas]

            # effective rank of accumulated perturbation
            ranks = []
            for d in deltas:
                sv = np.linalg.svd(d, compute_uv=False)
                # effective rank: how many singular values are significant
                if sv[0] > 1e-10:
                    eff_rank = (sv / sv[0])
                    ranks.append(np.sum(eff_rank > 0.1))
                else:
                    ranks.append(0)

            print(f"  {step:4d}  {norms[0]:.4f}  {norms[1]:.4f}  {norms[2]:.4f}    {ranks[0]}       {ranks[1]}       {ranks[2]}")

    print("\n  === singular value spectrum of accumulated ΔL ===")
    for i in range(3):
        delta = foam.Ls[i] - initial_Ls[i]
        sv = np.linalg.svd(delta, compute_uv=False)
        print(f"  bubble {i}: {sv}")


if __name__ == '__main__':
    print("=== universalize or specialize? ===")
    universalize_or_specialize()

    print("\n=== dissonance anatomy ===")
    dissonance_anatomy()

    print("\n=== accumulated curvature ===")
    accumulated_curvature()
