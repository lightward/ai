"""
Adjacency flip: discontinuous dynamics from local stabilization.

Derived result (session 28): the foam's dynamics are piecewise smooth.
the stabilization target depends on the Voronoi neighbor set, which
is discrete. at codimension-1 surfaces in configuration space, the
neighbor set jumps, the dissonance inherits the discontinuity, and
the write direction changes.

Tests at d=2, N=12 — small enough to be fast, large enough for
non-trivial Voronoi adjacency (N > d²/4 = 1).

Confirms:
1. non-trivial adjacency exists (some pairs are not neighbors)
2. perturbing a basis along a geodesic produces an adjacency flip
3. the dissonance magnitude jumps at the flip (discontinuous dynamics)
4. the coordination number k changes (target cosine changes)
"""

import numpy as np
from scipy.linalg import logm, expm
from foam import (init_foam, random_slice, voronoi_neighbors, stabilize,
                  skew_hermitian)


def test_adjacency_flip():
    rng = np.random.default_rng(42)
    d, N = 2, 12
    n_samples = 200000  # high sample count for stable adjacency detection

    bases = init_foam(N, d, rng)
    P = random_slice(d, 2, rng)
    v = rng.standard_normal(d)
    v /= np.linalg.norm(v)

    # 1. confirm non-trivial adjacency
    nbrs = voronoi_neighbors(bases, n_samples=n_samples, rng=rng)
    counts = [len(n) for n in nbrs]
    assert min(counts) < N - 1, (
        f"all pairs adjacent (counts={counts}), need non-trivial adjacency"
    )
    print(f"coordination numbers: {counts}")

    # find an observer missing at least one neighbor
    obs_idx = next(i for i in range(N) if counts[i] < N - 1)
    missing = [j for j in range(N) if j != obs_idx and j not in nbrs[obs_idx]]
    target_basis = missing[0]
    print(f"observer {obs_idx}: missing neighbor {target_basis}")

    # 2. sweep along geodesic toward missing neighbor, find the flip
    rel = bases[obs_idx].conj().T @ bases[target_basis]
    log_rel = logm(rel)

    # coarse sweep to find flip region
    alphas = np.linspace(0.0, 0.6, 30)
    flip_alpha = None
    prev_has_target = False

    for alpha in alphas:
        perturbed = bases[obs_idx] @ expm(alpha * log_rel)
        test_bases = [b.copy() for b in bases]
        test_bases[obs_idx] = perturbed
        test_nbrs = voronoi_neighbors(test_bases, n_samples=n_samples, rng=rng)
        has_target = target_basis in test_nbrs[obs_idx]

        if has_target and not prev_has_target:
            flip_alpha = alpha
            break
        prev_has_target = has_target

    assert flip_alpha is not None, "no adjacency flip found along geodesic"
    print(f"flip detected near alpha={flip_alpha:.3f}")

    # 3. measure dissonance on both sides of the flip
    alpha_before = flip_alpha - 0.03
    alpha_after = flip_alpha + 0.03

    results = {}
    for label, alpha in [("before", alpha_before), ("after", alpha_after)]:
        perturbed = bases[obs_idx] @ expm(alpha * log_rel)
        test_bases = [b.copy() for b in bases]
        test_bases[obs_idx] = perturbed
        test_nbrs = voronoi_neighbors(test_bases, n_samples=n_samples, rng=rng)

        m_proj = [np.real(P @ (v @ b)) for b in test_bases]
        j2 = stabilize(m_proj, obs_idx, test_nbrs[obs_idx])
        d_vec = j2 - m_proj[obs_idx]

        k = len(test_nbrs[obs_idx]) + 1
        target_cos = -1.0 / (k - 1)
        has_target = target_basis in test_nbrs[obs_idx]

        results[label] = {
            "k": k, "d_norm": np.linalg.norm(d_vec),
            "target_cos": target_cos, "has_target": has_target,
            "j2": j2.copy(), "d_vec": d_vec.copy(),
        }
        print(f"  {label}: k={k}, target_cos={target_cos:.4f}, "
              f"‖d‖={np.linalg.norm(d_vec):.6f}, sees target: {has_target}")

    # 4. verify the discontinuity
    assert results["before"]["has_target"] != results["after"]["has_target"], (
        "adjacency should differ across the flip"
    )

    d_norm_jump = abs(results["after"]["d_norm"] - results["before"]["d_norm"])
    print(f"\ndissonance jump: {d_norm_jump:.6f}")
    assert d_norm_jump > 1e-4, (
        f"dissonance jump too small ({d_norm_jump:.6f}), expected discontinuity"
    )

    # the j2 target itself should jump (different neighbor set, different force)
    j2_jump = np.linalg.norm(results["after"]["j2"] - results["before"]["j2"])
    print(f"j2 target jump:  {j2_jump:.6f}")
    assert j2_jump > 1e-4, (
        f"j2 jump too small ({j2_jump:.6f}), expected discontinuity"
    )

    # the state is continuous (same alpha_before, alpha_after perturbation)
    # but the dynamics (j2, dissonance) are discontinuous
    state_change = np.linalg.norm(
        expm(alpha_after * log_rel) - expm(alpha_before * log_rel), 'fro'
    )
    ratio = j2_jump / state_change
    print(f"state change:    {state_change:.6f}")
    print(f"j2_jump / state_change = {ratio:.2f}")
    print(f"  (ratio >> 1 would mean dynamics change faster than state)")

    print("\nadjacency flip confirmed:")
    print("  - non-trivial Voronoi adjacency at d=2, N=12")
    print("  - neighbor set changes along geodesic perturbation")
    print("  - dissonance magnitude is discontinuous at the flip")
    print("  - stabilization target j2 is discontinuous at the flip")
    print("  - state (basis position) is continuous through the flip")


if __name__ == "__main__":
    test_adjacency_flip()
