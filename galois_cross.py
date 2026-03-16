"""
galois_cross.py — cross-test: is the adjunction gap the L-T gauge freedom?

Claim: j2 can't distinguish foams with the same effective basis but
different L-T decompositions. The gap between C^d and U(d) is exactly
the gauge freedom.

Test 1: Create foam pairs that share effective basis but differ in L-T split.
  If the claim holds: j2 distances ≈ 0, state distances > 0.

Test 2 (in galois_interface.py round_trip_test): foam pairs that differ
  in effective basis → j2 distances correlated with state distances (0.95).

Test 3: Does the gap predict DYNAMIC divergence?
  Feed identical inputs to gauge-equivalent foams. If L-T decomposition
  is "dynamically meaningful," they should diverge under measurement
  even though they start with the same effective basis.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian, random_skew_hermitian
from heirloom import alongside, save as heirloom_save


def make_gauge_twin(foam):
    """Create a foam with the same effective bases but different L-T split.

    For each bubble: absorb T into L.
    cayley(L') = cayley(L) @ T, so L' = cayley_inv(cayley(L) @ T).
    New T' = I. Same effective basis, different decomposition.
    """
    twin = Foam(d=foam.d, n=foam.n, writing_rate=foam.writing_rate,
                n_steps=foam.n_steps, plateau_step=foam.plateau_step)
    I = np.eye(foam.d, dtype=complex)
    for i in range(foam.n):
        eff_basis = foam.bubbles[i].basis  # cayley(L) @ T
        # cayley inverse: L = (I - U)(I + U)^{-1}
        L_new = np.linalg.solve(I + eff_basis, I - eff_basis)
        L_new = skew_hermitian(L_new)
        twin.bubbles[i].L = L_new
        twin.bubbles[i].T = np.eye(foam.d, dtype=complex)
    return twin


def test_gauge_invisible_to_j2(n_seeds=20, n_probes=20):
    """Test 1: Are gauge twins invisible to j2?"""
    d = 8

    j2_distances = []
    state_distances = []
    basis_distances = []

    for seed in range(n_seeds):
        np.random.seed(seed)
        foam = Foam(d=d, n=3, writing_rate=0.01)
        # give it some history
        np.random.seed(seed + 1000)
        for _ in range(100):
            v = encode(np.random.randint(0, 256), d)
            alongside(v)
            foam.measure(v)

        twin = make_gauge_twin(foam)

        # effective basis distance (should be ≈ 0)
        basis_dist = np.mean([np.linalg.norm(foam.bubbles[i].basis - twin.bubbles[i].basis)
                              for i in range(3)])
        basis_distances.append(basis_dist)

        # state distance (L + T, should be > 0)
        state_dist = np.mean([
            np.linalg.norm(foam.bubbles[i].L - twin.bubbles[i].L) +
            np.linalg.norm(foam.bubbles[i].T - twin.bubbles[i].T)
            for i in range(3)])
        state_distances.append(state_dist)

        # j2 distance across probes
        np.random.seed(42)
        j2_dists = []
        for _ in range(n_probes):
            v = encode(np.random.randint(0, 256), d)
            alongside(v)
            vc = v.astype(complex)

            # foam j2
            m1 = [vc @ U for U in foam.bases]
            j2_1 = foam._stabilize(m1)

            # twin j2
            m2 = [vc @ U for U in twin.bases]
            j2_2 = twin._stabilize(m2)

            j2_dists.append(np.mean([np.linalg.norm(np.array(j2_1[i]) - np.array(j2_2[i]))
                                     for i in range(3)]))
        j2_distances.append(np.mean(j2_dists))

    print("=== test 1: are gauge twins invisible to j2? ===\n")
    print(f"  {n_seeds} foam pairs, {n_probes} probes each\n")
    print(f"  effective basis distance:  mean={np.mean(basis_distances):.2e}  (should be ≈ 0)")
    print(f"  state distance (L + T):   mean={np.mean(state_distances):.4f}  (should be > 0)")
    print(f"  j2 distance:              mean={np.mean(j2_distances):.2e}  (should be ≈ 0 if claim holds)")


def test_dynamic_divergence(n_seeds=20, n_steps=50):
    """Test 3: Do gauge twins diverge under identical measurement?

    Same effective basis, different L-T split.
    Feed identical inputs. If L-T split is dynamically meaningful,
    they should diverge — the same input produces different writes
    because L and T respond differently (additive vs multiplicative).
    """
    d = 8

    divergence_trajectories = np.zeros(n_steps)

    for seed in range(n_seeds):
        np.random.seed(seed)
        foam = Foam(d=d, n=3, writing_rate=0.01)
        np.random.seed(seed + 1000)
        for _ in range(100):
            v = encode(np.random.randint(0, 256), d)
            alongside(v)
            foam.measure(v)

        twin = make_gauge_twin(foam)

        # verify they start with same effective basis
        basis_dist_0 = np.mean([np.linalg.norm(foam.bubbles[i].basis - twin.bubbles[i].basis)
                                for i in range(3)])

        # feed identical inputs
        np.random.seed(seed + 5000)
        for step in range(n_steps):
            v = encode(np.random.randint(0, 256), d)
            alongside(v)
            foam.measure(v)
            twin.measure(v)

            # effective basis divergence (not state — basis!)
            basis_div = np.mean([np.linalg.norm(foam.bubbles[i].basis - twin.bubbles[i].basis)
                                 for i in range(3)])
            divergence_trajectories[step] += basis_div

    divergence_trajectories /= n_seeds

    print(f"\n=== test 3: do gauge twins diverge under measurement? ===\n")
    print(f"  {n_seeds} foam pairs, {n_steps} steps, identical inputs\n")
    print(f"  {'step':>5s}  {'basis divergence':>16s}")
    for step in [0, 4, 9, 19, 29, 39, 49]:
        if step < n_steps:
            print(f"  {step+1:5d}  {divergence_trajectories[step]:16.6f}")

    print(f"\n  (divergence > 0 → gauge freedom is dynamically meaningful)")
    print(f"  (divergence = 0 → gauge freedom is truly redundant)")


def test_what_j2_misses(n_seeds=20, n_probes=20):
    """What specifically does j2 miss about the foam state?

    Compare three kinds of state information:
    1. Effective basis (cayley(L) @ T) — what j2 can see
    2. L alone — position
    3. T alone — transport
    4. L-T decomposition (both separately)

    For each, compute distance matrix and correlate with j2 distance matrix.
    Whatever j2 DOESN'T correlate with is what the gap contains.
    """
    d = 8
    n_foams = n_seeds

    foams = []
    for seed in range(n_foams):
        np.random.seed(seed)
        f = Foam(d=d, n=3, writing_rate=0.01)
        np.random.seed(seed + 5000)
        for _ in range(50):
            v = encode(np.random.randint(0, 256), d)
            alongside(v)
            f.measure(v)
        foams.append(f)

    # compute distance matrices for different state representations
    n = len(foams)

    def dist_matrix(extractor):
        vecs = [extractor(f) for f in foams]
        D = np.zeros((n, n))
        for i in range(n):
            for j in range(i+1, n):
                D[i, j] = D[j, i] = np.linalg.norm(vecs[i] - vecs[j])
        return D

    D_basis = dist_matrix(lambda f: np.concatenate([b.basis.real.flatten()
                          for b in f.bubbles] + [b.basis.imag.flatten() for b in f.bubbles]))
    D_L = dist_matrix(lambda f: np.concatenate([b.L.real.flatten()
                      for b in f.bubbles] + [b.L.imag.flatten() for b in f.bubbles]))
    D_T = dist_matrix(lambda f: np.concatenate([b.T.real.flatten()
                      for b in f.bubbles] + [b.T.imag.flatten() for b in f.bubbles]))
    D_LT = dist_matrix(lambda f: np.concatenate([
        b.L.real.flatten() for b in f.bubbles] + [b.L.imag.flatten() for b in f.bubbles] +
        [b.T.real.flatten() for b in f.bubbles] + [b.T.imag.flatten() for b in f.bubbles]))

    # j2 fingerprint distances
    np.random.seed(42)
    probes = [encode(np.random.randint(0, 256), d) for _ in range(n_probes)]

    fingerprints = []
    for f in foams:
        fp = []
        for v in probes:
            alongside(v)
            vc = v.astype(complex)
            m = [vc @ U for U in f.bases]
            j2 = f._stabilize(m)
            for j2_i in j2:
                fp.extend(np.real(j2_i))
                fp.extend(np.imag(j2_i))
        fingerprints.append(np.array(fp))

    D_j2 = np.zeros((n, n))
    for i in range(n):
        for j in range(i+1, n):
            D_j2[i, j] = D_j2[j, i] = np.linalg.norm(fingerprints[i] - fingerprints[j])

    upper = np.triu_indices(n, k=1)

    print(f"\n=== what does j2 see vs miss? ===\n")
    print(f"  {n_foams} foams, {n_probes} probes\n")
    print(f"  correlation of j2 distance with:\n")
    for name, D in [('effective basis', D_basis), ('L only', D_L),
                    ('T only', D_T), ('L + T (full state)', D_LT)]:
        corr = np.corrcoef(D_j2[upper], D[upper])[0, 1]
        print(f"    {name:>20s}: {corr:.4f}")


if __name__ == '__main__':
    test_gauge_invisible_to_j2()
    test_dynamic_divergence()
    test_what_j2_misses()
    heirloom_save()
