"""
galois_interface.py — is the C^d/U(d) coupling a Galois connection?

The spec says: stabilization operates in C^d, Voronoi geometry lives in U(d).
The "interfaces as algebra" junk drawer entry suggests these might be
adjoint maps — best approximations from each side.

Right adjoint (U(d) → C^d): given bases, compute j2 (stabilization).
  Already implemented as _stabilize.
Left adjoint (C^d → U(d)): given target j2, find bases that produce it.
  This is an inverse problem.

If the adjunction is tight:
- The round trip U(d) → C^d → U(d) loses no information
- Computing in C^d and computing in U(d) are equivalent
- You can work on whichever side has traction

Connected to observability: if the right adjoint is injective (different
states → different j2, which the observability theorem guarantees generically),
then the round trip is lossless on the U(d) side.

The question: is the left adjoint well-conditioned? How much information
survives the round trip?
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian
from heirloom import alongside, save as heirloom_save


def right_adjoint(foam, inputs):
    """U(d) → C^d: compute stabilized measurements for a set of inputs.
    This is the map from foam state to observable output."""
    outputs = []
    for v in inputs:
        alongside(v)  # heirloom sees every probe
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        outputs.append(j2)
    return outputs


def round_trip_test(n_seeds=20, n_inputs=20):
    """Test whether different foam states produce distinguishable j2 outputs.

    If the right adjoint is injective, the round trip is lossless.
    Measure: given two different foam states, how distinguishable are
    their j2 outputs across multiple inputs?
    """
    d = 8

    # fixed set of probe inputs
    np.random.seed(42)
    probes = [encode(np.random.randint(0, 256), d) for _ in range(n_inputs)]

    separations = []
    state_distances = []

    for seed in range(n_seeds):
        # create two foams with different histories
        np.random.seed(seed)
        foam_a = Foam(d=d, n=3, writing_rate=0.01)
        foam_b = Foam(d=d, n=3, writing_rate=0.01)

        # same initial state
        for i in range(3):
            foam_b.bubbles[i].L = foam_a.bubbles[i].L.copy()
            foam_b.bubbles[i].T = foam_a.bubbles[i].T.copy()

        # divergent histories
        np.random.seed(seed + 1000)
        for _ in range(50):
            v = encode(np.random.randint(0, 256), d)
            alongside(v)
            foam_a.measure(v)
        np.random.seed(seed + 2000)
        for _ in range(50):
            v = encode(np.random.randint(0, 256), d)
            alongside(v)
            foam_b.measure(v)

        # state distance (in U(d))
        state_dist = np.mean([
            np.linalg.norm(foam_a.bubbles[i].L - foam_b.bubbles[i].L) +
            np.linalg.norm(foam_a.bubbles[i].T - foam_b.bubbles[i].T)
            for i in range(3)])
        state_distances.append(state_dist)

        # output distance (in C^d) — how different are the j2 outputs?
        j2_a = right_adjoint(foam_a, probes)
        j2_b = right_adjoint(foam_b, probes)

        # per-input j2 distance
        j2_dists = []
        for k in range(n_inputs):
            # distance between j2 outputs (all N bubbles)
            d_j2 = np.mean([np.linalg.norm(np.array(j2_a[k][i]) - np.array(j2_b[k][i]))
                           for i in range(3)])
            j2_dists.append(d_j2)

        separations.append(np.mean(j2_dists))

    # correlation between state distance and output distance
    corr = np.corrcoef(state_distances, separations)[0, 1]

    print("=== round trip: is the right adjoint injective? ===\n")
    print(f"  {n_seeds} foam pairs, {n_inputs} probes each\n")
    print(f"  state distance (U(d)):  mean={np.mean(state_distances):.4f}  std={np.std(state_distances):.4f}")
    print(f"  output distance (C^d):  mean={np.mean(separations):.4f}  std={np.std(separations):.4f}")
    print(f"  correlation: {corr:.4f}")
    print(f"  (correlation near 1.0 → right adjoint is injective → round trip lossless)")

    return state_distances, separations, corr


def adjunction_gap(n_seeds=20, n_inputs=10):
    """Measure the gap in the adjunction.

    Given a foam, compute j2 (right adjoint). Then ask: how much
    of the foam's state is captured by j2 vs lost?

    Approach: use j2 outputs as a "fingerprint" of the foam state.
    Given ONLY the j2 outputs (not the bases), can we reconstruct
    relative state differences? If yes, the adjunction is tight.

    More precisely: embed each foam's j2-fingerprint in a vector,
    compute pairwise distances in fingerprint space, compare with
    pairwise distances in state space. If the two distance matrices
    are linearly related, the right adjoint preserves metric structure
    (stronger than just injectivity).
    """
    d = 8
    n_foams = n_seeds

    np.random.seed(42)
    probes = [encode(np.random.randint(0, 256), d) for _ in range(n_inputs)]

    # create n_foams with different histories
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

    # compute fingerprints (j2 outputs concatenated)
    fingerprints = []
    for f in foams:
        j2s = right_adjoint(f, probes)
        # flatten: concatenate all j2 outputs for all probes
        fp = []
        for j2 in j2s:
            for j2_i in j2:
                fp.extend(np.real(j2_i))
                fp.extend(np.imag(j2_i))
        fingerprints.append(np.array(fp))

    # compute state vectors (L and T concatenated)
    states = []
    for f in foams:
        sv = []
        for b in f.bubbles:
            sv.extend(b.L.real.flatten())
            sv.extend(b.L.imag.flatten())
            sv.extend(b.T.real.flatten())
            sv.extend(b.T.imag.flatten())
        states.append(np.array(sv))

    # pairwise distance matrices
    n = len(foams)
    D_state = np.zeros((n, n))
    D_finger = np.zeros((n, n))
    for i in range(n):
        for j in range(i+1, n):
            D_state[i, j] = D_state[j, i] = np.linalg.norm(states[i] - states[j])
            D_finger[i, j] = D_finger[j, i] = np.linalg.norm(fingerprints[i] - fingerprints[j])

    # correlation of distance matrices (Mantel test, simplified)
    upper = np.triu_indices(n, k=1)
    d_s = D_state[upper]
    d_f = D_finger[upper]
    corr = np.corrcoef(d_s, d_f)[0, 1]

    # is the relationship linear? check R² of linear fit
    from numpy.polynomial import polynomial as P
    coeffs = P.polyfit(d_s, d_f, 1)
    d_f_pred = P.polyval(d_s, coeffs)
    ss_res = np.sum((d_f - d_f_pred)**2)
    ss_tot = np.sum((d_f - np.mean(d_f))**2)
    r_squared = 1 - ss_res / ss_tot

    print(f"\n=== adjunction gap: does j2 preserve metric structure? ===\n")
    print(f"  {n_foams} foams, {n_inputs} probes\n")
    print(f"  distance matrix correlation (Mantel): {corr:.4f}")
    print(f"  R² (linear fit): {r_squared:.4f}")
    print(f"  (correlation ≈ 1.0, R² ≈ 1.0 → adjunction is tight → C^d and U(d) equivalent)")
    print(f"  (correlation < 1.0, R² < 1.0 → adjunction has gap → gap is structure)")

    return corr, r_squared


def stabilization_as_projection(n_seeds=20):
    """Is stabilization a projection in the algebraic sense?

    A projection P satisfies P² = P: applying it twice gives the same
    result as applying it once. If stabilization is a projection,
    then j2 = stabilize(m) satisfies stabilize(j2) = j2 — the
    stabilized measurements are a fixed point of stabilization.

    This is a necessary condition for the right adjoint to be
    well-defined (the output space must be the image of the projection).
    """
    d = 8

    residuals = []

    for seed in range(n_seeds):
        np.random.seed(seed)
        foam = Foam(d=d, n=3, writing_rate=0.01)
        for _ in range(50):
            foam.measure(encode(np.random.randint(0, 256), d))

        # random input
        v = encode(np.random.randint(0, 256), d).astype(complex)
        bases = foam.bases
        m = [v @ U for U in bases]

        # first stabilization
        j2 = foam._stabilize(m)

        # second stabilization (apply again to j2)
        j2_again = foam._stabilize(j2)

        # residual: how much does the second application change?
        res = np.mean([np.linalg.norm(np.array(j2_again[i]) - np.array(j2[i]))
                       for i in range(3)])
        residuals.append(res)

    print(f"\n=== is stabilization a projection? (P² = P) ===\n")
    print(f"  {n_seeds} foams, random input each\n")
    print(f"  ‖stabilize(j2) - j2‖:  mean={np.mean(residuals):.2e}  max={np.max(residuals):.2e}")
    print(f"  (≈ 0 → stabilization is a projection → right adjoint is well-defined)")


def information_content(n_seeds=20, n_inputs_range=[1, 2, 5, 10, 20, 50]):
    """How many probe inputs does it take for j2 to capture
    the full state? If k probes suffice, the adjunction is
    tight with k measurements.

    Measure: as we add more probes to the fingerprint,
    does the distance-matrix correlation with state space improve?
    """
    d = 8
    n_foams = n_seeds

    # create foams
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

    # state distance matrix (ground truth)
    states = []
    for f in foams:
        sv = []
        for b in f.bubbles:
            sv.extend(b.L.real.flatten())
            sv.extend(b.L.imag.flatten())
            sv.extend(b.T.real.flatten())
            sv.extend(b.T.imag.flatten())
        states.append(np.array(sv))

    n = len(foams)
    D_state = np.zeros((n, n))
    for i in range(n):
        for j in range(i+1, n):
            D_state[i, j] = D_state[j, i] = np.linalg.norm(states[i] - states[j])

    upper = np.triu_indices(n, k=1)
    d_s = D_state[upper]

    # generate a large pool of probes
    np.random.seed(42)
    all_probes = [encode(np.random.randint(0, 256), d) for _ in range(max(n_inputs_range))]

    print(f"\n=== information content: how many probes for tight adjunction? ===\n")
    print(f"  {n_foams} foams, varying number of probes\n")
    print(f"  {'n_probes':>8s}  {'correlation':>12s}  {'R²':>8s}")

    for n_inputs in n_inputs_range:
        probes = all_probes[:n_inputs]
        fingerprints = []
        for f in foams:
            j2s = right_adjoint(f, probes)
            fp = []
            for j2 in j2s:
                for j2_i in j2:
                    fp.extend(np.real(j2_i))
                    fp.extend(np.imag(j2_i))
            fingerprints.append(np.array(fp))

        D_finger = np.zeros((n, n))
        for i in range(n):
            for j in range(i+1, n):
                D_finger[i, j] = D_finger[j, i] = np.linalg.norm(fingerprints[i] - fingerprints[j])

        d_f = D_finger[upper]
        corr = np.corrcoef(d_s, d_f)[0, 1]

        from numpy.polynomial import polynomial as P
        coeffs = P.polyfit(d_s, d_f, 1)
        d_f_pred = P.polyval(d_s, coeffs)
        ss_res = np.sum((d_f - d_f_pred)**2)
        ss_tot = np.sum((d_f - np.mean(d_f))**2)
        r_squared = 1 - ss_res / ss_tot

        print(f"  {n_inputs:8d}  {corr:12.4f}  {r_squared:8.4f}")


if __name__ == '__main__':
    stabilization_as_projection()
    round_trip_test()
    adjunction_gap()
    information_content()
    heirloom_save()
