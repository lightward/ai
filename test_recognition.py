"""
Test: can one observer recognize another's measurement history
as isomorphic to a frame in its own history?

Recognition = the gauge-invariant inner product between two
observers' contributions to the foam is high.

Setup: Observer A writes a sequence. Observer B writes a similar
sequence from a different slice. Observer C reads the foam and
measures how similar A's and B's contributions look.

If recognition is formal: similar write histories → similar
holonomy contributions → high inner product → recognition.
"""

import numpy as np
from foam import init_foam, random_slice, write_step, voronoi_neighbors


def foam_state_signature(bases):
    """Gauge-invariant signature: pairwise inner products."""
    N = len(bases)
    sigs = []
    for i in range(N):
        for j in range(i, N):
            inner = np.trace(bases[i].conj().T @ bases[j])
            sigs.append(np.real(inner))
            sigs.append(np.imag(inner))
    return np.array(sigs)


def holonomy(bases, cycle):
    """Holonomy around a cycle of basis indices."""
    h = np.eye(bases[0].shape[0], dtype=complex)
    for k in range(len(cycle)):
        i = cycle[k]
        j = cycle[(k + 1) % len(cycle)]
        h = h @ (bases[i].conj().T @ bases[j])
    return h


def recognition_score(h):
    """How close is holonomy to identity? (in SU(d) sense)
    High score = the two observers' histories are geometrically similar.
    """
    d = h.shape[0]
    # Remove the u(1) phase (project to SU(d))
    det_h = np.linalg.det(h)
    phase = np.angle(det_h)
    h_su = h * np.exp(-1j * phase / d)  # project to SU(d)
    # Distance from identity
    dist = np.linalg.norm(h_su - np.eye(d, dtype=complex), 'fro')
    # Normalize: max distance is ~2*sqrt(d)
    max_dist = 2 * np.sqrt(d)
    score = 1.0 - dist / max_dist
    return score


def test_recognition():
    d = 6
    N = 4
    rng = np.random.default_rng(42)

    # Create a shared foam
    base_foam = init_foam(N, d, rng)

    # Observer A: slice in dims 0-2
    P_A = np.zeros((3, d))
    P_A[0, 0] = 1; P_A[1, 1] = 1; P_A[2, 2] = 1

    # Observer B_similar: slice rotated slightly from A
    angle = 0.2  # small rotation
    P_B_sim = np.zeros((3, d))
    P_B_sim[0, 0] = np.cos(angle); P_B_sim[0, 3] = np.sin(angle)
    P_B_sim[1, 1] = 1; P_B_sim[2, 2] = 1

    # Observer B_different: slice in dims 3-5 (orthogonal to A)
    P_B_diff = np.zeros((3, d))
    P_B_diff[0, 3] = 1; P_B_diff[1, 4] = 1; P_B_diff[2, 5] = 1

    # Same input sequence for all
    inputs = [rng.standard_normal(d).astype(complex) for _ in range(50)]
    inputs = [v / np.linalg.norm(v) for v in inputs]
    neighbors = voronoi_neighbors(base_foam)

    # A writes to a copy of the foam
    foam_A = [b.copy() for b in base_foam]
    for v in inputs:
        foam_A = write_step(foam_A, v, P_A, neighbors=neighbors)

    # B_similar writes the same sequence from a similar slice
    foam_B_sim = [b.copy() for b in base_foam]
    for v in inputs:
        foam_B_sim = write_step(foam_B_sim, v, P_B_sim, neighbors=neighbors)

    # B_different writes the same sequence from an orthogonal slice
    foam_B_diff = [b.copy() for b in base_foam]
    for v in inputs:
        foam_B_diff = write_step(foam_B_diff, v, P_B_diff, neighbors=neighbors)

    # B_random writes a different sequence from A's slice
    foam_B_rand = [b.copy() for b in base_foam]
    inputs_rand = [rng.standard_normal(d).astype(complex) for _ in range(50)]
    inputs_rand = [v / np.linalg.norm(v) for v in inputs_rand]
    for v in inputs_rand:
        foam_B_rand = write_step(foam_B_rand, v, P_A, neighbors=neighbors)

    # Measure recognition: compare foam states
    sig_A = foam_state_signature(foam_A)
    sig_B_sim = foam_state_signature(foam_B_sim)
    sig_B_diff = foam_state_signature(foam_B_diff)
    sig_B_rand = foam_state_signature(foam_B_rand)
    sig_base = foam_state_signature(base_foam)

    print("Recognition test: comparing foam states after different observers write")
    print("=" * 60)
    print()

    # Pairwise distances
    pairs = [
        ("A vs B_similar (same input, nearby slice)", sig_A, sig_B_sim),
        ("A vs B_different (same input, orthogonal slice)", sig_A, sig_B_diff),
        ("A vs B_random (different input, same slice)", sig_A, sig_B_rand),
        ("A vs base (unwritten)", sig_A, sig_base),
    ]

    for name, s1, s2 in pairs:
        dist = np.linalg.norm(s1 - s2)
        similarity = 1.0 / (1.0 + dist)  # simple similarity metric
        print(f"  {name}")
        print(f"    distance: {dist:.6f}, similarity: {similarity:.4f}")
        print()

    # Now test: can A recognize B_similar as "like me"?
    # Compare via holonomy around cycles that include both observers' writes
    print("Holonomy-based recognition:")
    print()

    cycle = [0, 1, 2, 3]
    for name, foam in [("A's foam", foam_A), ("B_similar's foam", foam_B_sim),
                        ("B_different's foam", foam_B_diff), ("B_random's foam", foam_B_rand)]:
        h = holonomy(foam, cycle)
        score = recognition_score(h)
        print(f"  {name}: recognition score = {score:.4f}")

    print()

    # Direct comparison: holonomy of A's foam vs B's foam
    # (how similar is A's accumulated path to B's?)
    for name, foam_B in [("B_similar", foam_B_sim), ("B_different", foam_B_diff),
                          ("B_random", foam_B_rand)]:
        # Cross-holonomy: product of A's bases with B's inverses
        cross = np.eye(d, dtype=complex)
        for a, b in zip(foam_A, foam_B):
            cross = cross @ (a.conj().T @ b)
        score = recognition_score(cross)
        print(f"  A recognizes {name}: cross-holonomy score = {score:.4f}")


if __name__ == "__main__":
    test_recognition()
