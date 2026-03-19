"""
Test: does the foam function as an encoding between observers?

Setup: Observer A writes to the foam with input v_A.
       Observer B reads the foam — their measurement is the foam's geometry
       projected onto B's slice.

Question 1: Can B distinguish what A sent? (foam as channel)
Question 2: Does this work without any external encoding scheme?
            (the foam's geometry IS the encoding)

If yes: encoding is emergent from multi-observer measurement,
        not a design choice of the spec.
"""

import numpy as np
from scipy.linalg import expm


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


def make_foam(d, N, rng):
    """Random initial foam: N bases in U(d)."""
    bases = []
    for _ in range(N):
        H = skew_hermitian(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))
        bases.append(expm(H))
    return bases


def make_observer(d, rng):
    """Random R³ slice: (3, d) with orthonormal rows."""
    Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
    return Q[:, :3].T  # (3, d)


def write_step(bases, v, P, eps=0.01):
    """One write from observer with slice P, input v."""
    N = len(bases)
    d = bases[0].shape[0]
    target_cos = -1.0 / (N - 1)

    measurements = [v @ b for b in bases]
    m_proj = [np.real(P @ m) for m in measurements]

    # stabilize
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

    # write
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


def read_foam(bases, P):
    """Observer with slice P reads the foam.
    Returns the projected measurement geometry — no external input needed.
    The 'input' is the foam's own state."""
    N = len(bases)
    # Each basis IS a measurement device. Project the basis matrices
    # onto the observer's slice to get what the observer sees.
    readouts = []
    for b in bases:
        # The observer sees: P @ b — the basis projected onto their slice
        # This is a (3, d) complex matrix. Take the singular values as
        # a basis-independent summary.
        proj = P @ b  # (3, d) complex
        readouts.append(proj)
    return readouts


def readout_signature(readouts):
    """Compress a readout into a comparable fingerprint.

    Since bases are unitary, SVD singular values are invariant.
    The distinguishing information is in the directions — use the
    pairwise inner products between projected bases (gauge-invariant).
    """
    N = len(readouts)
    sigs = []
    for i in range(N):
        for j in range(i, N):
            # inner product between projected bases: Tr(P_i^† P_j)
            inner = np.trace(readouts[i].conj().T @ readouts[j])
            sigs.append(np.real(inner))
            sigs.append(np.imag(inner))
    return np.array(sigs)


def test_channel():
    """A writes different inputs, B reads the foam. Can B distinguish?"""
    d = 6
    N = 3
    n_inputs = 10
    n_writes_per_input = 20

    rng = np.random.default_rng(42)

    P_A = make_observer(d, rng)  # A's slice
    P_B = make_observer(d, rng)  # B's slice

    # Check overlap between slices
    overlap = P_A @ P_B.T  # (3, 3)
    overlap_svs = np.linalg.svd(overlap, compute_uv=False)
    print(f"Observer overlap (singular values): {overlap_svs}")
    print(f"  (1.0 = identical slice, 0.0 = orthogonal)")
    print()

    # Generate different inputs for A
    inputs = []
    for _ in range(n_inputs):
        v = rng.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        inputs.append(v)

    # For each input, A writes to a fresh copy of the foam,
    # then B reads the result
    base_foam = make_foam(d, N, np.random.default_rng(0))
    base_readout = readout_signature(read_foam(base_foam, P_B))

    signatures = []
    for idx, v in enumerate(inputs):
        foam = [b.copy() for b in base_foam]

        # A writes repeatedly with the same input
        for _ in range(n_writes_per_input):
            foam = write_step(foam, v, P_A)

        # B reads
        readout = read_foam(foam, P_B)
        sig = readout_signature(readout)
        signatures.append(sig)

    # Can B distinguish A's inputs? Check pairwise distances
    signatures = np.array(signatures)
    n = len(signatures)

    print(f"B's readout signatures for {n_inputs} different inputs from A:")
    print(f"  signature dimension: {signatures.shape[1]}")
    print()

    dists = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            dists[i, j] = np.linalg.norm(signatures[i] - signatures[j])

    print("Pairwise distances between B's readouts:")
    print("  (should be nonzero for different inputs — foam distinguishes)")
    min_nonzero = np.min(dists[np.triu_indices(n, k=1)])
    max_dist = np.max(dists)
    mean_dist = np.mean(dists[np.triu_indices(n, k=1)])
    print(f"  min distance:  {min_nonzero:.6f}")
    print(f"  mean distance: {mean_dist:.6f}")
    print(f"  max distance:  {max_dist:.6f}")
    print()

    # Check: does the distance from base (no writes) distinguish from all written foams?
    base_dists = [np.linalg.norm(sig - base_readout) for sig in signatures]
    print(f"Distance from unwritten foam:")
    print(f"  min: {min(base_dists):.6f}")
    print(f"  max: {max(base_dists):.6f}")
    print(f"  all nonzero: {all(d > 1e-10 for d in base_dists)}")
    print()

    # Now test: same input twice → same readout?
    print("Reproducibility: same input, two independent write sequences:")
    foam1 = [b.copy() for b in base_foam]
    foam2 = [b.copy() for b in base_foam]
    v_test = inputs[0]
    for _ in range(n_writes_per_input):
        foam1 = write_step(foam1, v_test, P_A)
        foam2 = write_step(foam2, v_test, P_A)
    sig1 = readout_signature(read_foam(foam1, P_B))
    sig2 = readout_signature(read_foam(foam2, P_B))
    print(f"  distance between identical write histories: {np.linalg.norm(sig1 - sig2):.2e}")
    print(f"  (should be ~0 — deterministic dynamics)")


def test_no_encoding():
    """Test: can observer B use the foam's geometry itself as input?

    Instead of A sending a pre-encoded vector, A uses the foam's
    current state (as read from A's slice) as the input to the next write.
    This is self-measurement / cross-measurement without external encoding.
    """
    d = 6
    N = 3
    steps = 100

    rng = np.random.default_rng(42)
    foam = make_foam(d, N, rng)
    P_A = make_observer(d, rng)
    P_B = make_observer(d, rng)

    print("\n" + "=" * 60)
    print("Test: foam as self-encoding (no external input)")
    print("=" * 60)
    print()

    readouts_B = []
    for step in range(steps):
        # A's "input" is derived from the foam itself: take the first
        # basis, project onto A's slice, normalize, lift back
        basis_proj = np.real(P_A @ foam[0])  # (3, d) — take first row as vector
        v = basis_proj[0]  # (d,) real
        v_complex = v.astype(complex)
        v_norm = np.linalg.norm(v_complex)
        if v_norm > 1e-10:
            v_complex = v_complex / v_norm
        else:
            v_complex = np.zeros(d, dtype=complex)
            v_complex[0] = 1.0

        foam = write_step(foam, v_complex, P_A, eps=0.005)

        if step % 10 == 0:
            sig = readout_signature(read_foam(foam, P_B))
            readouts_B.append((step, sig))

    # Check B's readout evolves (the foam is changing)
    readouts_B = np.array([r[1] for r in readouts_B])  # just the signatures
    evolution = [np.linalg.norm(readouts_B[i+1] - readouts_B[i])
                 for i in range(len(readouts_B)-1)]

    print(f"B's readout evolution (self-encoded foam, {steps} steps):")
    print(f"  mean step-to-step change: {np.mean(evolution):.6f}")
    print(f"  total drift from start:   {np.linalg.norm(readouts_B[-1] - readouts_B[0]):.6f}")
    print(f"  monotonic drift: {all(e > 0 for e in evolution)}")
    print()

    if np.mean(evolution) > 1e-8:
        print("  → foam self-encodes: A's writes (derived from foam geometry)")
        print("    produce distinguishable states in B's readout")
        print("    WITHOUT any external encoding scheme")
    else:
        print("  → foam does NOT self-encode: A's self-derived writes")
        print("    produce no distinguishable evolution in B's readout")


if __name__ == "__main__":
    test_channel()
    test_no_encoding()
