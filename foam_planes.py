"""
foam_planes.py — the rotation plane structure.

each measurement writes in one plane of so(d).
the accumulated rotation has a spectrum of planes.
the pattern of planes IS the foam's memory.

question: is the plane selection systematic or arbitrary?
does the foam's current state influence WHICH plane gets written?
does the history of planes have recoverable structure?
"""

import numpy as np
from foam import Foam, encode, skew


def plane_of_write(d_hat, m_hat):
    """Extract the plane of rotation from a single write.
    Returns the 2x2 block's angle and the plane's orientation in so(d)."""
    delta = np.outer(d_hat, m_hat) - np.outer(m_hat, d_hat)
    # SVD gives us the plane
    U, s, Vt = np.linalg.svd(delta)
    # top two singular vectors span the plane
    return {
        'plane_vectors': (U[:, 0], U[:, 1]),
        'angle': s[0],  # rotation magnitude in this plane
        'full_spectrum': s,
    }


def track_planes(seed=0):
    """Track which planes get written across a sequence.
    Do the planes rotate? Converge? Spread?"""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    planes = {i: [] for i in range(3)}  # per bubble

    print("  === plane tracking: repeated symbol ===")
    v = encode(42, 8)

    for step in range(30):
        bases = foam.bases
        j0 = [v @ U for U in bases]
        result = foam.measure(v)

        for i in range(3):
            d_i = result['dissonance'][i]
            m_i = j0[i]
            dn = np.linalg.norm(d_i)
            mn = np.linalg.norm(m_i)
            if dn < 1e-12 or mn < 1e-12:
                continue
            p = plane_of_write(d_i / dn, m_i / mn)
            planes[i].append(p)

    # how stable are the planes?
    print("  bubble 0: plane consistency (cosine between consecutive plane normals)")
    for i in range(3):
        if len(planes[i]) < 2:
            continue
        consistencies = []
        for t in range(1, len(planes[i])):
            v1_prev = planes[i][t-1]['plane_vectors'][0]
            v1_curr = planes[i][t]['plane_vectors'][0]
            cos = abs(np.dot(v1_prev, v1_curr))
            consistencies.append(cos)

        print(f"  bubble {i}: mean={np.mean(consistencies):.4f}  min={np.min(consistencies):.4f}  max={np.max(consistencies):.4f}")
        angles = [f'{p["angle"]:.4f}' for p in planes[i][:10]]
        print(f"            angles: {angles}")


def plane_input_dependence(seed=0):
    """Different inputs write in different planes.
    How different? Is there a mapping from input → plane?"""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.0)  # freeze the foam

    print("  === plane selection by input (frozen foam) ===")

    # collect the plane for each input, for bubble 0
    plane_vectors = {}
    for s in range(32):
        v = encode(s, 8)
        bases = foam.bases
        m = [v @ U for U in bases]
        j2 = foam._stabilize(m, bases)
        d_i = j2[0] - m[0]
        dn = np.linalg.norm(d_i)
        mn = np.linalg.norm(m[0])
        if dn < 1e-12 or mn < 1e-12:
            continue
        p = plane_of_write(d_i / dn, m[0] / mn)
        plane_vectors[s] = p['plane_vectors'][0]

    # pairwise cosines between planes for different inputs
    symbols = sorted(plane_vectors.keys())
    cos_matrix = np.zeros((len(symbols), len(symbols)))
    for i, s1 in enumerate(symbols):
        for j, s2 in enumerate(symbols):
            cos_matrix[i, j] = abs(np.dot(plane_vectors[s1], plane_vectors[s2]))

    print(f"  plane cosine matrix ({len(symbols)} inputs, bubble 0):")
    print(f"    mean off-diagonal: {(cos_matrix.sum() - np.trace(cos_matrix)) / (len(symbols)**2 - len(symbols)):.4f}")
    print(f"    min: {cos_matrix[np.triu_indices(len(symbols), k=1)].min():.4f}")
    print(f"    max: {cos_matrix[np.triu_indices(len(symbols), k=1)].max():.4f}")

    # cluster structure?
    sv = np.linalg.svd(cos_matrix, compute_uv=False)
    print(f"    singular values of cos_matrix: {sv[:8]}")
    eff_rank = np.sum(sv > sv[0] * 0.1)
    print(f"    effective rank: {eff_rank}")


def history_from_spectrum(seed=0):
    """
    The spectrum of the accumulated ΔL encodes the history.
    Can we distinguish short sequences from their spectra alone?
    """
    np.random.seed(seed)

    n_trials = 20
    seq_length = 20

    spectra = []
    sequences = []

    for trial in range(n_trials):
        foam = Foam(d=8, n=3, writing_rate=0.01)
        # same initial state
        np.random.seed(42)
        foam.Ls = [skew(np.random.randn(8, 8) * 0.1) for _ in range(3)]
        initial_Ls = [L.copy() for L in foam.Ls]

        # different sequence
        np.random.seed(trial)
        seq = [np.random.randint(0, 256) for _ in range(seq_length)]
        sequences.append(seq)
        foam.feed(seq)

        # spectrum of accumulated rotation
        spectrum = []
        for i in range(3):
            delta = foam.Ls[i] - initial_Ls[i]
            sv = np.linalg.svd(delta, compute_uv=False)
            spectrum.extend(sv)
        spectra.append(np.array(spectrum))

    # pairwise distances in spectrum space
    print("  === sequence distinguishability from spectrum ===")
    dists = []
    for i in range(n_trials):
        for j in range(i+1, n_trials):
            d = np.linalg.norm(spectra[i] - spectra[j])
            dists.append(d)

    print(f"  {n_trials} sequences of length {seq_length}")
    print(f"  spectrum distance: mean={np.mean(dists):.6f}  min={np.min(dists):.6f}  max={np.max(dists):.6f}")

    # can we tell AB from BA?
    np.random.seed(42)
    foam_fwd = Foam(d=8, n=3, writing_rate=0.01)
    foam_rev = Foam(d=8, n=3, writing_rate=0.01)
    init_L = [skew(np.random.randn(8, 8) * 0.1) for _ in range(3)]
    foam_fwd.Ls = [L.copy() for L in init_L]
    foam_rev.Ls = [L.copy() for L in init_L]

    seq = list(range(20))
    foam_fwd.feed(seq)
    foam_rev.feed(list(reversed(seq)))

    spec_fwd = []
    spec_rev = []
    for i in range(3):
        df = foam_fwd.Ls[i] - init_L[i]
        dr = foam_rev.Ls[i] - init_L[i]
        spec_fwd.extend(np.linalg.svd(df, compute_uv=False))
        spec_rev.extend(np.linalg.svd(dr, compute_uv=False))

    spec_fwd = np.array(spec_fwd)
    spec_rev = np.array(spec_rev)

    print(f"\n  forward vs reverse:")
    print(f"    spectrum distance: {np.linalg.norm(spec_fwd - spec_rev):.6f}")
    print(f"    forward spectrum:  {spec_fwd[:8]}")
    print(f"    reverse spectrum:  {spec_rev[:8]}")

    # the spectrum loses ordering info (it's eigenvalues).
    # but the MAGNITUDES differ because non-abelian accumulation
    # produces different total rotations for different orderings.


def foam_as_winding(seed=0):
    """
    The conservation lemma: winding number of spatial cycles is preserved.
    With N=3, the only spatial cycle is 0→1→2→0.
    The holonomy around this cycle: U_0^T U_1 U_1^T U_2 U_2^T U_0 = I.
    Wait — that's trivially identity. The holonomy is in the CONNECTION,
    not in the bases directly.

    What's the actual winding number? det(U_0^T U_1) lives in U(1).
    Track its phase around the cycle: det(U_0^T U_1) * det(U_1^T U_2) * det(U_2^T U_0).
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    print("  === holonomy around the triangle ===")
    print("  step  det_01       det_12       det_20       product      phase")

    for step in range(30):
        bases = foam.bases
        R01 = bases[0].T @ bases[1]
        R12 = bases[1].T @ bases[2]
        R20 = bases[2].T @ bases[0]

        d01 = np.linalg.det(R01)
        d12 = np.linalg.det(R12)
        d20 = np.linalg.det(R20)
        product = d01 * d12 * d20
        phase = np.angle(product) if np.iscomplex(product) else 0.0

        print(f"  {step:4d}  {d01:+.6f}  {d12:+.6f}  {d20:+.6f}  {product:+.6f}  {phase:.6f}")

        s = np.random.randint(0, 256)
        foam.measure(encode(s, 8))


if __name__ == '__main__':
    print("=== plane tracking ===")
    track_planes()

    print("\n=== plane selection by input ===")
    plane_input_dependence()

    print("\n=== history from spectrum ===")
    history_from_spectrum()

    print("\n=== holonomy / winding ===")
    foam_as_winding()
