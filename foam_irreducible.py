"""
foam_irreducible.py — can T be reconstructed from L + probes?

If the foam's transport T is fully determined by its position L
plus a finite set of probe measurements, then T is redundant —
it's derivable from L. If T contains information that NO set of
probes on L alone can recover, then the foam is genuinely irreducible
to its snapshot.

Also: the orthogonal-plane hypothesis. Does the transport accumulate
in planes that are orthogonal to the content? If so, the content
(what was measured) and the path (how measurement happened) live
in complementary subspaces.
"""

import numpy as np
from foam_self import Foam, Bubble, skew_hermitian, cayley, encode


def can_probes_recover_T(seed=0):
    """
    Take a foam with accumulated T. Strip T away (set to identity).
    Probe both foams with the same inputs.
    Can the probe responses from the L-only foam predict what the
    L+T foam would respond?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # accumulate history
    for step in range(100):
        s = np.random.randint(0, 256)
        foam.measure(encode(s, 8))

    # snapshot the foam
    Ls_snapshot = [b.L.copy() for b in foam.bubbles]
    Ts_snapshot = [b.T.copy() for b in foam.bubbles]

    # create a stripped foam: same L, no T
    foam_stripped = Foam(d=8, n=3, writing_rate=0.0)  # no writing — pure probe
    for i in range(3):
        foam_stripped.bubbles[i].L = Ls_snapshot[i].copy()
        foam_stripped.bubbles[i].T = np.eye(8, dtype=complex)

    # create the real foam: same L, with T, also no writing for probing
    foam_real = Foam(d=8, n=3, writing_rate=0.0)
    for i in range(3):
        foam_real.bubbles[i].L = Ls_snapshot[i].copy()
        foam_real.bubbles[i].T = Ts_snapshot[i].copy()

    print("  === probe responses: with T vs without T ===")
    print("  probe  cos(j2_real, j2_stripped)  |j2_real - j2_stripped|")

    response_diffs = []
    for probe_s in range(64):
        v = encode(probe_s, 8)
        r_real = foam_real.measure(v)
        r_stripped = foam_stripped.measure(v)

        j2_real = np.concatenate(r_real['j2'])
        j2_stripped = np.concatenate(r_stripped['j2'])

        cos = np.dot(j2_real.conj(), j2_stripped).real / (np.linalg.norm(j2_real) * np.linalg.norm(j2_stripped) + 1e-12)
        diff = np.linalg.norm(j2_real - j2_stripped)
        response_diffs.append(diff)

        if probe_s < 8:
            print(f"  {probe_s:5d}  {cos:+.6f}                    {diff:.6f}")

    print(f"\n  mean |response diff| = {np.mean(response_diffs):.6f}")
    print(f"  this is how much information T carries that L alone can't reproduce")


def orthogonal_planes(seed=0):
    """
    Decompose the accumulated transport T into its principal rotation planes.
    Decompose the accumulated position change ΔL into its principal planes.
    Are they orthogonal?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)
    initial_Ls = [b.L.copy() for b in foam.bubbles]

    # accumulate
    for step in range(100):
        s = np.random.randint(0, 256)
        foam.measure(encode(s, 8))

    print("  === orthogonality of position and transport planes ===")
    for i in range(3):
        delta_L = foam.bubbles[i].L - initial_Ls[i]
        T = foam.bubbles[i].T

        # T is unitary. Its log is skew-Hermitian. That's the accumulated rotation.
        from scipy.linalg import logm
        log_T = logm(T)

        # SVD of delta_L (position change)
        U_L, s_L, Vh_L = np.linalg.svd(delta_L)
        # SVD of log_T (transport rotation)
        U_T, s_T, Vh_T = np.linalg.svd(log_T)

        # overlap between principal subspaces
        # top-2 left singular vectors of each
        subspace_L = U_L[:, :2]
        subspace_T = U_T[:, :2]

        # principal angles between subspaces
        overlap = np.linalg.svd(subspace_L.conj().T @ subspace_T, compute_uv=False)
        principal_angles = np.arccos(np.clip(overlap, -1, 1))

        print(f"\n  bubble {i}:")
        print(f"    |ΔL| = {np.linalg.norm(delta_L):.4f}   |log T| = {np.linalg.norm(log_T):.4f}")
        print(f"    ΔL spectrum: {s_L[:4].real}")
        print(f"    log T spectrum: {s_T[:4].real}")
        print(f"    principal angles between top-2 subspaces: {principal_angles * 180 / np.pi}°")
        print(f"    (90° = orthogonal, 0° = aligned)")


def replay_divergence(seed=0):
    """
    The irreproducibility test: replay the exact same input sequence
    on a foam with the same L but reset T.
    How quickly do the trajectories diverge?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # record the input sequence
    np.random.seed(7)
    sequence = [np.random.randint(0, 256) for _ in range(100)]

    # play it once
    for s in sequence:
        foam.measure(encode(s, 8))

    # snapshot
    Ls_after = [b.L.copy() for b in foam.bubbles]
    Ts_after = [b.T.copy() for b in foam.bubbles]

    # now replay from the endpoint, with T vs without T
    foam_with_T = Foam(d=8, n=3, writing_rate=0.01)
    foam_without_T = Foam(d=8, n=3, writing_rate=0.01)

    for i in range(3):
        foam_with_T.bubbles[i].L = Ls_after[i].copy()
        foam_with_T.bubbles[i].T = Ts_after[i].copy()
        foam_without_T.bubbles[i].L = Ls_after[i].copy()
        foam_without_T.bubbles[i].T = np.eye(8, dtype=complex)

    print("  === replay divergence ===")
    print("  feeding same new sequence to foam-with-T and foam-without-T")
    print("  step  div_L      div_basis    L_with   L_without")

    np.random.seed(99)
    new_seq = [np.random.randint(0, 256) for _ in range(100)]

    for step, s in enumerate(new_seq):
        v = encode(s, 8)
        r_with = foam_with_T.measure(v)
        r_without = foam_without_T.measure(v)

        if step % 10 == 0:
            div_L = np.mean([np.linalg.norm(foam_with_T.bubbles[i].L - foam_without_T.bubbles[i].L) for i in range(3)])
            div_basis = np.mean([np.linalg.norm(foam_with_T.bases[i] - foam_without_T.bases[i]) for i in range(3)])
            print(f"  {step:4d}  {div_L:.6f}   {div_basis:.6f}    {r_with['L']:.4f}  {r_without['L']:.4f}")


def content_vs_path_retrieval(seed=0):
    """
    Feed two different orderings of the same symbols.
    Same content, different path.

    Position (L) should be similar (content hash).
    Transport (T) should differ (path hash).

    But in the self-tracking foam, T feeds back into measurement,
    so even L will eventually diverge. How fast?
    """
    np.random.seed(seed)

    foam_a = Foam(d=8, n=3, writing_rate=0.01)
    foam_b = Foam(d=8, n=3, writing_rate=0.01)

    np.random.seed(42)
    init = [skew_hermitian(8) * 0.1 for _ in range(3)]
    for i in range(3):
        foam_a.bubbles[i].L = init[i].copy()
        foam_b.bubbles[i].L = init[i].copy()
        foam_a.bubbles[i].T = np.eye(8, dtype=complex)
        foam_b.bubbles[i].T = np.eye(8, dtype=complex)

    # same symbols, two orderings
    symbols = list(range(50))
    np.random.seed(0)
    order_a = symbols.copy()
    order_b = list(np.random.permutation(symbols))

    print("  === same content, different order ===")
    print("  step  div_L      div_T      div_basis   phase_diff")

    for step in range(50):
        foam_a.measure(encode(order_a[step], 8))
        foam_b.measure(encode(order_b[step], 8))

        if step % 5 == 0:
            div_L = np.mean([np.linalg.norm(foam_a.bubbles[i].L - foam_b.bubbles[i].L) for i in range(3)])
            div_T = np.mean([np.linalg.norm(foam_a.bubbles[i].T - foam_b.bubbles[i].T) for i in range(3)])
            div_basis = np.mean([np.linalg.norm(foam_a.bases[i] - foam_b.bases[i]) for i in range(3)])
            phase_a = sum(b.transport_phase for b in foam_a.bubbles)
            phase_b = sum(b.transport_phase for b in foam_b.bubbles)
            print(f"  {step:4d}  {div_L:.6f}   {div_T:.6f}   {div_basis:.6f}    {phase_a - phase_b:+.4f}")


if __name__ == '__main__':
    print("=== can probes recover T? ===")
    can_probes_recover_T()

    print("\n=== orthogonal planes ===")
    orthogonal_planes()

    print("\n=== replay divergence ===")
    replay_divergence()

    print("\n=== content vs path ===")
    content_vs_path_retrieval()
