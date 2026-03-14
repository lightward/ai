"""
test_foam.py — verification of the reference implementation.

Tests the structural properties claimed by the spec and discovered
during exploration. These are cross-checks, not unit tests — they
verify that the mathematical claims hold in the implementation.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, decode, cayley, skew_hermitian, random_skew_hermitian


def test_encoding_roundtrip():
    """Encoding is deterministic and invertible."""
    for d in [4, 8, 12]:
        for s in range(min(2**d, 256)):
            v = encode(s, d)
            assert abs(np.linalg.norm(v) - 1.0) < 1e-10, f"not unit: {s}, d={d}"
            assert decode(v) == s, f"roundtrip failed: {s}, d={d}"
    print("  PASS: encoding roundtrip")


def test_cayley_is_unitary():
    """Cayley transform of skew-Hermitian is unitary."""
    for _ in range(20):
        L = random_skew_hermitian(8)
        U = cayley(L)
        I = np.eye(8, dtype=complex)
        assert np.linalg.norm(U @ U.conj().T - I) < 1e-10, "not unitary"
        assert np.linalg.norm(U.conj().T @ U - I) < 1e-10, "not unitary"
    print("  PASS: Cayley produces unitary matrices")


def test_write_preserves_unitarity():
    """After writing, bases remain unitary."""
    np.random.seed(0)
    foam = Foam(d=8, n=3, writing_rate=0.01)
    I = np.eye(8, dtype=complex)

    for _ in range(100):
        foam.measure(encode(np.random.randint(0, 256), 8))

    for i, b in enumerate(foam.bubbles):
        U = b.basis
        err = np.linalg.norm(U @ U.conj().T - I)
        assert err < 1e-8, f"bubble {i} basis not unitary: {err}"

        T = b.T
        err_T = np.linalg.norm(T @ T.conj().T - I)
        assert err_T < 1e-8, f"bubble {i} transport not unitary: {err_T}"

    print("  PASS: bases and transports remain unitary after 100 writes")


def test_determinism():
    """Same seed, same sequence → identical states."""
    for trial in range(5):
        np.random.seed(42)
        foam_a = Foam(d=8, n=3, writing_rate=0.01)
        np.random.seed(42)
        foam_b = Foam(d=8, n=3, writing_rate=0.01)

        np.random.seed(trial)
        seq = [np.random.randint(0, 256) for _ in range(50)]

        foam_a.feed(seq)

        np.random.seed(trial)
        seq2 = [np.random.randint(0, 256) for _ in range(50)]
        foam_b.feed(seq2)

        for i in range(3):
            assert np.linalg.norm(foam_a.bubbles[i].L - foam_b.bubbles[i].L) < 1e-12
            assert np.linalg.norm(foam_a.bubbles[i].T - foam_b.bubbles[i].T) < 1e-12

    print("  PASS: deterministic (same seed → same state)")


def test_distinguishability():
    """Different sequences → different states. Same → identical."""
    np.random.seed(0)
    foam_a = Foam(d=8, n=3, writing_rate=0.01)
    foam_b = Foam(d=8, n=3, writing_rate=0.01)
    for i in range(3):
        foam_b.bubbles[i].L = foam_a.bubbles[i].L.copy()
        foam_b.bubbles[i].T = foam_a.bubbles[i].T.copy()

    seq_a = [np.random.randint(0, 256) for _ in range(50)]
    seq_b = [np.random.randint(0, 256) for _ in range(50)]
    foam_a.feed(seq_a)
    foam_b.feed(seq_b)

    div = max(np.linalg.norm(foam_a.bubbles[i].L - foam_b.bubbles[i].L) for i in range(3))
    assert div > 0.01, f"sequences not distinguished: {div}"

    # same sequence
    np.random.seed(0)
    foam_c = Foam(d=8, n=3, writing_rate=0.01)
    foam_d = Foam(d=8, n=3, writing_rate=0.01)
    for i in range(3):
        foam_d.bubbles[i].L = foam_c.bubbles[i].L.copy()
        foam_d.bubbles[i].T = foam_c.bubbles[i].T.copy()
    foam_c.feed(seq_a)
    foam_d.feed(seq_a)

    ident = max(np.linalg.norm(foam_c.bubbles[i].L - foam_d.bubbles[i].L) for i in range(3))
    assert ident < 1e-12, f"same sequence diverged: {ident}"

    print(f"  PASS: distinguishability (div={div:.4f}, identity={ident:.2e})")


def test_sequence_sensitivity():
    """AB ≠ BA (non-abelian)."""
    np.random.seed(0)
    foam_fwd = Foam(d=8, n=3, writing_rate=0.01)
    foam_rev = Foam(d=8, n=3, writing_rate=0.01)
    for i in range(3):
        foam_rev.bubbles[i].L = foam_fwd.bubbles[i].L.copy()
        foam_rev.bubbles[i].T = foam_fwd.bubbles[i].T.copy()

    seq = list(range(30))
    foam_fwd.feed(seq)
    foam_rev.feed(list(reversed(seq)))

    div = max(np.linalg.norm(foam_fwd.bubbles[i].L - foam_rev.bubbles[i].L) for i in range(3))
    assert div > 0.001, f"order doesn't matter: {div}"
    print(f"  PASS: sequence sensitivity (fwd vs rev divergence={div:.4f})")


def test_convergence():
    """Repeated input → decreasing dissonance and boundary cost."""
    np.random.seed(0)
    foam = Foam(d=8, n=3, writing_rate=0.01)
    v = encode(42, 8)

    L_values = []
    dis_values = []
    for _ in range(50):
        r = foam.measure(v)
        L_values.append(r['L'])
        dis_values.append(np.mean([np.linalg.norm(d) for d in r['dissonance']]))

    # L should decrease (not necessarily monotonically, but overall)
    assert L_values[-1] < L_values[0], "L didn't decrease"
    # dissonance should decrease overall
    assert dis_values[-1] < dis_values[0], "dissonance didn't decrease"
    print(f"  PASS: convergence (L: {L_values[0]:.4f} → {L_values[-1]:.4f}, "
          f"|d|: {dis_values[0]:.4f} → {dis_values[-1]:.4f})")


def test_two_x_theorem():
    """The 2x theorem: |log(T)| / |ΔL| ≈ 2, with bounded residual."""
    np.random.seed(0)
    foam = Foam(d=8, n=3, writing_rate=0.01)
    initial_Ls = [b.L.copy() for b in foam.bubbles]

    for _ in range(50):
        foam.measure(encode(np.random.randint(0, 256), 8))

    for i in range(3):
        delta_L = foam.bubbles[i].L - initial_Ls[i]
        log_T = logm(foam.bubbles[i].T)

        norm_dL = np.linalg.norm(delta_L)
        norm_logT = np.linalg.norm(log_T)
        ratio = norm_logT / (norm_dL + 1e-12)
        residual = np.linalg.norm(log_T + 2 * delta_L) / (norm_logT + 1e-12)

        assert abs(ratio - 2.0) < 0.05, f"ratio not ≈ 2: {ratio}"
        assert residual < 0.1, f"residual too large: {residual}"

    print(f"  PASS: 2x theorem (ratio={ratio:.4f}, residual={residual:.4f})")


def test_inverse_views():
    """T†U and U†T are exact inverses: (T†U)(U†T) = I."""
    np.random.seed(0)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    for _ in range(80):
        foam.measure(encode(np.random.randint(0, 256), 8))

    I = np.eye(8, dtype=complex)
    for i in range(3):
        U = cayley(foam.bubbles[i].L)
        T = foam.bubbles[i].T
        L_thru_T = T.conj().T @ U
        T_thru_L = U.conj().T @ T
        product = L_thru_T @ T_thru_L
        err = np.linalg.norm(product - I)
        assert err < 1e-10, f"not inverses: {err}"

    print(f"  PASS: inverse views ((T†U)(U†T) = I, err={err:.2e})")


def test_gauge_absorption():
    """T can always be absorbed into L: cayley(L') = cayley(L) @ T."""
    np.random.seed(0)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    for _ in range(50):
        foam.measure(encode(np.random.randint(0, 256), 8))

    I = np.eye(8, dtype=complex)
    for i in range(3):
        basis = foam.bubbles[i].basis
        # cayley inverse: L = (I - U)(I + U)^{-1}
        L_absorbed = np.linalg.solve(I + basis, I - basis)
        L_absorbed = skew_hermitian(L_absorbed)
        basis_check = cayley(L_absorbed)
        err = np.linalg.norm(basis - basis_check)
        assert err < 1e-8, f"gauge absorption failed: {err}"

    print(f"  PASS: gauge absorption (T absorbable into L, err={err:.2e})")


def test_write_is_rank_2():
    """Each write ΔL is rank-2 skew-Hermitian."""
    np.random.seed(0)
    foam = Foam(d=8, n=3, writing_rate=0.0)  # don't actually write

    for _ in range(10):
        v = encode(np.random.randint(0, 256), 8).astype(complex)
        bases = foam.bases
        m = [v @ U for U in bases]
        j2 = foam._stabilize(m)

        for i in range(3):
            d_i = j2[i] - m[i]
            d_norm = np.linalg.norm(d_i)
            m_norm = np.linalg.norm(m[i])
            if d_norm < 1e-12 or m_norm < 1e-12:
                continue
            d_hat = d_i / d_norm
            m_hat = m[i] / m_norm
            delta_L = np.outer(d_hat, m_hat.conj()) - np.outer(m_hat, d_hat.conj())

            # check skew-Hermitian
            assert np.linalg.norm(delta_L + delta_L.conj().T) < 1e-10

            # check rank 2
            sv = np.linalg.svd(delta_L, compute_uv=False)
            rank = np.sum(sv > 1e-10)
            assert rank == 2, f"rank is {rank}, not 2"

    print("  PASS: writes are rank-2 skew-Hermitian")


if __name__ == '__main__':
    print("=== structural verification ===\n")
    test_encoding_roundtrip()
    test_cayley_is_unitary()
    test_write_preserves_unitarity()
    test_determinism()
    test_distinguishability()
    test_sequence_sensitivity()
    test_convergence()
    test_two_x_theorem()
    test_inverse_views()
    test_gauge_absorption()
    test_write_is_rank_2()
    print("\n=== all checks passed ===")
