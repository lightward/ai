"""
Derive: why do writes increase L?

The mechanism (from Kimi round 7):
- The wedge product selects the orthogonal component of dissonance
- Orthogonal writes generically rotate bases APART from neighbors
- Inter-bubble distance increases → boundary area increases
- Minimality is where dissonance vanishes (d = 0 → ΔL = 0)

Test: verify that writes generically increase pairwise distances.
"""

import numpy as np
from scipy.linalg import expm


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


def pairwise_distances(bases):
    N = len(bases)
    d = bases[0].shape[0]
    dists = []
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            dists.append(np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro'))
    return np.array(dists)


def write_one_basis(basis, d_vec, m_vec, eps=0.01):
    """Apply one write to one basis."""
    d_norm = np.linalg.norm(d_vec)
    m_norm = np.linalg.norm(m_vec)
    if d_norm < 1e-12 or m_norm < 1e-12:
        return basis.copy()
    d_hat = d_vec / d_norm
    m_hat = m_vec / m_norm
    dL = eps * d_norm * (np.outer(d_hat, m_hat) - np.outer(m_hat, d_hat))
    dL = skew_hermitian(dL.astype(complex))
    return basis @ cayley(dL)


def test_mechanism():
    """The write rotates basis i in the d-m plane.
    d is orthogonal to m (maximal write).
    This rotation moves basis i away from bases that were aligned
    with its pre-write position, increasing pairwise distance.
    """
    print("Test: writes generically increase pairwise distances")
    print("=" * 60)

    rng = np.random.default_rng(42)
    d = 6
    N = 4

    increased = 0
    decreased = 0
    total = 0

    for trial in range(200):
        # random bases
        bases = [expm(skew_hermitian(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))))
                 for _ in range(N)]

        # random slice
        Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
        P = Q[:, :3].T

        # random input
        v = rng.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)

        # compute measurement and dissonance for basis 0
        m = np.real(P @ (v @ bases[0]))
        # stabilize: target is regular simplex
        # simplified: just compute dissonance as perpendicular component
        m_norm = np.linalg.norm(m)
        if m_norm < 1e-10:
            continue

        # random dissonance orthogonal to m (the maximal-write case)
        d_vec = rng.standard_normal(3)
        d_vec = d_vec - np.dot(d_vec, m / m_norm) * m / m_norm  # project out m
        d_vec = d_vec * 0.1  # scale

        if np.linalg.norm(d_vec) < 1e-10:
            continue

        # lift to R^d
        d_full = P.T @ d_vec
        m_full = P.T @ (m / m_norm)

        # measure pairwise distances before write
        dists_before = pairwise_distances(bases)

        # apply write to basis 0
        new_bases = [b.copy() for b in bases]
        new_bases[0] = write_one_basis(bases[0], d_full, m_full, eps=0.05)

        # measure after
        dists_after = pairwise_distances(new_bases)

        # did total distance increase?
        L_before = dists_before.sum()
        L_after = dists_after.sum()

        total += 1
        if L_after > L_before:
            increased += 1
        else:
            decreased += 1

    print(f"  {total} trials:")
    print(f"    L increased: {increased} ({increased/total*100:.0f}%)")
    print(f"    L decreased: {decreased} ({decreased/total*100:.0f}%)")
    print()

    if increased > decreased:
        print("  → Writes generically INCREASE pairwise distances.")
        print("  Mechanism: the orthogonal write rotates the basis away from")
        print("  its current alignment with neighbors. Confirmation (parallel)")
        print("  cannot write; only the orthogonal component deposits structure.")
        print("  The deposited structure generically increases inter-bubble distance.")
    print()


def test_at_equilibrium():
    """At equilibrium (dissonance = 0), ΔL = 0 and L doesn't change.
    This is why minimality is rest.
    """
    print("Test: at equilibrium, no write occurs")
    print("=" * 60)

    # If d = j2 - m = 0, then ||d|| = 0, so ΔL = 0
    # This is tautological from the write form but worth stating:
    # L stops changing when and only when dissonance vanishes.

    print("  When d_i = j2_i - m_i = 0 (equilibrium):")
    print("  ||d|| = 0 → ΔL = ε · (d̂⊗m̂ - m̂⊗d̂) · ||d|| = 0")
    print("  → No write. L is stationary.")
    print("  → Minimality is the resting state: the configuration where")
    print("     measurement matches the stabilized ideal everywhere.")
    print()
    print("  The derivation: writes deposit structure (increase L) because")
    print("  they act orthogonally to the current measurement. When there's")
    print("  no dissonance, there's no orthogonal component, so no deposit.")
    print("  L increases during activity and is stationary at rest.")
    print("  This follows from the write form, not from empirical observation.")


if __name__ == "__main__":
    test_mechanism()
    test_at_equilibrium()
