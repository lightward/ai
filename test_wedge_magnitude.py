"""
Is √2/2 the perpendicularity cost?

The write form is d̂ ∧ m̂. The magnitude of this wedge product is
sin(θ) where θ is the angle between d and m. For two random unit
vectors in R^k (the observer's R³ slice), what is E[sin(θ)]?

If E[sin(θ)] ≈ √2/2 ≈ 0.707, then the perpendicularity cost
might simply be the expected geometric efficiency of the wedge product
over random measurement-dissonance pairs.

Also: the foam's d and m are NOT random — d is the dissonance (j2 - m)
and m is the measurement, so they have a specific angular relationship
determined by the stabilization. Measure the actual distribution of
angles between d and m, and compare E[sin(θ)] to the perpendicularity cost.
"""

import numpy as np
from scipy.linalg import expm
from scipy.special import gamma


def expected_sin_random(k):
    """E[sin(θ)] for two random unit vectors in R^k.

    The angle θ between two random unit vectors in R^k has
    pdf: p(θ) = B(k/2-1/2, 1/2)^{-1} · sin^{k-2}(θ), θ ∈ [0,π]
    where B is the Beta function.

    E[sin(θ)] = ∫₀^π sin(θ) · p(θ) dθ = ∫₀^π sin^{k-1}(θ) / B(k/2-1/2, 1/2) dθ

    For large k: E[sin(θ)] → 1 (vectors are nearly orthogonal in high dim).
    For k=2: E[sin(θ)] = 2/π ≈ 0.637
    For k=3: E[sin(θ)] = π/4 ≈ 0.785
    """
    # numerical integration
    theta = np.linspace(0, np.pi, 10000)
    dtheta = theta[1] - theta[0]
    pdf = np.sin(theta)**(k-2)
    pdf /= np.sum(pdf) * dtheta  # normalize
    return np.sum(np.sin(theta) * pdf) * dtheta


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


def random_unitary(d, rng):
    return expm(skew_hermitian(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))))


def compute_L(bases):
    N = len(bases)
    d = bases[0].shape[0]
    L = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            L += np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro')
    return L


def run_and_measure_angles(d, N, eps, n_steps, rng_seed=42):
    """Run foam and measure the angle between d and m at each step."""
    rng = np.random.default_rng(rng_seed)
    bases = [random_unitary(d, rng) for _ in range(N)]

    Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
    P = Q[:, :3].T

    input_rng = np.random.default_rng(rng_seed + 1000)

    L_history = []
    angles = []  # angle between d and m in R³ for each observer at each step
    sin_angles = []  # sin(θ) = magnitude of the wedge product

    for t in range(n_steps):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)

        all_m = []
        all_m_hat = []
        for k in range(N):
            mk = np.real(P @ (v @ bases[k]))
            n_val = np.linalg.norm(mk)
            all_m.append(mk)
            all_m_hat.append(mk / n_val if n_val > 1e-12 else mk)

        step_angles = []
        step_sins = []
        for i in range(N):
            m = all_m[i]
            m_norm = np.linalg.norm(m)
            if m_norm < 1e-12:
                continue
            m_hat = m / m_norm
            others = [all_m_hat[k] for k in range(N) if k != i]
            centroid = np.mean(others, axis=0)
            target = m_hat - centroid
            t_norm = np.linalg.norm(target)
            if t_norm > 1e-12:
                target = target / t_norm
            j2 = target * m_norm
            d_vec = j2 - m
            d_norm = np.linalg.norm(d_vec)
            if d_norm < 1e-12:
                continue
            d_hat = d_vec / d_norm

            # angle between d_hat and m_hat (in R³)
            cos_theta = np.clip(np.dot(d_hat, m_hat), -1, 1)
            theta = np.arccos(np.abs(cos_theta))
            sin_theta = np.sin(theta)

            step_angles.append(theta)
            step_sins.append(sin_theta)

            # update basis
            d_full = P.T @ d_hat
            m_full = P.T @ m_hat
            dL = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
            dL = skew_hermitian(dL)
            bases[i] = bases[i] @ cayley(dL)

        if step_angles:
            angles.append(np.mean(step_angles))
            sin_angles.append(np.mean(step_sins))

        L_history.append(compute_L(bases))

    return L_history, angles, sin_angles


if __name__ == "__main__":
    print("=" * 70)
    print("WEDGE MAGNITUDE AND THE PERPENDICULARITY COST")
    print("=" * 70)
    print()

    # ── Theoretical E[sin(θ)] for random vectors ──
    print("Theoretical E[sin(θ)] for random unit vectors in R^k:")
    for k in [2, 3, 4, 5, 6, 10, 20]:
        es = expected_sin_random(k)
        print(f"  k={k:2d}: E[sin(θ)] = {es:.4f}")
    print(f"  k→∞:  E[sin(θ)] → 1.0000")
    print(f"  Note: √2/2 = {np.sqrt(2)/2:.4f}")
    print()

    # ── Actual angles in the foam ──
    print("Actual d-m angle distribution in the foam:")
    print("-" * 50)
    for d_val in [4, 6, 8, 10]:
        L_h, angles, sins = run_and_measure_angles(d=d_val, N=3, eps=0.1, n_steps=3000)
        n = len(angles)
        tail = int(0.7 * n)

        early_sin = np.mean(sins[:int(0.2*n)])
        sat_sin = np.mean(sins[tail:])
        sat_angle = np.mean(angles[tail:])

        L_sat = np.mean(L_h[tail:])
        L_max = 3 * 2 * np.sqrt(d_val)

        print(f"  d={d_val}, N=3:")
        print(f"    E[sin(θ)] early:   {early_sin:.4f}")
        print(f"    E[sin(θ)] sat:     {sat_sin:.4f}")
        print(f"    E[θ] sat:          {np.degrees(sat_angle):.1f}°")
        print(f"    L_sat/L_max:       {L_sat/L_max:.4f}")
        print(f"    E[sin(θ)]² sat:    {sat_sin**2:.4f}")
    print()

    # ── Comparison ──
    print("KEY COMPARISON:")
    print(f"  √2/2 = {np.sqrt(2)/2:.4f}")
    print(f"  E[sin(θ)] for random vectors in R³ = {expected_sin_random(3):.4f}")
    print(f"  If the foam's d-m angles match random R³ vectors,")
    print(f"  the perpendicularity cost IS the expected wedge magnitude.")
    print()
    print("  If E[sin(θ)]_foam ≠ E[sin(θ)]_random, the dynamics")
    print("  constrain the angle beyond geometric randomness.")
