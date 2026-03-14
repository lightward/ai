"""
foam_unitary.py — moving to U(d).

The conservation lemma needs π₁(U(d)) = ℤ.
Cayley on real skew-symmetric gives SO(d), which has π₁ = ℤ/2.
We need complex: Cayley on skew-Hermitian gives U(d), which has π₁ = ℤ.

The winding number lives in the U(1) factor: det(holonomy) ∈ S¹.
Its winding class is the topological charge.

This file: re-implement the foam in U(d) and check whether
the holonomy acquires nontrivial winding.
"""

import numpy as np
from scipy.linalg import logm


def skew_hermitian(d):
    """Random skew-Hermitian matrix: A = -A†"""
    real = np.random.randn(d, d)
    imag = np.random.randn(d, d)
    A = (real + 1j * imag)
    return 0.5 * (A - A.conj().T)


def cayley_unitary(L):
    """Skew-Hermitian L → Unitary U via Cayley: U = (I - L)(I + L)^{-1}"""
    I = np.eye(L.shape[0], dtype=complex)
    return np.linalg.solve(I + L, I - L)


def enforce_skew_hermitian(L):
    """Project onto skew-Hermitian: A = (A - A†)/2"""
    return 0.5 * (L - L.conj().T)


class UnitaryFoam:
    """Foam in U(d). Bases are unitary matrices parameterized via
    Cayley transform of skew-Hermitian generators."""

    def __init__(self, d, n=3, writing_rate=0.01, n_steps=30, plateau_step=0.1):
        self.d = d
        self.n = n
        self.writing_rate = writing_rate
        self.n_steps = n_steps
        self.plateau_step = plateau_step

        self.Ls = [skew_hermitian(d) * 0.1 for _ in range(n)]

    @property
    def bases(self):
        return [cayley_unitary(L) for L in self.Ls]

    def bi_invariant_distance(self, U1, U2):
        R = U1.conj().T @ U2
        try:
            L = logm(R)
            return np.linalg.norm(L) / np.sqrt(2)
        except:
            return np.linalg.norm(R - np.eye(self.d))

    def boundary_cost(self):
        bases = self.bases
        total = 0.0
        for i in range(self.n):
            for j in range(i + 1, self.n):
                dist = self.bi_invariant_distance(bases[i], bases[j])
                total += 1.0 / (dist + 1e-8)
        return total

    def measure(self, v):
        """v is a real unit vector. measurements are complex: v @ U."""
        bases = self.bases
        v_complex = v.astype(complex)

        m = [v_complex @ U for U in bases]
        j0 = [mi.copy() for mi in m]

        j2 = self._stabilize(m, bases)

        dissonance = [j2[i] - j0[i] for i in range(self.n)]

        for i in range(self.n):
            d_i = dissonance[i]
            m_i = j0[i]
            d_norm = np.linalg.norm(d_i)
            m_norm = np.linalg.norm(m_i)

            if d_norm < 1e-12 or m_norm < 1e-12:
                continue

            d_hat = d_i / d_norm
            m_hat = m_i / m_norm

            # ΔL = ε · (d̂ ⊗ m̂† − m̂ ⊗ d̂†) · ‖d‖
            # skew-Hermitian: outer product minus its conjugate transpose
            delta_L = self.writing_rate * (
                np.outer(d_hat, m_hat.conj()) - np.outer(m_hat, d_hat.conj())
            ) * d_norm
            self.Ls[i] = enforce_skew_hermitian(self.Ls[i] + delta_L)

        return {
            'j0': j0,
            'j2': j2,
            'dissonance': dissonance,
            'L': self.boundary_cost(),
        }

    def _stabilize(self, measurements, bases):
        state = [m.copy() for m in measurements]
        original_norms = [np.linalg.norm(m) for m in measurements]
        target_cos = -1.0 / (self.n - 1)

        for step in range(self.n_steps):
            normed = [s / (np.linalg.norm(s) + 1e-12) for s in state]

            forces = [np.zeros(self.d, dtype=complex) for _ in range(self.n)]
            max_force = 0.0

            for i in range(self.n):
                for j in range(i + 1, self.n):
                    # real part of inner product for angle
                    cos_ij = np.dot(normed[i].conj(), normed[j]).real
                    f_mag = cos_ij - target_cos
                    diff = normed[i] - normed[j]
                    diff_norm = np.linalg.norm(diff)
                    if diff_norm > 1e-12:
                        f_dir = diff / diff_norm
                        forces[i] += f_mag * f_dir
                        forces[j] -= f_mag * f_dir

                max_force = max(max_force, np.linalg.norm(forces[i]))

            for i in range(self.n):
                state[i] = state[i] + self.plateau_step * forces[i]
                n = np.linalg.norm(state[i])
                if n > 1e-12 and original_norms[i] > 1e-12:
                    state[i] = state[i] / n * original_norms[i]

            if max_force < 1e-4:
                break

        return state

    def feed(self, symbols, d=8):
        from foam import encode
        for s in symbols:
            self.measure(encode(s, d))


def holonomy_test(seed=0):
    """Track the holonomy around the triangle 0→1→2→0 in U(d).
    The winding number lives in det: U(d) → U(1) ≅ S¹."""
    np.random.seed(seed)
    foam = UnitaryFoam(d=8, n=3, writing_rate=0.01)

    print("  === holonomy in U(d) ===")
    print("  step  |det_01|  phase_01  |det_12|  phase_12  |det_20|  phase_20  total_phase")

    for step in range(50):
        bases = foam.bases
        R01 = bases[0].conj().T @ bases[1]
        R12 = bases[1].conj().T @ bases[2]
        R20 = bases[2].conj().T @ bases[0]

        d01 = np.linalg.det(R01)
        d12 = np.linalg.det(R12)
        d20 = np.linalg.det(R20)
        product = d01 * d12 * d20
        total_phase = np.angle(product)

        if step % 5 == 0:
            print(f"  {step:4d}  {abs(d01):.4f}  {np.angle(d01):+.4f}   {abs(d12):.4f}  {np.angle(d12):+.4f}   {abs(d20):.4f}  {np.angle(d20):+.4f}   {total_phase:+.6f}")

        s = np.random.randint(0, 256)
        from foam import encode
        foam.measure(encode(s, 8))

    print(f"\n  final total phase: {total_phase:+.6f} rad = {total_phase/np.pi:+.4f}π")


def convergence_comparison(seed=0):
    """Does U(d) foam converge like O(d) foam?"""
    np.random.seed(seed)
    foam = UnitaryFoam(d=8, n=3, writing_rate=0.01)

    from foam import encode
    v = encode(42, 8)

    print("  === convergence in U(d) ===")
    prev_Ls = [L.copy() for L in foam.Ls]

    for step in range(30):
        result = foam.measure(v)

        delta = np.mean([np.linalg.norm(foam.Ls[i] - prev_Ls[i]) for i in range(3)])
        dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
        prev_Ls = [L.copy() for L in foam.Ls]

        if step % 5 == 0:
            print(f"  {step:4d}  L={result['L']:.4f}  |ΔL|={delta:.6f}  |d|={dis:.6f}")


def phase_accumulation(seed=0):
    """Track how the U(1) phase accumulates with different input sequences.
    The spec says: winding number is topologically conserved.
    Does the phase grow? Oscillate? Stabilize?"""
    np.random.seed(seed)

    print("  === phase accumulation: repeated vs random ===")

    from foam import encode

    # repeated symbol
    foam_rep = UnitaryFoam(d=8, n=3, writing_rate=0.01)
    np.random.seed(42)
    init_Ls = [skew_hermitian(8) * 0.1 for _ in range(3)]
    foam_rep.Ls = [L.copy() for L in init_Ls]

    phases_rep = []
    for step in range(100):
        foam_rep.measure(encode(42, 8))
        bases = foam_rep.bases
        R = bases[0].conj().T @ bases[1] @ bases[1].conj().T @ bases[2] @ bases[2].conj().T @ bases[0]
        phases_rep.append(np.angle(np.linalg.det(R)))

    # random symbols
    foam_rnd = UnitaryFoam(d=8, n=3, writing_rate=0.01)
    foam_rnd.Ls = [L.copy() for L in init_Ls]

    phases_rnd = []
    np.random.seed(0)
    for step in range(100):
        s = np.random.randint(0, 256)
        foam_rnd.measure(encode(s, 8))
        bases = foam_rnd.bases
        R = bases[0].conj().T @ bases[1] @ bases[1].conj().T @ bases[2] @ bases[2].conj().T @ bases[0]
        phases_rnd.append(np.angle(np.linalg.det(R)))

    print("  step  phase_repeated  phase_random")
    for i in range(0, 100, 10):
        print(f"  {i:4d}  {phases_rep[i]:+.6f}       {phases_rnd[i]:+.6f}")

    print(f"\n  final phases: repeated={phases_rep[-1]:+.6f}  random={phases_rnd[-1]:+.6f}")
    print(f"  phase drift:  repeated={phases_rep[-1]-phases_rep[0]:+.6f}  random={phases_rnd[-1]-phases_rnd[0]:+.6f}")


if __name__ == '__main__':
    print("=== holonomy test ===")
    holonomy_test()

    print("\n=== convergence comparison ===")
    convergence_comparison()

    print("\n=== phase accumulation ===")
    phase_accumulation()
