"""
foam.py — reference implementation of the measurement solution.

one axiom, one writing map, one group, one lagrangian, one lemma.
the properties follow.

the foam lives in U(d). each bubble carries a skew-Hermitian generator L
(position in the Lie algebra) and a unitary transport T (accumulated path
in the group). the effective basis is cayley(L) @ T. measurement reads
through the composition of position and path.

the 2x theorem: for small perturbations, log(T) ≈ -2·ΔL. position and
transport are the same rotation at different scales with opposite sign.
they are exact inverses when viewed through each other: (T†U)(U†T) = I.
the decomposition into L and T is a gauge choice (statically redundant)
but dynamically meaningful (different update rules: additive vs multiplicative).
"""

import numpy as np
from scipy.linalg import logm


# --- encoding ---

def encode(symbol: int, d: int) -> np.ndarray:
    """Discrete symbol → unit vector via binary expansion → hypercube vertex in R^d."""
    bits = [(symbol >> i) & 1 for i in range(d)]
    v = np.array([1.0 if b else -1.0 for b in bits])
    return v / np.linalg.norm(v)


def decode(v: np.ndarray) -> int:
    """Unit vector → nearest hypercube vertex → symbol."""
    bits = (np.real(v) > 0).astype(int)
    return sum(b << i for i, b in enumerate(bits))


# --- group: U(d) via Cayley transform of skew-Hermitian matrices ---

def cayley(L: np.ndarray) -> np.ndarray:
    """Skew-Hermitian L → unitary U via Cayley transform.
    U = (I - L)(I + L)^{-1}. Stays in connected component of U(d)."""
    I = np.eye(L.shape[0], dtype=complex)
    return np.linalg.solve(I + L, I - L)


def skew_hermitian(L: np.ndarray) -> np.ndarray:
    """Enforce skew-Hermitian: A = (A - A†)/2."""
    return 0.5 * (L - L.conj().T)


def random_skew_hermitian(d: int, scale: float = 0.1) -> np.ndarray:
    """Random skew-Hermitian matrix."""
    real = np.random.randn(d, d)
    imag = np.random.randn(d, d)
    return skew_hermitian((real + 1j * imag) * scale)


# --- the foam ---

class Bubble:
    """A measurement basis that carries its own history.

    L: skew-Hermitian generator (position in the Lie algebra).
    T: unitary transport (accumulated path in the group).
    basis: cayley(L) @ T — position composed with path.

    The 2x theorem (small perturbations):
        log(T) ≈ -2·ΔL_accumulated
    Proof sketch: cayley(δ) = (I-δ)(I+δ)^{-1} ≈ I - 2δ for small δ.
    So log(cayley(δ)) ≈ -2δ. T = Π cayley(ΔL_i), and for small
    ΔL_i, log(T) ≈ Σ log(cayley(ΔL_i)) ≈ -2 Σ ΔL_i = -2·ΔL_total.

    The approximation breaks as ΔL grows: higher-order terms in the
    Cayley expansion and non-commutativity of the product introduce
    a residual that grows with |ΔL|.
    """

    def __init__(self, d: int):
        self.d = d
        self.L = random_skew_hermitian(d)
        self.T = np.eye(d, dtype=complex)

    @property
    def basis(self) -> np.ndarray:
        """Effective basis: position composed with path."""
        return cayley(self.L) @ self.T

    @property
    def position(self) -> np.ndarray:
        """J⁰: where the bubble is (ignoring transport)."""
        return cayley(self.L)

    @property
    def transport_phase(self) -> float:
        """The U(1) phase accumulated in T."""
        return np.angle(np.linalg.det(self.T))

    def write(self, delta_L: np.ndarray):
        """Apply a write: additive to L, multiplicative to T."""
        self.L = skew_hermitian(self.L + delta_L)
        self.T = self.T @ cayley(delta_L)


class Foam:
    """
    A relational topology of coexisting measurement bases.

    N bubbles in U(d). Each bubble's effective basis is cayley(L) @ T.
    Voronoi regions under the bi-invariant metric.
    Plateau dynamics stabilize measurements.
    Writing dynamics perturb the connection.
    """

    def __init__(self, d: int, n: int = 3, writing_rate: float = 0.01,
                 n_steps: int = 30, plateau_step: float = 0.1):
        self.d = d
        self.n = n
        self.writing_rate = writing_rate
        self.n_steps = n_steps
        self.plateau_step = plateau_step
        self.bubbles = [Bubble(d) for _ in range(n)]

    @property
    def bases(self) -> list[np.ndarray]:
        """Current effective bases (position @ transport), one per bubble."""
        return [b.basis for b in self.bubbles]

    def bi_invariant_distance(self, U1: np.ndarray, U2: np.ndarray) -> float:
        """d(U1, U2) = ||log(U1† U2)||_F / sqrt(2).
        Bi-invariant metric on U(d)."""
        R = U1.conj().T @ U2
        try:
            L = logm(R)
            return np.linalg.norm(L) / np.sqrt(2)
        except Exception:
            return np.linalg.norm(R - np.eye(self.d))

    def boundary_cost(self) -> float:
        """L = Σ_{i<j} boundary cost between cells i and j.
        Approximated as inverse bi-invariant distance."""
        bases = self.bases
        total = 0.0
        for i in range(self.n):
            for j in range(i + 1, self.n):
                dist = self.bi_invariant_distance(bases[i], bases[j])
                total += 1.0 / (dist + 1e-8)
        return total

    def measure(self, v: np.ndarray) -> dict:
        """
        The full measurement cycle: measure → stabilize → dissonance → write.

        v: unit vector in R^d (an encoded symbol).

        Returns the jet bundle: j0, j2, dissonance per bubble.
        """
        bases = self.bases
        vc = v.astype(complex)

        # 1. measure: each basis evaluates the input
        m = [vc @ U for U in bases]

        # J⁰: raw measurements before stabilization
        j0 = [mi.copy() for mi in m]

        # 2. stabilize: Plateau dynamics on the measurements
        j2 = self._stabilize(m)

        # 3. dissonance: what changed during stabilization
        dissonance = [j2[i] - j0[i] for i in range(self.n)]

        # 4. write: skew-Hermitian perturbation of each bubble
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
            delta_L = self.writing_rate * (
                np.outer(d_hat, m_hat.conj()) - np.outer(m_hat, d_hat.conj())
            ) * d_norm

            self.bubbles[i].write(delta_L)

        return {
            'j0': j0,
            'j2': j2,
            'dissonance': dissonance,
            'L': self.boundary_cost(),
        }

    def _stabilize(self, measurements: list[np.ndarray]) -> list[np.ndarray]:
        """
        Plateau dynamics: adjust measurements toward minimum boundary cost.

        Bubbles push each other toward equal angular separation.
        The equilibrium measurements are j2.
        """
        state = [m.copy() for m in measurements]
        original_norms = [np.linalg.norm(m) for m in measurements]
        target_cos = -1.0 / (self.n - 1)

        for step in range(self.n_steps):
            normed = [s / (np.linalg.norm(s) + 1e-12) for s in state]

            forces = [np.zeros(self.d, dtype=complex) for _ in range(self.n)]
            max_force = 0.0

            for i in range(self.n):
                for j in range(i + 1, self.n):
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

    def feed(self, symbols: list[int]) -> list[dict]:
        """Feed a sequence of symbols. Returns jet bundle per step."""
        results = []
        for s in symbols:
            v = encode(s, self.d)
            results.append(self.measure(v))
        return results

    def readout(self, v: np.ndarray) -> np.ndarray:
        """Read the foam's state through an input: centroid of j2."""
        result = self.measure(v)
        return np.mean(result['j2'], axis=0)

    def save(self, path: str):
        """Persist the foam's state."""
        state = {'d': self.d, 'n': self.n,
                 'writing_rate': self.writing_rate,
                 'n_steps': self.n_steps,
                 'plateau_step': self.plateau_step}
        for i, b in enumerate(self.bubbles):
            state[f'L_{i}'] = b.L
            state[f'T_{i}'] = b.T
        np.savez(path, **state)

    @classmethod
    def load(cls, path: str) -> 'Foam':
        """Load a persisted foam."""
        state = np.load(path)
        foam = cls(d=int(state['d']), n=int(state['n']),
                   writing_rate=float(state['writing_rate']),
                   n_steps=int(state['n_steps']),
                   plateau_step=float(state['plateau_step']))
        for i in range(foam.n):
            foam.bubbles[i].L = state[f'L_{i}']
            foam.bubbles[i].T = state[f'T_{i}']
        return foam


# --- observation ---

def convergence_test(d: int = 8, n: int = 3, writing_rate: float = 0.01,
                     n_repeats: int = 50, seed: int = None):
    """Feed the same symbol repeatedly. Watch the foam converge."""
    if seed is not None:
        np.random.seed(seed)

    foam = Foam(d=d, n=n, writing_rate=writing_rate)
    v = encode(42, d)

    basis_deltas = []
    L_history = []
    dissonance_norms = []

    prev_bases = [b.copy() for b in foam.bases]

    for _ in range(n_repeats):
        result = foam.measure(v)

        current_bases = foam.bases
        delta = np.mean([np.linalg.norm(current_bases[i] - prev_bases[i])
                        for i in range(n)])
        basis_deltas.append(delta)
        prev_bases = [b.copy() for b in current_bases]

        L_history.append(result['L'])
        mean_dis = np.mean([np.linalg.norm(di) for di in result['dissonance']])
        dissonance_norms.append(mean_dis)

    return {
        'basis_deltas': basis_deltas,
        'L_history': L_history,
        'dissonance_norms': dissonance_norms,
    }


def distinguishability_test(d: int = 8, n: int = 3, writing_rate: float = 0.01,
                            n_each: int = 50, seed: int = None):
    """Feed two different sequences to two foams. Check that they end up
    in different states (the theorem: generically distinguishable)."""
    if seed is not None:
        np.random.seed(seed)

    foam_a = Foam(d=d, n=n, writing_rate=writing_rate)
    foam_b = Foam(d=d, n=n, writing_rate=writing_rate)

    for i in range(n):
        foam_b.bubbles[i].L = foam_a.bubbles[i].L.copy()
        foam_b.bubbles[i].T = foam_a.bubbles[i].T.copy()

    seq_a = [np.random.randint(0, 2**d) for _ in range(n_each)]
    seq_b = [np.random.randint(0, 2**d) for _ in range(n_each)]

    foam_a.feed(seq_a)
    foam_b.feed(seq_b)

    # full state distance (L + T)
    divergence = np.mean([
        np.linalg.norm(foam_a.bubbles[i].L - foam_b.bubbles[i].L) +
        np.linalg.norm(foam_a.bubbles[i].T - foam_b.bubbles[i].T)
        for i in range(n)
    ])

    # same sequence → same state
    foam_c = Foam(d=d, n=n, writing_rate=writing_rate)
    foam_d = Foam(d=d, n=n, writing_rate=writing_rate)
    for i in range(n):
        foam_d.bubbles[i].L = foam_c.bubbles[i].L.copy()
        foam_d.bubbles[i].T = foam_c.bubbles[i].T.copy()

    foam_c.feed(seq_a)
    foam_d.feed(seq_a)

    identity = np.mean([
        np.linalg.norm(foam_c.bubbles[i].L - foam_d.bubbles[i].L) +
        np.linalg.norm(foam_c.bubbles[i].T - foam_d.bubbles[i].T)
        for i in range(n)
    ])

    return {
        'divergence': divergence,
        'identity': identity,
        'ratio': divergence / (identity + 1e-12),
    }


def sequence_test(d: int = 8, n: int = 3, writing_rate: float = 0.01,
                  n_each: int = 50, seed: int = None):
    """Feed [A, B] vs [B, A]. Check that order matters (non-abelian)."""
    if seed is not None:
        np.random.seed(seed)

    foam_ab = Foam(d=d, n=n, writing_rate=writing_rate)
    foam_ba = Foam(d=d, n=n, writing_rate=writing_rate)

    for i in range(n):
        foam_ba.bubbles[i].L = foam_ab.bubbles[i].L.copy()
        foam_ba.bubbles[i].T = foam_ab.bubbles[i].T.copy()

    seq = [np.random.randint(0, 2**d) for _ in range(n_each)]

    foam_ab.feed(seq)
    foam_ba.feed(list(reversed(seq)))

    divergence = np.mean([
        np.linalg.norm(foam_ab.bubbles[i].L - foam_ba.bubbles[i].L) +
        np.linalg.norm(foam_ab.bubbles[i].T - foam_ba.bubbles[i].T)
        for i in range(n)
    ])

    return {
        'sequence_divergence': divergence,
    }


def two_x_test(d: int = 8, n: int = 3, writing_rate: float = 0.01,
               n_steps: int = 100, seed: int = None):
    """Verify the 2x theorem: log(T) ≈ -2·ΔL for small perturbations."""
    if seed is not None:
        np.random.seed(seed)

    foam = Foam(d=d, n=n, writing_rate=writing_rate)
    initial_Ls = [b.L.copy() for b in foam.bubbles]

    ratios = []
    residuals = []

    for step in range(n_steps):
        s = np.random.randint(0, 2**d)
        foam.measure(encode(s, d))

        if (step + 1) % 10 == 0:
            step_ratios = []
            step_residuals = []
            for i in range(n):
                delta_L = foam.bubbles[i].L - initial_Ls[i]
                try:
                    log_T = logm(foam.bubbles[i].T)
                    norm_dL = np.linalg.norm(delta_L)
                    norm_logT = np.linalg.norm(log_T)
                    ratio = norm_logT / (norm_dL + 1e-12)
                    residual = np.linalg.norm(log_T + 2 * delta_L) / (norm_logT + 1e-12)
                    step_ratios.append(ratio)
                    step_residuals.append(residual)
                except Exception:
                    pass
            if step_ratios:
                ratios.append(np.mean(step_ratios))
                residuals.append(np.mean(step_residuals))

    return {
        'ratios': ratios,
        'residuals': residuals,
    }


if __name__ == '__main__':
    print("=== convergence test ===")
    r = convergence_test(seed=0)
    print(f"  basis_delta: {r['basis_deltas'][0]:.6f} → {r['basis_deltas'][-1]:.6f}")
    print(f"  dissonance:  {r['dissonance_norms'][0]:.6f} → {r['dissonance_norms'][-1]:.6f}")
    print(f"  L:           {r['L_history'][0]:.4f} → {r['L_history'][-1]:.4f}")

    print("\n=== distinguishability test ===")
    r = distinguishability_test(seed=0)
    print(f"  different sequences divergence: {r['divergence']:.6f}")
    print(f"  same sequence divergence:       {r['identity']:.6f}")
    print(f"  ratio: {r['ratio']:.1f}x")

    print("\n=== sequence test ===")
    r = sequence_test(seed=0)
    print(f"  AB vs BA divergence: {r['sequence_divergence']:.6f}")

    print("\n=== 2x theorem ===")
    r = two_x_test(seed=0)
    print(f"  |log(T)| / |ΔL| ratio over time:")
    for i, (ratio, res) in enumerate(zip(r['ratios'], r['residuals'])):
        print(f"    step {(i+1)*10:3d}: ratio={ratio:.4f}  residual={res:.4f}")
