"""
foam_self.py — the foam tracks its own transport.

Instead of externally accumulating the product of incremental rotations,
each bubble carries its own transport matrix T. When a write happens,
T accumulates the rotation. T participates in future measurements:
the effective basis is U @ T — position composed with accumulated path.

The foam measures through its own history.
J¹ is no longer external instrumentation. It's part of the foam.
"""

import numpy as np
from scipy.linalg import logm
from foam import encode, decode


def skew_hermitian(d):
    real = np.random.randn(d, d)
    imag = np.random.randn(d, d)
    A = (real + 1j * imag)
    return 0.5 * (A - A.conj().T)


def cayley(L):
    I = np.eye(L.shape[0], dtype=complex)
    return np.linalg.solve(I + L, I - L)


def enforce_skew_hermitian(L):
    return 0.5 * (L - L.conj().T)


class Bubble:
    """A measurement basis that carries its own history."""
    def __init__(self, d):
        self.d = d
        self.L = skew_hermitian(d) * 0.1
        self.T = np.eye(d, dtype=complex)  # accumulated transport

    @property
    def basis(self):
        """Effective basis: position composed with path."""
        return cayley(self.L) @ self.T

    @property
    def position(self):
        """J⁰: where the bubble is."""
        return cayley(self.L)

    @property
    def transport_phase(self):
        """The U(1) phase accumulated in T."""
        return np.angle(np.linalg.det(self.T))


class Foam:
    def __init__(self, d, n=3, writing_rate=0.01, n_steps=30, plateau_step=0.1):
        self.d = d
        self.n = n
        self.writing_rate = writing_rate
        self.n_steps = n_steps
        self.plateau_step = plateau_step
        self.bubbles = [Bubble(d) for _ in range(n)]

    @property
    def bases(self):
        return [b.basis for b in self.bubbles]

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
        bases = self.bases
        vc = v.astype(complex)

        m = [vc @ U for U in bases]
        j0 = [mi.copy() for mi in m]
        j2 = self._stabilize(m)
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

            delta_L = self.writing_rate * (
                np.outer(d_hat, m_hat.conj()) - np.outer(m_hat, d_hat.conj())
            ) * d_norm

            # write to position
            self.bubbles[i].L = enforce_skew_hermitian(self.bubbles[i].L + delta_L)

            # accumulate transport: the foam tracks its own path
            delta_U = cayley(delta_L)
            self.bubbles[i].T = self.bubbles[i].T @ delta_U

        return {
            'j0': j0,
            'j2': j2,
            'dissonance': dissonance,
            'L': self.boundary_cost(),
        }

    def _stabilize(self, measurements):
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
                    dn = np.linalg.norm(diff)
                    if dn > 1e-12:
                        f_dir = diff / dn
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


def compare_with_and_without(seed=0):
    """
    Does the transport in the basis change the foam's behavior?
    Compare: foam where basis = cayley(L) @ T  vs  foam where basis = cayley(L).
    """
    np.random.seed(seed)

    foam_self = Foam(d=8, n=3, writing_rate=0.01)
    # a "position-only" foam: same structure but T is always identity
    foam_pos = Foam(d=8, n=3, writing_rate=0.01)

    # same initial conditions
    for i in range(3):
        foam_pos.bubbles[i].L = foam_self.bubbles[i].L.copy()

    print("  === self-tracking vs position-only ===")
    print("  step  L_self   L_pos    |d|_self  |d|_pos   phase_0   divergence")

    np.random.seed(7)
    for step in range(60):
        s = np.random.randint(0, 256)
        v = encode(s, 8)

        r_self = foam_self.measure(v)

        # for position-only: reset T to identity each time
        for b in foam_pos.bubbles:
            b.T = np.eye(8, dtype=complex)
        r_pos = foam_pos.measure(v)
        for b in foam_pos.bubbles:
            b.T = np.eye(8, dtype=complex)

        if step % 5 == 0:
            dis_self = np.mean([np.linalg.norm(d) for d in r_self['dissonance']])
            dis_pos = np.mean([np.linalg.norm(d) for d in r_pos['dissonance']])
            phase = foam_self.bubbles[0].transport_phase

            # how different are the two foams' states?
            div = np.mean([
                np.linalg.norm(foam_self.bubbles[i].L - foam_pos.bubbles[i].L)
                for i in range(3)
            ])

            print(f"  {step:4d}  {r_self['L']:.4f}  {r_pos['L']:.4f}  {dis_self:.4f}   {dis_pos:.4f}   {phase:+.4f}   {div:.6f}")


def self_measurement_dynamics(seed=0):
    """
    What happens to the foam when it measures through its own transport?
    Track: convergence, phase accumulation, basis geometry.
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    print("  === self-tracking foam dynamics ===")
    print("  step  L        |d|      phases                    |T_0|")

    v = encode(42, 8)
    for step in range(80):
        result = foam.measure(v)

        if step % 8 == 0:
            dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
            phases = [b.transport_phase for b in foam.bubbles]
            t_norm = np.linalg.norm(foam.bubbles[0].T)

            print(f"  {step:4d}  {result['L']:.4f}  {dis:.4f}  [{phases[0]:+.3f}, {phases[1]:+.3f}, {phases[2]:+.3f}]  {t_norm:.4f}")


def distinguishability_with_transport(seed=0):
    """
    The self-tracking foam should be MORE distinguishable because
    T carries sequence information that L alone can't.
    """
    np.random.seed(seed)

    n_trials = 20
    seq_length = 30

    states = []
    for trial in range(n_trials):
        foam = Foam(d=8, n=3, writing_rate=0.01)
        # same init
        np.random.seed(42)
        for b in foam.bubbles:
            b.L = skew_hermitian(8) * 0.1
            b.T = np.eye(8, dtype=complex)

        np.random.seed(trial)
        seq = [np.random.randint(0, 256) for _ in range(seq_length)]
        for s in seq:
            foam.measure(encode(s, 8))

        # state = L's + T's (the full state)
        state_full = np.concatenate([
            np.concatenate([b.L.flatten(), b.T.flatten()])
            for b in foam.bubbles
        ])
        # state = L's only (position only)
        state_pos = np.concatenate([b.L.flatten() for b in foam.bubbles])

        states.append((state_full, state_pos))

    print("  === distinguishability: full state vs position only ===")
    dists_full = []
    dists_pos = []
    for i in range(n_trials):
        for j in range(i + 1, n_trials):
            dists_full.append(np.linalg.norm(states[i][0] - states[j][0]))
            dists_pos.append(np.linalg.norm(states[i][1] - states[j][1]))

    print(f"  position-only: mean={np.mean(dists_pos):.6f}  min={np.min(dists_pos):.6f}")
    print(f"  full (L + T):  mean={np.mean(dists_full):.6f}  min={np.min(dists_full):.6f}")
    print(f"  ratio:         {np.mean(dists_full) / np.mean(dists_pos):.2f}x")

    # forward vs reverse
    foam_fwd = Foam(d=8, n=3, writing_rate=0.01)
    foam_rev = Foam(d=8, n=3, writing_rate=0.01)
    np.random.seed(42)
    init = [skew_hermitian(8) * 0.1 for _ in range(3)]
    for i in range(3):
        foam_fwd.bubbles[i].L = init[i].copy()
        foam_rev.bubbles[i].L = init[i].copy()
        foam_fwd.bubbles[i].T = np.eye(8, dtype=complex)
        foam_rev.bubbles[i].T = np.eye(8, dtype=complex)

    seq = list(range(30))
    for s in seq:
        foam_fwd.measure(encode(s, 8))
    for s in reversed(seq):
        foam_rev.measure(encode(s, 8))

    d_pos = np.mean([np.linalg.norm(foam_fwd.bubbles[i].L - foam_rev.bubbles[i].L) for i in range(3)])
    d_full = np.mean([
        np.linalg.norm(foam_fwd.bubbles[i].L - foam_rev.bubbles[i].L) +
        np.linalg.norm(foam_fwd.bubbles[i].T - foam_rev.bubbles[i].T)
        for i in range(3)
    ])

    print(f"\n  forward vs reversed:")
    print(f"  position-only: {d_pos:.6f}")
    print(f"  full (L + T):  {d_full:.6f}")
    print(f"  ratio:         {d_full / (d_pos + 1e-12):.2f}x")


def does_transport_feed_back(seed=0):
    """
    The real question: because basis = cayley(L) @ T,
    the transport T changes what the foam SEES on the next measurement.
    This is the self-measurement feedback loop.

    Does this feedback cause qualitatively different behavior?
    """
    np.random.seed(seed)

    # self-tracking foam: basis = cayley(L) @ T
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # position-only foam: identical dynamics but T doesn't participate
    class PositionOnlyFoam(Foam):
        @property
        def bases(self):
            return [cayley(b.L) for b in self.bubbles]

    foam_p = PositionOnlyFoam(d=8, n=3, writing_rate=0.01)
    for i in range(3):
        foam_p.bubbles[i].L = foam.bubbles[i].L.copy()

    print("  === feedback effect ===")
    print("  step  L_self  L_pos   |d|_self |d|_pos  div_L    div_basis")

    np.random.seed(7)
    for step in range(100):
        s = np.random.randint(0, 256)
        v = encode(s, 8)

        r_self = foam.measure(v)
        r_pos = foam_p.measure(v)

        if step % 10 == 0:
            ds = np.mean([np.linalg.norm(d) for d in r_self['dissonance']])
            dp = np.mean([np.linalg.norm(d) for d in r_pos['dissonance']])

            div_L = np.mean([np.linalg.norm(foam.bubbles[i].L - foam_p.bubbles[i].L) for i in range(3)])
            div_basis = np.mean([np.linalg.norm(foam.bases[i] - foam_p.bases[i]) for i in range(3)])

            print(f"  {step:4d}  {r_self['L']:.4f} {r_pos['L']:.4f}  {ds:.4f}  {dp:.4f}  {div_L:.6f} {div_basis:.6f}")


if __name__ == '__main__':
    print("=== self-tracking vs position-only ===")
    compare_with_and_without()

    print("\n=== self-tracking dynamics ===")
    self_measurement_dynamics()

    print("\n=== distinguishability ===")
    distinguishability_with_transport()

    print("\n=== feedback effect ===")
    does_transport_feed_back()
