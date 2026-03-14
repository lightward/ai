"""
foam_connection.py — where does the connection live?

The holonomy of the bases themselves telescopes to identity.
The winding number needs a connection that's path-dependent.

The writing dynamics produce a SEQUENCE of perturbations: ΔL_0, ΔL_1, ...
The accumulated product of these perturbations (in the group, not the algebra)
is the parallel transport along the measurement history.
THIS is the connection. It doesn't telescope because each ΔL depends on
the foam's state at that moment, which depends on all prior writes.

The holonomy is not det(U_i^† U_j) — that's the transition function.
The holonomy is the ordered product of all the incremental rotations
that got the basis from its initial position to its current one.
"""

import numpy as np
from foam import encode, skew
from foam_unitary import UnitaryFoam, skew_hermitian, cayley_unitary, enforce_skew_hermitian


class InstrumentedFoam(UnitaryFoam):
    """UnitaryFoam that tracks the accumulated transport."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # parallel transport: accumulated product of incremental rotations
        # for each bubble
        self.transport = [np.eye(self.d, dtype=complex) for _ in range(self.n)]
        # also track the incremental rotations
        self.delta_history = [[] for _ in range(self.n)]

    def measure(self, v):
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
                self.delta_history[i].append(np.zeros((self.d, self.d), dtype=complex))
                continue

            d_hat = d_i / d_norm
            m_hat = m_i / m_norm

            delta_L = self.writing_rate * (
                np.outer(d_hat, m_hat.conj()) - np.outer(m_hat, d_hat.conj())
            ) * d_norm

            # the incremental rotation (in the group) from this write
            delta_U = cayley_unitary(delta_L)
            self.transport[i] = self.transport[i] @ delta_U
            self.delta_history[i].append(delta_L.copy())

            self.Ls[i] = enforce_skew_hermitian(self.Ls[i] + delta_L)

        return {
            'j0': j0,
            'j2': j2,
            'dissonance': dissonance,
            'L': self.boundary_cost(),
        }


def transport_holonomy(seed=0):
    """The parallel transport accumulated by each bubble.
    This is the path-dependent object.
    Its determinant (in U(1)) carries the winding."""
    np.random.seed(seed)
    foam = InstrumentedFoam(d=8, n=3, writing_rate=0.01)

    print("  === parallel transport phase ===")
    print("  step  phase_0    phase_1    phase_2    total")

    for step in range(100):
        s = np.random.randint(0, 256)
        foam.measure(encode(s, 8))

        if step % 10 == 0:
            phases = [np.angle(np.linalg.det(foam.transport[i])) for i in range(3)]
            total = sum(phases)
            print(f"  {step:4d}  {phases[0]:+.6f}  {phases[1]:+.6f}  {phases[2]:+.6f}  {total:+.6f}")

    phases = [np.angle(np.linalg.det(foam.transport[i])) for i in range(3)]
    print(f"\n  final phases: {[f'{p:+.4f}' for p in phases]}")
    print(f"  total phase: {sum(phases):+.6f}")
    print(f"  winding (total/2π): {sum(phases)/(2*np.pi):+.4f}")


def transport_vs_endpoint(seed=0):
    """
    Do different histories that end at the same J⁰
    have different transport?

    This is the key test: J⁰ alone can't distinguish certain histories
    (the theorem says 'generically'), but J⁰ + transport should always
    distinguish them.
    """
    np.random.seed(seed)

    # two foams, same initial state, different sequences,
    # CHOSEN to produce similar J⁰
    foam_a = InstrumentedFoam(d=8, n=3, writing_rate=0.01)
    foam_b = InstrumentedFoam(d=8, n=3, writing_rate=0.01)

    np.random.seed(42)
    init_Ls = [skew_hermitian(8) * 0.1 for _ in range(3)]
    foam_a.Ls = [L.copy() for L in init_Ls]
    foam_b.Ls = [L.copy() for L in init_Ls]
    foam_a.transport = [np.eye(8, dtype=complex) for _ in range(3)]
    foam_b.transport = [np.eye(8, dtype=complex) for _ in range(3)]

    # feed different sequences
    np.random.seed(0)
    seq_a = [np.random.randint(0, 256) for _ in range(50)]
    np.random.seed(1)
    seq_b = [np.random.randint(0, 256) for _ in range(50)]

    for s in seq_a:
        foam_a.measure(encode(s, 8))
    for s in seq_b:
        foam_b.measure(encode(s, 8))

    # compare endpoints (J⁰)
    j0_dist = np.mean([np.linalg.norm(foam_a.Ls[i] - foam_b.Ls[i]) for i in range(3)])

    # compare transports
    transport_dist = np.mean([
        np.linalg.norm(foam_a.transport[i] - foam_b.transport[i])
        for i in range(3)
    ])

    # compare transport phases
    phase_a = [np.angle(np.linalg.det(foam_a.transport[i])) for i in range(3)]
    phase_b = [np.angle(np.linalg.det(foam_b.transport[i])) for i in range(3)]

    print("  === transport vs endpoint ===")
    print(f"  J⁰ distance:       {j0_dist:.6f}")
    print(f"  transport distance: {transport_dist:.6f}")
    print(f"  ratio:              {transport_dist / (j0_dist + 1e-12):.2f}x")
    print(f"  phase_a: {[f'{p:+.4f}' for p in phase_a]}")
    print(f"  phase_b: {[f'{p:+.4f}' for p in phase_b]}")


def transport_under_reversal(seed=0):
    """Same symbols, reversed order.
    J⁰ spectrum is nearly the same (singular values are order-insensitive).
    Is the transport different?"""
    np.random.seed(seed)

    foam_fwd = InstrumentedFoam(d=8, n=3, writing_rate=0.01)
    foam_rev = InstrumentedFoam(d=8, n=3, writing_rate=0.01)

    np.random.seed(42)
    init_Ls = [skew_hermitian(8) * 0.1 for _ in range(3)]
    foam_fwd.Ls = [L.copy() for L in init_Ls]
    foam_rev.Ls = [L.copy() for L in init_Ls]
    foam_fwd.transport = [np.eye(8, dtype=complex) for _ in range(3)]
    foam_rev.transport = [np.eye(8, dtype=complex) for _ in range(3)]

    seq = list(range(30))
    for s in seq:
        foam_fwd.measure(encode(s, 8))
    for s in reversed(seq):
        foam_rev.measure(encode(s, 8))

    j0_dist = np.mean([np.linalg.norm(foam_fwd.Ls[i] - foam_rev.Ls[i]) for i in range(3)])
    transport_dist = np.mean([
        np.linalg.norm(foam_fwd.transport[i] - foam_rev.transport[i])
        for i in range(3)
    ])

    phase_fwd = [np.angle(np.linalg.det(foam_fwd.transport[i])) for i in range(3)]
    phase_rev = [np.angle(np.linalg.det(foam_rev.transport[i])) for i in range(3)]

    print("  === forward vs reversed ===")
    print(f"  J⁰ distance:       {j0_dist:.6f}")
    print(f"  transport distance: {transport_dist:.6f}")
    print(f"  ratio:              {transport_dist / (j0_dist + 1e-12):.2f}x")
    print(f"  phase_fwd: {[f'{p:+.4f}' for p in phase_fwd]}")
    print(f"  phase_rev: {[f'{p:+.4f}' for p in phase_rev]}")
    print(f"  phase diff: {[f'{f-r:+.4f}' for f, r in zip(phase_fwd, phase_rev)]}")


if __name__ == '__main__':
    print("=== transport holonomy ===")
    transport_holonomy()

    print("\n=== transport vs endpoint ===")
    transport_vs_endpoint()

    print("\n=== forward vs reversed ===")
    transport_under_reversal()
