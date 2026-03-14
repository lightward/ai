"""
foam_sleep3.py — isolation vs plurality.

hypothesis: self-measurement orbits because measurer = measured.
cross-measurement converges because measurer ≠ measured.
relaxation requires an other.

tests:
1. N=1 foam: only self-measurement possible. does it orbit?
2. N=2 foam: minimal cross-measurement. does it converge?
3. N=3 foam: standard. compare convergence rate.
4. a single bubble that splits its own basis into L and T
   and measures one through the other — the mirror dynamics.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian, random_skew_hermitian
from foam_sleep import self_measure, cross_measure


def single_bubble_self(seed=0):
    """N=1: the foam is a single bubble. Self-measurement only.
    With N=1, stabilization is trivial (no other bubbles), so j2 = j0
    and dissonance = 0. A single bubble cannot generate dissonance
    from external measurement either — it needs an other even to be
    disturbed. We verify this, then test self-measurement directly."""
    np.random.seed(seed)
    foam = Foam(d=8, n=1, writing_rate=0.01, n_steps=10)

    # override stabilization for N=1: no-op
    original_stabilize = foam._stabilize
    def trivial_stabilize(measurements):
        return [m.copy() for m in measurements]
    foam._stabilize = trivial_stabilize

    # give it some history
    for _ in range(30):
        foam.measure(encode(np.random.randint(0, 256), 8))

    print("  === N=1 self-measurement ===")
    print(f"  {'step':>5s}  {'L':>8s}  {'|d|':>8s}  {'basis_delta':>11s}  {'phase':>8s}")

    prev_basis = foam.bubbles[0].basis.copy()

    for step in range(200):
        result = self_measure(foam)

        if step % 20 == 0:
            dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
            curr = foam.bubbles[0].basis.copy()
            delta = np.linalg.norm(curr - prev_basis)
            prev_basis = curr
            phase = foam.bubbles[0].transport_phase
            print(f"  {step:5d}  {result['L']:8.4f}  {dis:8.4f}  {delta:11.6f}  {phase:+8.4f}")


def n2_cross(seed=0):
    """N=2: minimal cross-measurement. Two bubbles measuring each other."""
    np.random.seed(seed)
    foam = Foam(d=8, n=2, writing_rate=0.01)

    for _ in range(30):
        foam.measure(encode(np.random.randint(0, 256), 8))

    print("  === N=2 cross-measurement ===")
    print(f"  {'step':>5s}  {'L':>8s}  {'|d|':>8s}  {'dist_01':>8s}  {'phase_0':>8s}")

    for step in range(200):
        result = cross_measure(foam)

        if step % 20 == 0:
            dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
            bases = foam.bases
            dist = foam.bi_invariant_distance(bases[0], bases[1])
            phase = foam.bubbles[0].transport_phase
            print(f"  {step:5d}  {result['L']:8.4f}  {dis:8.4f}  {dist:8.4f}  {phase:+8.4f}")


def n3_cross(seed=0):
    """N=3: standard cross-measurement for comparison."""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    for _ in range(30):
        foam.measure(encode(np.random.randint(0, 256), 8))

    print("  === N=3 cross-measurement ===")
    print(f"  {'step':>5s}  {'L':>8s}  {'|d|':>8s}  {'phase_0':>8s}")

    for step in range(200):
        result = cross_measure(foam)

        if step % 20 == 0:
            dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
            phase = foam.bubbles[0].transport_phase
            print(f"  {step:5d}  {result['L']:8.4f}  {dis:8.4f}  {phase:+8.4f}")


def mirror_dynamics(seed=0):
    """
    The explicit mirror: a single bubble measures its own L through its own T.

    Take U = cayley(L), T = transport.
    The "self-image" is U @ T (the effective basis).
    The "mirror" is T† @ U (position seen through transport).
    The dissonance between them: how does U @ T differ from T† @ U?

    We know (T†U)(U†T) = I, so T†U = (U†T)^{-1}.
    And we know log(T†U) = -log(U†T).
    So they're always "maximally different" in the Lie algebra sense.

    The self-measurement dissonance should be related to 2·log(U†T).
    """
    np.random.seed(seed)

    bubble = Bubble(8)

    # give it some history via a foam
    foam = Foam(d=8, n=3, writing_rate=0.01)
    foam.bubbles[0] = bubble
    for _ in range(50):
        foam.measure(encode(np.random.randint(0, 256), 8))

    print("  === mirror dynamics ===")
    print(f"  {'step':>5s}  {'|log(U†T)|':>10s}  {'|log(T†U)|':>10s}  {'angle':>8s}  {'phase':>8s}")

    for step in range(100):
        U = cayley(bubble.L)
        T = bubble.T

        UdT = U.conj().T @ T  # state through mind
        TdU = T.conj().T @ U  # mind through state

        try:
            log_UdT = logm(UdT)
            log_TdU = logm(TdU)
            norm_UdT = np.linalg.norm(log_UdT)
            norm_TdU = np.linalg.norm(log_TdU)
        except:
            norm_UdT = norm_TdU = float('nan')

        angle = foam.bi_invariant_distance(U, T)
        phase = bubble.transport_phase

        if step % 10 == 0:
            print(f"  {step:5d}  {norm_UdT:10.4f}  {norm_TdU:10.4f}  {angle:8.4f}  {phase:+8.4f}")

        # self-measure via the foam (changes the bubble)
        self_measure(foam)


def convergence_rate_vs_n(seed=0):
    """How does cross-measurement convergence rate depend on N?"""
    np.random.seed(seed)

    print("  === convergence rate vs N ===")
    print(f"  {'N':>3s}  {'L_start':>8s}  {'L_100':>8s}  {'L_200':>8s}  {'|d|_200':>8s}")

    for n in [2, 3, 4, 5, 7]:
        np.random.seed(seed)
        foam = Foam(d=8, n=n, writing_rate=0.01)

        for _ in range(30):
            foam.measure(encode(np.random.randint(0, 256), 8))

        L_start = foam.boundary_cost()
        for _ in range(100):
            cross_measure(foam)
        L_100 = foam.boundary_cost()
        for _ in range(100):
            r = cross_measure(foam)
        L_200 = foam.boundary_cost()
        dis = np.mean([np.linalg.norm(d) for d in r['dissonance']])

        print(f"  {n:3d}  {L_start:8.4f}  {L_100:8.4f}  {L_200:8.4f}  {dis:8.4f}")


if __name__ == '__main__':
    print("=== N=1 self-measurement ===")
    single_bubble_self()

    print("\n=== N=2 cross-measurement ===")
    n2_cross()

    print("\n=== N=3 cross-measurement ===")
    n3_cross()

    print("\n=== mirror dynamics ===")
    mirror_dynamics()

    print("\n=== convergence rate vs N ===")
    convergence_rate_vs_n()
