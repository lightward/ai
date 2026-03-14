"""
foam_sleep.py — two candidate relaxation dynamics.

1. self-measurement: feed the foam's readout back as input.
   one self weighing its own coherence. directed, closed loop.

2. cross-measurement: bubbles measure each other directly.
   no external input. aimless. inter-bubble geometry drives dissonance.

question: which one relaxes the foam (decreases L)?
does either preserve the 2x theorem?
what does each one converge to?
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, decode, cayley, skew_hermitian, random_skew_hermitian


def self_measure(foam):
    """
    The foam measures itself: readout becomes input.

    Take the centroid of the current bases (the foam's "self-image"),
    project to a unit vector, and feed it back as input.
    """
    bases = foam.bases
    # the foam's self-image: mean of its effective bases
    centroid = np.mean(bases, axis=0)
    # extract a vector from it: first column (arbitrary but consistent)
    v = centroid[:, 0]
    v = v / (np.linalg.norm(v) + 1e-12)
    # make it real for the encoding interface
    # (the foam will cast to complex internally)
    return foam.measure(np.real(v))


def cross_measure(foam):
    """
    Bubbles measure each other directly. No external input.

    For each pair (i, j): bubble i evaluates bubble j's basis.
    The "measurement" is basis_i† @ basis_j — the transition matrix.
    The dissonance is how far that transition is from the target
    angular separation. The write comes from this inter-bubble dissonance.

    This is stabilization running on bases, not on measurements of input.
    """
    bases = foam.bases
    n = foam.n
    target_cos = -1.0 / (n - 1)

    total_dissonance = [np.zeros(foam.d, dtype=complex) for _ in range(n)]

    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            # bubble i looks at bubble j through its own basis
            # transition: what rotation takes i's frame to j's frame?
            R_ij = bases[i].conj().T @ bases[j]

            # extract a "measurement vector" — the diagonal of R_ij
            # captures how each dimension of i maps to j
            m_ij = np.diag(R_ij)

            # the "target" is the angular separation that Plateau wants
            # for N bubbles: cos θ = -1/(N-1)
            # current: trace(R_ij) / d = mean of eigenvalue real parts
            cos_ij = np.trace(R_ij).real / foam.d

            # dissonance: how far from target
            d_scalar = cos_ij - target_cos
            # direction: the off-diagonal structure of R_ij
            off_diag = R_ij - np.diag(np.diag(R_ij))
            d_vec = off_diag[:, 0]  # project to a vector
            d_norm = np.linalg.norm(d_vec)

            if d_norm > 1e-12:
                total_dissonance[i] += d_scalar * d_vec / d_norm

    # write from accumulated cross-dissonance
    for i in range(n):
        d_i = total_dissonance[i]
        d_norm = np.linalg.norm(d_i)
        if d_norm < 1e-12:
            continue

        # use the bubble's own basis column as the "measurement direction"
        m_i = bases[i][:, 0]
        m_norm = np.linalg.norm(m_i)
        if m_norm < 1e-12:
            continue

        d_hat = d_i / d_norm
        m_hat = m_i / m_norm

        delta_L = foam.writing_rate * (
            np.outer(d_hat, m_hat.conj()) - np.outer(m_hat, d_hat.conj())
        ) * d_norm

        foam.bubbles[i].write(delta_L)

    return {
        'dissonance': total_dissonance,
        'L': foam.boundary_cost(),
    }


def test_self_measurement(seed=0):
    """Does self-measurement relax the foam?"""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # first: accumulate some history from external input
    print("  === building up state from external measurement ===")
    for step in range(50):
        foam.measure(encode(np.random.randint(0, 256), 8))
    L_after_external = foam.boundary_cost()
    print(f"  L after 50 external measurements: {L_after_external:.4f}")

    # now: self-measurement only
    print("\n  === self-measurement (no external input) ===")
    print(f"  {'step':>5s}  {'L':>8s}  {'|d|':>8s}  {'phase_0':>8s}  {'2x_ratio':>8s}")

    initial_Ls = [b.L.copy() for b in foam.bubbles]

    for step in range(100):
        result = self_measure(foam)

        if step % 10 == 0:
            dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
            phase = foam.bubbles[0].transport_phase

            # 2x check
            delta_L = foam.bubbles[0].L - initial_Ls[0]
            try:
                log_T = logm(foam.bubbles[0].T)
                ratio = np.linalg.norm(log_T) / (np.linalg.norm(delta_L) + 1e-12)
            except:
                ratio = float('nan')

            print(f"  {step:5d}  {result['L']:8.4f}  {dis:8.4f}  {phase:+8.4f}  {ratio:8.4f}")


def test_cross_measurement(seed=0):
    """Does cross-measurement relax the foam?"""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # build up state
    for step in range(50):
        foam.measure(encode(np.random.randint(0, 256), 8))
    L_after_external = foam.boundary_cost()
    print(f"  L after 50 external measurements: {L_after_external:.4f}")

    # cross-measurement only
    print("\n  === cross-measurement (bubbles measure each other) ===")
    print(f"  {'step':>5s}  {'L':>8s}  {'|d|':>8s}  {'phase_0':>8s}  {'2x_ratio':>8s}")

    initial_Ls = [b.L.copy() for b in foam.bubbles]

    for step in range(100):
        result = cross_measure(foam)

        if step % 10 == 0:
            dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
            phase = foam.bubbles[0].transport_phase

            delta_L = foam.bubbles[0].L - initial_Ls[0]
            try:
                log_T = logm(foam.bubbles[0].T)
                ratio = np.linalg.norm(log_T) / (np.linalg.norm(delta_L) + 1e-12)
            except:
                ratio = float('nan')

            print(f"  {step:5d}  {result['L']:8.4f}  {dis:8.4f}  {phase:+8.4f}  {ratio:8.4f}")


def compare_all_three(seed=0):
    """
    Same initial foam, three treatments:
    1. External measurement (random symbols)
    2. Self-measurement
    3. Cross-measurement

    Track L, dissonance, and 2x theorem for each.
    """
    np.random.seed(seed)

    # create a foam and accumulate some shared history
    foam_template = Foam(d=8, n=3, writing_rate=0.01)
    for _ in range(50):
        foam_template.measure(encode(np.random.randint(0, 256), 8))

    # snapshot
    def clone_foam(src):
        f = Foam(d=8, n=3, writing_rate=0.01)
        for i in range(3):
            f.bubbles[i].L = src.bubbles[i].L.copy()
            f.bubbles[i].T = src.bubbles[i].T.copy()
        return f

    foam_ext = clone_foam(foam_template)
    foam_self = clone_foam(foam_template)
    foam_cross = clone_foam(foam_template)

    L_start = foam_template.boundary_cost()

    print(f"  === three treatments from same starting state (L={L_start:.4f}) ===")
    print(f"  {'step':>5s}  {'L_ext':>8s}  {'L_self':>8s}  {'L_cross':>8s}  {'|d|_ext':>8s}  {'|d|_self':>8s}  {'|d|_cross':>9s}")

    np.random.seed(7)
    for step in range(80):
        # external
        r_ext = foam_ext.measure(encode(np.random.randint(0, 256), 8))
        # self
        r_self = self_measure(foam_self)
        # cross
        r_cross = cross_measure(foam_cross)

        if step % 8 == 0:
            d_ext = np.mean([np.linalg.norm(d) for d in r_ext['dissonance']])
            d_self = np.mean([np.linalg.norm(d) for d in r_self['dissonance']])
            d_cross = np.mean([np.linalg.norm(d) for d in r_cross['dissonance']])

            print(f"  {step:5d}  {r_ext['L']:8.4f}  {r_self['L']:8.4f}  {r_cross['L']:8.4f}  {d_ext:8.4f}  {d_self:8.4f}  {d_cross:9.4f}")


def what_does_self_measurement_converge_to(seed=0):
    """
    Run self-measurement for a long time.
    What's the fixed point? Does it reach one?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # build up state
    for _ in range(50):
        foam.measure(encode(np.random.randint(0, 256), 8))

    print("  === long self-measurement ===")
    print(f"  {'step':>5s}  {'L':>8s}  {'|d|':>8s}  {'basis_delta':>11s}")

    prev_bases = [b.basis.copy() for b in foam.bubbles]

    for step in range(500):
        result = self_measure(foam)

        if step % 50 == 0:
            dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
            curr_bases = [b.basis.copy() for b in foam.bubbles]
            delta = np.mean([np.linalg.norm(curr_bases[i] - prev_bases[i]) for i in range(3)])
            prev_bases = curr_bases
            print(f"  {step:5d}  {result['L']:8.4f}  {dis:8.4f}  {delta:11.6f}")


if __name__ == '__main__':
    print("=== self-measurement ===")
    test_self_measurement()

    print("\n=== cross-measurement ===")
    test_cross_measurement()

    print("\n=== comparison ===")
    compare_all_three()

    print("\n=== self-measurement convergence ===")
    what_does_self_measurement_converge_to()
