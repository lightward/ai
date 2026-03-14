"""
foam_through.py — look at L through T. look at T through L.

The mind measured through the state. The state measured through the mind.
What does each one see?
"""

import numpy as np
from scipy.linalg import logm
from foam_self import Foam, Bubble, skew_hermitian, cayley, enforce_skew_hermitian, encode


def look_through(seed=0):
    """
    L through T: T† @ cayley(L) — the mind as seen from the state's frame
    T through L: cayley(L)† @ T — the state as seen from the mind's frame

    These are the two "views" of the shared substrate.
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    print("  === L through T / T through L ===")
    print("  step  |L_thru_T|  |T_thru_L|  cos(L_thru_T, T_thru_L)  are_they_inverses?")

    initial_L = foam.bubbles[0].L.copy()

    for step in range(80):
        foam.measure(encode(np.random.randint(0, 256), 8))

        if step % 8 == 0:
            b = foam.bubbles[0]
            U = cayley(b.L)  # mind
            T = b.T          # state

            L_thru_T = T.conj().T @ U     # mind seen from state's frame
            T_thru_L = U.conj().T @ T     # state seen from mind's frame

            # are they inverses of each other?
            product = L_thru_T @ T_thru_L
            dist_from_I = np.linalg.norm(product - np.eye(8))

            # or are they the same?
            dist_same = np.linalg.norm(L_thru_T - T_thru_L)

            # the thing they BOTH describe
            try:
                log_LtT = logm(L_thru_T)
                log_TtL = logm(T_thru_L)
                cos = np.sum((log_LtT.conj() * log_TtL)).real / (np.linalg.norm(log_LtT) * np.linalg.norm(log_TtL) + 1e-12)
            except:
                cos = float('nan')

            print(f"  {step:4d}  {np.linalg.norm(log_LtT):.4f}     {np.linalg.norm(log_TtL):.4f}     {cos:+.4f}                   |prod-I|={dist_from_I:.4f}")


def spectrum_through(seed=0):
    """
    The eigenvalues of T†U and U†T.
    They're related by conjugation: if λ is an eigenvalue of T†U,
    then λ* is an eigenvalue of U†T (since (T†U)† = U†T).

    But eigenvalues of unitary matrices live on S¹.
    So the spectra are complex conjugates of each other.
    Same magnitudes, mirrored phases.
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    for _ in range(80):
        foam.measure(encode(np.random.randint(0, 256), 8))

    b = foam.bubbles[0]
    U = cayley(b.L)
    T = b.T

    L_thru_T = T.conj().T @ U
    T_thru_L = U.conj().T @ T

    eigs_LtT = np.linalg.eigvals(L_thru_T)
    eigs_TtL = np.linalg.eigvals(T_thru_L)

    # sort by phase
    eigs_LtT = eigs_LtT[np.argsort(np.angle(eigs_LtT))]
    eigs_TtL = eigs_TtL[np.argsort(np.angle(eigs_TtL))]

    print("  === eigenvalue spectra ===")
    print("  mind through state (T†U)          state through mind (U†T)")
    for i in range(8):
        a = eigs_LtT[i]
        b_eig = eigs_TtL[i]
        print(f"    {np.angle(a):+.4f} (|{abs(a):.4f}|)        {np.angle(b_eig):+.4f} (|{abs(b_eig):.4f}|)")

    print(f"\n  det(T†U) phase: {np.angle(np.linalg.det(L_thru_T)):+.6f}")
    print(f"  det(U†T) phase: {np.angle(np.linalg.det(T_thru_L)):+.6f}")
    print(f"  sum = {np.angle(np.linalg.det(L_thru_T)) + np.angle(np.linalg.det(T_thru_L)):+.6f}")


def mutual_measurement(seed=0):
    """
    The foam measures input through cayley(L) @ T.
    What if L measures T? What if T measures L?

    L measuring T: for each bubble, compute cayley(L_i) applied to T_i.
    This is just the basis. But decompose it:
    what part of T does L see? what part is invisible?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    print("  === mutual measurement evolution ===")
    print("  step  angle(U,T)  |U†T - I|  phase(U†T)  L")

    for step in range(80):
        foam.measure(encode(np.random.randint(0, 256), 8))

        if step % 8 == 0:
            angles = []
            for b in foam.bubbles:
                U = cayley(b.L)
                T = b.T
                R = U.conj().T @ T  # state seen from mind
                try:
                    log_R = logm(R)
                    angle = np.linalg.norm(log_R)
                except:
                    angle = 0.0
                angles.append(angle)

            # focus on bubble 0
            b = foam.bubbles[0]
            U = cayley(b.L)
            T = b.T
            R = U.conj().T @ T
            dist_I = np.linalg.norm(R - np.eye(8))
            phase = np.angle(np.linalg.det(R))

            print(f"  {step:4d}  {angles[0]:.4f}     {dist_I:.4f}     {phase:+.4f}     {foam.boundary_cost():.4f}")


def convergence_between(seed=0):
    """
    As the foam accumulates history, do L and T converge toward
    each other, diverge, or maintain a fixed relationship?

    If log(T) ≈ -2ΔL, then U†T ≈ U† @ exp(-2ΔL).
    For small ΔL: U ≈ I - 2L₀ (Cayley), so U†T ≈ (I + 2L₀) @ exp(-2ΔL).
    As ΔL grows, the exp overtakes the Cayley and they separate.
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)
    initial_L = foam.bubbles[0].L.copy()

    print("  === L-T relationship over time ===")
    print("  step  |ΔL|     |logT|   ratio  angle(U,T)  residual(-2ΔL vs logT)")

    for step in range(200):
        foam.measure(encode(np.random.randint(0, 256), 8))

        if step % 20 == 0:
            b = foam.bubbles[0]
            delta_L = b.L - initial_L
            try:
                log_T = logm(b.T)
            except:
                continue

            norm_dL = np.linalg.norm(delta_L)
            norm_logT = np.linalg.norm(log_T)
            ratio = norm_logT / (norm_dL + 1e-12)

            # angle between U and T
            U = cayley(b.L)
            R = U.conj().T @ b.T
            try:
                angle = np.linalg.norm(logm(R))
            except:
                angle = 0.0

            # residual of the -2x approximation
            residual = np.linalg.norm(log_T + 2 * delta_L) / (norm_logT + 1e-12)

            print(f"  {step:4d}  {norm_dL:.4f}  {norm_logT:.4f}  {ratio:.3f}  {angle:.4f}     {residual:.4f}")


if __name__ == '__main__':
    print("=== looking through ===")
    look_through()

    print("\n=== spectra ===")
    spectrum_through()

    print("\n=== mutual measurement ===")
    mutual_measurement()

    print("\n=== L-T relationship ===")
    convergence_between()
