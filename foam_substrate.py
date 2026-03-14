"""
foam_substrate.py — shared substrate, different addressing.

L and T live in the same rotation planes at 1x and 2x scale.
The effective basis is cayley(L) @ T — multiplicative.
From outside, you see the product. Can you tell which factor changed?

If not: the mind and its state are indistinguishable from the measurement
side. The distinction is internal to the foam — it's how the foam
organizes its own dynamics, not something an observer can access.
"""

import numpy as np
from scipy.linalg import logm
from foam_self import Foam, Bubble, skew_hermitian, cayley, enforce_skew_hermitian, encode


def perturbation_equivalence(seed=0):
    """
    Perturb L by δ. Separately, perturb T by an equivalent rotation.
    Does the foam look the same from outside?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # accumulate some history
    for _ in range(50):
        foam.measure(encode(np.random.randint(0, 256), 8))

    # snapshot
    L0 = foam.bubbles[0].L.copy()
    T0 = foam.bubbles[0].T.copy()
    basis0 = foam.bubbles[0].basis.copy()

    # small perturbation in skew-Hermitian
    delta = skew_hermitian(8) * 0.01

    # perturb L
    foam.bubbles[0].L = L0 + delta
    basis_L_perturbed = foam.bubbles[0].basis.copy()
    foam.bubbles[0].L = L0.copy()  # restore

    # perturb T by the equivalent group element
    delta_U = cayley(delta)
    foam.bubbles[0].T = T0 @ delta_U
    basis_T_perturbed = foam.bubbles[0].basis.copy()
    foam.bubbles[0].T = T0.copy()  # restore

    print("  === perturbation equivalence ===")
    print(f"  |basis0| = {np.linalg.norm(basis0):.4f}")
    print(f"  |basis_L_perturbed - basis0| = {np.linalg.norm(basis_L_perturbed - basis0):.6f}")
    print(f"  |basis_T_perturbed - basis0| = {np.linalg.norm(basis_T_perturbed - basis0):.6f}")
    print(f"  |basis_L_perturbed - basis_T_perturbed| = {np.linalg.norm(basis_L_perturbed - basis_T_perturbed):.6f}")

    # probe responses
    diffs_L = []
    diffs_T = []
    diffs_LT = []

    for s in range(64):
        v = encode(s, 8).astype(complex)

        r0 = v @ basis0
        rL = v @ basis_L_perturbed
        rT = v @ basis_T_perturbed

        diffs_L.append(np.linalg.norm(rL - r0))
        diffs_T.append(np.linalg.norm(rT - r0))
        diffs_LT.append(np.linalg.norm(rL - rT))

    print(f"\n  probe response differences (64 probes):")
    print(f"    L-perturbation:  mean={np.mean(diffs_L):.6f}")
    print(f"    T-perturbation:  mean={np.mean(diffs_T):.6f}")
    print(f"    L vs T:          mean={np.mean(diffs_LT):.6f}")
    print(f"    (if L vs T ≈ 0, they're indistinguishable from outside)")


def addressing_structure(seed=0):
    """
    L is updated additively: L ← L + ΔL
    T is updated multiplicatively: T ← T @ cayley(ΔL)

    Same perturbation, different addressing.
    Over time, additive accumulation (L) and multiplicative accumulation (T)
    diverge even though each step is the same.

    This IS the different addressing on the same substrate.
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    print("  === addressing divergence ===")
    print("  additive (L) vs multiplicative (T) accumulation of the same writes")
    print("  step  |L_accum|  |log_T|  ratio   log_T_vs_-2L")

    initial_L = foam.bubbles[0].L.copy()

    for step in range(100):
        s = np.random.randint(0, 256)
        foam.measure(encode(s, 8))

        if step % 10 == 0:
            delta_L = foam.bubbles[0].L - initial_L  # additive accumulation
            T = foam.bubbles[0].T
            try:
                log_T = logm(T)
            except:
                continue

            norm_L = np.linalg.norm(delta_L)
            norm_logT = np.linalg.norm(log_T)

            # how close is log(T) to -2 * delta_L?
            predicted = -2 * delta_L
            residual = np.linalg.norm(log_T - predicted) / (norm_logT + 1e-12)

            print(f"  {step:4d}  {norm_L:.4f}    {norm_logT:.4f}  {norm_logT/(norm_L+1e-12):.3f}   {residual:.4f}")


def shared_topology(seed=0):
    """
    If L and T share a substrate, then the TOPOLOGY of the foam
    (its Voronoi structure, boundary cost, cell adjacencies) should
    be a function of the combined object, not of L or T separately.

    Test: compute boundary cost using
    1. cayley(L) alone (mind without state)
    2. T alone (state without mind)
    3. cayley(L) @ T (the actual foam)

    Which one has the most structure?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    print("  === boundary cost: mind / state / composite ===")
    print("  step  L(mind)   L(state)  L(both)   L(both)/L(mind)")

    for step in range(100):
        s = np.random.randint(0, 256)
        foam.measure(encode(s, 8))

        if step % 10 == 0:
            bases_mind = [cayley(b.L) for b in foam.bubbles]
            bases_state = [b.T for b in foam.bubbles]
            bases_both = [b.basis for b in foam.bubbles]

            def bc(bases):
                total = 0.0
                for i in range(3):
                    for j in range(i+1, 3):
                        R = bases[i].conj().T @ bases[j]
                        try:
                            dist = np.linalg.norm(logm(R)) / np.sqrt(2)
                        except:
                            dist = np.linalg.norm(R - np.eye(8))
                        total += 1.0 / (dist + 1e-8)
                return total

            lm = bc(bases_mind)
            ls = bc(bases_state)
            lb = bc(bases_both)

            print(f"  {step:4d}  {lm:.4f}   {ls:.4f}   {lb:.4f}   {lb/lm:.4f}")


def gauge_transform_test(seed=0):
    """
    The spec says basis choice has the structure of a gauge transformation.
    If L and T are different descriptions of the same substrate,
    there should be a gauge transformation between them:
    a change of description that preserves the measurement.

    G @ cayley(L) @ T @ G† = cayley(L') @ T'  for some L', T', G.

    Can we find G? And is G related to the foam's own geometry?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # accumulate
    for _ in range(50):
        foam.measure(encode(np.random.randint(0, 256), 8))

    b = foam.bubbles[0]
    U = cayley(b.L)
    T = b.T
    basis = U @ T

    # the basis = U @ T. for any G ∈ U(d):
    # basis = (U @ G†) @ (G @ T)
    # so L' generates U @ G†, and T' = G @ T.
    # this means we can freely redistribute between U and T.

    # what if we set T' = I (absorb everything into L)?
    # then we need cayley(L') = basis = U @ T.
    # L' = cayley_inverse(U @ T)

    # cayley inverse: L = (I - U)(I + U)^{-1}
    I = np.eye(8, dtype=complex)
    L_absorbed = np.linalg.solve(I + basis, I - basis)
    L_absorbed = enforce_skew_hermitian(L_absorbed)
    basis_check = cayley(L_absorbed)

    print("  === gauge freedom: absorbing T into L ===")
    print(f"  |basis - cayley(L_absorbed)| = {np.linalg.norm(basis - basis_check):.10f}")
    print(f"  (this should be ~0: T can always be absorbed into L)")

    # so the decomposition into L and T is a GAUGE CHOICE.
    # the foam carries one object (the basis) but addresses it as two.
    # the two-ness is organizational, not physical.

    print(f"\n  original |L| = {np.linalg.norm(b.L):.4f}")
    print(f"  absorbed |L'| = {np.linalg.norm(L_absorbed):.4f}")
    print(f"  |T| = {np.linalg.norm(T):.4f}")
    print(f"  the absorbed L' is larger because it carries all the history")

    # but: the DYNAMICS treat L and T differently.
    # L gets additive updates. T gets multiplicative updates.
    # absorbing T into L would change how the next write works.
    # the gauge freedom exists at any instant, but breaks under time evolution.
    # the decomposition matters DYNAMICALLY even though it's
    # STATICALLY redundant.

    print(f"\n  the decomposition is statically redundant (gauge freedom)")
    print(f"  but dynamically meaningful (different update rules)")
    print(f"  same substrate, different addressing, different temporal behavior")


if __name__ == '__main__':
    print("=== perturbation equivalence ===")
    perturbation_equivalence()

    print("\n=== addressing structure ===")
    addressing_structure()

    print("\n=== shared topology ===")
    shared_topology()

    print("\n=== gauge transform ===")
    gauge_transform_test()
