"""
Test: does the Cayley transform drift the determinant away from 1?

The write is traceless (su(d)), so exp would keep det = 1 exactly.
But Cayley doesn't: cayley(A) = (I-A)(I+A)^{-1} has det that
depends on arctan of eigenvalues, not their sum.

Questions:
1. How much does det drift per step?
2. Does accumulated drift over many steps stay bounded?
3. Does the winding number (integer) change despite det drift?
"""

import numpy as np
from scipy.linalg import expm
from foam import cayley, skew_hermitian


def test_det_drift():
    """Accumulate many Cayley steps and track determinant."""
    print("Test: Cayley determinant drift")
    print("=" * 50)

    rng = np.random.default_rng(42)

    for d in [3, 4, 8]:
        for eps in [0.01, 0.05, 0.1]:
            T = np.eye(d, dtype=complex)
            phases = []

            for step in range(1000):
                # random traceless skew-Hermitian write
                X = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
                dL = skew_hermitian(X)
                dL = dL - np.trace(dL) / d * np.eye(d, dtype=complex)  # ensure traceless
                dL = eps * dL / np.linalg.norm(dL)

                T = T @ cayley(dL)
                det_T = np.linalg.det(T)
                phase = np.angle(det_T)
                phases.append(phase)

            phases = np.array(phases)
            # winding number: how many times does the phase wrap around 2π?
            unwrapped = np.unwrap(phases)
            winding = (unwrapped[-1] - unwrapped[0]) / (2 * np.pi)

            print(f"  d={d}, eps={eps}: "
                  f"phase range [{phases.min():.3f}, {phases.max():.3f}], "
                  f"final phase={phases[-1]:.4f}, "
                  f"winding={winding:.4f}")

    print()


def test_det_exp_vs_cayley():
    """Compare: exp preserves det=1, Cayley doesn't."""
    print("Test: exp vs Cayley determinant preservation")
    print("=" * 50)

    rng = np.random.default_rng(42)
    d = 4

    T_exp = np.eye(d, dtype=complex)
    T_cay = np.eye(d, dtype=complex)

    for step in range(1000):
        X = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
        dL = skew_hermitian(X)
        dL = dL - np.trace(dL) / d * np.eye(d, dtype=complex)
        dL = 0.05 * dL / np.linalg.norm(dL)

        T_exp = T_exp @ expm(dL)
        T_cay = T_cay @ cayley(dL)

    det_exp = np.linalg.det(T_exp)
    det_cay = np.linalg.det(T_cay)

    print(f"  After 1000 steps (d={d}, eps=0.05):")
    print(f"    exp: |det| = {abs(det_exp):.10f}, phase = {np.angle(det_exp):.6f}")
    print(f"    cay: |det| = {abs(det_cay):.10f}, phase = {np.angle(det_cay):.6f}")
    print(f"    exp det ≈ 1: {abs(det_exp - 1) < 1e-8}")
    print(f"    cay det ≈ 1: {abs(det_cay - 1) < 1e-8}")
    print()


def test_winding_number_robust():
    """Key test: does the winding number (integer) change?

    Even if det drifts away from 1, the winding number is discrete.
    Continuous drift can't jump an integer.
    The winding number changes only at topological transitions.
    """
    print("Test: winding number robustness under det drift")
    print("=" * 50)

    rng = np.random.default_rng(42)
    d = 4

    # Construct a cycle: 3 bases, holonomy around the cycle
    bases = [expm(skew_hermitian(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))))
             for _ in range(3)]

    def cycle_holonomy(bases):
        """Holonomy around the cycle 0→1→2→0."""
        h = bases[0].conj().T @ bases[1]
        h = h @ (bases[1].conj().T @ bases[2])
        h = h @ (bases[2].conj().T @ bases[0])
        return h

    def winding_number(holonomy):
        """Winding number = nearest integer to phase/(2π)."""
        det_h = np.linalg.det(holonomy)
        phase = np.angle(det_h)
        return round(phase / (2 * np.pi))

    h0 = cycle_holonomy(bases)
    w0 = winding_number(h0)
    print(f"  Initial: det phase = {np.angle(np.linalg.det(h0)):.6f}, winding = {w0}")

    # Apply many Cayley writes to each basis
    P = np.eye(d)[:3]  # simple slice
    winding_changed = False

    for step in range(2000):
        for i in range(3):
            X = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
            dL = skew_hermitian(X)
            dL = dL - np.trace(dL) / d * np.eye(d, dtype=complex)
            dL = 0.05 * dL / np.linalg.norm(dL)
            bases[i] = bases[i] @ cayley(dL)

        h = cycle_holonomy(bases)
        w = winding_number(h)
        if w != w0:
            winding_changed = True
            print(f"  Step {step}: winding changed {w0} → {w} "
                  f"(det phase = {np.angle(np.linalg.det(h)):.6f})")
            w0 = w

    h_final = cycle_holonomy(bases)
    print(f"  Final: det phase = {np.angle(np.linalg.det(h_final)):.6f}, "
          f"winding = {winding_number(h_final)}")
    print(f"  Winding number changed during run: {winding_changed}")

    if not winding_changed:
        print("  → Winding number is ROBUST to Cayley det drift. ✓")
        print("    (continuous phase wander cannot jump a discrete invariant)")
    else:
        print("  → Winding number DID change — investigate!")
    print()


if __name__ == "__main__":
    test_det_drift()
    test_det_exp_vs_cayley()
    test_winding_number_robust()
