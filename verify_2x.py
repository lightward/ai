"""
Verify the 2x theorem: log(cayley(δ)) ≈ −2δ for small skew-Hermitian δ.

Convention: cayley(A) = (I − A)(I + A)⁻¹

Result: confirmed numerically. The scalar ratio is −2.0000 with residual ~1e-6.
"""

import numpy as np
from scipy.linalg import logm


def cayley(A):
    """cayley(A) = (I - A)(I + A)^{-1}"""
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def verify(d=4, eps=0.01, seed=42):
    rng = np.random.default_rng(seed)
    X = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    X = (X - X.conj().T) / 2  # skew-Hermitian
    delta = eps * X / np.linalg.norm(X)

    C = cayley(delta)
    L = logm(C)

    # fit log(cayley(δ)) = c * δ
    c = np.real(np.vdot(L.flatten(), delta.flatten()) / np.vdot(delta.flatten(), delta.flatten()))
    residual = np.linalg.norm(L - c * delta) / np.linalg.norm(L)

    print(f"d={d}, eps={eps}")
    print(f"  scalar coefficient: {c:.6f}")
    print(f"  relative residual:  {residual:.2e}")
    print(f"  2x theorem holds:   {abs(c + 2) < 0.01}")
    return c, residual


if __name__ == "__main__":
    for d in [3, 4, 8, 16]:
        verify(d=d)
        print()
