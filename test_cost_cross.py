"""
Test: does cross-measurement (multiple observers) decrease L?

The single-observer test showed L tends to increase.
The spec says "cross-measurement relaxes." Does this extend to L?
"""

import numpy as np
from foam import (cayley, skew_hermitian, random_unitary, random_slice,
                  compute_L)


def write_step_multi_observer(bases, v, observer_slices, eps=0.005):
    """Multiple observers each write from their own R³ slice.

    This is a test-specific variant: all observers' writes are accumulated
    additively in the Lie algebra before applying, unlike the sequential
    write_step in foam.py.
    """
    N = len(bases)
    d = bases[0].shape[0]

    # Each observer writes independently, then we compose
    total_dL = [np.zeros((d, d), dtype=complex) for _ in range(N)]

    for P in observer_slices:
        target_cos = -1.0 / (N - 1)
        measurements = [v @ b for b in bases]
        m_proj = [np.real(P @ m) for m in measurements]

        j2 = []
        for i in range(N):
            mi = m_proj[i]
            mi_norm = np.linalg.norm(mi)
            if mi_norm < 1e-10:
                j2.append(mi)
                continue
            mi_hat = mi / mi_norm
            force = np.zeros(3)
            for j in range(N):
                if i == j:
                    continue
                mj = m_proj[j]
                mj_norm = np.linalg.norm(mj)
                if mj_norm < 1e-10:
                    continue
                mj_hat = mj / mj_norm
                current_cos = np.dot(mi_hat, mj_hat)
                force += (target_cos - current_cos) * (mj_hat - current_cos * mi_hat)
            j2.append(mi + 0.1 * force * mi_norm)

        for i in range(N):
            di = j2[i] - m_proj[i]
            mi = m_proj[i]
            di_norm = np.linalg.norm(di)
            mi_norm = np.linalg.norm(mi)
            if di_norm < 1e-12 or mi_norm < 1e-12:
                continue
            d_hat = di / di_norm
            m_hat = mi / mi_norm
            d_full = P.T @ d_hat
            m_full = P.T @ m_hat
            dL_real = eps * di_norm * (np.outer(d_full, m_full) - np.outer(m_full, d_full))
            total_dL[i] += skew_hermitian(dL_real.astype(complex))

    new_bases = []
    for i in range(N):
        new_bases.append(bases[i] @ cayley(total_dL[i]))
    return new_bases


def run_trial(d, N, n_observers, steps, rng, varying_input=False):
    bases = [random_unitary(d, rng) for _ in range(N)]

    observer_slices = [random_slice(d, rng=rng) for _ in range(n_observers)]

    L0 = compute_L(bases)
    v = rng.standard_normal(d).astype(complex)
    v = v / np.linalg.norm(v)

    for _ in range(steps):
        if varying_input:
            v = rng.standard_normal(d).astype(complex)
            v = v / np.linalg.norm(v)
        bases = write_step_multi_observer(bases, v, observer_slices)

    Lf = compute_L(bases)
    return L0, Lf


if __name__ == "__main__":
    n_trials = 50

    for n_obs in [1, 2, 3, 5]:
        for d in [4, 8]:
            N = 3
            decreased = 0
            magnitudes = []
            for trial in range(n_trials):
                rng = np.random.default_rng(trial)
                L0, Lf = run_trial(d, N, n_obs, 200, rng, varying_input=True)
                pct = (Lf - L0) / L0 * 100
                magnitudes.append(pct)
                if Lf < L0:
                    decreased += 1

            mag_arr = np.array(magnitudes)
            print(f"observers={n_obs}, d={d}, N={N}: "
                  f"decreased {decreased}/{n_trials}, "
                  f"mean {mag_arr.mean():+.3f}%")
    print()
