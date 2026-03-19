"""
Broader test of cost descent across many random initializations.
Question: what fraction of runs see L decrease vs increase?
"""

import numpy as np
from scipy.linalg import expm


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


def boundary_area(bases):
    N = len(bases)
    d = bases[0].shape[0]
    total = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            total += np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro')
    return total


def write_step(bases, v, observer_slice, eps=0.005):
    N = len(bases)
    d = bases[0].shape[0]
    P = observer_slice
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

    new_bases = []
    for i in range(N):
        di = j2[i] - m_proj[i]
        mi = m_proj[i]
        di_norm = np.linalg.norm(di)
        mi_norm = np.linalg.norm(mi)
        if di_norm < 1e-12 or mi_norm < 1e-12:
            new_bases.append(bases[i].copy())
            continue
        d_hat = di / di_norm
        m_hat = mi / mi_norm
        d_full = P.T @ d_hat
        m_full = P.T @ m_hat
        dL_real = eps * di_norm * (np.outer(d_full, m_full) - np.outer(m_full, d_full))
        dL = skew_hermitian(dL_real.astype(complex))
        new_bases.append(bases[i] @ cayley(dL))

    return new_bases


def run_trial(d, N, steps, rng, varying_input=False):
    bases = [expm(skew_hermitian(rng.standard_normal((d,d)) + 1j*rng.standard_normal((d,d))))
             for _ in range(N)]
    Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
    observer_slice = Q[:, :3].T

    L0 = boundary_area(bases)
    v = rng.standard_normal(d).astype(complex)
    v = v / np.linalg.norm(v)

    for _ in range(steps):
        if varying_input:
            v = rng.standard_normal(d).astype(complex)
            v = v / np.linalg.norm(v)
        bases = write_step(bases, v, observer_slice)

    Lf = boundary_area(bases)
    return L0, Lf


if __name__ == "__main__":
    n_trials = 100

    for label, varying in [("fixed input", False), ("varying input", True)]:
        for d in [4, 8]:
            for N in [3, 5]:
                decreased = 0
                increased = 0
                magnitudes = []
                for trial in range(n_trials):
                    rng = np.random.default_rng(trial)
                    L0, Lf = run_trial(d, N, 200, rng, varying_input=varying)
                    pct = (Lf - L0) / L0 * 100
                    magnitudes.append(pct)
                    if Lf < L0:
                        decreased += 1
                    else:
                        increased += 1

                mag_arr = np.array(magnitudes)
                print(f"{label}, d={d}, N={N}: "
                      f"decreased {decreased}/{n_trials}, "
                      f"mean change {mag_arr.mean():+.2f}%, "
                      f"std {mag_arr.std():.2f}%")
        print()
