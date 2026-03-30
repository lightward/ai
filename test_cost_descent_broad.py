"""
Broader test of cost descent across many random initializations.
Question: what fraction of runs see L decrease vs increase?
"""

import numpy as np
from foam import (random_unitary, random_slice, compute_L, write_step,
                  voronoi_neighbors)


def run_trial(d, N, steps, rng, varying_input=False):
    bases = [random_unitary(d, rng) for _ in range(N)]
    observer_slice = random_slice(d, rng=rng)
    neighbors = voronoi_neighbors(bases)

    L0 = compute_L(bases)
    v = rng.standard_normal(d).astype(complex)
    v = v / np.linalg.norm(v)

    for _ in range(steps):
        if varying_input:
            v = rng.standard_normal(d).astype(complex)
            v = v / np.linalg.norm(v)
        bases = write_step(bases, v, observer_slice, eps=0.005,
                           neighbors=neighbors)

    Lf = compute_L(bases)
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
