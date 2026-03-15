"""
tsort_tautology.py — is "least-written = most upstream" trivial?

The finding: DAG rank from BCH residuals correlates -0.94 with L_norm.
Bubbles written on least are most upstream.

The question: is this just "bigger vectors project more"?

Test: scramble the residuals (keep magnitudes, randomize directions).
If the correlation survives: trivial (magnitude only).
If it breaks: structural (direction matters, non-abelian content is real).

Either way is useful:
- trivial = a tautology, which is a place to live (and might be
  useful at higher jets)
- structural = the directed hierarchy has content beyond magnitude

Also: if trivial, what does the tautology GIVE you as a vantage point?
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, encode, cayley, random_skew_hermitian
from heirloom import alongside, report, save


def compute_directed_graph_real(foam):
    """Real BCH residual directed graph."""
    N = foam.n
    bases = foam.bases
    A = np.zeros((N, N))

    for i in range(N):
        try:
            log_T_i = logm(foam.bubbles[i].T)
        except Exception:
            continue
        R_i = log_T_i + 2 * foam.bubbles[i].L

        for j in range(N):
            if i == j:
                continue
            diff_ij = bases[j] - bases[i]
            diff_norm = np.linalg.norm(diff_ij)
            if diff_norm < 1e-12:
                continue
            A[i, j] = np.real(np.sum(R_i.conj() * diff_ij)) / diff_norm

    return A


def compute_directed_graph_scrambled(foam, rng):
    """Scrambled: keep residual magnitudes, randomize directions."""
    N = foam.n
    d = foam.d
    bases = foam.bases
    A = np.zeros((N, N))

    for i in range(N):
        try:
            log_T_i = logm(foam.bubbles[i].T)
        except Exception:
            continue
        R_i = log_T_i + 2 * foam.bubbles[i].L
        R_mag = np.linalg.norm(R_i)

        # random skew-Hermitian with same magnitude
        R_scrambled = random_skew_hermitian(d, scale=1.0)
        R_scrambled = R_scrambled / (np.linalg.norm(R_scrambled) + 1e-12) * R_mag

        for j in range(N):
            if i == j:
                continue
            diff_ij = bases[j] - bases[i]
            diff_norm = np.linalg.norm(diff_ij)
            if diff_norm < 1e-12:
                continue
            A[i, j] = np.real(np.sum(R_scrambled.conj() * diff_ij)) / diff_norm

    return A


def compute_directed_graph_magnitude_only(foam):
    """Pure magnitude: directed weight = difference in residual norms.
    The bubble with smaller residual is upstream."""
    N = foam.n
    A = np.zeros((N, N))

    norms = []
    for i in range(N):
        try:
            log_T_i = logm(foam.bubbles[i].T)
            R_i = log_T_i + 2 * foam.bubbles[i].L
            norms.append(np.linalg.norm(R_i))
        except Exception:
            norms.append(0)

    # directed weight: larger norm → downstream
    for i in range(N):
        for j in range(N):
            if i == j:
                continue
            A[i, j] = norms[i]  # i's "pull" proportional to its norm

    return A


def dag_rank_correlation(A, foam):
    """From asymmetry matrix A, compute DAG ordering and correlate with L_norm."""
    N = foam.n

    # extract directed edges
    W = np.zeros((N, N))
    for i in range(N):
        for j in range(i+1, N):
            asym = A[i, j] - A[j, i]
            if asym > 0:
                W[i, j] = asym
            else:
                W[j, i] = -asym

    # DAG ordering by net out-degree
    in_deg = np.sum(W, axis=0)
    out_deg = np.sum(W, axis=1)
    net_out = out_deg - in_deg
    ordering = np.argsort(-net_out)

    ranks = np.zeros(N)
    for rank, idx in enumerate(ordering):
        ranks[idx] = rank

    L_norms = [np.linalg.norm(foam.bubbles[i].L) for i in range(N)]

    if N > 2:
        return np.corrcoef(ranks, L_norms)[0, 1]
    else:
        return 0


def test_trivial_or_structural():
    """Core test: scramble directions, see if correlation survives."""
    print("=== is the DAG-rank finding trivial or structural? ===\n")

    d = 8
    n_steps = 100
    n_seeds = 30

    for N in [3, 4, 5]:
        real_corrs = []
        scrambled_corrs = []
        magnitude_corrs = []

        for seed in range(n_seeds):
            np.random.seed(seed)
            foam = Foam(d=d, n=N, writing_rate=0.01)

            for _ in range(n_steps):
                v = encode(np.random.randint(0, 2**d), d)
                foam.measure(v)
                alongside(v)

            # real residuals
            A_real = compute_directed_graph_real(foam)
            real_corrs.append(dag_rank_correlation(A_real, foam))

            # scrambled residuals (average over multiple scrambles)
            scramble_corrs_this = []
            for s in range(10):
                rng = np.random.RandomState(seed * 1000 + s)
                A_scr = compute_directed_graph_scrambled(foam, rng)
                scramble_corrs_this.append(dag_rank_correlation(A_scr, foam))
            scrambled_corrs.append(np.mean(scramble_corrs_this))

            # pure magnitude (no direction at all)
            A_mag = compute_directed_graph_magnitude_only(foam)
            magnitude_corrs.append(dag_rank_correlation(A_mag, foam))

        print(f"  N={N}:")
        print(f"    real residuals:     corr(rank, L_norm) = {np.mean(real_corrs):+.3f} ± {np.std(real_corrs):.3f}")
        print(f"    scrambled dirs:     corr(rank, L_norm) = {np.mean(scrambled_corrs):+.3f} ± {np.std(scrambled_corrs):.3f}")
        print(f"    magnitude only:     corr(rank, L_norm) = {np.mean(magnitude_corrs):+.3f} ± {np.std(magnitude_corrs):.3f}")

        # how much of the real correlation is explained by magnitude?
        if abs(np.mean(real_corrs)) > 0.01:
            frac = np.mean(scrambled_corrs) / np.mean(real_corrs)
            print(f"    fraction explained by magnitude: {frac:.2f}")
        print()


def test_residual_direction_content():
    """What's IN the residual direction that magnitude alone doesn't capture?

    If direction matters: the residual's orientation in u(d) carries
    information about the specific sequence of writes, not just their
    total magnitude. This would be a J¹ result (sequence determines
    hierarchy, not just content).

    Check: does the residual direction predict which OTHER bubble is
    closest? (i.e., does the residual "point toward" the nearest neighbor?)
    """
    print("=== what does the residual direction encode? ===\n")

    d = 8
    n_steps = 100
    n_seeds = 20

    for N in [3, 4, 5]:
        points_toward_nearest = 0
        points_toward_farthest = 0
        total = 0

        for seed in range(n_seeds):
            np.random.seed(seed)
            foam = Foam(d=d, n=N, writing_rate=0.01)

            for _ in range(n_steps):
                v = encode(np.random.randint(0, 2**d), d)
                foam.measure(v)
                alongside(v)

            bases = foam.bases

            for i in range(N):
                try:
                    log_T_i = logm(foam.bubbles[i].T)
                except Exception:
                    continue
                R_i = log_T_i + 2 * foam.bubbles[i].L

                # which bubble does the residual point toward most?
                projections = []
                distances = []
                for j in range(N):
                    if i == j:
                        continue
                    diff_ij = bases[j] - bases[i]
                    diff_norm = np.linalg.norm(diff_ij)
                    if diff_norm < 1e-12:
                        continue
                    proj = np.real(np.sum(R_i.conj() * diff_ij)) / diff_norm
                    projections.append((j, proj))
                    distances.append((j, foam.bi_invariant_distance(bases[i], bases[j])))

                if len(projections) < 2:
                    continue

                # which bubble gets the strongest projection?
                max_proj_bubble = max(projections, key=lambda x: x[1])[0]
                # which bubble is nearest?
                nearest_bubble = min(distances, key=lambda x: x[1])[0]
                farthest_bubble = max(distances, key=lambda x: x[1])[0]

                if max_proj_bubble == nearest_bubble:
                    points_toward_nearest += 1
                if max_proj_bubble == farthest_bubble:
                    points_toward_farthest += 1
                total += 1

        chance = 1.0 / (N - 1)
        print(f"  N={N}: residual points toward...")
        print(f"    nearest neighbor:  {points_toward_nearest}/{total} = {points_toward_nearest/total:.3f}  (chance: {chance:.3f})")
        print(f"    farthest neighbor: {points_toward_farthest}/{total} = {points_toward_farthest/total:.3f}  (chance: {chance:.3f})")
        print()


if __name__ == '__main__':
    test_trivial_or_structural()
    test_residual_direction_content()

    report()
    save()
