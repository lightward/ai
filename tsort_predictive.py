"""
tsort_predictive.py — does the DAG hierarchy predict future behavior?

The directed hierarchy orders bubbles by accumulated perturbation,
with the least-written bubble upstream. The residual direction
encodes equilibration history (points toward farthest neighbor).

Question: does DAG rank predict per-bubble dissonance on fresh input?

If yes: the hierarchy tells you which parts of the foam are most
available to new measurement. The tsort ordering is a readout of
differential availability.

If no: the hierarchy is a historical record that doesn't predict
future behavior.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, encode, cayley
from heirloom import alongside, report, save


def compute_dag_ordering(foam):
    """Get DAG ordering from BCH residual directed graph.
    Returns: ordering (array of bubble indices, most upstream first)
             and net_out (net outflow per bubble)."""
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

    # directed edges
    W = np.zeros((N, N))
    for i in range(N):
        for j in range(i+1, N):
            asym = A[i, j] - A[j, i]
            if asym > 0:
                W[i, j] = asym
            else:
                W[j, i] = -asym

    in_deg = np.sum(W, axis=0)
    out_deg = np.sum(W, axis=1)
    net_out = out_deg - in_deg
    ordering = np.argsort(-net_out)

    ranks = np.zeros(N)
    for rank, idx in enumerate(ordering):
        ranks[idx] = rank

    return ordering, ranks, net_out


def per_bubble_dissonance(foam, v):
    """Measure dissonance per bubble for input v, without writing."""
    vc = v.astype(complex)
    bases = foam.bases
    m = [vc @ U for U in bases]
    j2 = foam._stabilize(m)
    return [np.linalg.norm(j2[i] - m[i]) for i in range(foam.n)]


def test_rank_predicts_dissonance():
    """Core test: does DAG rank predict per-bubble dissonance on fresh input?"""
    print("=== does DAG rank predict per-bubble dissonance? ===\n")

    d = 8
    n_train = 100
    n_probe = 50

    for N in [3, 4, 5]:
        all_corrs = []
        upstream_dis = []
        downstream_dis = []

        for seed in range(30):
            np.random.seed(seed)
            foam = Foam(d=d, n=N, writing_rate=0.01)

            # train the foam
            for _ in range(n_train):
                v = encode(np.random.randint(0, 2**d), d)
                foam.measure(v)
                alongside(v)

            # get DAG ordering
            ordering, ranks, net_out = compute_dag_ordering(foam)

            # probe with fresh inputs (no writing — snapshot the state)
            # make a copy so probing doesn't change the foam
            probe_dis_by_rank = [[] for _ in range(N)]

            rng = np.random.RandomState(seed + 5000)
            for _ in range(n_probe):
                v = encode(rng.randint(0, 2**d), d)
                dis = per_bubble_dissonance(foam, v)
                alongside(v)

                for i in range(N):
                    rank = int(ranks[i])
                    probe_dis_by_rank[rank].append(dis[i])

            # mean dissonance by rank
            mean_by_rank = [np.mean(probe_dis_by_rank[r]) for r in range(N)]

            # correlation: rank vs mean dissonance
            corr = np.corrcoef(range(N), mean_by_rank)[0, 1]
            all_corrs.append(corr)

            upstream_dis.append(mean_by_rank[0])
            downstream_dis.append(mean_by_rank[-1])

        print(f"  N={N}:")
        print(f"    corr(rank, dissonance): {np.mean(all_corrs):+.3f} ± {np.std(all_corrs):.3f}")
        print(f"    upstream (rank 0) mean dissonance:   {np.mean(upstream_dis):.4f}")
        print(f"    downstream (rank {N-1}) mean dissonance: {np.mean(downstream_dis):.4f}")
        print(f"    ratio upstream/downstream: {np.mean(upstream_dis)/np.mean(downstream_dis):.3f}")
        print()


def test_rank_predicts_write_magnitude():
    """Does DAG rank predict how much each bubble CHANGES on the next write?"""
    print("=== does DAG rank predict per-bubble write magnitude? ===\n")

    d = 8
    n_train = 100

    for N in [3, 4, 5]:
        all_corrs = []
        upstream_dL = []
        downstream_dL = []

        for seed in range(30):
            np.random.seed(seed)
            foam = Foam(d=d, n=N, writing_rate=0.01)

            for _ in range(n_train):
                v = encode(np.random.randint(0, 2**d), d)
                foam.measure(v)
                alongside(v)

            ordering, ranks, net_out = compute_dag_ordering(foam)

            # measure write magnitudes on fresh inputs
            write_mag_by_rank = [[] for _ in range(N)]

            rng = np.random.RandomState(seed + 5000)
            for _ in range(50):
                v = encode(rng.randint(0, 2**d), d)

                # snapshot L before
                L_before = [foam.bubbles[i].L.copy() for i in range(N)]

                result = foam.measure(v)
                alongside(v)

                for i in range(N):
                    dL = np.linalg.norm(foam.bubbles[i].L - L_before[i])
                    rank = int(ranks[i])
                    write_mag_by_rank[rank].append(dL)

            mean_by_rank = [np.mean(write_mag_by_rank[r]) for r in range(N)]
            corr = np.corrcoef(range(N), mean_by_rank)[0, 1]
            all_corrs.append(corr)

            upstream_dL.append(mean_by_rank[0])
            downstream_dL.append(mean_by_rank[-1])

        print(f"  N={N}:")
        print(f"    corr(rank, |ΔL|): {np.mean(all_corrs):+.3f} ± {np.std(all_corrs):.3f}")
        print(f"    upstream (rank 0) mean |ΔL|:   {np.mean(upstream_dL):.6f}")
        print(f"    downstream (rank {N-1}) mean |ΔL|: {np.mean(downstream_dL):.6f}")
        print(f"    ratio upstream/downstream: {np.mean(upstream_dL)/np.mean(downstream_dL):.3f}")
        print()


def test_rank_stability():
    """Does the DAG ordering change as the foam continues to evolve?
    A stable hierarchy means the ordering is structural; an unstable
    one means it's ephemeral."""
    print("=== does the DAG ordering persist under continued measurement? ===\n")

    d = 8
    N = 4

    for seed in range(5):
        np.random.seed(seed)
        foam = Foam(d=d, n=N, writing_rate=0.01)

        orderings = []
        checkpoints = [25, 50, 75, 100, 150, 200]

        for step in range(201):
            v = encode(np.random.randint(0, 2**d), d)
            foam.measure(v)
            alongside(v)

            if (step + 1) in checkpoints:
                ordering, _, _ = compute_dag_ordering(foam)
                orderings.append(list(ordering))

        # check: how many pairs of consecutive orderings are identical?
        same = sum(1 for i in range(len(orderings)-1)
                   if orderings[i] == orderings[i+1])

        print(f"  seed {seed}: orderings at steps {checkpoints}")
        for i, (cp, o) in enumerate(zip(checkpoints, orderings)):
            print(f"    step {cp:3d}: {o}")
        print(f"    consecutive matches: {same}/{len(orderings)-1}")
        print()


if __name__ == '__main__':
    test_rank_predicts_dissonance()
    test_rank_predicts_write_magnitude()
    test_rank_stability()

    report()
    save()
