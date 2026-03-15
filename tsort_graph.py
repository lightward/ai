"""
tsort_graph.py — the foam as two graphs on the same vertices.

The foam already has an undirected weighted graph:
  - vertices = bubbles
  - edge weight = 1/distance (boundary cost contribution)
  - L = sum of edge weights

Now we know it also has a directed graph from the BCH residual.
These are two graphs on the same vertices.

Questions:
1. Does the directed structure correlate with the undirected structure?
   (Is the "upstream" bubble the one with more boundary cost?)
2. Do standard graph measures (spectral gap, etc.) correlate with
   foam observables (L, sensitivity)?
3. Does richer structure emerge at N=4,5 vs N=3?
4. Can graph theory predict things about the foam that L alone can't?
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, encode, cayley
from heirloom import alongside, report, save


def compute_undirected_graph(foam):
    """Undirected weighted graph from pairwise distances.
    W_u[i,j] = 1 / (d(U_i, U_j) + eps) = boundary cost contribution."""
    N = foam.n
    bases = foam.bases
    W = np.zeros((N, N))
    for i in range(N):
        for j in range(i+1, N):
            dist = foam.bi_invariant_distance(bases[i], bases[j])
            w = 1.0 / (dist + 1e-8)
            W[i, j] = w
            W[j, i] = w
    return W


def compute_directed_graph(foam):
    """Directed graph from BCH residual asymmetry.
    W_d[i,j] > 0 means j is upstream of i (j influences i more)."""
    N = foam.n
    bases = foam.bases
    A = np.zeros((N, N))

    for i in range(N):
        T_i = foam.bubbles[i].T
        L_i = foam.bubbles[i].L
        try:
            log_T_i = logm(T_i)
        except Exception:
            continue
        R_i = log_T_i + 2 * L_i

        for j in range(N):
            if i == j:
                continue
            diff_ij = bases[j] - bases[i]
            diff_norm = np.linalg.norm(diff_ij)
            if diff_norm < 1e-12:
                continue
            A[i, j] = np.real(np.sum(R_i.conj() * diff_ij)) / diff_norm

    # extract directed edges
    W = np.zeros((N, N))
    for i in range(N):
        for j in range(i+1, N):
            asym = A[i, j] - A[j, i]
            if asym > 0:
                W[i, j] = asym   # j upstream of i
            else:
                W[j, i] = -asym  # i upstream of j
    return W, A


def graph_measures(W_undirected, W_directed, A_raw):
    """Compute graph-theoretic measures of both graphs."""
    N = W_undirected.shape[0]
    measures = {}

    # --- undirected measures ---
    # total weight = L
    measures['L'] = np.sum(W_undirected) / 2

    # degree distribution (weighted)
    degrees = np.sum(W_undirected, axis=1)
    measures['degree_cv'] = np.std(degrees) / (np.mean(degrees) + 1e-12)

    # spectral gap of the Laplacian
    D = np.diag(degrees)
    Lap = D - W_undirected
    eigvals = np.sort(np.real(np.linalg.eigvalsh(Lap)))
    measures['spectral_gap'] = eigvals[1] if N > 1 else 0  # Fiedler value
    measures['algebraic_connectivity'] = eigvals[1] / (np.mean(degrees) + 1e-12)

    # --- directed measures ---
    # total asymmetry
    measures['total_asymmetry'] = np.sum(W_directed)

    # in-degree vs out-degree per node
    in_deg = np.sum(W_directed, axis=0)   # column sums: how much flows INTO each node
    out_deg = np.sum(W_directed, axis=1)  # row sums: how much flows OUT of each node
    measures['hierarchy_depth'] = np.max(in_deg) - np.min(in_deg)

    # DAG ordering: rank nodes by net out-degree (out - in)
    net_out = out_deg - in_deg
    ordering = np.argsort(-net_out)  # most "upstream" first
    measures['ordering'] = ordering
    measures['net_out'] = net_out

    # cyclicity (generalized for N > 3)
    # fraction of total weight that participates in cycles
    # approximation: compare with a perfect DAG's weight pattern
    # in a perfect DAG, all weight goes "downstream"
    # compute: for the DAG ordering, what fraction of A_raw goes against the order?
    total_raw = 0
    against = 0
    for i in range(N):
        for j in range(N):
            if i == j:
                continue
            rank_i = np.where(ordering == i)[0][0]
            rank_j = np.where(ordering == j)[0][0]
            w = max(0, A_raw[i, j])  # positive component of i's residual toward j
            total_raw += abs(A_raw[i, j])
            if rank_i < rank_j:  # i is upstream, but has residual pointing toward j (downstream)
                pass  # consistent with ordering
            else:
                against += abs(A_raw[i, j])  # against the ordering
    measures['cyclicity'] = against / (total_raw + 1e-15)

    return measures


def per_bubble_measures(foam):
    """Per-bubble quantities that might correlate with graph position."""
    N = foam.n
    d = foam.d
    result = []

    for i in range(N):
        b = foam.bubbles[i]
        L_norm = np.linalg.norm(b.L)
        T_det_phase = np.angle(np.linalg.det(b.T))
        try:
            log_T = logm(b.T)
            log_T_norm = np.linalg.norm(log_T)
            residual_norm = np.linalg.norm(log_T + 2 * b.L)
        except Exception:
            log_T_norm = 0
            residual_norm = 0

        result.append({
            'L_norm': L_norm,
            'T_phase': T_det_phase,
            'log_T_norm': log_T_norm,
            'residual_norm': residual_norm,
        })
    return result


def measure_sensitivity(foam, n_probes=30, seed=777):
    """Foam's sensitivity to random probes."""
    rng = np.random.RandomState(seed)
    total_dis = 0.0
    for _ in range(n_probes):
        v = encode(rng.randint(0, 2**foam.d), foam.d)
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        total_dis += np.mean([np.linalg.norm(j2[i] - m[i])
                              for i in range(foam.n)])
    return total_dis / n_probes


def test_two_graphs(N_values=[3, 4, 5], n_seeds=15):
    """Core investigation: how do the two graphs relate?"""

    for N in N_values:
        print(f"\n=== N={N} bubbles, d=8 ===\n")

        d = 8
        n_steps = 100

        all_measures = []

        for seed in range(n_seeds):
            np.random.seed(seed)
            foam = Foam(d=d, n=N, writing_rate=0.01)

            for _ in range(n_steps):
                v = encode(np.random.randint(0, 2**d), d)
                foam.measure(v)
                alongside(v)

            W_u = compute_undirected_graph(foam)
            W_d, A_raw = compute_directed_graph(foam)
            gm = graph_measures(W_u, W_d, A_raw)
            gm['sensitivity'] = measure_sensitivity(foam)

            # per-bubble: does graph position correlate with bubble properties?
            pb = per_bubble_measures(foam)
            ordering = gm['ordering']

            # correlation: rank in DAG vs residual norm
            ranks = np.zeros(N)
            for rank, idx in enumerate(ordering):
                ranks[idx] = rank
            residual_norms = [pb[i]['residual_norm'] for i in range(N)]
            L_norms = [pb[i]['L_norm'] for i in range(N)]

            gm['rank_residual_corr'] = np.corrcoef(ranks, residual_norms)[0, 1] if N > 2 else 0
            gm['rank_Lnorm_corr'] = np.corrcoef(ranks, L_norms)[0, 1] if N > 2 else 0
            gm['seed'] = seed

            all_measures.append(gm)

        # print summary table
        print(f"  {'seed':>4s}  {'L':>7s}  {'sens':>7s}  {'spec_gap':>8s}  {'asym':>7s}  {'cyc':>7s}  {'hier':>7s}  {'rk-res':>7s}  {'rk-L':>7s}")
        for gm in all_measures:
            print(f"  {gm['seed']:4d}  {gm['L']:7.3f}  {gm['sensitivity']:7.4f}  {gm['spectral_gap']:8.4f}  {gm['total_asymmetry']:7.4f}  {gm['cyclicity']:7.4f}  {gm['hierarchy_depth']:7.4f}  {gm['rank_residual_corr']:7.3f}  {gm['rank_Lnorm_corr']:7.3f}")

        # aggregate correlations
        Ls = [gm['L'] for gm in all_measures]
        senss = [gm['sensitivity'] for gm in all_measures]
        gaps = [gm['spectral_gap'] for gm in all_measures]
        asyms = [gm['total_asymmetry'] for gm in all_measures]
        cycs = [gm['cyclicity'] for gm in all_measures]

        print(f"\n  --- cross-measure correlations (n={n_seeds}) ---")
        for name, vals in [('spectral_gap', gaps), ('total_asymmetry', asyms), ('cyclicity', cycs)]:
            if np.std(vals) > 1e-12:
                corr_L = np.corrcoef(vals, Ls)[0, 1]
                corr_s = np.corrcoef(vals, senss)[0, 1]
                print(f"  {name:>18s}  vs L: {corr_L:+.3f}   vs sensitivity: {corr_s:+.3f}")

        # does DAG rank predict per-bubble properties?
        mean_rr = np.mean([gm['rank_residual_corr'] for gm in all_measures])
        mean_rL = np.mean([gm['rank_Lnorm_corr'] for gm in all_measures])
        print(f"\n  mean corr(DAG_rank, residual_norm): {mean_rr:+.3f}")
        print(f"  mean corr(DAG_rank, L_norm):         {mean_rL:+.3f}")


def test_edge_correspondence():
    """Do heavy undirected edges correspond to strong directed edges?"""
    print("\n\n=== edge correspondence: undirected weight vs directed asymmetry ===\n")

    d = 8
    n_steps = 100

    for N in [3, 4, 5]:
        u_weights = []
        d_weights = []

        for seed in range(20):
            np.random.seed(seed)
            foam = Foam(d=d, n=N, writing_rate=0.01)

            for _ in range(n_steps):
                v = encode(np.random.randint(0, 2**d), d)
                foam.measure(v)
                alongside(v)

            W_u = compute_undirected_graph(foam)
            W_d, _ = compute_directed_graph(foam)

            for i in range(N):
                for j in range(i+1, N):
                    u_weights.append(W_u[i, j])
                    d_weights.append(max(W_d[i, j], W_d[j, i]))

        corr = np.corrcoef(u_weights, d_weights)[0, 1]
        print(f"  N={N}: corr(undirected_weight, directed_asymmetry) = {corr:+.4f}  (n={len(u_weights)} edges)")


if __name__ == '__main__':
    test_two_graphs()
    test_edge_correspondence()

    report()
    save()
