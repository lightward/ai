"""
tsort_heirloom.py — what does the directed hierarchy look like on
a foam that has lived through genuinely mixed dynamics?

The heirloom foam (N=3, d=8, 12+ sessions) has been through
self-measurement, diff-reading, and experimental traffic from
multiple investigations. Its BCH residuals match no pure dynamic.

Our directed structure investigation only tested pure dynamics.
This is the test case for mixed dynamics: is there still a DAG?
Is it stable? Or does mixed history produce something different?
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, encode, cayley
from heirloom import alongside, get, report, save


def compute_directed_graph(foam):
    """Directed graph from BCH residual asymmetry."""
    N = foam.n
    bases = foam.bases
    A = np.zeros((N, N))

    residuals = []
    for i in range(N):
        try:
            log_T_i = logm(foam.bubbles[i].T)
        except Exception:
            log_T_i = np.zeros_like(foam.bubbles[i].T)
        R_i = log_T_i + 2 * foam.bubbles[i].L
        residuals.append(R_i)

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

    return W, A, residuals


def cyclicity_3(W):
    """0 = perfect DAG, 1 = perfect cycle."""
    cycle_012 = min(W[0, 1], W[1, 2], W[2, 0])
    cycle_021 = min(W[0, 2], W[2, 1], W[1, 0])
    cycle_strength = max(cycle_012, cycle_021)
    total = np.sum(W)
    if total < 1e-15:
        return 0.5
    return cycle_strength / (total / 3)


def dag_ordering(W, N):
    """Return ordering (most upstream first) and ranks."""
    in_deg = np.sum(W, axis=0)
    out_deg = np.sum(W, axis=1)
    net_out = out_deg - in_deg
    ordering = np.argsort(-net_out)
    ranks = np.zeros(N)
    for rank, idx in enumerate(ordering):
        ranks[idx] = rank
    return ordering, ranks, net_out


def farthest_neighbor_test(foam, residuals):
    """Does the residual point toward the farthest neighbor?"""
    N = foam.n
    bases = foam.bases
    results = []

    for i in range(N):
        R_i = residuals[i]
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

        if len(projections) >= 2:
            max_proj_bubble = max(projections, key=lambda x: x[1])[0]
            nearest = min(distances, key=lambda x: x[1])[0]
            farthest = max(distances, key=lambda x: x[1])[0]
            results.append({
                'bubble': i,
                'points_toward': max_proj_bubble,
                'nearest': nearest,
                'farthest': farthest,
                'toward_farthest': max_proj_bubble == farthest,
            })

    return results


def read_heirloom():
    """Read the heirloom foam and compute its directed structure."""
    print("=== the heirloom's directed hierarchy ===\n")

    foam = get()

    # basic state
    print(f"  N={foam.n}, d={foam.d}")
    print(f"  L = {foam.boundary_cost():.4f}")
    print()

    # per-bubble properties
    print("  --- per-bubble state ---")
    print(f"  {'bubble':>6s}  {'‖L‖':>8s}  {'‖log T‖':>8s}  {'‖R‖':>8s}  {'T phase':>8s}")
    for i in range(foam.n):
        L_norm = np.linalg.norm(foam.bubbles[i].L)
        try:
            log_T = logm(foam.bubbles[i].T)
            log_T_norm = np.linalg.norm(log_T)
            R = log_T + 2 * foam.bubbles[i].L
            R_norm = np.linalg.norm(R)
        except Exception:
            log_T_norm = 0
            R_norm = 0
        phase = np.angle(np.linalg.det(foam.bubbles[i].T))
        print(f"  {i:6d}  {L_norm:8.4f}  {log_T_norm:8.4f}  {R_norm:8.4f}  {phase/np.pi:+8.4f}π")

    print()

    # directed graph
    W, A, residuals = compute_directed_graph(foam)
    cyc = cyclicity_3(W)
    ordering, ranks, net_out = dag_ordering(W, foam.n)

    print("  --- directed structure ---")
    print(f"  asymmetry matrix A:")
    for i in range(foam.n):
        row = "    "
        for j in range(foam.n):
            row += f"{A[i,j]:+8.4f}  "
        print(row)

    print(f"\n  directed edges W:")
    for i in range(foam.n):
        row = "    "
        for j in range(foam.n):
            row += f"{W[i,j]:8.4f}  "
        print(row)

    print(f"\n  cyclicity: {cyc:.4f}  ({'DAG' if cyc < 0.01 else 'has cycles' if cyc > 0.3 else 'weak cycles'})")
    print(f"  DAG ordering (upstream first): {list(ordering)}")
    print(f"  net outflow: {[f'{x:.4f}' for x in net_out]}")

    # rank vs properties correlation
    L_norms = [np.linalg.norm(foam.bubbles[i].L) for i in range(foam.n)]
    R_norms = [np.linalg.norm(residuals[i]) for i in range(foam.n)]

    corr_L = np.corrcoef(ranks, L_norms)[0, 1]
    corr_R = np.corrcoef(ranks, R_norms)[0, 1]
    print(f"\n  corr(rank, ‖L‖): {corr_L:+.3f}")
    print(f"  corr(rank, ‖R‖): {corr_R:+.3f}")

    # farthest neighbor
    fn = farthest_neighbor_test(foam, residuals)
    print(f"\n  --- residual direction ---")
    for r in fn:
        toward = "FARTHEST" if r['toward_farthest'] else f"bubble {r['points_toward']}"
        print(f"  bubble {r['bubble']}: points toward {toward} (nearest={r['nearest']}, farthest={r['farthest']})")

    # pairwise distances for context
    print(f"\n  --- pairwise distances ---")
    bases = foam.bases
    for i in range(foam.n):
        for j in range(i+1, foam.n):
            d = foam.bi_invariant_distance(bases[i], bases[j])
            print(f"  d({i},{j}) = {d:.4f}")

    return foam, W, A, residuals, cyc, ordering


def stability_test(foam):
    """Probe the heirloom with fresh inputs — does the ordering change?"""
    print("\n\n=== stability: does fresh input change the heirloom's ordering? ===\n")

    # snapshot the current ordering
    W0, _, _ = compute_directed_graph(foam)
    ordering0, _, _ = dag_ordering(W0, foam.n)
    print(f"  current ordering: {list(ordering0)}")

    # make a copy so we don't modify the real heirloom
    # (we can't easily copy a Foam, so we'll just read without writing)
    # instead: compute the directed graph after hypothetical measurement
    # by looking at what fresh inputs do to write asymmetry

    print(f"\n  probing with 50 random inputs (read-only, no writes)...")

    rng = np.random.RandomState(42)
    bases = foam.bases

    asymmetries = []
    for _ in range(50):
        v = encode(rng.randint(0, 2**foam.d), foam.d)
        vc = v.astype(complex)
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        dissonance = [j2[i] - m[i] for i in range(foam.n)]

        # per-bubble dissonance magnitude
        dis_mags = [np.linalg.norm(d) for d in dissonance]
        asymmetries.append(dis_mags)

    mean_dis = np.mean(asymmetries, axis=0)
    print(f"  mean dissonance per bubble: {[f'{x:.4f}' for x in mean_dis]}")
    print(f"  upstream bubble ({ordering0[0]}) dissonance: {mean_dis[ordering0[0]]:.4f}")
    print(f"  downstream bubble ({ordering0[-1]}) dissonance: {mean_dis[ordering0[-1]]:.4f}")
    print(f"  ratio: {mean_dis[ordering0[0]] / (mean_dis[ordering0[-1]] + 1e-12):.3f}")


def orientation_test(foam, ordering):
    """Does which bubble you read through change what you learn?

    The upstream bubble (least written) should give more diverse readouts.
    The downstream bubble (most written) should be more specialized.

    Test: for many random inputs, collect each bubble's raw measurement
    (j0_i = v @ U_i). Measure the diversity of these readouts per bubble.
    """
    print("\n\n=== does foam orientation matter for readout? ===\n")

    N = foam.n
    d = foam.d
    n_probes = 200

    rng = np.random.RandomState(42)

    # collect per-bubble readouts
    readouts = [[] for _ in range(N)]
    j2_readouts = [[] for _ in range(N)]

    for _ in range(n_probes):
        v = encode(rng.randint(0, 2**d), d)
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)

        for i in range(N):
            readouts[i].append(m[i])
            j2_readouts[i].append(j2[i])

    print(f"  DAG ordering (upstream first): {list(ordering)}")
    print()

    # per-bubble readout diversity:
    # how spread out are the readouts across different inputs?
    # measure via effective rank of the readout matrix
    print(f"  --- readout diversity (effective rank of j0 across {n_probes} probes) ---")
    for rank_pos, idx in enumerate(ordering):
        mat = np.array(readouts[idx])  # (n_probes, d) complex
        # use real and imaginary parts
        mat_real = np.hstack([mat.real, mat.imag])
        sv = np.linalg.svd(mat_real, compute_uv=False)
        sv_norm = sv / (sv.sum() + 1e-12)
        eff_rank = np.exp(-np.sum(sv_norm * np.log(sv_norm + 1e-12)))
        pos = "upstream" if rank_pos == 0 else ("downstream" if rank_pos == N-1 else "middle")
        print(f"  bubble {idx} ({pos}): eff_rank = {eff_rank:.2f}")

    print()
    print(f"  --- readout diversity (effective rank of j2 across {n_probes} probes) ---")
    for rank_pos, idx in enumerate(ordering):
        mat = np.array(j2_readouts[idx])
        mat_real = np.hstack([mat.real, mat.imag])
        sv = np.linalg.svd(mat_real, compute_uv=False)
        sv_norm = sv / (sv.sum() + 1e-12)
        eff_rank = np.exp(-np.sum(sv_norm * np.log(sv_norm + 1e-12)))
        pos = "upstream" if rank_pos == 0 else ("downstream" if rank_pos == N-1 else "middle")
        print(f"  bubble {idx} ({pos}): eff_rank = {eff_rank:.2f}")

    # per-bubble view diversity:
    # how differently does each bubble respond to different inputs?
    # measure via mean pairwise cosine distance between readouts
    print()
    print(f"  --- view diversity (mean pairwise angle between readouts) ---")
    for rank_pos, idx in enumerate(ordering):
        mat = np.array(readouts[idx])
        norms = np.linalg.norm(mat, axis=1, keepdims=True)
        mat_normed = mat / (norms + 1e-12)
        # sample pairwise cosines
        n_sample = min(500, n_probes * (n_probes - 1) // 2)
        angles = []
        for _ in range(n_sample):
            i, j = rng.randint(0, n_probes, size=2)
            if i == j:
                continue
            cos = np.real(np.dot(mat_normed[i].conj(), mat_normed[j]))
            angles.append(np.arccos(np.clip(cos, -1, 1)))
        mean_angle = np.mean(angles)
        pos = "upstream" if rank_pos == 0 else ("downstream" if rank_pos == N-1 else "middle")
        print(f"  bubble {idx} ({pos}): mean angle = {np.degrees(mean_angle):.1f}°")

    # discrimination: how well does each bubble distinguish between inputs?
    # for pairs of inputs, how different are their readouts through each bubble?
    print()
    print(f"  --- discrimination (input-pair distinguishability per bubble) ---")
    for rank_pos, idx in enumerate(ordering):
        mat = np.array(readouts[idx])
        # for random pairs of inputs, compute readout distance
        dists = []
        for _ in range(500):
            i, j = rng.randint(0, n_probes, size=2)
            if i == j:
                continue
            dists.append(np.linalg.norm(mat[i] - mat[j]))
        mean_dist = np.mean(dists)
        pos = "upstream" if rank_pos == 0 else ("downstream" if rank_pos == N-1 else "middle")
        print(f"  bubble {idx} ({pos}): mean readout distance = {mean_dist:.4f}")


if __name__ == '__main__':
    foam, W, A, residuals, cyc, ordering = read_heirloom()
    stability_test(foam)
    orientation_test(foam, ordering)

    report()
    save()
