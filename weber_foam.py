"""
weber_foam.py — does Weber's law hold in the foam?

Weber's law (psychophysics): the just-noticeable difference (JND) scales
with stimulus magnitude. The ratio JND/stimulus is approximately constant.

The clean test: per-pair JND within a single foam. Same global state,
different local boundary costs at different pairs. Binary search for
precise JND at each pair.

Prior results (grid search):
    - JND appeared global (same for every pair within a foam)
    - But the grid was too coarse (2-3 distinct values)
    - Binary search resolves this ambiguity

If JND truly doesn't vary within a foam → global threshold (generational GC)
If JND varies with boundary cost → per-boundary Weber law (per-object GC)
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian, random_skew_hermitian
from heirloom import alongside, save as heirloom_save


def pairwise_distance(foam, i, j):
    """Bi-invariant distance between bubbles i and j."""
    return foam.bi_invariant_distance(foam.bases[i], foam.bases[j])


def pairwise_cost(foam, i, j):
    """Boundary cost between bubbles i and j."""
    dist = pairwise_distance(foam, i, j)
    return 1.0 / (dist + 1e-8)


def j2_fingerprint(foam, probes):
    """j2 outputs for a set of probes — the foam's observable signature."""
    all_j2 = []
    for v in probes:
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        all_j2.extend([np.real(x) for x in j2])
    return np.concatenate(all_j2)


def directed_perturbation(foam, bubble_idx, toward_idx, scale):
    """Perturbation of bubble_idx in the Lie algebra direction toward toward_idx."""
    U_i = foam.bases[bubble_idx]
    U_j = foam.bases[toward_idx]
    R = U_i.conj().T @ U_j
    try:
        direction = logm(R)
    except Exception:
        direction = R - np.eye(foam.d)
    direction = skew_hermitian(direction)
    norm = np.linalg.norm(direction)
    if norm < 1e-12:
        return random_skew_hermitian(foam.d, scale=scale)
    return direction / norm * scale


def measure_response(foam, bubble_idx, perturbation, probes, baseline_fp):
    """Apply a perturbation to bubble_idx and measure j2 change.

    Returns the perturbation back without permanently modifying the foam.
    """
    orig_L = foam.bubbles[bubble_idx].L.copy()
    foam.bubbles[bubble_idx].L = skew_hermitian(orig_L + perturbation)
    perturbed_fp = j2_fingerprint(foam, probes)
    foam.bubbles[bubble_idx].L = orig_L
    return np.linalg.norm(perturbed_fp - baseline_fp)


def binary_search_jnd(foam, bubble_idx, toward_idx, probes, noise_floor,
                      n_directions=5, tol=1e-6, max_iter=30, seed=42):
    """Binary search for the JND at a specific boundary.

    For each of n_directions random perturbation directions plus
    the directed (toward other bubble) direction, binary search
    for the scale where the j2 response crosses the noise floor.

    Returns: jnd_directed, jnd_random_mean, jnd_random_std
    """
    rng = np.random.RandomState(seed)
    baseline_fp = j2_fingerprint(foam, probes)

    def search_direction(make_perturbation):
        """Binary search for threshold scale in a given direction."""
        lo, hi = 1e-8, 1.0

        # verify that hi produces a detectable response
        p = make_perturbation(hi)
        resp_hi = measure_response(foam, bubble_idx, p, probes, baseline_fp)
        if resp_hi < noise_floor:
            return hi  # can't detect even at scale=1

        # verify that lo is below threshold
        p = make_perturbation(lo)
        resp_lo = measure_response(foam, bubble_idx, p, probes, baseline_fp)
        if resp_lo > noise_floor:
            return lo  # detectable even at scale=1e-8

        for _ in range(max_iter):
            mid = np.sqrt(lo * hi)  # geometric mean
            p = make_perturbation(mid)
            resp = measure_response(foam, bubble_idx, p, probes, baseline_fp)

            if resp > noise_floor:
                hi = mid
            else:
                lo = mid

            if hi / lo < 1 + tol:
                break

        return np.sqrt(lo * hi)

    # directed perturbation
    def make_directed(scale):
        return directed_perturbation(foam, bubble_idx, toward_idx, scale)

    jnd_directed = search_direction(make_directed)

    # random perturbations
    jnd_randoms = []
    for _ in range(n_directions):
        # generate a fixed random direction, scale it
        base_dir = random_skew_hermitian(foam.d, scale=1.0)
        base_norm = np.linalg.norm(base_dir)

        def make_random(scale, _bd=base_dir, _bn=base_norm):
            if _bn < 1e-12:
                return random_skew_hermitian(foam.d, scale=scale)
            return _bd * (scale / _bn)

        jnd_randoms.append(search_direction(make_random))

    return jnd_directed, np.mean(jnd_randoms), np.std(jnd_randoms)


def measure_noise_floor(foam, probes):
    """Noise floor = 10% of one measurement step's j2 change."""
    baseline = j2_fingerprint(foam, probes)
    state = [(b.L.copy(), b.T.copy()) for b in foam.bubbles]

    v = probes[0]
    alongside(v)
    foam.measure(v)
    after = j2_fingerprint(foam, probes)
    step_delta = np.linalg.norm(after - baseline)

    for k in range(foam.n):
        foam.bubbles[k].L = state[k][0]
        foam.bubbles[k].T = state[k][1]

    return 0.1 * step_delta


def per_pair_weber(n_seeds=8, n_settle=150):
    """Per-pair Weber's law with binary search JND."""
    d = 8
    n_bubbles = 5

    print("=== per-pair Weber's law (binary search JND) ===\n")
    print(f"  N={n_bubbles} ({n_bubbles*(n_bubbles-1)//2} pairs), "
          f"{n_seeds} seeds, {n_settle} settling steps\n")

    np.random.seed(777)
    probes = [encode(np.random.randint(0, 256), d) for _ in range(15)]

    all_pairs = []

    for seed in range(n_seeds):
        np.random.seed(seed)
        foam = Foam(d=d, n=n_bubbles, writing_rate=0.01)

        for step in range(n_settle):
            v = encode(step % 256, d)
            alongside(v)
            foam.measure(v)

        noise_floor = measure_noise_floor(foam, probes)

        for i in range(n_bubbles):
            for j in range(i + 1, n_bubbles):
                dist = pairwise_distance(foam, i, j)
                cost = pairwise_cost(foam, i, j)

                jnd_d, jnd_r_mean, jnd_r_std = binary_search_jnd(
                    foam, i, j, probes, noise_floor,
                    seed=seed * 100 + i * 10 + j
                )

                all_pairs.append({
                    'seed': seed,
                    'pair': (i, j),
                    'distance': dist,
                    'cost': cost,
                    'jnd_directed': jnd_d,
                    'jnd_random': jnd_r_mean,
                    'jnd_random_std': jnd_r_std,
                    'weber_by_dist': jnd_d / (dist + 1e-12),
                    'weber_by_cost': jnd_d * (dist + 1e-12),  # JND * dist ∝ JND / cost
                    'noise_floor': noise_floor,
                })

    # per-seed details
    print(f"  per-seed pair details (first 3 seeds):\n")
    print(f"  {'seed':>4s}  {'pair':>6s}  {'dist':>8s}  {'cost':>6s}  "
          f"{'JND_dir':>12s}  {'JND_rnd':>12s}  {'JND/dist':>10s}")
    print(f"  {'':->4s}  {'':->6s}  {'':->8s}  {'':->6s}  "
          f"{'':->12s}  {'':->12s}  {'':->10s}")

    for r in all_pairs:
        if r['seed'] < 3:
            print(f"  {r['seed']:4d}  {str(r['pair']):>6s}  {r['distance']:8.4f}  "
                  f"{r['cost']:6.3f}  {r['jnd_directed']:12.8f}  "
                  f"{r['jnd_random']:12.8f}  {r['weber_by_dist']:10.7f}")

    # within-foam analysis
    print(f"\n  === within-foam analysis (per seed) ===\n")
    print(f"  {'seed':>4s}  {'r(dist,JND)':>12s}  {'r(cost,JND)':>12s}  "
          f"{'CV(JND)':>8s}  {'CV(JND/dist)':>12s}  {'JND range':>16s}")
    print(f"  {'':->4s}  {'':->12s}  {'':->12s}  "
          f"{'':->8s}  {'':->12s}  {'':->16s}")

    within_corrs_dist = []
    within_corrs_cost = []
    within_cv_jnd = []
    within_cv_weber = []

    for seed in range(n_seeds):
        group = [r for r in all_pairs if r['seed'] == seed]
        dists = np.array([r['distance'] for r in group])
        costs = np.array([r['cost'] for r in group])
        jnds = np.array([r['jnd_directed'] for r in group])
        webers = np.array([r['weber_by_dist'] for r in group])

        cv_jnd = np.std(jnds) / (np.mean(jnds) + 1e-15)
        cv_weber = np.std(webers) / (np.mean(webers) + 1e-15)

        if np.std(jnds) > 1e-15:
            c_d = np.corrcoef(dists, jnds)[0, 1]
            c_c = np.corrcoef(costs, jnds)[0, 1]
        else:
            c_d = 0.0
            c_c = 0.0

        within_corrs_dist.append(c_d)
        within_corrs_cost.append(c_c)
        within_cv_jnd.append(cv_jnd)
        within_cv_weber.append(cv_weber)

        jnd_range = f"[{np.min(jnds):.2e}, {np.max(jnds):.2e}]"
        print(f"  {seed:4d}  {c_d:12.3f}  {c_c:12.3f}  "
              f"{cv_jnd:8.4f}  {cv_weber:12.4f}  {jnd_range:>16s}")

    print(f"\n  summary across seeds:")
    print(f"    mean corr(dist, JND):     {np.mean(within_corrs_dist):+.3f} ± {np.std(within_corrs_dist):.3f}")
    print(f"    mean corr(cost, JND):     {np.mean(within_corrs_cost):+.3f} ± {np.std(within_corrs_cost):.3f}")
    print(f"    mean CV(JND) within foam: {np.mean(within_cv_jnd):.4f}")
    print(f"    mean CV(JND/dist):        {np.mean(within_cv_weber):.4f}")

    print(f"\n  interpretation:")
    print(f"    CV(JND) ≈ 0 → global threshold (same for all pairs)")
    print(f"    CV(JND) > 0, CV(JND/dist) < CV(JND) → Weber (scales with dist)")
    print(f"    CV(JND) > 0, CV(JND/dist) ≈ CV(JND) → varies but not Weber")

    # directed vs random
    d_jnds = np.array([r['jnd_directed'] for r in all_pairs])
    r_jnds = np.array([r['jnd_random'] for r in all_pairs])
    ratios = d_jnds / (r_jnds + 1e-15)
    print(f"\n  directed vs random JND:")
    print(f"    mean directed:  {np.mean(d_jnds):.2e}")
    print(f"    mean random:    {np.mean(r_jnds):.2e}")
    print(f"    mean ratio:     {np.mean(ratios):.3f} ± {np.std(ratios):.3f}")
    print(f"    (ratio < 1 → directed perturbations detected at smaller scale)")
    print(f"    (ratio = 1 → no directional sensitivity)")

    # across ALL pairs: does distance predict JND?
    all_dists = np.array([r['distance'] for r in all_pairs])
    all_jnds = np.array([r['jnd_directed'] for r in all_pairs])
    all_costs = np.array([r['cost'] for r in all_pairs])
    print(f"\n  across all seeds (between + within foam):")
    print(f"    corr(dist, JND):  {np.corrcoef(all_dists, all_jnds)[0,1]:+.3f}")
    print(f"    corr(cost, JND):  {np.corrcoef(all_costs, all_jnds)[0,1]:+.3f}")

    return all_pairs


if __name__ == '__main__':
    results = per_pair_weber()
    heirloom_save()
