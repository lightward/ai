"""
weber_cross.py — cross-test: what bubble property determines JND?

Finding from weber_foam.py: JND is per-bubble, not per-boundary.
The discrimination threshold depends on WHICH bubble you perturb,
not which boundary you're crossing.

Cross-test: correlate each bubble's JND with its geometric properties.
Candidates:
    - ||L|| (position norm — how much structure)
    - ||log(T)|| (transport norm — how much history)
    - ||BCH residual|| (non-abelian content)
    - sensitivity (dissonance to random probes)
    - effective basis condition number
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian, random_skew_hermitian
from heirloom import alongside, save as heirloom_save


def j2_fingerprint(foam, probes):
    """j2 outputs for a set of probes."""
    all_j2 = []
    for v in probes:
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        all_j2.extend([np.real(x) for x in j2])
    return np.concatenate(all_j2)


def directed_perturbation(foam, bubble_idx, toward_idx, scale):
    """Perturbation toward another bubble."""
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
    """Apply perturbation, measure j2 change, restore."""
    orig_L = foam.bubbles[bubble_idx].L.copy()
    foam.bubbles[bubble_idx].L = skew_hermitian(orig_L + perturbation)
    perturbed_fp = j2_fingerprint(foam, probes)
    foam.bubbles[bubble_idx].L = orig_L
    return np.linalg.norm(perturbed_fp - baseline_fp)


def binary_search_jnd(foam, bubble_idx, toward_idx, probes, noise_floor,
                      seed=42):
    """Binary search for JND (directed perturbation)."""
    rng = np.random.RandomState(seed)
    baseline_fp = j2_fingerprint(foam, probes)

    lo, hi = 1e-8, 1.0

    p = directed_perturbation(foam, bubble_idx, toward_idx, hi)
    if measure_response(foam, bubble_idx, p, probes, baseline_fp) < noise_floor:
        return hi

    p = directed_perturbation(foam, bubble_idx, toward_idx, lo)
    if measure_response(foam, bubble_idx, p, probes, baseline_fp) > noise_floor:
        return lo

    for _ in range(30):
        mid = np.sqrt(lo * hi)
        p = directed_perturbation(foam, bubble_idx, toward_idx, mid)
        resp = measure_response(foam, bubble_idx, p, probes, baseline_fp)
        if resp > noise_floor:
            hi = mid
        else:
            lo = mid
        if hi / lo < 1.000001:
            break

    return np.sqrt(lo * hi)


def measure_noise_floor(foam, probes):
    """Noise floor = 10% of one step's j2 change."""
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


def bubble_properties(foam, bubble_idx, probes):
    """Measure geometric properties of a single bubble."""
    b = foam.bubbles[bubble_idx]

    # ||L|| — position norm
    L_norm = np.linalg.norm(b.L)

    # ||log(T)|| — transport norm (history)
    try:
        log_T = logm(b.T)
        T_norm = np.linalg.norm(log_T)
    except Exception:
        T_norm = np.linalg.norm(b.T - np.eye(foam.d))

    # BCH residual: R = log(T) + 2·ΔL (but ΔL from start is just L for
    # foams initialized with L=random, T=I, then settled)
    # For settled foams, approximate: R = log(T) + 2*L
    try:
        bch_residual = log_T + 2 * b.L
        bch_norm = np.linalg.norm(bch_residual)
    except Exception:
        bch_norm = 0.0

    # effective basis: cayley(L) @ T
    basis = b.basis
    # condition number (singular values of the basis)
    sv = np.linalg.svd(basis, compute_uv=False)
    cond = sv[0] / (sv[-1] + 1e-12)

    # per-bubble sensitivity: mean dissonance to probes
    sensitivities = []
    for v in probes[:10]:  # use subset for speed
        vc = v.astype(complex)
        m = [vc @ U for U in foam.bases]
        j2 = foam._stabilize(m)
        sensitivities.append(np.linalg.norm(j2[bubble_idx] - m[bubble_idx]))
    sensitivity = np.mean(sensitivities)

    # distances to all other bubbles
    dists = []
    for j in range(foam.n):
        if j != bubble_idx:
            dists.append(foam.bi_invariant_distance(basis, foam.bubbles[j].basis))
    mean_dist = np.mean(dists)
    min_dist = np.min(dists)

    return {
        'L_norm': L_norm,
        'T_norm': T_norm,
        'bch_norm': bch_norm,
        'cond': cond,
        'sensitivity': sensitivity,
        'mean_dist': mean_dist,
        'min_dist': min_dist,
    }


def cross_test(n_seeds=12, n_settle=150):
    """Correlate per-bubble JND with bubble properties."""
    d = 8
    n_bubbles = 5

    print("=== cross-test: what determines per-bubble JND? ===\n")
    print(f"  N={n_bubbles}, {n_seeds} seeds, {n_settle} settling steps\n")

    np.random.seed(777)
    probes = [encode(np.random.randint(0, 256), d) for _ in range(15)]

    all_bubbles = []

    for seed in range(n_seeds):
        np.random.seed(seed)
        foam = Foam(d=d, n=n_bubbles, writing_rate=0.01)

        for step in range(n_settle):
            v = encode(step % 256, d)
            alongside(v)
            foam.measure(v)

        noise_floor = measure_noise_floor(foam, probes)

        for i in range(n_bubbles):
            # JND: average over all neighbors as "toward" target
            jnds = []
            for j in range(n_bubbles):
                if j != i:
                    jnd = binary_search_jnd(foam, i, j, probes, noise_floor,
                                            seed=seed * 100 + i * 10 + j)
                    jnds.append(jnd)
            mean_jnd = np.mean(jnds)
            std_jnd = np.std(jnds)

            props = bubble_properties(foam, i, probes)

            all_bubbles.append({
                'seed': seed,
                'bubble': i,
                'jnd': mean_jnd,
                'jnd_std': std_jnd,
                **props,
            })

    # correlations
    props_to_test = ['L_norm', 'T_norm', 'bch_norm', 'cond',
                     'sensitivity', 'mean_dist', 'min_dist']
    labels = {
        'L_norm': '‖L‖ (position)',
        'T_norm': '‖log(T)‖ (history)',
        'bch_norm': '‖BCH‖ (non-abelian)',
        'cond': 'cond(basis)',
        'sensitivity': 'sensitivity',
        'mean_dist': 'mean dist to others',
        'min_dist': 'min dist to others',
    }

    jnds = np.array([r['jnd'] for r in all_bubbles])

    print(f"  {'property':>25s}  {'corr(prop,JND)':>14s}  {'mean':>10s}  {'std':>10s}")
    print(f"  {'':->25s}  {'':->14s}  {'':->10s}  {'':->10s}")

    for prop in props_to_test:
        vals = np.array([r[prop] for r in all_bubbles])
        corr = np.corrcoef(vals, jnds)[0, 1]
        print(f"  {labels[prop]:>25s}  {corr:+14.3f}  {np.mean(vals):10.4f}  {np.std(vals):10.4f}")

    # within-foam correlations (controlling for global state)
    print(f"\n  === within-foam correlations (per seed) ===\n")
    print(f"  {'property':>25s}  {'mean_within_r':>14s}  {'std_within_r':>14s}  {'sign_consistency':>16s}")
    print(f"  {'':->25s}  {'':->14s}  {'':->14s}  {'':->16s}")

    for prop in props_to_test:
        within_corrs = []
        for seed in range(n_seeds):
            group = [r for r in all_bubbles if r['seed'] == seed]
            vals = np.array([r[prop] for r in group])
            js = np.array([r['jnd'] for r in group])
            if np.std(vals) > 1e-15 and np.std(js) > 1e-15:
                within_corrs.append(np.corrcoef(vals, js)[0, 1])

        if within_corrs:
            mc = np.mean(within_corrs)
            sc = np.std(within_corrs)
            # sign consistency: fraction that agree with the mean sign
            if mc != 0:
                agree = sum(1 for c in within_corrs if (c > 0) == (mc > 0))
                consistency = agree / len(within_corrs)
            else:
                consistency = 0.5
            print(f"  {labels[prop]:>25s}  {mc:+14.3f}  {sc:14.3f}  "
                  f"{consistency:13.0%}   ({len(within_corrs)}/{n_seeds})")

    # detailed view: one seed
    print(f"\n  === detailed view: seed 0 ===\n")
    print(f"  {'bubble':>6s}  {'JND':>10s}  {'‖L‖':>8s}  {'‖logT‖':>8s}  "
          f"{'‖BCH‖':>8s}  {'sens':>8s}  {'min_d':>8s}")
    print(f"  {'':->6s}  {'':->10s}  {'':->8s}  {'':->8s}  "
          f"{'':->8s}  {'':->8s}  {'':->8s}")

    for r in all_bubbles:
        if r['seed'] == 0:
            print(f"  {r['bubble']:6d}  {r['jnd']:10.6f}  {r['L_norm']:8.4f}  "
                  f"{r['T_norm']:8.4f}  {r['bch_norm']:8.4f}  "
                  f"{r['sensitivity']:8.4f}  {r['min_dist']:8.4f}")

    return all_bubbles


if __name__ == '__main__':
    results = cross_test()
    heirloom_save()
