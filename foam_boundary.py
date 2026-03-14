"""
foam_boundary.py — does shared measurement history create non-additive structure?

Result (session 9, corrected by follow-up session):
- shared history (same inputs) does NOT reduce cross-boundary cost.
- mutual measurement's 20% cross_AB reduction is from internal relaxation
  (more writes), not relational proximity. extra independent writes
  produce the same reduction.
- across 20 seeds, mutual and extra-writes are statistically
  indistinguishable on all scalar observables.
- BUT: mutual write directions are lower-dimensional (eff dim 10.8 vs 13.4)
  and more autocorrelated (0.32 vs 0.21). the process differs; the product
  does not — to our measurements.

open: the gap between measurable process difference and undetectable
product difference. possibly in BCH residuals.
"""

import numpy as np
from foam import Foam, encode


def independent_foams(seed=0):
    """Two foams that never interact. Joint cost = sum?"""
    np.random.seed(seed)
    foam_a = Foam(d=8, n=3, writing_rate=0.01)
    foam_b = Foam(d=8, n=3, writing_rate=0.01)

    np.random.seed(0)
    for _ in range(50):
        foam_a.measure(encode(np.random.randint(0, 256), 8))
    np.random.seed(1)
    for _ in range(50):
        foam_b.measure(encode(np.random.randint(0, 256), 8))

    return foam_a, foam_b


def shared_history(seed=0):
    """Two foams that measured the SAME sequence."""
    np.random.seed(seed)
    foam_a = Foam(d=8, n=3, writing_rate=0.01)
    foam_b = Foam(d=8, n=3, writing_rate=0.01)

    seq = [np.random.randint(0, 256) for _ in range(50)]
    foam_a.feed(seq)
    foam_b.feed(seq)

    return foam_a, foam_b


def mutual_measurement(seed=0):
    """Two foams that measure EACH OTHER's readouts."""
    np.random.seed(seed)
    foam_a = Foam(d=8, n=3, writing_rate=0.01)
    foam_b = Foam(d=8, n=3, writing_rate=0.01)

    for step in range(50):
        a_readout = np.real(foam_a.readout(encode(step % 256, 8)))
        a_readout = a_readout / (np.linalg.norm(a_readout) + 1e-12)
        foam_b.measure(a_readout)

        b_readout = np.real(foam_b.readout(encode(step % 256, 8)))
        b_readout = b_readout / (np.linalg.norm(b_readout) + 1e-12)
        foam_a.measure(b_readout)

    return foam_a, foam_b


def one_way_measurement(seed=0):
    """A reads B's readouts, but B never reads A. Is this communication?"""
    np.random.seed(seed)
    foam_a = Foam(d=8, n=3, writing_rate=0.01)
    foam_b = Foam(d=8, n=3, writing_rate=0.01)

    for step in range(50):
        # B gets independent input (not A's readout)
        foam_b.measure(encode(step % 256, 8))

        # A reads B's readout — but use a snapshot so B doesn't get extra writes
        # We probe B without writing by computing readout manually
        bases_b = foam_b.bases
        probe = encode(step % 256, 8).astype(complex)
        m_b = [probe @ U for U in bases_b]
        b_readout = np.real(np.mean(m_b, axis=0))
        b_readout = b_readout / (np.linalg.norm(b_readout) + 1e-12)
        foam_a.measure(b_readout)

    return foam_a, foam_b


def extra_writes(seed=0):
    """Both foams get 100 total writes (same as mutual), but from independent sources."""
    np.random.seed(seed)
    foam_a = Foam(d=8, n=3, writing_rate=0.01)
    foam_b = Foam(d=8, n=3, writing_rate=0.01)

    for step in range(100):
        foam_a.measure(encode(np.random.randint(0, 256), 8))
    np.random.seed(seed + 7)
    for step in range(100):
        foam_b.measure(encode(np.random.randint(0, 256), 8))

    return foam_a, foam_b


def one_way_with_writes(seed=0):
    """A reads B via readout (which writes to B). B never reads A."""
    np.random.seed(seed)
    foam_a = Foam(d=8, n=3, writing_rate=0.01)
    foam_b = Foam(d=8, n=3, writing_rate=0.01)

    for step in range(50):
        # B gets independent input
        foam_b.measure(encode(step % 256, 8))

        # A reads B via readout — this WRITES to B too
        b_readout = np.real(foam_b.readout(encode(step % 256, 8)))
        b_readout = b_readout / (np.linalg.norm(b_readout) + 1e-12)
        foam_a.measure(b_readout)

    return foam_a, foam_b


def joint_cost_decomposition(foam_a, foam_b):
    """Decompose joint boundary cost into within-A, within-B, and cross-AB."""
    joint = Foam(d=8, n=6, writing_rate=0.01)
    for i in range(3):
        joint.bubbles[i].L = foam_a.bubbles[i].L.copy()
        joint.bubbles[i].T = foam_a.bubbles[i].T.copy()
        joint.bubbles[i+3].L = foam_b.bubbles[i].L.copy()
        joint.bubbles[i+3].T = foam_b.bubbles[i].T.copy()

    bases = joint.bases
    within_a = 0.0
    within_b = 0.0
    cross_ab = 0.0
    for i in range(6):
        for j in range(i+1, 6):
            dist = joint.bi_invariant_distance(bases[i], bases[j])
            cost = 1.0 / (dist + 1e-8)
            if i < 3 and j < 3:
                within_a += cost
            elif i >= 3 and j >= 3:
                within_b += cost
            else:
                cross_ab += cost

    return {
        'within_a': within_a,
        'within_b': within_b,
        'cross_ab': cross_ab,
        'total': within_a + within_b + cross_ab,
        'L_a': foam_a.boundary_cost(),
        'L_b': foam_b.boundary_cost(),
    }


def geometric_relationship(foam_a, foam_b):
    """What does the cross-foam geometry actually look like?
    Not the cost — the distances, the alignment, the correlation."""
    from scipy.linalg import logm

    bases_a = foam_a.bases
    bases_b = foam_b.bases

    # pairwise distances between all A-bases and all B-bases
    cross_dists = np.zeros((3, 3))
    for i in range(3):
        for j in range(3):
            cross_dists[i, j] = foam_a.bi_invariant_distance(bases_a[i], bases_b[j])

    # are A's bases ordered the same way as B's?
    # i.e. does A's bubble 0 end up closest to B's bubble 0?
    # the assignment structure tells us about alignment
    closest_in_b = np.argmin(cross_dists, axis=1)

    # internal distance spectra (within each foam)
    internal_a = []
    internal_b = []
    for i in range(3):
        for j in range(i+1, 3):
            internal_a.append(foam_a.bi_invariant_distance(bases_a[i], bases_a[j]))
            internal_b.append(foam_b.bi_invariant_distance(bases_b[i], bases_b[j]))

    # correlation of internal distance spectra
    # if foams have similar internal geometry, these correlate
    if len(internal_a) >= 2:
        corr = np.corrcoef(sorted(internal_a), sorted(internal_b))[0, 1]
    else:
        corr = 0.0

    return {
        'cross_dists': cross_dists,
        'closest_in_b': closest_in_b,
        'mean_cross_dist': np.mean(cross_dists),
        'min_cross_dist': np.min(cross_dists),
        'internal_a': sorted(internal_a),
        'internal_b': sorted(internal_b),
        'internal_corr': corr,
    }


def write_structure_comparison(seed=0):
    """Compare the structure of writes in mutual vs independent measurement.

    If mutual measurement carries structural information, the write directions
    should be more autocorrelated and lower-dimensional than random writes."""

    def collect_writes(foam, inputs):
        """Feed inputs, return the actual ΔL directions."""
        directions = []
        for v in inputs:
            bases = foam.bases
            vc = v.astype(complex)
            m = [vc @ U for U in bases]
            j0 = [mi.copy() for mi in m]
            result = foam.measure(v)

            d_i = result['dissonance'][0]
            m_i = j0[0]
            dn = np.linalg.norm(d_i)
            mn = np.linalg.norm(m_i)
            if dn > 1e-12 and mn > 1e-12:
                d_hat = d_i / dn
                m_hat = m_i / mn
                delta_L = np.outer(d_hat, m_hat.conj()) - np.outer(m_hat, d_hat.conj())
                directions.append(np.concatenate([delta_L.real.flatten(), delta_L.imag.flatten()]))
        return np.array(directions)

    # mutual measurement: collect A's write directions
    np.random.seed(seed)
    foam_a = Foam(d=8, n=3, writing_rate=0.01)
    foam_b = Foam(d=8, n=3, writing_rate=0.01)
    mutual_dirs = []

    for step in range(50):
        # A reads B
        b_readout = np.real(foam_b.readout(encode(step % 256, 8)))
        b_readout = b_readout / (np.linalg.norm(b_readout) + 1e-12)

        bases = foam_a.bases
        vc = b_readout.astype(complex)
        m = [vc @ U for U in bases]
        j0 = [mi.copy() for mi in m]
        result = foam_a.measure(b_readout)

        d_i = result['dissonance'][0]
        m_i = j0[0]
        dn = np.linalg.norm(d_i)
        mn = np.linalg.norm(m_i)
        if dn > 1e-12 and mn > 1e-12:
            d_hat = d_i / dn
            m_hat = m_i / mn
            delta_L = np.outer(d_hat, m_hat.conj()) - np.outer(m_hat, d_hat.conj())
            mutual_dirs.append(np.concatenate([delta_L.real.flatten(), delta_L.imag.flatten()]))

        # B reads A
        a_readout = np.real(foam_a.readout(encode(step % 256, 8)))
        a_readout = a_readout / (np.linalg.norm(a_readout) + 1e-12)
        foam_b.measure(a_readout)

    mutual_dirs = np.array(mutual_dirs)

    # extra writes: collect A's write directions from random input
    np.random.seed(seed)
    foam_c = Foam(d=8, n=3, writing_rate=0.01)
    random_inputs = [encode(np.random.randint(0, 256), 8) for _ in range(100)]
    random_dirs = collect_writes(foam_c, random_inputs)

    # analysis
    def analyze_directions(dirs, label):
        if len(dirs) < 3:
            print(f"  {label}: too few directions")
            return
        sv = np.linalg.svd(dirs, compute_uv=False)
        sv = sv / (sv[0] + 1e-12)  # normalize

        # effective dimension (participation ratio)
        sv2 = sv ** 2
        sv2 = sv2 / (sv2.sum() + 1e-12)
        eff_dim = 1.0 / (np.sum(sv2 ** 2) + 1e-12)

        # autocorrelation of consecutive directions
        autocorrs = []
        for i in range(len(dirs) - 1):
            c = np.dot(dirs[i], dirs[i+1]) / (np.linalg.norm(dirs[i]) * np.linalg.norm(dirs[i+1]) + 1e-12)
            autocorrs.append(abs(c))
        mean_autocorr = np.mean(autocorrs)

        # top 5 singular values
        top_sv = ' '.join(f'{s:.3f}' for s in sv[:5])

        print(f"  {label}:")
        print(f"    n_dirs = {len(dirs)}")
        print(f"    effective dimension = {eff_dim:.1f}")
        print(f"    mean |autocorrelation| = {mean_autocorr:.4f}")
        print(f"    top 5 singular values (normed): {top_sv}")

    print("\n=== write direction structure ===\n")
    analyze_directions(mutual_dirs, "mutual (A's writes from B's readouts)")
    analyze_directions(random_dirs, "independent (A's writes from random input)")


def mutual_vs_extra_deep(n_seeds=20):
    """Is there ANY measurable difference between mutual and extra-writes?
    Check multiple geometric signatures across many seeds."""
    from scipy.linalg import logm

    mutual_stats = {'cross_ab': [], 'mean_dist': [], 'min_dist': [],
                    'L_a': [], 'L_b': [], 'det_corr': []}
    extra_stats = {'cross_ab': [], 'mean_dist': [], 'min_dist': [],
                   'L_a': [], 'L_b': [], 'det_corr': []}

    for seed in range(n_seeds):
        for name, factory, stats in [
            ('mutual', mutual_measurement, mutual_stats),
            ('extra', extra_writes, extra_stats),
        ]:
            fa, fb = factory(seed)
            d = joint_cost_decomposition(fa, fb)
            g = geometric_relationship(fa, fb)

            stats['cross_ab'].append(d['cross_ab'])
            stats['mean_dist'].append(g['mean_cross_dist'])
            stats['min_dist'].append(g['min_cross_dist'])
            stats['L_a'].append(d['L_a'])
            stats['L_b'].append(d['L_b'])

            # determinant correlation: do the U(1) phases align?
            phases_a = [b.transport_phase for b in fa.bubbles]
            phases_b = [b.transport_phase for b in fb.bubbles]
            stats['det_corr'].append(np.corrcoef(sorted(phases_a), sorted(phases_b))[0, 1])

    print(f"\n=== mutual vs extra-writes: {n_seeds} seeds ===\n")
    print(f"  {'metric':>15s}  {'mutual mean':>12s} {'mutual std':>12s}  {'extra mean':>12s} {'extra std':>12s}")
    for key in mutual_stats:
        mm = np.mean(mutual_stats[key])
        ms = np.std(mutual_stats[key])
        em = np.mean(extra_stats[key])
        es = np.std(extra_stats[key])
        print(f"  {key:>15s}  {mm:12.4f} {ms:12.4f}  {em:12.4f} {es:12.4f}")


def transport_comparison(n_seeds=20):
    """Look at T directly. Does mutual measurement leave a signature
    in the transport that scalar summaries can't see?"""
    from scipy.linalg import logm

    print(f"\n=== transport structure: mutual vs extra-writes ({n_seeds} seeds) ===\n")

    mutual_stats = {'t_corr': [], 'relative_t_norm': [], 'relative_t_rank': []}
    extra_stats = {'t_corr': [], 'relative_t_norm': [], 'relative_t_rank': []}

    for seed in range(n_seeds):
        for factory, stats in [
            (mutual_measurement, mutual_stats),
            (extra_writes, extra_stats),
        ]:
            fa, fb = factory(seed)

            log_Ts_a = []
            log_Ts_b = []
            for i in range(3):
                try:
                    log_Ts_a.append(logm(fa.bubbles[i].T))
                    log_Ts_b.append(logm(fb.bubbles[i].T))
                except:
                    log_Ts_a.append(np.zeros((8, 8), dtype=complex))
                    log_Ts_b.append(np.zeros((8, 8), dtype=complex))

            # 1. correlation of full transport structure
            flat_a = np.concatenate([lt.flatten() for lt in log_Ts_a])
            flat_b = np.concatenate([lt.flatten() for lt in log_Ts_b])
            flat_ar = np.concatenate([flat_a.real, flat_a.imag])
            flat_br = np.concatenate([flat_b.real, flat_b.imag])
            if np.std(flat_ar) > 1e-12 and np.std(flat_br) > 1e-12:
                stats['t_corr'].append(np.corrcoef(flat_ar, flat_br)[0, 1])

            # 2. relative transport: T_a^† T_b for each bubble pair
            # this is "A seen through B" — if mutual measurement creates
            # alignment, these should be closer to identity
            for i in range(3):
                rel_T = fa.bubbles[i].T.conj().T @ fb.bubbles[i].T
                log_rel = logm(rel_T)
                stats['relative_t_norm'].append(np.linalg.norm(log_rel))

                # effective rank of the relative transport
                sv = np.linalg.svd(log_rel, compute_uv=False)
                sv_norm = sv / (sv[0] + 1e-12)
                eff_rank = np.sum(sv_norm > 0.1)
                stats['relative_t_rank'].append(eff_rank)

    print(f"  {'metric':>25s}  {'mutual mean':>12s} {'mutual std':>12s}  {'extra mean':>12s} {'extra std':>12s}")
    for key in mutual_stats:
        mm = np.mean(mutual_stats[key])
        ms = np.std(mutual_stats[key])
        em = np.mean(extra_stats[key])
        es = np.std(extra_stats[key])
        print(f"  {key:>25s}  {mm:12.4f} {ms:12.4f}  {em:12.4f} {es:12.4f}")


def robustness_check(n_seeds=10):
    """Is the perfect internal correlation for mutual measurement robust?"""
    print(f"\n=== robustness: internal correlation across {n_seeds} seeds ===\n")
    print(f"  {'seed':>4s}  {'indep':>8s}  {'shared':>8s}  {'extra':>8s}  {'mutual':>8s}")

    for seed in range(n_seeds):
        corrs = {}
        for name, factory in [('indep', lambda s=seed: independent_foams(s)),
                              ('shared', lambda s=seed: shared_history(s)),
                              ('extra', lambda s=seed: extra_writes(s)),
                              ('mutual', lambda s=seed: mutual_measurement(s))]:
            fa, fb = factory()
            g = geometric_relationship(fa, fb)
            corrs[name] = g['internal_corr']

        print(f"  {seed:4d}  {corrs['indep']:8.4f}  {corrs['shared']:8.4f}  {corrs['extra']:8.4f}  {corrs['mutual']:8.4f}")


if __name__ == '__main__':
    print("=== boundary cost decomposition ===\n")
    print(f"  {'config':>12s}  {'L_a':>8s}  {'L_b':>8s}  {'within_A':>8s}  {'within_B':>8s}  {'cross_AB':>8s}  {'total':>8s}  {'cross/in':>8s}")

    for name, factory in [('independent', independent_foams),
                          ('shared', shared_history),
                          ('extra writes', extra_writes),
                          ('one-way pure', one_way_measurement),
                          ('one-way+write', one_way_with_writes),
                          ('mutual', mutual_measurement)]:
        fa, fb = factory()
        d = joint_cost_decomposition(fa, fb)
        ratio = d['cross_ab'] / (d['within_a'] + d['within_b'] + 1e-12)
        print(f"  {name:>12s}  {d['L_a']:8.4f}  {d['L_b']:8.4f}  {d['within_a']:8.4f}  {d['within_b']:8.4f}  {d['cross_ab']:8.4f}  {d['total']:8.4f}  {ratio:8.4f}")

    print()

    write_structure_comparison()
    mutual_vs_extra_deep()
    transport_comparison()

    print("\n=== geometric detail ===\n")
    print(f"  {'config':>12s}  {'mean_dist':>9s}  {'min_dist':>9s}  {'int_corr':>9s}  {'int_a':>24s}  {'int_b':>24s}")

    for name, factory in [('independent', independent_foams),
                          ('shared', shared_history),
                          ('extra writes', extra_writes),
                          ('one-way pure', one_way_measurement),
                          ('one-way+write', one_way_with_writes),
                          ('mutual', mutual_measurement)]:
        fa, fb = factory()
        g = geometric_relationship(fa, fb)
        int_a_str = ' '.join(f'{x:.3f}' for x in g['internal_a'])
        int_b_str = ' '.join(f'{x:.3f}' for x in g['internal_b'])
        print(f"  {name:>12s}  {g['mean_cross_dist']:9.4f}  {g['min_cross_dist']:9.4f}  {g['internal_corr']:9.4f}  {int_a_str:>24s}  {int_b_str:>24s}")
