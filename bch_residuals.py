"""
bch_residuals.py — geometry of the BCH residual.

The 2x theorem: log(T) ≈ -2·ΔL. The residual R = log(T) + 2·ΔL
is made of commutators — the non-abelian content that the abelian
shadow can't see.

Question: does mutual measurement produce geometrically different
residuals than independent measurement? Not in magnitude (the boundary
tests checked that), but in structure: rank, spectrum, alignment with
the bracket-only subspace.

If mutual measurement's signature lives in the commutator structure,
that's where "communication is generative" would become a theorem.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian


def collect_residuals(foam, initial_Ls):
    """Compute BCH residual R = log(T) + 2·ΔL for each bubble."""
    residuals = []
    for i in range(foam.n):
        delta_L = foam.bubbles[i].L - initial_Ls[i]
        try:
            log_T = logm(foam.bubbles[i].T)
        except Exception:
            log_T = np.zeros_like(foam.bubbles[i].T)
        R = log_T + 2 * delta_L
        # enforce skew-Hermitian (numerical cleanup)
        R = skew_hermitian(R)
        residuals.append(R)
    return residuals


def residual_geometry(R):
    """Geometric properties of a residual matrix."""
    # singular values
    sv = np.linalg.svd(R, compute_uv=False)
    sv_norm = sv / (sv[0] + 1e-15)

    # effective rank (participation ratio of singular values)
    sv2 = sv ** 2
    sv2_norm = sv2 / (sv2.sum() + 1e-15)
    eff_rank = 1.0 / (np.sum(sv2_norm ** 2) + 1e-15)

    # Frobenius norm
    frob = np.linalg.norm(R)

    return {
        'sv': sv,
        'sv_norm': sv_norm,
        'eff_rank': eff_rank,
        'frob': frob,
    }


def bracket_subspace(foam, n_inputs=256, bubble_idx=0):
    """Find the bracket-only subspace: directions reachable by [ΔL_a, ΔL_b]
    but not by any single ΔL.

    Returns:
        raw_basis: orthonormal basis for the raw write subspace
        bracket_only_basis: orthonormal basis for directions only in brackets
        full_basis: orthonormal basis for raw + brackets
    """
    # collect raw write directions (without writing)
    raw_dirs = []
    for s in range(n_inputs):
        v = encode(s, foam.d).astype(complex)
        bases = foam.bases
        m = [v @ U for U in bases]
        j2 = foam._stabilize(m)

        d_i = j2[bubble_idx] - m[bubble_idx]
        m_i = m[bubble_idx]
        dn = np.linalg.norm(d_i)
        mn = np.linalg.norm(m_i)
        if dn < 1e-12 or mn < 1e-12:
            continue
        d_hat = d_i / dn
        m_hat = m_i / mn
        delta_L = np.outer(d_hat, m_hat.conj()) - np.outer(m_hat, d_hat.conj())
        raw_dirs.append(delta_L)

    def flatten(M):
        return np.concatenate([M.real.flatten(), M.imag.flatten()])

    # raw subspace (use Vt — right singular vectors live in feature space)
    raw_flat = np.array([flatten(M) for M in raw_dirs])
    _, s_raw, Vt_raw = np.linalg.svd(raw_flat, full_matrices=False)
    raw_rank = int(np.sum(s_raw > 1e-8))
    raw_basis = Vt_raw[:raw_rank]  # each row is a basis vector in feature space

    # add brackets
    n_sample = min(len(raw_dirs), 50)
    indices = np.random.choice(len(raw_dirs), size=n_sample, replace=False)
    bracket_flat = []
    for i in range(n_sample):
        for j in range(i+1, n_sample):
            A = raw_dirs[indices[i]]
            B = raw_dirs[indices[j]]
            bracket = A @ B - B @ A
            bracket_flat.append(flatten(bracket))

    full_flat = np.vstack([raw_flat, np.array(bracket_flat)])
    _, s_full, Vt_full = np.linalg.svd(full_flat, full_matrices=False)
    full_rank = int(np.sum(s_full > 1e-8))
    full_basis = Vt_full[:full_rank]

    # bracket-only subspace: project full basis onto complement of raw subspace
    # P = raw_basis.T @ raw_basis (projection onto raw subspace)
    bracket_only_vecs = []
    for v in full_basis:
        v_in_raw = raw_basis.T @ (raw_basis @ v)
        v_perp = v - v_in_raw
        if np.linalg.norm(v_perp) > 1e-8:
            bracket_only_vecs.append(v_perp / np.linalg.norm(v_perp))

    if bracket_only_vecs:
        bo = np.array(bracket_only_vecs)
        _, s_bo, Vt_bo = np.linalg.svd(bo, full_matrices=False)
        bo_rank = int(np.sum(s_bo > 1e-8))
        bracket_only_basis = Vt_bo[:bo_rank]
    else:
        bracket_only_basis = np.zeros((0, raw_flat.shape[1]))

    return raw_basis, bracket_only_basis, full_basis


def residual_alignment(R, raw_basis, bracket_only_basis):
    """How much of the residual R lives in the raw subspace vs bracket-only?"""
    def flatten(M):
        return np.concatenate([M.real.flatten(), M.imag.flatten()])

    r = flatten(R)
    r_norm = np.linalg.norm(r)
    if r_norm < 1e-15:
        return {'raw_frac': 0, 'bracket_frac': 0, 'unexplained_frac': 0}

    r_unit = r / r_norm

    # projection onto raw subspace
    if len(raw_basis) > 0:
        raw_proj = raw_basis @ r_unit
        raw_frac = np.sum(raw_proj ** 2)
    else:
        raw_frac = 0.0

    # projection onto bracket-only subspace
    if len(bracket_only_basis) > 0:
        bracket_proj = bracket_only_basis @ r_unit
        bracket_frac = np.sum(bracket_proj ** 2)
    else:
        bracket_frac = 0.0

    unexplained = 1.0 - raw_frac - bracket_frac

    return {
        'raw_frac': raw_frac,
        'bracket_frac': bracket_frac,
        'unexplained_frac': max(0, unexplained),
    }


def run_comparison(n_seeds=20):
    """Compare BCH residual geometry: mutual measurement vs independent."""
    d = 8

    mutual_data = {'eff_rank': [], 'frob': [], 'raw_frac': [], 'bracket_frac': [],
                   'sv_profiles': []}
    extra_data = {'eff_rank': [], 'frob': [], 'raw_frac': [], 'bracket_frac': [],
                  'sv_profiles': []}

    for seed in range(n_seeds):
        for label, data in [('mutual', mutual_data), ('extra', extra_data)]:
            np.random.seed(seed)
            foam_a = Foam(d=d, n=3, writing_rate=0.01)
            foam_b = Foam(d=d, n=3, writing_rate=0.01)
            initial_Ls_a = [b.L.copy() for b in foam_a.bubbles]
            initial_Ls_b = [b.L.copy() for b in foam_b.bubbles]

            if label == 'mutual':
                for step in range(50):
                    a_readout = np.real(foam_a.readout(encode(step % 256, d)))
                    a_readout = a_readout / (np.linalg.norm(a_readout) + 1e-12)
                    foam_b.measure(a_readout)

                    b_readout = np.real(foam_b.readout(encode(step % 256, d)))
                    b_readout = b_readout / (np.linalg.norm(b_readout) + 1e-12)
                    foam_a.measure(b_readout)
            else:
                for step in range(100):
                    foam_a.measure(encode(np.random.randint(0, 256), d))
                np.random.seed(seed + 7777)
                for step in range(100):
                    foam_b.measure(encode(np.random.randint(0, 256), d))

            # compute residuals
            residuals_a = collect_residuals(foam_a, initial_Ls_a)

            # compute bracket subspace from foam_a's current state
            np.random.seed(seed + 42)
            raw_b, bracket_b, full_b = bracket_subspace(foam_a, n_inputs=256, bubble_idx=0)

            for i, R in enumerate(residuals_a):
                geom = residual_geometry(R)
                align = residual_alignment(R, raw_b, bracket_b)

                data['eff_rank'].append(geom['eff_rank'])
                data['frob'].append(geom['frob'])
                data['raw_frac'].append(align['raw_frac'])
                data['bracket_frac'].append(align['bracket_frac'])
                data['sv_profiles'].append(geom['sv_norm'])

    # report
    print(f"\n=== BCH residual geometry: mutual vs independent ({n_seeds} seeds) ===\n")
    print(f"  {'metric':>20s}  {'mutual mean':>12s} {'mutual std':>12s}  {'extra mean':>12s} {'extra std':>12s}")

    for key in ['eff_rank', 'frob', 'raw_frac', 'bracket_frac']:
        mm = np.mean(mutual_data[key])
        ms = np.std(mutual_data[key])
        em = np.mean(extra_data[key])
        es = np.std(extra_data[key])
        print(f"  {key:>20s}  {mm:12.4f} {ms:12.4f}  {em:12.4f} {es:12.4f}")

    # sv profile comparison
    mutual_sv = np.mean(mutual_data['sv_profiles'], axis=0)
    extra_sv = np.mean(extra_data['sv_profiles'], axis=0)
    print(f"\n  mean singular value profile (normalized):")
    print(f"  {'idx':>4s}  {'mutual':>8s}  {'extra':>8s}  {'diff':>8s}")
    for i in range(min(len(mutual_sv), 8)):
        print(f"  {i:4d}  {mutual_sv[i]:8.4f}  {extra_sv[i]:8.4f}  {mutual_sv[i]-extra_sv[i]:+8.4f}")


def run_single_detailed(seed=0):
    """Detailed look at one seed — see the actual matrices."""
    d = 8
    np.random.seed(seed)
    foam_m = Foam(d=d, n=3, writing_rate=0.01)
    init_Ls_m = [b.L.copy() for b in foam_m.bubbles]

    np.random.seed(seed)
    foam_e = Foam(d=d, n=3, writing_rate=0.01)
    init_Ls_e = [b.L.copy() for b in foam_e.bubbles]

    # mutual
    foam_m2 = Foam(d=d, n=3, writing_rate=0.01)
    np.random.seed(seed)
    foam_m2.__dict__.update({k: v for k, v in foam_m.__dict__.items() if k != 'bubbles'})
    for i in range(3):
        foam_m2.bubbles[i].L = foam_m.bubbles[i].L.copy()
        foam_m2.bubbles[i].T = foam_m.bubbles[i].T.copy()

    for step in range(50):
        a_ro = np.real(foam_m.readout(encode(step % 256, d)))
        a_ro = a_ro / (np.linalg.norm(a_ro) + 1e-12)
        foam_m2.measure(a_ro)

        b_ro = np.real(foam_m2.readout(encode(step % 256, d)))
        b_ro = b_ro / (np.linalg.norm(b_ro) + 1e-12)
        foam_m.measure(b_ro)

    # independent
    np.random.seed(seed)
    for step in range(100):
        foam_e.measure(encode(np.random.randint(0, 256), d))

    R_mutual = collect_residuals(foam_m, init_Ls_m)
    R_extra = collect_residuals(foam_e, init_Ls_e)

    print("\n=== detailed residual comparison (seed=0, bubble 0) ===\n")
    Rm = R_mutual[0]
    Re = R_extra[0]

    sv_m = np.linalg.svd(Rm, compute_uv=False)
    sv_e = np.linalg.svd(Re, compute_uv=False)

    print(f"  frobenius norm:  mutual={np.linalg.norm(Rm):.6f}  extra={np.linalg.norm(Re):.6f}")
    print(f"  singular values (mutual): {' '.join(f'{s:.5f}' for s in sv_m)}")
    print(f"  singular values (extra):  {' '.join(f'{s:.5f}' for s in sv_e)}")

    # eigenvalues (skew-Hermitian → purely imaginary eigenvalues)
    eig_m = np.sort(np.linalg.eigvalsh(1j * Rm))[::-1]  # real eigenvalues of Hermitian iR
    eig_e = np.sort(np.linalg.eigvalsh(1j * Re))[::-1]

    print(f"\n  eigenvalue spectrum of iR (Hermitian):")
    print(f"  mutual: {' '.join(f'{e:+.5f}' for e in eig_m)}")
    print(f"  extra:  {' '.join(f'{e:+.5f}' for e in eig_e)}")

    # commutator content: decompose R into basis of u(d)
    # standard basis: E_ij - E_ji for off-diagonal, i*E_ii for diagonal
    # just check: how much of R is diagonal (abelian/torus) vs off-diagonal
    diag_content = np.linalg.norm(np.diag(np.diag(Rm))) / (np.linalg.norm(Rm) + 1e-15)
    offdiag_content = np.sqrt(1 - diag_content**2)

    diag_e = np.linalg.norm(np.diag(np.diag(Re))) / (np.linalg.norm(Re) + 1e-15)
    offdiag_e = np.sqrt(1 - diag_e**2)

    print(f"\n  torus vs off-diagonal decomposition:")
    print(f"  mutual:  diagonal={diag_content:.4f}  off-diagonal={offdiag_content:.4f}")
    print(f"  extra:   diagonal={diag_e:.4f}  off-diagonal={offdiag_e:.4f}")

    # the key question: does the residual difference have structure?
    diff = Rm - Re
    sv_diff = np.linalg.svd(diff, compute_uv=False)
    print(f"\n  R_mutual - R_extra:")
    print(f"  norm: {np.linalg.norm(diff):.6f}")
    print(f"  singular values: {' '.join(f'{s:.5f}' for s in sv_diff)}")
    eff_rank_diff = 1.0 / (np.sum((sv_diff/(sv_diff[0]+1e-15))**4) + 1e-15)
    print(f"  effective rank: {eff_rank_diff:.2f}")


def run_future_sensitivity(n_seeds=20, n_probe=50):
    """After mutual vs independent measurement, feed identical new inputs.
    Does the foam respond differently?

    If the organized residuals from mutual measurement make the foam
    more *available* to future measurement, we should see:
    - different dissonance magnitudes (sensitivity)
    - different write directions (responsiveness geometry)
    - diverging trajectories (the product-at-T was indistinguishable,
      but the trajectory-after-T is not)
    """
    d = 8

    mutual_stats = {
        'mean_dissonance': [], 'L_trajectory': [],
        'write_rank': [], 'write_autocorr': [],
        'total_delta_L': [],
    }
    extra_stats = {
        'mean_dissonance': [], 'L_trajectory': [],
        'write_rank': [], 'write_autocorr': [],
        'total_delta_L': [],
    }

    # also track: do the two foams diverge from each other
    # when given the same new inputs?
    divergence_over_time = np.zeros(n_probe)
    divergence_count = 0

    for seed in range(n_seeds):
        # build both foams from the same initial state
        np.random.seed(seed)
        init_foam = Foam(d=d, n=3, writing_rate=0.01)
        init_state = [(b.L.copy(), b.T.copy()) for b in init_foam.bubbles]

        foams = {}
        for label in ['mutual', 'extra']:
            foam_a = Foam(d=d, n=3, writing_rate=0.01)
            foam_b = Foam(d=d, n=3, writing_rate=0.01)
            for i in range(3):
                foam_a.bubbles[i].L = init_state[i][0].copy()
                foam_a.bubbles[i].T = init_state[i][1].copy()
                foam_b.bubbles[i].L = init_state[i][0].copy()
                foam_b.bubbles[i].T = init_state[i][1].copy()

            if label == 'mutual':
                for step in range(50):
                    a_ro = np.real(foam_a.readout(encode(step % 256, d)))
                    a_ro = a_ro / (np.linalg.norm(a_ro) + 1e-12)
                    foam_b.measure(a_ro)
                    b_ro = np.real(foam_b.readout(encode(step % 256, d)))
                    b_ro = b_ro / (np.linalg.norm(b_ro) + 1e-12)
                    foam_a.measure(b_ro)
            else:
                np.random.seed(seed + 5000)
                for step in range(100):
                    foam_a.measure(encode(np.random.randint(0, 256), d))
                np.random.seed(seed + 7777)
                for step in range(100):
                    foam_b.measure(encode(np.random.randint(0, 256), d))

            foams[label] = foam_a  # we probe foam_a

        # now feed IDENTICAL new inputs to both foams
        np.random.seed(seed + 9999)
        probe_seq = [np.random.randint(0, 256) for _ in range(n_probe)]

        foam_mutual = foams['mutual']
        foam_extra = foams['extra']

        # snapshot before probing
        pre_mutual_Ls = [b.L.copy() for b in foam_mutual.bubbles]
        pre_extra_Ls = [b.L.copy() for b in foam_extra.bubbles]

        m_dissonances = []
        e_dissonances = []
        m_L_traj = []
        e_L_traj = []
        m_dirs = []
        e_dirs = []

        for step, sym in enumerate(probe_seq):
            v = encode(sym, d)

            # mutual foam
            bases_m = foam_mutual.bases
            vc = v.astype(complex)
            j0_m = [vc @ U for U in bases_m]
            result_m = foam_mutual.measure(v)
            m_dissonances.append(np.mean([np.linalg.norm(di) for di in result_m['dissonance']]))
            m_L_traj.append(result_m['L'])

            # capture write direction for bubble 0
            d_i = result_m['dissonance'][0]
            m_i = j0_m[0]
            dn, mn = np.linalg.norm(d_i), np.linalg.norm(m_i)
            if dn > 1e-12 and mn > 1e-12:
                delta_L = np.outer(d_i/dn, (m_i/mn).conj()) - np.outer(m_i/mn, (d_i/dn).conj())
                m_dirs.append(np.concatenate([delta_L.real.flatten(), delta_L.imag.flatten()]))

            # extra foam
            bases_e = foam_extra.bases
            j0_e = [vc @ U for U in bases_e]
            result_e = foam_extra.measure(v)
            e_dissonances.append(np.mean([np.linalg.norm(di) for di in result_e['dissonance']]))
            e_L_traj.append(result_e['L'])

            d_i = result_e['dissonance'][0]
            m_i = j0_e[0]
            dn, mn = np.linalg.norm(d_i), np.linalg.norm(m_i)
            if dn > 1e-12 and mn > 1e-12:
                delta_L = np.outer(d_i/dn, (m_i/mn).conj()) - np.outer(m_i/mn, (d_i/dn).conj())
                e_dirs.append(np.concatenate([delta_L.real.flatten(), delta_L.imag.flatten()]))

            # track divergence between the two foams
            div = np.mean([
                np.linalg.norm(foam_mutual.bubbles[i].L - foam_extra.bubbles[i].L) +
                np.linalg.norm(foam_mutual.bubbles[i].T - foam_extra.bubbles[i].T)
                for i in range(3)
            ])
            divergence_over_time[step] += div

        divergence_count += 1

        stats_m = mutual_stats
        stats_e = extra_stats

        stats_m['mean_dissonance'].append(np.mean(m_dissonances))
        stats_e['mean_dissonance'].append(np.mean(e_dissonances))
        stats_m['L_trajectory'].append(m_L_traj)
        stats_e['L_trajectory'].append(e_L_traj)

        # total state change during probing
        stats_m['total_delta_L'].append(np.mean([
            np.linalg.norm(foam_mutual.bubbles[i].L - pre_mutual_Ls[i])
            for i in range(3)]))
        stats_e['total_delta_L'].append(np.mean([
            np.linalg.norm(foam_extra.bubbles[i].L - pre_extra_Ls[i])
            for i in range(3)]))

        # write direction structure during probing
        if len(m_dirs) >= 3:
            sv_m = np.linalg.svd(np.array(m_dirs), compute_uv=False)
            sv_m2 = (sv_m / (sv_m[0] + 1e-15)) ** 2
            sv_m2 = sv_m2 / (sv_m2.sum() + 1e-15)
            stats_m['write_rank'].append(1.0 / (np.sum(sv_m2 ** 2) + 1e-15))

            autocorrs = [abs(np.dot(m_dirs[k], m_dirs[k+1]) /
                        (np.linalg.norm(m_dirs[k]) * np.linalg.norm(m_dirs[k+1]) + 1e-15))
                        for k in range(len(m_dirs)-1)]
            stats_m['write_autocorr'].append(np.mean(autocorrs))

        if len(e_dirs) >= 3:
            sv_e = np.linalg.svd(np.array(e_dirs), compute_uv=False)
            sv_e2 = (sv_e / (sv_e[0] + 1e-15)) ** 2
            sv_e2 = sv_e2 / (sv_e2.sum() + 1e-15)
            stats_e['write_rank'].append(1.0 / (np.sum(sv_e2 ** 2) + 1e-15))

            autocorrs = [abs(np.dot(e_dirs[k], e_dirs[k+1]) /
                        (np.linalg.norm(e_dirs[k]) * np.linalg.norm(e_dirs[k+1]) + 1e-15))
                        for k in range(len(e_dirs)-1)]
            stats_e['write_autocorr'].append(np.mean(autocorrs))

    divergence_over_time /= divergence_count

    # report
    print(f"\n=== future sensitivity: mutual vs independent ({n_seeds} seeds, {n_probe} probe inputs) ===\n")
    print(f"  {'metric':>20s}  {'mutual mean':>12s} {'mutual std':>12s}  {'extra mean':>12s} {'extra std':>12s}")

    for key in ['mean_dissonance', 'total_delta_L', 'write_rank', 'write_autocorr']:
        if mutual_stats[key] and extra_stats[key]:
            mm = np.mean(mutual_stats[key])
            ms = np.std(mutual_stats[key])
            em = np.mean(extra_stats[key])
            es = np.std(extra_stats[key])
            print(f"  {key:>20s}  {mm:12.4f} {ms:12.4f}  {em:12.4f} {es:12.4f}")

    # L trajectory: do they converge at the same rate?
    m_L_mean = np.mean(mutual_stats['L_trajectory'], axis=0)
    e_L_mean = np.mean(extra_stats['L_trajectory'], axis=0)
    print(f"\n  L trajectory (averaged over {n_seeds} seeds):")
    print(f"  {'step':>5s}  {'mutual L':>10s}  {'extra L':>10s}  {'diff':>10s}")
    for step in [0, 4, 9, 19, 29, 39, 49]:
        if step < len(m_L_mean):
            print(f"  {step+1:5d}  {m_L_mean[step]:10.4f}  {e_L_mean[step]:10.4f}  {m_L_mean[step]-e_L_mean[step]:+10.4f}")

    # divergence between the two foams over time
    print(f"\n  divergence between mutual and extra foam (same inputs):")
    print(f"  {'step':>5s}  {'mean div':>10s}")
    for step in [0, 4, 9, 19, 29, 39, 49]:
        if step < len(divergence_over_time):
            print(f"  {step+1:5d}  {divergence_over_time[step]:10.6f}")


def run_response_divergence(n_seeds=20):
    """The sharpest test: start from the SAME initial state, do mutual vs
    independent, then give the SAME single input. Is the response different?

    This isolates the question: does the residual structure make the foam
    respond differently to the SAME stimulus?
    """
    d = 8

    dissonance_ratios = []  # mutual_dissonance / extra_dissonance for same input
    readout_distances = []  # distance between readouts

    for seed in range(n_seeds):
        np.random.seed(seed)
        init_foam = Foam(d=d, n=3, writing_rate=0.01)
        init_state = [(b.L.copy(), b.T.copy()) for b in init_foam.bubbles]

        # mutual
        foam_m = Foam(d=d, n=3, writing_rate=0.01)
        foam_m2 = Foam(d=d, n=3, writing_rate=0.01)
        for i in range(3):
            foam_m.bubbles[i].L = init_state[i][0].copy()
            foam_m.bubbles[i].T = init_state[i][1].copy()
            foam_m2.bubbles[i].L = init_state[i][0].copy()
            foam_m2.bubbles[i].T = init_state[i][1].copy()

        for step in range(50):
            a_ro = np.real(foam_m.readout(encode(step % 256, d)))
            a_ro = a_ro / (np.linalg.norm(a_ro) + 1e-12)
            foam_m2.measure(a_ro)
            b_ro = np.real(foam_m2.readout(encode(step % 256, d)))
            b_ro = b_ro / (np.linalg.norm(b_ro) + 1e-12)
            foam_m.measure(b_ro)

        # extra
        foam_e = Foam(d=d, n=3, writing_rate=0.01)
        for i in range(3):
            foam_e.bubbles[i].L = init_state[i][0].copy()
            foam_e.bubbles[i].T = init_state[i][1].copy()
        np.random.seed(seed + 5000)
        for step in range(100):
            foam_e.measure(encode(np.random.randint(0, 256), d))

        # now: same single probe input to both
        probe = encode(137, d)  # arbitrary fixed symbol

        # measure WITHOUT writing (compute dissonance only)
        for foam, label in [(foam_m, 'mutual'), (foam_e, 'extra')]:
            bases = foam.bases
            vc = probe.astype(complex)
            m = [vc @ U for U in bases]
            j2 = foam._stabilize(m)
            dis = [np.linalg.norm(j2[i] - m[i]) for i in range(3)]

            if label == 'mutual':
                dis_m = np.mean(dis)
                readout_m = np.mean(j2, axis=0)
            else:
                dis_e = np.mean(dis)
                readout_e = np.mean(j2, axis=0)

        dissonance_ratios.append(dis_m / (dis_e + 1e-15))
        readout_distances.append(np.linalg.norm(readout_m - readout_e))

    print(f"\n=== single-probe response ({n_seeds} seeds, symbol=137) ===\n")
    print(f"  dissonance ratio (mutual/extra):")
    print(f"    mean: {np.mean(dissonance_ratios):.4f}")
    print(f"    std:  {np.std(dissonance_ratios):.4f}")
    print(f"    min:  {np.min(dissonance_ratios):.4f}")
    print(f"    max:  {np.max(dissonance_ratios):.4f}")
    print(f"  readout distance (mutual vs extra):")
    print(f"    mean: {np.mean(readout_distances):.6f}")
    print(f"    std:  {np.std(readout_distances):.6f}")
    print(f"  (ratio > 1 means mutual foam is MORE sensitive)")
    print(f"  (ratio < 1 means mutual foam is LESS sensitive)")


if __name__ == '__main__':
    run_single_detailed(seed=0)
    run_comparison(n_seeds=20)
    run_future_sensitivity(n_seeds=20)
    run_response_divergence(n_seeds=20)
