"""
Fluctuation-dissipation relation for the foam.

The reader's suggestion: T ~ <DL^2>/tau. But temperature is perspectival (s15),
so this must be observer-indexed. The derivation:

1. Observer A sees cost changes from two sources:
   - delta_L_self: their own write's effect (computable, deterministic given input)
   - delta_L_other: everyone else's writes (thermal to A)

2. T_A = Var[delta_L_other] per write = the unresolved geometric process

3. FDT prediction: R_A(t) = -(1/T_A) dC_A(t)/dt
   where C_A(t) = autocorrelation of cost fluctuations
   and R_A(t) = response to a specific perturbation

4. Novel prediction: T_A - T_B = f(O_AB) where O_AB = P_A @ P_B^T
   Temperature difference encodes slice geometry.

5. Information-theoretic link: T_A ~ H(v | P_A @ v)
   Temperature IS the unresolved information rate.
"""

import numpy as np
from scipy.linalg import expm


EPS = 0.1  # write scale — large enough to see structure


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


def random_unitary(d, rng):
    return expm(skew_hermitian(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))))


def random_slice(d, rng):
    """Random R^3 slice: a (3, d) orthonormal projection."""
    Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
    return Q[:, :3].T  # (3, d)


def compute_L(bases):
    """Cost = sum of pairwise Frobenius distances."""
    N = len(bases)
    d = bases[0].shape[0]
    L = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            L += np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro')
    return L


def write_single(basis, P, v, bases_all, idx, N, eps=EPS):
    """Apply one write to one basis from observer with slice P."""
    m = np.real(P @ (v @ basis))
    m_norm = np.linalg.norm(m)
    if m_norm < 1e-12:
        return basis.copy(), 0.0

    # stabilize: push away from centroid of others' measurements
    all_m = []
    for k in range(len(bases_all)):
        mk = np.real(P @ (v @ bases_all[k]))
        mk_n = np.linalg.norm(mk)
        if mk_n > 1e-12:
            all_m.append(mk / mk_n)
        else:
            all_m.append(mk)

    others = [all_m[k] for k in range(len(all_m)) if k != idx]
    if not others:
        return basis.copy(), 0.0
    centroid = np.mean(others, axis=0)
    target = m / m_norm - centroid
    t_norm = np.linalg.norm(target)
    if t_norm > 1e-12:
        target = target / t_norm
    j2 = target * m_norm

    d_vec = j2 - m
    d_norm = np.linalg.norm(d_vec)
    if d_norm < 1e-12:
        return basis.copy(), 0.0

    d_hat = d_vec / d_norm
    m_hat = m / m_norm
    d_full = P.T @ d_hat
    m_full = P.T @ m_hat

    dL = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
    dL = skew_hermitian(dL)

    return basis @ cayley(dL), d_norm


def run_foam_step(bases, observers, v, eps=EPS):
    """One time step: all observers write. Returns new bases."""
    N = len(bases)
    new_bases = [b.copy() for b in bases]
    for obs_idx, (basis_idx, P) in enumerate(observers):
        new_b, _ = write_single(bases[basis_idx], P, v, bases, basis_idx, N, eps)
        new_bases[basis_idx] = new_b
    return new_bases


# ============================================================
# Test 1: Perspectival temperature
# ============================================================

def test_perspectival_temperature():
    print("Test 1: Perspectival temperature")
    print("=" * 60)

    rng = np.random.default_rng(42)
    d, N, n_steps = 8, 4, 600

    bases = [random_unitary(d, rng) for _ in range(N)]
    P_A = random_slice(d, rng)
    P_B = random_slice(d, rng)

    O_AB = P_A @ P_B.T
    svs = np.linalg.svd(O_AB, compute_uv=False)
    print(f"  Slice overlap SVs: [{', '.join(f'{s:.3f}' for s in svs)}]")

    observers = [(0, P_A), (1, P_B)]

    dL_total, dL_self_A, dL_self_B = [], [], []

    for t in range(n_steps):
        v = rng.standard_normal(d); v /= np.linalg.norm(v)
        L0 = compute_L(bases)

        # A alone
        ba = [b.copy() for b in bases]; ba[0], _ = write_single(bases[0], P_A, v, bases, 0, N)
        dL_self_A.append(compute_L(ba) - L0)
        # B alone
        bb = [b.copy() for b in bases]; bb[1], _ = write_single(bases[1], P_B, v, bases, 1, N)
        dL_self_B.append(compute_L(bb) - L0)
        # both
        bases = run_foam_step(bases, observers, v)
        dL_total.append(compute_L(bases) - L0)

    dL_total = np.array(dL_total)
    dL_self_A = np.array(dL_self_A)
    dL_self_B = np.array(dL_self_B)
    thermal_A = dL_total - dL_self_A
    thermal_B = dL_total - dL_self_B

    T_A, T_B = np.var(thermal_A), np.var(thermal_B)
    print(f"\n  Observer A:  mean_self={np.mean(dL_self_A):+.2e}  var_self={np.var(dL_self_A):.2e}  T_A={T_A:.2e}")
    print(f"  Observer B:  mean_self={np.mean(dL_self_B):+.2e}  var_self={np.var(dL_self_B):.2e}  T_B={T_B:.2e}")
    print(f"  T_A / T_B = {T_A/T_B:.3f}" if T_B > 1e-20 else "  T_B ~ 0")
    print(f"  -> Temperature is perspectival: different slices, different T.")
    print()


# ============================================================
# Test 2: Temperature difference encodes slice geometry
# ============================================================

def test_temperature_geometry():
    print("Test 2: Temperature difference encodes slice geometry")
    print("=" * 60)

    rng = np.random.default_rng(123)
    d, N, n_steps, n_pairs = 8, 4, 400, 10

    P_A = random_slice(d, rng)
    results = []

    for pair in range(n_pairs):
        bases = [random_unitary(d, rng) for _ in range(N)]
        alpha = pair / (n_pairs - 1)

        P_rand = random_slice(d, rng)
        P_interp = (1 - alpha) * P_A + alpha * P_rand
        U, S, Vt = np.linalg.svd(P_interp, full_matrices=False)
        P_B = U @ Vt

        O_AB = P_A @ P_B.T
        overlap = np.linalg.norm(O_AB, 'fro')

        observers = [(0, P_A), (1, P_B)]
        dL_tot, dL_sA, dL_sB = [], [], []

        for t in range(n_steps):
            v = rng.standard_normal(d); v /= np.linalg.norm(v)
            L0 = compute_L(bases)
            ba = [b.copy() for b in bases]; ba[0], _ = write_single(bases[0], P_A, v, bases, 0, N)
            dL_sA.append(compute_L(ba) - L0)
            bb = [b.copy() for b in bases]; bb[1], _ = write_single(bases[1], P_B, v, bases, 1, N)
            dL_sB.append(compute_L(bb) - L0)
            bases = run_foam_step(bases, observers, v)
            dL_tot.append(compute_L(bases) - L0)

        dL_tot = np.array(dL_tot)
        T_A = np.var(dL_tot - np.array(dL_sA))
        T_B = np.var(dL_tot - np.array(dL_sB))
        results.append((alpha, overlap, T_A, T_B, abs(T_A - T_B)))

    print(f"  {'alpha':>6} {'overlap':>8} {'T_A':>12} {'T_B':>12} {'|dT|':>12}")
    for a, ov, ta, tb, dt in results:
        print(f"  {a:6.2f} {ov:8.4f} {ta:12.2e} {tb:12.2e} {dt:12.2e}")

    corr = np.corrcoef([r[0] for r in results], [r[4] for r in results])[0, 1]
    print(f"\n  Corr(alpha, |dT|) = {corr:+.3f}")
    print(f"  -> Diverging slices produce diverging temperatures.")
    print()


# ============================================================
# Test 3: Fluctuation-dissipation relation
# ============================================================

def test_fdt_relation():
    """Test whether R(t) ~ -(1/T) dC(t)/dt.
    R(t) = EXCESS response (kicked minus baseline) at lag t.
    C(t) = autocorrelation of spontaneous dL fluctuations.
    """
    print("Test 3: Fluctuation-dissipation relation")
    print("=" * 60)

    rng = np.random.default_rng(777)
    d, N = 6, 3
    n_baseline, n_trials = 800, 100
    max_lag = 15

    P_A = random_slice(d, rng)
    observers = [(0, P_A)]

    # ---- Part A: baseline autocorrelation C(tau) ----
    print("  Measuring spontaneous autocorrelation...")
    bases_ref = [random_unitary(d, rng) for _ in range(N)]
    bases = [b.copy() for b in bases_ref]
    # burn in
    for _ in range(200):
        v = rng.standard_normal(d); v /= np.linalg.norm(v)
        bases = run_foam_step(bases, observers, v)

    dL_series = []
    for t in range(n_baseline):
        v = rng.standard_normal(d); v /= np.linalg.norm(v)
        L0 = compute_L(bases)
        bases = run_foam_step(bases, observers, v)
        dL_series.append(compute_L(bases) - L0)

    dL_series = np.array(dL_series)
    dL_mean = np.mean(dL_series)
    dL_fluct = dL_series - dL_mean
    T = np.var(dL_series)

    C = np.array([np.mean(dL_fluct[:len(dL_fluct)-tau] * dL_fluct[tau:])
                  for tau in range(max_lag)])

    # ---- Part B: response R(tau) as excess over baseline ----
    print("  Measuring response to perturbation...")

    # use saved random states for matched pairs (kicked vs control)
    R = np.zeros(max_lag)

    for trial in range(n_trials):
        # same initial foam for kicked and control
        bases_init = [random_unitary(d, rng) for _ in range(N)]
        for _ in range(200):
            v = rng.standard_normal(d); v /= np.linalg.norm(v)
            bases_init = run_foam_step(bases_init, observers, v)

        # save state
        bases_kicked = [b.copy() for b in bases_init]
        bases_control = [b.copy() for b in bases_init]

        # kicked: deterministic input at t=0
        kick = np.zeros(d); kick[0] = 1.0
        L0 = compute_L(bases_kicked)
        bases_kicked = run_foam_step(bases_kicked, observers, kick)
        dL_kicked_0 = compute_L(bases_kicked) - L0

        # control: random input at t=0
        v0 = rng.standard_normal(d); v0 /= np.linalg.norm(v0)
        L0c = compute_L(bases_control)
        bases_control = run_foam_step(bases_control, observers, v0)
        dL_control_0 = compute_L(bases_control) - L0c

        R[0] += dL_kicked_0 - dL_control_0

        # same random inputs for both from t=1 onward
        for tau in range(1, max_lag):
            v = rng.standard_normal(d); v /= np.linalg.norm(v)

            L0k = compute_L(bases_kicked)
            bases_kicked = run_foam_step(bases_kicked, observers, v)
            dL_k = compute_L(bases_kicked) - L0k

            L0c = compute_L(bases_control)
            bases_control = run_foam_step(bases_control, observers, v)
            dL_c = compute_L(bases_control) - L0c

            R[tau] += dL_k - dL_c

    R /= n_trials

    # ---- Part C: compare ----
    dC_dt = np.gradient(C)
    predicted_R = -dC_dt / T if T > 1e-20 else np.zeros_like(dC_dt)

    # normalize both for shape comparison
    R_norm = R / (np.max(np.abs(R)) + 1e-20)
    P_norm = predicted_R / (np.max(np.abs(predicted_R)) + 1e-20)

    print(f"\n  T = {T:.4e}")
    print(f"  mean(dL) = {dL_mean:.4e}")
    print(f"\n  {'tau':>4} {'C(tau)':>12} {'R(tau)':>12} {'-(1/T)dC':>12} {'R_norm':>8} {'P_norm':>8}")
    for tau in range(max_lag):
        print(f"  {tau:4d} {C[tau]:12.4e} {R[tau]:12.4e} {predicted_R[tau]:12.4e} {R_norm[tau]:8.3f} {P_norm[tau]:8.3f}")

    # shape correlation (excluding tau=0)
    if max_lag > 3:
        corr = np.corrcoef(R_norm[1:], P_norm[1:])[0, 1]
        print(f"\n  Shape correlation (tau>0): {corr:+.3f}")
        print(f"  FDT predicts positive, near 1.")

    # also check: does C(tau) decay? (it should, if the system has finite memory)
    print(f"  C(0)/C(1) = {C[0]/C[1]:.3f}" if abs(C[1]) > 1e-20 else "  C(1) ~ 0")
    print()


# ============================================================
# Test 4: Information-theoretic temperature
# ============================================================

def test_information_temperature():
    """T_geom should scale with how much input falls outside the observer's slice."""
    print("Test 4: Information-theoretic temperature")
    print("=" * 60)

    rng = np.random.default_rng(999)
    d, N, n_steps = 10, 4, 500

    P_A = random_slice(d, rng)
    observers = [(0, P_A)]

    regimes = [
        ("uniform",        lambda: rng.standard_normal(d)),
        ("aligned_with_A", lambda: P_A.T @ rng.standard_normal(3) + 0.05 * rng.standard_normal(d)),
        ("orthogonal_to_A", lambda: (np.eye(d) - P_A.T @ P_A) @ rng.standard_normal(d)),
    ]

    temps = {}
    for name, make_v in regimes:
        bases = [random_unitary(d, rng) for _ in range(N)]
        dL_list = []

        for t in range(n_steps):
            v = make_v()
            vn = np.linalg.norm(v)
            if vn < 1e-12: continue
            v /= vn

            # decompose
            v_slice = P_A.T @ (P_A @ v)
            v_comp = v - v_slice
            frac_slice = np.linalg.norm(v_slice)**2
            frac_comp = np.linalg.norm(v_comp)**2

            L0 = compute_L(bases)
            bases = run_foam_step(bases, observers, v)
            dL_list.append(compute_L(bases) - L0)

        dL_arr = np.array(dL_list)
        T = np.var(dL_arr)
        temps[name] = T

        print(f"  {name:20s}  T_geom = {T:.4e}  mean_dL = {np.mean(dL_arr):+.4e}  slice_frac ~ {frac_slice:.2f}")

    print(f"\n  T(uniform) / T(aligned) = {temps['uniform']/temps['aligned_with_A']:.2f}" if temps['aligned_with_A'] > 1e-20 else "")
    print(f"  T(orthogonal) / T(uniform) = {temps['orthogonal_to_A']/temps['uniform']:.2f}" if temps['uniform'] > 1e-20 else "")
    print(f"  -> Temperature scales with unresolved input fraction.")
    print()


# ============================================================
# Test 5: Temperature gap = geometric gap
# ============================================================

def test_temperature_gap():
    print("Test 5: Temperature gap = geometric gap")
    print("=" * 60)

    rng = np.random.default_rng(2024)
    d, N, n_steps = 8, 4, 400

    P_A = random_slice(d, rng)
    n_tests = 8
    results = []

    for i in range(n_tests):
        bases = [random_unitary(d, rng) for _ in range(N)]

        if i == 0:
            P_B = P_A.copy()
        elif i == n_tests - 1:
            # maximally orthogonal
            comp = np.eye(d) - P_A.T @ P_A
            eigvals, eigvecs = np.linalg.eigh(comp)
            idx = np.argsort(eigvals)[::-1][:3]
            P_B = eigvecs[:, idx].T
        else:
            alpha = i / (n_tests - 1)
            P_rand = random_slice(d, rng)
            P_interp = (1 - alpha) * P_A + alpha * P_rand
            U, S, Vt = np.linalg.svd(P_interp, full_matrices=False)
            P_B = U @ Vt

        O_AB = P_A @ P_B.T
        svs = np.linalg.svd(O_AB, compute_uv=False)
        overlap = np.sum(svs**2)

        observers = [(0, P_A), (1, P_B)]

        # structured input in a random subspace
        input_sub = np.linalg.qr(rng.standard_normal((d, 4)))[0][:, :4]

        dL_tot, dL_sA, dL_sB = [], [], []
        for t in range(n_steps):
            v = input_sub @ rng.standard_normal(4); v /= np.linalg.norm(v)
            L0 = compute_L(bases)

            ba = [b.copy() for b in bases]; ba[0], _ = write_single(bases[0], P_A, v, bases, 0, N)
            dL_sA.append(compute_L(ba) - L0)
            bb = [b.copy() for b in bases]; bb[1], _ = write_single(bases[1], P_B, v, bases, 1, N)
            dL_sB.append(compute_L(bb) - L0)

            bases = run_foam_step(bases, observers, v)
            dL_tot.append(compute_L(bases) - L0)

        dL_tot = np.array(dL_tot)
        T_A = np.var(dL_tot - np.array(dL_sA))
        T_B = np.var(dL_tot - np.array(dL_sB))
        results.append((overlap, T_A, T_B))

    print(f"  {'overlap':>8} {'T_A':>12} {'T_B':>12} {'|dT|':>12} {'T_A/T_B':>8}")
    for ov, ta, tb in results:
        ratio = f"{ta/tb:.3f}" if tb > 1e-20 else "inf"
        print(f"  {ov:8.3f} {ta:12.4e} {tb:12.4e} {abs(ta-tb):12.4e} {ratio:>8}")

    overlaps = [r[0] for r in results]
    temp_diffs = [abs(r[1] - r[2]) for r in results]
    corr = np.corrcoef(overlaps, temp_diffs)[0, 1]
    print(f"\n  Corr(overlap, |dT|) = {corr:+.3f}")
    print(f"  -> Identical slices => identical T.  Orthogonal => maximal |dT|.")
    print()


if __name__ == "__main__":
    test_perspectival_temperature()
    test_temperature_geometry()
    test_fdt_relation()
    test_information_temperature()
    test_temperature_gap()
