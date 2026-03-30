"""
Lévy flights on the saturation level set.

At saturation, the foam wanders on a ~2D surface in U(d)^N.
Each write is full-strength with random direction (from L's perspective).
On a curved surface, random-direction steps of fixed Lie algebra magnitude
produce variable-length steps ON THE SURFACE because:
  - curvature varies across the level set
  - the projection of a fixed-magnitude step onto the level set tangent
    depends on the angle between the step and the surface normal

If the step-size distribution on the level set is heavy-tailed (Lévy),
the big jumps are candidates for epoch micro-structure — moments where
the foam crosses topological features of the level set.

Measurements:
  1. Step size on the level set: ||S_{t+1} - S_t|| at saturation
  2. Step size in L: |ΔL_t| at saturation
  3. Distribution shape: fit to power law, compare to Gaussian
  4. Autocorrelation of step sizes (Lévy flights have clustered large steps)
  5. Return statistics: how often does the foam return near a previous state?
"""

import numpy as np
from foam import cayley, skew_hermitian, random_unitary, compute_L


def flatten_state(bases):
    parts = []
    for U in bases:
        parts.append(U.real.flatten())
        parts.append(U.imag.flatten())
    return np.concatenate(parts)


def foam_step(bases, P, v, N, eps):
    """Custom foam step for this test (centroid-based stabilization)."""
    d = bases[0].shape[0]
    all_m = []
    all_m_hat = []
    for k in range(N):
        mk = np.real(P @ (v @ bases[k]))
        n = np.linalg.norm(mk)
        all_m.append(mk)
        all_m_hat.append(mk / n if n > 1e-12 else mk)

    new_bases = []
    for i in range(N):
        m = all_m[i]
        m_norm = np.linalg.norm(m)
        if m_norm < 1e-12:
            new_bases.append(bases[i].copy())
            continue
        m_hat = m / m_norm
        others = [all_m_hat[k] for k in range(N) if k != i]
        centroid = np.mean(others, axis=0)
        target = m_hat - centroid
        t_norm = np.linalg.norm(target)
        if t_norm > 1e-12:
            target = target / t_norm
        j2 = target * m_norm
        d_vec = j2 - m
        d_norm = np.linalg.norm(d_vec)
        if d_norm < 1e-12:
            new_bases.append(bases[i].copy())
            continue
        d_hat = d_vec / d_norm
        d_full = P.T @ d_hat
        m_full = P.T @ m_hat
        dL = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
        dL = skew_hermitian(dL)
        new_bases.append(bases[i] @ cayley(dL))

    return new_bases


def run_and_collect(d, N, eps, n_steps, n_slices=1, rng_seed=42):
    """Run foam, collect step sizes and L changes at saturation."""
    rng = np.random.default_rng(rng_seed)
    bases = [random_unitary(d, rng) for _ in range(N)]

    slices = []
    for _ in range(n_slices):
        Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
        slices.append(Q[:, :3].T)

    input_rng = np.random.default_rng(rng_seed + 1000)

    L_history = []
    state_steps = []     # ||S_{t+1} - S_t||
    L_steps = []         # |ΔL|
    dissonance_norms = []  # ||d|| at each step (write magnitude proxy)

    prev_state = flatten_state(bases)
    prev_L = compute_L(bases)

    for t in range(n_steps):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)
        P = slices[t % n_slices]

        # capture dissonance before write
        all_m = []
        all_m_hat = []
        for k in range(N):
            mk = np.real(P @ (v @ bases[k]))
            n_val = np.linalg.norm(mk)
            all_m.append(mk)
            all_m_hat.append(mk / n_val if n_val > 1e-12 else mk)

        d_norms = []
        for i in range(N):
            m = all_m[i]
            m_norm = np.linalg.norm(m)
            if m_norm < 1e-12:
                d_norms.append(0.0)
                continue
            m_hat = m / m_norm
            others = [all_m_hat[k] for k in range(N) if k != i]
            centroid = np.mean(others, axis=0)
            target = m_hat - centroid
            t_norm = np.linalg.norm(target)
            if t_norm > 1e-12:
                target = target / t_norm
            j2 = target * m_norm
            d_vec = j2 - m
            d_norms.append(np.linalg.norm(d_vec))

        dissonance_norms.append(np.mean(d_norms))

        bases = foam_step(bases, P, v, N, eps)
        new_state = flatten_state(bases)
        new_L = compute_L(bases)

        state_step = np.linalg.norm(new_state - prev_state)
        L_step = abs(new_L - prev_L)

        state_steps.append(state_step)
        L_steps.append(L_step)
        L_history.append(new_L)

        prev_state = new_state
        prev_L = new_L

    return L_history, state_steps, L_steps, dissonance_norms


def analyze_tail_distribution(values, label):
    """Analyze the tail of a distribution: Gaussian vs heavy-tailed."""
    v = np.array(values)
    mean, std = np.mean(v), np.std(v)

    # kurtosis (Gaussian = 3, heavy-tailed > 3)
    kurt = np.mean((v - mean)**4) / std**4

    # fraction of values > 2σ (Gaussian: ~4.6%)
    frac_2sigma = np.mean(v > mean + 2*std)
    # fraction > 3σ (Gaussian: ~0.27%)
    frac_3sigma = np.mean(v > mean + 3*std)
    # fraction > 4σ (Gaussian: ~0.006%)
    frac_4sigma = np.mean(v > mean + 4*std)

    # max / mean (Lévy: can be very large; Gaussian: typically < 5)
    max_over_mean = np.max(v) / mean if mean > 0 else float('inf')

    # log-log slope of CCDF (complementary CDF)
    # for power law P(X > x) ~ x^{-α}, the CCDF slope gives α
    sorted_v = np.sort(v)[::-1]
    ranks = np.arange(1, len(sorted_v) + 1) / len(sorted_v)
    # fit log(rank) vs log(value) in the upper 20%
    upper = int(0.2 * len(sorted_v))
    if upper > 10:
        log_v = np.log(sorted_v[:upper])
        log_r = np.log(ranks[:upper])
        # linear regression
        slope, intercept = np.polyfit(log_v, log_r, 1)
        alpha = -slope  # power law exponent
    else:
        alpha = float('nan')

    print(f"  {label}:")
    print(f"    mean={mean:.6f}  std={std:.6f}  max={np.max(v):.6f}")
    print(f"    kurtosis={kurt:.2f}  (Gaussian=3)")
    print(f"    >2σ: {frac_2sigma*100:.2f}%  (Gaussian: 4.6%)")
    print(f"    >3σ: {frac_3sigma*100:.2f}%  (Gaussian: 0.27%)")
    print(f"    >4σ: {frac_4sigma*100:.2f}%  (Gaussian: 0.006%)")
    print(f"    max/mean: {max_over_mean:.2f}")
    print(f"    CCDF power law α: {alpha:.2f}  (Lévy stable: 1-2)")
    return kurt, alpha


def analyze_autocorrelation(values, max_lag=50):
    """Autocorrelation of step sizes (Lévy: clustered large steps)."""
    v = np.array(values) - np.mean(values)
    var = np.var(values)
    if var < 1e-30:
        return np.zeros(max_lag)
    acf = np.correlate(v, v, mode='full')
    acf = acf[len(v)-1:]
    acf = acf / (var * len(v))
    return acf[:max_lag]


if __name__ == "__main__":
    print("=" * 70)
    print("LÉVY FLIGHTS ON THE SATURATION LEVEL SET")
    print("=" * 70)
    print()

    # ── Main test: d=6, N=3, long run ──
    print("Test 1: Reference (d=6, N=3, eps=0.1, 10000 steps)")
    print("-" * 50)
    L_h, ss, Ls, dn = run_and_collect(d=6, N=3, eps=0.1, n_steps=10000)

    # split into pre-saturation and saturation
    # use CV < 0.5% as onset
    onset = 200  # approximate
    for t in range(200, len(L_h)):
        window = L_h[max(0,t-100):t]
        if len(window) > 50 and np.std(window)/np.mean(window) < 0.005:
            onset = t - 100
            break

    print(f"  Saturation onset: ~step {onset}")
    print(f"  L at saturation: {np.mean(L_h[onset:]):.3f}")
    print()

    # analyze step sizes in saturation regime only
    sat_ss = ss[onset:]
    sat_Ls = Ls[onset:]
    sat_dn = dn[onset:]

    print("  Step-size distributions (saturation regime):")
    print()
    k_state, a_state = analyze_tail_distribution(sat_ss, "State step ||ΔS||")
    print()
    k_L, a_L = analyze_tail_distribution(sat_Ls, "L step |ΔL|")
    print()
    k_d, a_d = analyze_tail_distribution(sat_dn, "Dissonance ||d||")
    print()

    # autocorrelation of state step sizes
    acf = analyze_autocorrelation(sat_ss, max_lag=30)
    print("  Autocorrelation of state step sizes (lags 1-10):")
    for lag in range(1, min(11, len(acf))):
        bar = "█" * int(abs(acf[lag]) * 50)
        sign = "+" if acf[lag] > 0 else "-"
        print(f"    lag {lag:2d}: {sign}{abs(acf[lag]):.4f} {bar}")
    print()

    # ── Dimension sweep ──
    print("Test 2: Dimension sweep")
    print("-" * 50)
    for d_val in [4, 6, 8, 10]:
        L_h, ss, Ls, dn = run_and_collect(d=d_val, N=3, eps=0.1, n_steps=5000)
        sat = ss[int(0.5*len(ss)):]
        sat_L = Ls[int(0.5*len(Ls)):]
        v = np.array(sat)
        mean, std = np.mean(v), np.std(v)
        kurt = np.mean((v - mean)**4) / std**4
        frac_3s = np.mean(v > mean + 3*std)

        v_L = np.array(sat_L)
        mean_L, std_L = np.mean(v_L), np.std(v_L)
        kurt_L = np.mean((v_L - mean_L)**4) / std_L**4

        print(f"  d={d_val}: state_kurt={kurt:.2f}  L_kurt={kurt_L:.2f}  "
              f"state_>3σ={frac_3s*100:.2f}%  max/mean={np.max(v)/mean:.2f}")
    print()

    # ── eps sweep ──
    print("Test 3: eps sweep (d=6, N=3)")
    print("-" * 50)
    for eps in [0.01, 0.05, 0.1, 0.2]:
        L_h, ss, Ls, dn = run_and_collect(d=6, N=3, eps=eps, n_steps=5000)
        sat = ss[int(0.5*len(ss)):]
        v = np.array(sat)
        mean, std = np.mean(v), np.std(v)
        kurt = np.mean((v - mean)**4) / std**4
        frac_3s = np.mean(v > mean + 3*std)
        print(f"  eps={eps}: kurt={kurt:.2f}  >3σ={frac_3s*100:.2f}%  "
              f"max/mean={np.max(v)/mean:.2f}  mean_step={mean:.6f}")
    print()

    # ── Return statistics ──
    print("Test 4: Return statistics (d=6, N=3)")
    print("-" * 50)
    L_h, ss, Ls, dn = run_and_collect(d=6, N=3, eps=0.1, n_steps=10000)
    # at saturation, track distance from a reference state
    ref_idx = int(0.5 * len(L_h))
    # collect states at saturation
    # re-run to collect actual states (expensive but necessary)
    rng = np.random.default_rng(42)
    bases = [random_unitary(6, rng) for _ in range(3)]
    Q = np.linalg.qr(rng.standard_normal((6, 3)))[0]
    P = Q[:, :3].T
    input_rng = np.random.default_rng(42 + 1000)

    states_at_sat = []
    for t in range(10000):
        v = input_rng.standard_normal(6)
        v /= np.linalg.norm(v)
        bases = foam_step(bases, P, v, 3, 0.1)
        if t >= ref_idx:
            states_at_sat.append(flatten_state(bases))

    # distance from first saturated state
    ref = states_at_sat[0]
    dists = [np.linalg.norm(s - ref) for s in states_at_sat]
    print(f"  Distance from reference state (saturation):")
    print(f"    mean: {np.mean(dists):.4f}")
    print(f"    std:  {np.std(dists):.4f}")
    print(f"    min:  {np.min(dists):.4f}")
    print(f"    max:  {np.max(dists):.4f}")
    # how often does it return within 1σ of the reference?
    sigma = np.std(dists)
    returns = np.sum(np.array(dists) < sigma)
    print(f"    returns within 1σ: {returns} / {len(dists)} ({returns/len(dists)*100:.1f}%)")
    # how often does it return within 0.5σ?
    returns_half = np.sum(np.array(dists) < 0.5 * sigma)
    print(f"    returns within 0.5σ: {returns_half} / {len(dists)} ({returns_half/len(dists)*100:.1f}%)")
    print()

    # ── Summary ──
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"""
  Kurtosis > 3 → heavy-tailed (Lévy-like)
  Kurtosis = 3 → Gaussian (Brownian)
  Kurtosis < 3 → light-tailed (sub-Gaussian)

  Power law α ∈ (1,2) → Lévy stable regime
  Power law α > 2 → finite variance, Gaussian CLT applies
  Power law α < 1 → extremely heavy (infinite mean)

  Positive autocorrelation → clustered large steps (Lévy signature)
  Zero autocorrelation → independent steps (Brownian)
""")
