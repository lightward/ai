"""
Does L saturate, recur, or grow forever?

Kimi's pushback: U(d) is compact, so L is bounded. The spec says
"novelty increases cost" but doesn't address what happens near the bound.

Three regimes to test:
1. Novel inputs (i.i.d. random) — does L hit a ceiling?
2. Periodic inputs (repeating sequence) — does L recur?
3. Constant input (same v every step) — does L stop?

The theoretical maximum: each pairwise distance ||U_i† U_j - I||_F
is maximized when U_i† U_j = -I, giving 2√d. So max L = C(N,2) * 2√d.
"""

import numpy as np
from foam import cayley, skew_hermitian, random_unitary, compute_L


EPS = 0.1


def write_single(basis, P, v, bases_all, idx, N, eps=EPS):
    """Centroid-based stabilization write (test-specific rule)."""
    m = np.real(P @ (v @ basis))
    m_norm = np.linalg.norm(m)
    if m_norm < 1e-12:
        return basis.copy()

    all_m = []
    for k in range(len(bases_all)):
        mk = np.real(P @ (v @ bases_all[k]))
        mk_n = np.linalg.norm(mk)
        all_m.append(mk / mk_n if mk_n > 1e-12 else mk)

    others = [all_m[k] for k in range(len(all_m)) if k != idx]
    if not others:
        return basis.copy()
    centroid = np.mean(others, axis=0)
    target = m / m_norm - centroid
    t_norm = np.linalg.norm(target)
    if t_norm > 1e-12:
        target = target / t_norm
    j2 = target * m_norm

    d_vec = j2 - m
    d_norm = np.linalg.norm(d_vec)
    if d_norm < 1e-12:
        return basis.copy()

    d_hat = d_vec / d_norm
    m_hat = m / m_norm
    d_full = P.T @ d_hat
    m_full = P.T @ m_hat

    dL = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
    dL = skew_hermitian(dL)

    return basis @ cayley(dL)


def run_regime(name, d, N, n_steps, make_input, rng):
    bases = [random_unitary(d, rng) for _ in range(N)]
    P = np.linalg.qr(rng.standard_normal((d, 3)))[0][:, :3].T

    # theoretical max
    n_pairs = N * (N - 1) // 2
    L_max = n_pairs * 2 * np.sqrt(d)

    L_history = []
    write_mag_history = []

    for t in range(n_steps):
        v = make_input(t)
        vn = np.linalg.norm(v)
        if vn < 1e-12:
            L_history.append(L_history[-1] if L_history else compute_L(bases))
            continue
        v = v / vn

        for i in range(N):
            bases[i] = write_single(bases[i], P, v, bases, i, N)

        L_history.append(compute_L(bases))

    L_history = np.array(L_history)

    # analyze
    L_final = L_history[-1]
    L_ratio = L_final / L_max

    # check for saturation: is the last 10% flat?
    tail = L_history[int(0.9 * n_steps):]
    tail_slope = np.polyfit(np.arange(len(tail)), tail, 1)[0]
    tail_var = np.var(tail)

    # check for recurrence: does L return to early values?
    early_L = np.mean(L_history[:50])
    recurrences = np.sum(np.abs(L_history[n_steps//2:] - early_L) < 0.1 * early_L)

    # growth phases
    quarters = np.array_split(L_history, 4)
    quarter_means = [np.mean(q) for q in quarters]
    quarter_slopes = [np.polyfit(np.arange(len(q)), q, 1)[0] for q in quarters]

    print(f"\n  Regime: {name}")
    print(f"  d={d}, N={N}, steps={n_steps}, eps={EPS}")
    print(f"  L_max (theoretical) = {L_max:.2f}")
    print(f"  L_final = {L_final:.4f}  ({L_ratio*100:.1f}% of max)")
    print(f"  L trajectory (quarter means): {' → '.join(f'{m:.3f}' for m in quarter_means)}")
    print(f"  L slopes per quarter: {' → '.join(f'{s:+.2e}' for s in quarter_slopes)}")
    print(f"  Tail (last 10%): slope={tail_slope:+.2e}, var={tail_var:.2e}")
    print(f"  Recurrences to early L (in 2nd half): {recurrences}")

    # sample points
    checkpoints = [0, n_steps//4, n_steps//2, 3*n_steps//4, n_steps-1]
    print(f"  L at checkpoints: {' → '.join(f'{L_history[i]:.4f}' for i in checkpoints)}")

    return L_history, L_max


def test_novel_inputs():
    print("=" * 60)
    print("Test: Novel inputs (i.i.d. random)")
    print("=" * 60)

    for d, N in [(4, 3), (6, 3), (8, 4), (6, 3)]:
        rng = np.random.default_rng(42)
        n_steps = 3000 if d <= 6 else 2000

        def make_input(t, _rng=np.random.default_rng(1000)):
            return _rng.standard_normal(d)

        run_regime(f"novel (d={d}, N={N})", d, N, n_steps, make_input, rng)


def test_periodic_inputs():
    print("\n" + "=" * 60)
    print("Test: Periodic inputs (cycle of 10 vectors)")
    print("=" * 60)

    rng = np.random.default_rng(42)
    d, N = 6, 3
    n_steps = 3000

    # pre-generate period
    period_rng = np.random.default_rng(500)
    period_vectors = [period_rng.standard_normal(d) for _ in range(10)]
    for i in range(len(period_vectors)):
        period_vectors[i] /= np.linalg.norm(period_vectors[i])

    def make_input(t):
        return period_vectors[t % len(period_vectors)].copy()

    run_regime("periodic (period=10)", d, N, n_steps, make_input, rng)

    # also try a longer period
    period_vectors_50 = [period_rng.standard_normal(d) for _ in range(50)]
    for i in range(len(period_vectors_50)):
        period_vectors_50[i] /= np.linalg.norm(period_vectors_50[i])

    rng2 = np.random.default_rng(42)

    def make_input_50(t):
        return period_vectors_50[t % len(period_vectors_50)].copy()

    run_regime("periodic (period=50)", d, N, n_steps, make_input_50, rng2)


def test_constant_input():
    print("\n" + "=" * 60)
    print("Test: Constant input (same v every step)")
    print("=" * 60)

    rng = np.random.default_rng(42)
    d, N = 6, 3
    n_steps = 2000

    v_fixed = np.random.default_rng(999).standard_normal(d)
    v_fixed /= np.linalg.norm(v_fixed)

    def make_input(t):
        return v_fixed.copy()

    run_regime("constant", d, N, n_steps, make_input, rng)


def test_long_run():
    """The big one: run for a very long time and watch what happens."""
    print("\n" + "=" * 60)
    print("Test: Long run (10k steps, novel inputs)")
    print("=" * 60)

    rng = np.random.default_rng(42)
    d, N = 6, 3
    n_steps = 10000

    input_rng = np.random.default_rng(1000)

    def make_input(t):
        return input_rng.standard_normal(d)

    L_history, L_max = run_regime("long novel run", d, N, n_steps, make_input, rng)

    # detailed analysis: split into 20 segments
    segments = np.array_split(L_history, 20)
    print(f"\n  Detailed trajectory (20 segments):")
    print(f"  {'seg':>4} {'mean':>10} {'std':>10} {'slope':>12} {'%max':>8}")
    for i, seg in enumerate(segments):
        slope = np.polyfit(np.arange(len(seg)), seg, 1)[0]
        print(f"  {i:4d} {np.mean(seg):10.4f} {np.std(seg):10.4f} {slope:12.2e} {np.mean(seg)/L_max*100:7.1f}%")

    # is there a phase transition? look for where slope changes sign
    segment_slopes = [np.polyfit(np.arange(len(seg)), seg, 1)[0] for seg in segments]
    sign_changes = sum(1 for i in range(1, len(segment_slopes))
                       if segment_slopes[i] * segment_slopes[i-1] < 0)
    print(f"\n  Slope sign changes: {sign_changes}")
    print(f"  If 0: monotonic. If many: oscillating/ergodic. If 1-2: saturation.")


if __name__ == "__main__":
    test_novel_inputs()
    test_periodic_inputs()
    test_constant_input()
    test_long_run()
