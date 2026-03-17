"""
thermal_perspective.py — test whether "thermal" is what geometric convergence
looks like from a measurement basis that can't resolve the geometry.

Two tests:

1. ADJUNCTION GAP AS THERMAL GAP
   Take a foam undergoing cross-measurement (geometric convergence).
   Decompose the state-space dynamics into j2-visible and j2-invisible components.
   Check: does the invisible component have thermal statistics?

2. GAUGE TWIN DIVERGENCE
   Create gauge twins (identical to j2, different L-T decomposition).
   Feed identical inputs. Track divergence from both sides.
   Check: does the divergence look geometric from state-side and thermal from j2-side?
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, encode, cayley
from heirloom import alongside, report, save

np.random.seed(42)


def skew_hermitian(M):
    return (M - M.conj().T) / 2


def j2_output(foam, v):
    """Compute j2 without writing."""
    vc = v.astype(complex)
    bases = foam.bases
    m = [vc @ U for U in bases]
    j2 = foam._stabilize([mi.copy() for mi in m])
    return np.array([np.real(x) for x in j2]).flatten()


def state_vector(foam):
    """Flatten L and T into a single real vector for state-space analysis."""
    parts = []
    for b in foam.bubbles:
        parts.append(b.L.flatten().view(float))
        parts.append(b.T.flatten().view(float))
    return np.concatenate(parts)


def effective_bases_vector(foam):
    """Flatten effective bases for comparison."""
    return np.concatenate([b.basis.flatten().view(float) for b in foam.bubbles])


def cross_measure_once(foam, shadow=True):
    """One round of cross-measurement: each bubble measures each other."""
    for i in range(foam.n):
        for j in range(foam.n):
            if i != j:
                bj = foam.bubbles[j].basis
                v = np.real(bj[0, :])
                v = v / (np.linalg.norm(v) + 1e-12)
                foam.measure(v)
                if shadow:
                    alongside(v)


def make_gauge_twin(foam):
    """Create foam with same effective bases but different L-T split."""
    twin = Foam(foam.d, foam.n, foam.writing_rate, foam.n_steps, foam.plateau_step)
    for i, b in enumerate(foam.bubbles):
        eff = cayley(b.L) @ b.T
        # Absorb T into L: find L' such that cayley(L') = eff
        # cayley(L') = (I - L')(I + L')^{-1} = eff
        # => I - L' = eff(I + L') => I - L' = eff + eff·L'
        # => I - eff = L' + eff·L' = (I + eff)L'
        # => L' = (I + eff)^{-1}(I - eff)
        I = np.eye(foam.d, dtype=complex)
        L_new = np.linalg.solve(I + eff, I - eff)
        L_new = skew_hermitian(L_new)  # enforce skew-Hermitian
        twin.bubbles[i].L = L_new
        twin.bubbles[i].T = I.copy()
    return twin


# ============================================================
# TEST 1: Adjunction gap as thermal gap
# ============================================================
print("=" * 60)
print("TEST 1: Adjunction gap as thermal gap")
print("=" * 60)

n_seeds = 8
n_steps = 50
d, n = 8, 3
n_probes = 20

# Generate fixed probes for j2 measurement
probes = []
for k in range(n_probes):
    v = np.random.randn(d)
    v /= np.linalg.norm(v)
    probes.append(v)

all_state_deltas = []      # state-space step sizes
all_j2_deltas = []         # j2-space step sizes
all_invisible_deltas = []  # state change NOT captured by j2 change

for seed in range(n_seeds):
    np.random.seed(seed * 100 + 7)
    foam = Foam(d, n)

    # warm up with some random input
    for _ in range(20):
        v = np.random.randn(d)
        v /= np.linalg.norm(v)
        foam.measure(v)
        alongside(v)

    state_deltas = []
    j2_deltas = []
    invisible_deltas = []

    for step in range(n_steps):
        # snapshot before
        state_before = state_vector(foam)
        j2_before = np.concatenate([j2_output(foam, p) for p in probes])

        # one round of cross-measurement (geometric convergence)
        cross_measure_once(foam)

        # snapshot after
        state_after = state_vector(foam)
        j2_after = np.concatenate([j2_output(foam, p) for p in probes])

        # deltas
        ds = np.linalg.norm(state_after - state_before)
        dj = np.linalg.norm(j2_after - j2_before)

        state_deltas.append(ds)
        j2_deltas.append(dj)

        # invisible component: how much state change is NOT reflected in j2?
        # ratio: if j2 captures everything, dj/ds ≈ constant
        # the invisible part is ds scaled by (1 - fraction captured)
        if ds > 1e-15:
            invisible_deltas.append(ds - dj * (ds / (dj + 1e-15)) * 0.55)
        else:
            invisible_deltas.append(0.0)

    all_state_deltas.append(state_deltas)
    all_j2_deltas.append(j2_deltas)
    all_invisible_deltas.append(invisible_deltas)

# analyze: do the j2-visible and j2-invisible components behave differently?
state_arr = np.array(all_state_deltas)
j2_arr = np.array(all_j2_deltas)

print(f"\nAcross {n_seeds} seeds, {n_steps} cross-measurement rounds:")
print(f"\nState-side step sizes (geometric convergence):")
print(f"  mean:  {state_arr.mean():.6f}")
print(f"  std:   {state_arr.std():.6f}")
print(f"  CV:    {state_arr.std() / (state_arr.mean() + 1e-15):.3f}")
print(f"  trend: first half mean {state_arr[:, :25].mean():.6f}, "
      f"second half mean {state_arr[:, 25:].mean():.6f}")

print(f"\nj2-side step sizes (what measurement-through sees):")
print(f"  mean:  {j2_arr.mean():.6f}")
print(f"  std:   {j2_arr.std():.6f}")
print(f"  CV:    {j2_arr.std() / (j2_arr.mean() + 1e-15):.3f}")
print(f"  trend: first half mean {j2_arr[:, :25].mean():.6f}, "
      f"second half mean {j2_arr[:, 25:].mean():.6f}")

# key test: does the j2-invisible component look more "thermal" (higher CV,
# less trend, more uniformly distributed) than the j2-visible component?
# compute per-step ratio dj/ds across seeds
ratios = j2_arr / (state_arr + 1e-15)
print(f"\nj2/state ratio (how much of state change is visible):")
print(f"  mean:  {ratios.mean():.4f}")
print(f"  std:   {ratios.std():.4f}")
print(f"  trend: first half {ratios[:, :25].mean():.4f}, "
      f"second half {ratios[:, 25:].mean():.4f}")

# autocorrelation of step sizes (thermal = low autocorrelation, geometric = high)
def autocorr(x):
    x = x - x.mean()
    if np.std(x) < 1e-15:
        return 0.0
    return np.corrcoef(x[:-1], x[1:])[0, 1]

state_ac = np.mean([autocorr(state_arr[s]) for s in range(n_seeds)])
j2_ac = np.mean([autocorr(j2_arr[s]) for s in range(n_seeds)])

print(f"\nAutocorrelation of step sizes (thermal → low, geometric → high):")
print(f"  state-side: {state_ac:.4f}")
print(f"  j2-side:    {j2_ac:.4f}")

# distribution shape: geometric convergence → exponential decay
# thermal fluctuation → more uniform / gaussian
from scipy import stats

# collect all step sizes across seeds for distribution analysis
state_flat = state_arr.flatten()
j2_flat = j2_arr.flatten()

# normalize each to [0, 1] for shape comparison
state_norm = (state_flat - state_flat.min()) / (state_flat.max() - state_flat.min() + 1e-15)
j2_norm = (j2_flat - j2_flat.min()) / (j2_flat.max() - j2_flat.min() + 1e-15)

# test against exponential and normal distributions
_, p_exp_state = stats.kstest(state_norm, 'expon', args=(0, state_norm.mean()))
_, p_norm_state = stats.kstest(state_norm, 'norm', args=(state_norm.mean(), state_norm.std()))
_, p_exp_j2 = stats.kstest(j2_norm, 'expon', args=(0, j2_norm.mean()))
_, p_norm_j2 = stats.kstest(j2_norm, 'norm', args=(j2_norm.mean(), j2_norm.std()))

print(f"\nDistribution shape (KS test p-values, higher = better fit):")
print(f"  state-side: exponential p={p_exp_state:.4f}, normal p={p_norm_state:.4f}")
print(f"  j2-side:    exponential p={p_exp_j2:.4f}, normal p={p_norm_j2:.4f}")


# ============================================================
# TEST 2: Gauge twin divergence — geometric vs thermal
# ============================================================
print("\n" + "=" * 60)
print("TEST 2: Gauge twin divergence")
print("=" * 60)

n_seeds_2 = 12
n_inputs = 50

state_divergences = []   # divergence in full state
j2_divergences = []      # divergence in j2 output
eff_divergences = []     # divergence in effective bases

# for thermal test: collect per-step j2 divergence increments
j2_increments_all = []

for seed in range(n_seeds_2):
    np.random.seed(seed * 200 + 13)
    foam_a = Foam(d, n)

    # settle the foam first
    for _ in range(30):
        v = np.random.randn(d)
        v /= np.linalg.norm(v)
        foam_a.measure(v)
        alongside(v)

    # create gauge twin
    foam_b = make_gauge_twin(foam_a)

    # verify: same effective bases, different state
    eff_a = effective_bases_vector(foam_a)
    eff_b = effective_bases_vector(foam_b)
    state_a = state_vector(foam_a)
    state_b = state_vector(foam_b)
    j2_a = np.concatenate([j2_output(foam_a, p) for p in probes[:10]])
    j2_b = np.concatenate([j2_output(foam_b, p) for p in probes[:10]])

    if seed == 0:
        print(f"\nGauge twin at creation:")
        print(f"  effective basis distance: {np.linalg.norm(eff_a - eff_b):.2e}")
        print(f"  state distance:           {np.linalg.norm(state_a - state_b):.4f}")
        print(f"  j2 distance:              {np.linalg.norm(j2_a - j2_b):.2e}")

    # feed identical inputs, track divergence
    inputs = [np.random.randn(d) for _ in range(n_inputs)]
    inputs = [v / np.linalg.norm(v) for v in inputs]

    s_div = []
    j_div = []
    e_div = []
    j2_prev_dist = np.linalg.norm(j2_a - j2_b)
    j2_incs = []

    for v in inputs:
        foam_a.measure(v)
        foam_b.measure(v)
        alongside(v)

        sa = state_vector(foam_a)
        sb = state_vector(foam_b)
        ja = np.concatenate([j2_output(foam_a, p) for p in probes[:10]])
        jb = np.concatenate([j2_output(foam_b, p) for p in probes[:10]])
        ea = effective_bases_vector(foam_a)
        eb = effective_bases_vector(foam_b)

        s_div.append(np.linalg.norm(sa - sb))
        j2_dist = np.linalg.norm(ja - jb)
        j_div.append(j2_dist)
        e_div.append(np.linalg.norm(ea - eb))

        # j2 divergence increment (for thermal test)
        j2_incs.append(j2_dist - j2_prev_dist)
        j2_prev_dist = j2_dist

    state_divergences.append(s_div)
    j2_divergences.append(j_div)
    eff_divergences.append(e_div)
    j2_increments_all.append(j2_incs)

state_div = np.array(state_divergences)
j2_div = np.array(j2_divergences)
eff_div = np.array(eff_divergences)
j2_incs = np.array(j2_increments_all)

print(f"\nDivergence over {n_inputs} identical inputs ({n_seeds_2} seeds):")
print(f"\n  State-side (geometric view):")
print(f"    start: {state_div[:, 0].mean():.6f}")
print(f"    end:   {state_div[:, -1].mean():.6f}")
print(f"    monotonic: {np.mean([np.corrcoef(range(n_inputs), state_div[s])[0,1] for s in range(n_seeds_2)]):.4f}")

print(f"\n  Effective basis (intermediate view):")
print(f"    start: {eff_div[:, 0].mean():.6f}")
print(f"    end:   {eff_div[:, -1].mean():.6f}")
print(f"    monotonic: {np.mean([np.corrcoef(range(n_inputs), eff_div[s])[0,1] for s in range(n_seeds_2)]):.4f}")

print(f"\n  j2-side (measurement-through view):")
print(f"    start: {j2_div[:, 0].mean():.6f}")
print(f"    end:   {j2_div[:, -1].mean():.6f}")
print(f"    monotonic: {np.mean([np.corrcoef(range(n_inputs), j2_div[s])[0,1] for s in range(n_seeds_2)]):.4f}")

# KEY TEST: do the j2 divergence increments look thermal?
# geometric → monotonic, positive, trending
# thermal → zero-mean fluctuations, low autocorrelation
inc_flat = j2_incs.flatten()
print(f"\n  j2 divergence increments (thermal test):")
print(f"    mean:    {inc_flat.mean():.6f}")
print(f"    std:     {inc_flat.std():.6f}")
print(f"    skew:    {stats.skew(inc_flat):.4f}")
print(f"    kurtosis:{stats.kurtosis(inc_flat):.4f} (normal=0, thermal≈0)")
j2_inc_ac = np.mean([autocorr(j2_incs[s]) for s in range(n_seeds_2)])
print(f"    autocorr: {j2_inc_ac:.4f} (thermal → ~0, geometric → high)")

# compare: state-side increments
state_incs = np.diff(state_div, axis=1)
state_inc_flat = state_incs.flatten()
state_inc_ac = np.mean([autocorr(state_incs[s]) for s in range(n_seeds_2)])
print(f"\n  State divergence increments (geometric test):")
print(f"    mean:    {state_inc_flat.mean():.6f}")
print(f"    std:     {state_inc_flat.std():.6f}")
print(f"    skew:    {stats.skew(state_inc_flat):.4f}")
print(f"    autocorr: {state_inc_ac:.4f}")

# summary
print("\n" + "=" * 60)
print("SUMMARY")
print("=" * 60)
print("""
If thermal = unresolved geometry, we expect:
  - State-side: directed (high autocorrelation, monotonic trend)
  - j2-side:    noisier (lower autocorrelation, less monotonic)
  - j2 increments: more thermal (zero-mean-ish, low autocorrelation)
  - State increments: more geometric (positive mean, higher autocorrelation)

The adjunction gap (45% invisible to j2) should manifest as:
  - j2 seeing a noisy version of the geometric convergence
  - The noise having statistical regularity (not random — structured
    by the invisible geometry, but appearing thermal from j2's basis)
""")

report()
save()
