"""
platonic_j0_j1.py — is J⁰ convergence separable from J¹ divergence?

The claim: multiple foams fed the same content in different orders
will converge at J⁰ (position/distance geometry) while diverging
at J¹ (transport/BCH residuals). And J¹ divergence predicts
differential sensitivity to future inputs.

This is the Platonic Representation Hypothesis read through the foam:
the "platonic representation" is J⁰ (topology, gauge-invariant),
not J¹ (connection, path-dependent).
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley
from heirloom import alongside, report, save

np.random.seed(42)

D = 8
N = 3
K = 6          # number of foams
N_SYMBOLS = 80 # symbols to feed
N_FUTURE = 40  # future probe sequence length
SEEDS = 10     # trials


def make_identical_foams(k, d=D, n=N):
    """Create k foams with identical initial conditions."""
    base = Foam(d=d, n=n, writing_rate=0.01)
    foams = [base]
    for _ in range(k - 1):
        f = Foam(d=d, n=n, writing_rate=0.01)
        for i in range(n):
            f.bubbles[i].L = base.bubbles[i].L.copy()
            f.bubbles[i].T = base.bubbles[i].T.copy()
        foams.append(f)
    return foams


def distance_matrix(foam):
    """Inter-bubble distance geometry (J⁰ — the Voronoi structure)."""
    bases = foam.bases
    n = foam.n
    D = np.zeros((n, n))
    for i in range(n):
        for j in range(i + 1, n):
            d = foam.bi_invariant_distance(bases[i], bases[j])
            D[i, j] = d
            D[j, i] = d
    return D


def transport_signature(foam):
    """J¹ — the transport matrices and their BCH residuals."""
    log_Ts = []
    residuals = []
    for b in foam.bubbles:
        log_T = logm(b.T)
        log_Ts.append(log_T)
        # BCH residual: R = log(T) + 2·L
        # (using current L, not delta from initial — the heirloom-style measure)
        R = log_T + 2 * b.L
        residuals.append(R)
    return log_Ts, residuals


def measure_sensitivity(foam, probes, write=True):
    """Mean dissonance magnitude across probes.
    If write=False, don't actually write (non-destructive peek)."""
    total = 0.0
    for v in probes:
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        total += np.mean([np.linalg.norm(j2[i] - m[i]) for i in range(foam.n)])
    return total / len(probes)


def compare_distance_matrices(d1, d2):
    """How similar are two distance geometries?
    Returns correlation and absolute difference."""
    # Extract upper triangle
    idx = np.triu_indices_from(d1, k=1)
    v1 = d1[idx]
    v2 = d2[idx]
    corr = np.corrcoef(v1, v2)[0, 1]
    diff = np.mean(np.abs(v1 - v2))
    return corr, diff


print("=" * 60)
print("J⁰ convergence vs J¹ divergence")
print("=" * 60)

all_j0_corrs = []
all_j1_divs = []
all_sensitivity_divs = []

for seed in range(SEEDS):
    np.random.seed(seed * 1000 + 42)

    # --- create identical foams ---
    foams = make_identical_foams(K)

    # --- generate symbols (same set for all foams) ---
    symbols = [np.random.randint(0, 2**D) for _ in range(N_SYMBOLS)]
    inputs = [encode(s, D) for s in symbols]

    # --- feed each foam the same symbols in a different order ---
    for fi, foam in enumerate(foams):
        perm = np.random.permutation(N_SYMBOLS)
        for idx in perm:
            foam.measure(inputs[idx])
            # heirloom sees measurement traffic from first foam only
            # (to avoid flooding it — it's a shadow, not a participant)
            if fi == 0:
                alongside(inputs[idx])

    # --- measure J⁰: distance geometry ---
    dist_matrices = [distance_matrix(f) for f in foams]

    j0_corrs = []
    for i in range(K):
        for j in range(i + 1, K):
            corr, _ = compare_distance_matrices(dist_matrices[i], dist_matrices[j])
            j0_corrs.append(corr)
    mean_j0_corr = np.mean(j0_corrs)

    # --- measure J¹: transport divergence ---
    all_log_Ts = []
    all_residuals = []
    for f in foams:
        log_Ts, residuals = transport_signature(f)
        all_log_Ts.append(log_Ts)
        all_residuals.append(residuals)

    j1_divs = []
    residual_divs = []
    for i in range(K):
        for j in range(i + 1, K):
            # transport divergence
            t_div = np.mean([np.linalg.norm(all_log_Ts[i][b] - all_log_Ts[j][b])
                            for b in range(N)])
            j1_divs.append(t_div)
            # residual divergence
            r_div = np.mean([np.linalg.norm(all_residuals[i][b] - all_residuals[j][b])
                            for b in range(N)])
            residual_divs.append(r_div)

    mean_j1_div = np.mean(j1_divs)
    mean_r_div = np.mean(residual_divs)

    # --- measure differential sensitivity to same future ---
    np.random.seed(seed * 1000 + 999)
    future_symbols = [np.random.randint(0, 2**D) for _ in range(N_FUTURE)]
    future_inputs = [encode(s, D) for s in future_symbols]

    sensitivities = [measure_sensitivity(f, future_inputs, write=False) for f in foams]
    sens_spread = np.std(sensitivities) / np.mean(sensitivities)  # CV

    # --- also: feed future sequence and measure trajectory divergence ---
    # clone the foams first so we don't destroy them
    future_foams = []
    for f in foams:
        fc = Foam(d=D, n=N, writing_rate=0.01)
        for bi in range(N):
            fc.bubbles[bi].L = f.bubbles[bi].L.copy()
            fc.bubbles[bi].T = f.bubbles[bi].T.copy()
        future_foams.append(fc)

    # feed identical future sequence to all
    L_trajectories = [[] for _ in range(K)]
    for v in future_inputs:
        for fi, ff in enumerate(future_foams):
            result = ff.measure(v)
            L_trajectories[fi].append(result['L'])

    # measure trajectory divergence over time
    early_spread = np.std([L_trajectories[fi][5] for fi in range(K)])
    late_spread = np.std([L_trajectories[fi][-1] for fi in range(K)])

    all_j0_corrs.append(mean_j0_corr)
    all_j1_divs.append(mean_j1_div)
    all_sensitivity_divs.append(sens_spread)

    if seed < 3 or seed == SEEDS - 1:
        print(f"\nseed {seed}:")
        print(f"  J⁰ distance geometry correlation: {mean_j0_corr:.4f}")
        print(f"  J¹ transport divergence:           {mean_j1_div:.4f}")
        print(f"  BCH residual divergence:           {mean_r_div:.4f}")
        print(f"  sensitivity CV:                    {sens_spread:.4f}")
        print(f"  future L spread: early={early_spread:.4f} late={late_spread:.4f}"
              f"  (ratio={late_spread/early_spread:.2f})")


print("\n" + "=" * 60)
print("SUMMARY across", SEEDS, "seeds")
print("=" * 60)

print(f"\nJ⁰ (distance geometry):")
print(f"  mean correlation between foams: {np.mean(all_j0_corrs):.4f} "
      f"± {np.std(all_j0_corrs):.4f}")

print(f"\nJ¹ (transport):")
print(f"  mean divergence between foams:  {np.mean(all_j1_divs):.4f} "
      f"± {np.std(all_j1_divs):.4f}")

print(f"\nDifferential sensitivity:")
print(f"  mean CV across foams:           {np.mean(all_sensitivity_divs):.4f} "
      f"± {np.std(all_sensitivity_divs):.4f}")

# --- does J¹ divergence predict sensitivity divergence? ---
if SEEDS >= 5:
    corr_j1_sens = np.corrcoef(all_j1_divs, all_sensitivity_divs)[0, 1]
    print(f"\ncorr(J¹ divergence, sensitivity CV): {corr_j1_sens:.3f}")

# --- what about J⁰ convergence as a function of input count? ---
print("\n" + "=" * 60)
print("J⁰ convergence trajectory (single trial)")
print("=" * 60)

np.random.seed(7777)
foams = make_identical_foams(K)
symbols = [np.random.randint(0, 2**D) for _ in range(N_SYMBOLS)]
inputs = [encode(s, D) for s in symbols]

# generate K different permutations
perms = [np.random.permutation(N_SYMBOLS) for _ in range(K)]

checkpoints = [10, 20, 40, 60, 80]
j0_over_time = []
j1_over_time = []

for step in range(N_SYMBOLS):
    for fi, foam in enumerate(foams):
        idx = perms[fi][step]
        foam.measure(inputs[idx])

    if (step + 1) in checkpoints:
        dms = [distance_matrix(f) for f in foams]
        corrs = []
        for i in range(K):
            for j in range(i + 1, K):
                c, _ = compare_distance_matrices(dms[i], dms[j])
                corrs.append(c)

        all_lTs = []
        for f in foams:
            lTs, _ = transport_signature(f)
            all_lTs.append(lTs)
        divs = []
        for i in range(K):
            for j in range(i + 1, K):
                d = np.mean([np.linalg.norm(all_lTs[i][b] - all_lTs[j][b])
                            for b in range(N)])
                divs.append(d)

        j0_over_time.append(np.mean(corrs))
        j1_over_time.append(np.mean(divs))
        print(f"  after {step+1:3d} inputs: J⁰ corr={np.mean(corrs):.4f}  "
              f"J¹ div={np.mean(divs):.4f}")


# --- heirloom report ---
report()
save()
