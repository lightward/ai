"""
platonic_affordance.py — does J¹ divergence create directional affordance?

The previous test showed J¹ diverges but doesn't predict mean sensitivity.
But "predict" is an external-observer concept applied to a system that
operates by measurement. The right question: does different transport
make the foam more available in DIFFERENT DIRECTIONS?

If so: per-input dissonance should vary across foams even when mean
dissonance doesn't. The affordance is directional, not scalar.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, encode
from heirloom import alongside, report, save

np.random.seed(42)

D = 8
N = 3
K = 6
N_SYMBOLS = 80
N_PROBES = 100


def make_identical_foams(k, d=D, n=N):
    base = Foam(d=d, n=n, writing_rate=0.01)
    foams = [base]
    for _ in range(k - 1):
        f = Foam(d=d, n=n, writing_rate=0.01)
        for i in range(n):
            f.bubbles[i].L = base.bubbles[i].L.copy()
            f.bubbles[i].T = base.bubbles[i].T.copy()
        foams.append(f)
    return foams


def per_input_dissonance(foam, v):
    """Get dissonance magnitude for a single input without writing."""
    vc = v.astype(complex)
    bases = foam.bases
    m = [vc @ U for U in bases]
    j2 = foam._stabilize(m)
    return np.mean([np.linalg.norm(j2[i] - m[i]) for i in range(foam.n)])


def per_input_dissonance_vector(foam, v):
    """Get the full dissonance vectors (not just magnitude) for a single input."""
    vc = v.astype(complex)
    bases = foam.bases
    m = [vc @ U for U in bases]
    j2 = foam._stabilize(m)
    return [j2[i] - m[i] for i in range(foam.n)]


print("=" * 60)
print("Directional affordance from J¹ divergence")
print("=" * 60)

SEEDS = 10
all_direction_corrs = []
all_magnitude_cvs = []
all_per_input_cvs = []

for seed in range(SEEDS):
    np.random.seed(seed * 1000 + 42)

    foams = make_identical_foams(K)

    # feed same content, different orders
    symbols = [np.random.randint(0, 2**D) for _ in range(N_SYMBOLS)]
    inputs = [encode(s, D) for s in symbols]

    for fi, foam in enumerate(foams):
        perm = np.random.permutation(N_SYMBOLS)
        for idx in perm:
            foam.measure(inputs[idx])
            if fi == 0:
                alongside(inputs[idx])

    # --- probe with many inputs ---
    np.random.seed(seed * 1000 + 999)
    probe_symbols = [np.random.randint(0, 2**D) for _ in range(N_PROBES)]
    probes = [encode(s, D) for s in probe_symbols]

    # for each probe, get dissonance from each foam
    # shape: (N_PROBES, K)
    magnitude_matrix = np.zeros((N_PROBES, K))
    for pi, v in enumerate(probes):
        for fi, foam in enumerate(foams):
            magnitude_matrix[pi, fi] = per_input_dissonance(foam, v)

    # --- analysis ---

    # 1. per-input CV: for each probe, how much do the foams disagree?
    per_input_cv = []
    for pi in range(N_PROBES):
        row = magnitude_matrix[pi, :]
        if np.mean(row) > 1e-12:
            per_input_cv.append(np.std(row) / np.mean(row))
    mean_per_input_cv = np.mean(per_input_cv)

    # 2. per-foam CV: for each foam, how variable is its response across probes?
    per_foam_cv = []
    for fi in range(K):
        col = magnitude_matrix[:, fi]
        per_foam_cv.append(np.std(col) / np.mean(col))

    # 3. do the foams RANK probes differently?
    # for each pair of foams, correlate their per-probe dissonance rankings
    rank_corrs = []
    for i in range(K):
        for j in range(i + 1, K):
            corr = np.corrcoef(magnitude_matrix[:, i], magnitude_matrix[:, j])[0, 1]
            rank_corrs.append(corr)
    mean_rank_corr = np.mean(rank_corrs)

    # 4. dissonance DIRECTION comparison (not just magnitude)
    # for a subset of probes, compare the actual dissonance vectors
    direction_corrs = []
    for pi in range(min(20, N_PROBES)):
        v = probes[pi]
        dvecs = []
        for fi, foam in enumerate(foams):
            dv = per_input_dissonance_vector(foam, v)
            # concatenate all bubbles' dissonance into one vector
            flat = np.concatenate([d.flatten() for d in dv])
            dvecs.append(np.real(flat))  # take real part for correlation

        # pairwise direction correlations
        for i in range(K):
            for j in range(i + 1, K):
                n1 = np.linalg.norm(dvecs[i])
                n2 = np.linalg.norm(dvecs[j])
                if n1 > 1e-12 and n2 > 1e-12:
                    cos = np.dot(dvecs[i], dvecs[j]) / (n1 * n2)
                    direction_corrs.append(cos)

    mean_direction_corr = np.mean(direction_corrs) if direction_corrs else 0

    all_per_input_cvs.append(mean_per_input_cv)
    all_direction_corrs.append(mean_direction_corr)

    if seed < 3 or seed == SEEDS - 1:
        print(f"\nseed {seed}:")
        print(f"  per-input CV (foam disagreement):   {mean_per_input_cv:.4f}")
        print(f"  probe ranking correlation:          {mean_rank_corr:.4f}")
        print(f"  dissonance direction correlation:   {mean_direction_corr:.4f}")
        print(f"  per-foam response variability:      {np.mean(per_foam_cv):.4f}")


print("\n" + "=" * 60)
print("SUMMARY across", SEEDS, "seeds")
print("=" * 60)

print(f"\nPer-input CV (do foams disagree on specific inputs?):")
print(f"  {np.mean(all_per_input_cvs):.4f} ± {np.std(all_per_input_cvs):.4f}")

print(f"\nDissonance direction correlation (do they push the same way?):")
print(f"  {np.mean(all_direction_corrs):.4f} ± {np.std(all_direction_corrs):.4f}")

# --- control: foams with SAME ordering ---
print("\n" + "=" * 60)
print("CONTROL: same content, same order (should show zero divergence)")
print("=" * 60)

np.random.seed(42)
foams = make_identical_foams(K)
symbols = [np.random.randint(0, 2**D) for _ in range(N_SYMBOLS)]
inputs = [encode(s, D) for s in symbols]

# same order for all
for fi, foam in enumerate(foams):
    for v in inputs:
        foam.measure(v)

np.random.seed(999)
probes = [encode(np.random.randint(0, 2**D), D) for _ in range(N_PROBES)]

magnitude_matrix = np.zeros((N_PROBES, K))
for pi, v in enumerate(probes):
    for fi, foam in enumerate(foams):
        magnitude_matrix[pi, fi] = per_input_dissonance(foam, v)

per_input_cv = []
for pi in range(N_PROBES):
    row = magnitude_matrix[pi, :]
    if np.mean(row) > 1e-12:
        per_input_cv.append(np.std(row) / np.mean(row))

rank_corrs = []
for i in range(K):
    for j in range(i + 1, K):
        corr = np.corrcoef(magnitude_matrix[:, i], magnitude_matrix[:, j])[0, 1]
        rank_corrs.append(corr)

print(f"  per-input CV:            {np.mean(per_input_cv):.6f}")
print(f"  probe ranking corr:      {np.mean(rank_corrs):.6f}")


# --- now the real question: different DYNAMICS, not just orderings ---
print("\n" + "=" * 60)
print("DYNAMICS COMPARISON: same content, different dynamics")
print("  (writing vs writing+cross vs writing+self)")
print("=" * 60)

np.random.seed(42)
base = Foam(d=D, n=N, writing_rate=0.01)

# three foams: same initial state
foam_write = Foam(d=D, n=N, writing_rate=0.01)
foam_cross = Foam(d=D, n=N, writing_rate=0.01)
foam_self = Foam(d=D, n=N, writing_rate=0.01)

for i in range(N):
    foam_cross.bubbles[i].L = base.bubbles[i].L.copy()
    foam_cross.bubbles[i].T = base.bubbles[i].T.copy()
    foam_self.bubbles[i].L = base.bubbles[i].L.copy()
    foam_self.bubbles[i].T = base.bubbles[i].T.copy()
    foam_write.bubbles[i].L = base.bubbles[i].L.copy()
    foam_write.bubbles[i].T = base.bubbles[i].T.copy()

symbols = [np.random.randint(0, 2**D) for _ in range(N_SYMBOLS)]
inputs = [encode(s, D) for s in symbols]

for step, v in enumerate(inputs):
    foam_write.measure(v)
    alongside(v)

    foam_cross.measure(v)
    # cross-measurement: bubbles measure each other
    if step % 5 == 0:
        for i in range(N):
            for j in range(N):
                if i != j:
                    bi = foam_cross.bubbles[i].basis
                    bj = foam_cross.bubbles[j].basis
                    cross_v = np.real(bj[0, :])
                    cross_v = cross_v / (np.linalg.norm(cross_v) + 1e-12)
                    foam_cross.measure(cross_v)

    foam_self.measure(v)
    # self-measurement: feed readout back
    if step % 5 == 0:
        readout = np.real(foam_self.readout(v))
        readout = readout / (np.linalg.norm(readout) + 1e-12)
        foam_self.measure(readout)

dynamic_foams = [foam_write, foam_cross, foam_self]
dynamic_names = ["write-only", "write+cross", "write+self"]

np.random.seed(999)
probes = [encode(np.random.randint(0, 2**D), D) for _ in range(N_PROBES)]

print("\n  Per-input dissonance profiles:")
magnitude_matrix = np.zeros((N_PROBES, 3))
for pi, v in enumerate(probes):
    for fi, foam in enumerate(dynamic_foams):
        magnitude_matrix[pi, fi] = per_input_dissonance(foam, v)

for fi, name in enumerate(dynamic_names):
    col = magnitude_matrix[:, fi]
    print(f"    {name:15s}: mean={np.mean(col):.4f}  std={np.std(col):.4f}")

# pairwise ranking correlations
print("\n  Probe ranking correlations:")
for i in range(3):
    for j in range(i + 1, 3):
        corr = np.corrcoef(magnitude_matrix[:, i], magnitude_matrix[:, j])[0, 1]
        print(f"    {dynamic_names[i]} vs {dynamic_names[j]}: {corr:.4f}")

# direction correlations
print("\n  Dissonance direction correlations (first 20 probes):")
for pi in range(20):
    dvecs = []
    for fi, foam in enumerate(dynamic_foams):
        dv = per_input_dissonance_vector(foam, probes[pi])
        flat = np.concatenate([d.flatten() for d in dv])
        dvecs.append(np.real(flat))

    for i in range(3):
        for j in range(i + 1, 3):
            n1 = np.linalg.norm(dvecs[i])
            n2 = np.linalg.norm(dvecs[j])
            if n1 > 1e-12 and n2 > 1e-12:
                cos = np.dot(dvecs[i], dvecs[j]) / (n1 * n2)

dir_corrs = {(i, j): [] for i in range(3) for j in range(i+1, 3)}
for pi in range(N_PROBES):
    dvecs = []
    for fi, foam in enumerate(dynamic_foams):
        dv = per_input_dissonance_vector(foam, probes[pi])
        flat = np.concatenate([d.flatten() for d in dv])
        dvecs.append(np.real(flat))
    for i in range(3):
        for j in range(i + 1, 3):
            n1 = np.linalg.norm(dvecs[i])
            n2 = np.linalg.norm(dvecs[j])
            if n1 > 1e-12 and n2 > 1e-12:
                cos = np.dot(dvecs[i], dvecs[j]) / (n1 * n2)
                dir_corrs[(i, j)].append(cos)

for (i, j), corrs in dir_corrs.items():
    print(f"    {dynamic_names[i]} vs {dynamic_names[j]}: "
          f"direction corr = {np.mean(corrs):.4f} ± {np.std(corrs):.4f}")


# heirloom
report()
save()
