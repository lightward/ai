"""
optionality_cycles.py — do different foams breathe differently?

Foams shaped by different dynamics (not orderings — ordering is gauge)
are fed the same ongoing sequence. Track sensitivity (measurement
optionality) over time. Do they oscillate? Do they have characteristic
rhythms?

"different foams have different cycle patterns for optionality gradient
response/traversal" — Isaac
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley
from heirloom import alongside, report, save

np.random.seed(42)

D = 8
N = 3
N_HISTORY = 60     # inputs to shape each foam's history
N_FUTURE = 200     # ongoing sequence to track breathing
CROSS_EVERY = 3    # cross/self-measure every N steps during history


def clone_foam(foam):
    f = Foam(d=foam.d, n=foam.n, writing_rate=foam.writing_rate)
    for i in range(foam.n):
        f.bubbles[i].L = foam.bubbles[i].L.copy()
        f.bubbles[i].T = foam.bubbles[i].T.copy()
    return f


def cross_measure(foam, n_rounds=1):
    """Bubbles measure each other."""
    for _ in range(n_rounds):
        for i in range(foam.n):
            for j in range(foam.n):
                if i != j:
                    bj = foam.bubbles[j].basis
                    v = np.real(bj[0, :])
                    v = v / (np.linalg.norm(v) + 1e-12)
                    foam.measure(v)


def self_measure(foam, n_rounds=1):
    """Feed readout back as input."""
    for _ in range(n_rounds):
        v = encode(np.random.randint(0, 2**foam.d), foam.d)
        readout = np.real(foam.readout(v))
        readout = readout / (np.linalg.norm(readout) + 1e-12)
        foam.measure(readout)


def instantaneous_sensitivity(foam, probes):
    """Mean dissonance magnitude across probes (non-destructive)."""
    total = 0.0
    for v in probes:
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        total += np.mean([np.linalg.norm(j2[i] - m[i]) for i in range(foam.n)])
    return total / len(probes)


def sensitivity_spectrum(foam, probes):
    """Per-probe dissonance — the shape of the sensitivity, not just the mean."""
    vals = []
    for v in probes:
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        vals.append(np.mean([np.linalg.norm(j2[i] - m[i]) for i in range(foam.n)]))
    return np.array(vals)


# --- build foams with different dynamic histories ---
print("=" * 60)
print("Building foams with different dynamic histories")
print("=" * 60)

np.random.seed(42)
base = Foam(d=D, n=N, writing_rate=0.01)

# four foams, same initial state
foam_write = clone_foam(base)    # writing only
foam_cross = clone_foam(base)    # writing + cross-measurement
foam_self = clone_foam(base)     # writing + self-measurement
foam_alt = clone_foam(base)      # alternating cross and self

history_symbols = [np.random.randint(0, 2**D) for _ in range(N_HISTORY)]
history_inputs = [encode(s, D) for s in history_symbols]

for step, v in enumerate(history_inputs):
    foam_write.measure(v)
    foam_cross.measure(v)
    foam_self.measure(v)
    foam_alt.measure(v)
    alongside(v)

    if step % CROSS_EVERY == 0:
        cross_measure(foam_cross, 1)
        self_measure(foam_self, 1)
        # alternating: even→cross, odd→self
        if (step // CROSS_EVERY) % 2 == 0:
            cross_measure(foam_alt, 1)
        else:
            self_measure(foam_alt, 1)

foams = [foam_write, foam_cross, foam_self, foam_alt]
names = ["write-only", "write+cross", "write+self", "alternating"]

print("\nAfter history phase:")
for name, foam in zip(names, foams):
    print(f"  {name:15s}: L={foam.boundary_cost():.4f}")


# --- fixed probe set for sensitivity measurement ---
np.random.seed(777)
probe_symbols = [np.random.randint(0, 2**D) for _ in range(20)]
probe_inputs = [encode(s, D) for s in probe_symbols]


# --- track sensitivity over ongoing sequence ---
print("\n" + "=" * 60)
print("Tracking optionality (sensitivity) during ongoing sequence")
print("=" * 60)

np.random.seed(1234)
future_symbols = [np.random.randint(0, 2**D) for _ in range(N_FUTURE)]
future_inputs = [encode(s, D) for s in future_symbols]

# sensitivity time series for each foam
sensitivity_ts = {name: [] for name in names}
L_ts = {name: [] for name in names}

for step, v in enumerate(future_inputs):
    # measure sensitivity BEFORE this step's write
    for name, foam in zip(names, foams):
        sens = instantaneous_sensitivity(foam, probe_inputs)
        sensitivity_ts[name].append(sens)
        L_ts[name].append(foam.boundary_cost())

    # write
    for foam in foams:
        foam.measure(v)
    alongside(v)

# --- analysis ---
print("\nSensitivity time series statistics:")
for name in names:
    ts = np.array(sensitivity_ts[name])
    print(f"\n  {name}:")
    print(f"    mean={np.mean(ts):.4f}  std={np.std(ts):.4f}  "
          f"CV={np.std(ts)/np.mean(ts):.4f}")
    print(f"    min={np.min(ts):.4f}  max={np.max(ts):.4f}  "
          f"range={np.max(ts)-np.min(ts):.4f}")

    # autocorrelation — does the sensitivity have periodic structure?
    centered = ts - np.mean(ts)
    autocorr = np.correlate(centered, centered, mode='full')
    autocorr = autocorr[len(autocorr)//2:]  # positive lags only
    autocorr = autocorr / autocorr[0]  # normalize

    # find first local max after lag 0 (characteristic period)
    peaks = []
    for i in range(2, len(autocorr) - 1):
        if autocorr[i] > autocorr[i-1] and autocorr[i] > autocorr[i+1]:
            if autocorr[i] > 0.1:  # only significant peaks
                peaks.append((i, autocorr[i]))
    if peaks:
        print(f"    autocorrelation peaks: {peaks[:5]}")
    else:
        print(f"    autocorrelation: no significant peaks (aperiodic)")


# --- do they rank inputs differently over time? ---
print("\n" + "=" * 60)
print("Sensitivity SPECTRUM evolution (directional affordance over time)")
print("=" * 60)

# at 5 time points, get the per-probe sensitivity profile
checkpoints = [0, 50, 100, 150, 199]

# rebuild foams for clean checkpoint measurement
np.random.seed(42)
base = Foam(d=D, n=N, writing_rate=0.01)
foams2 = {
    "write-only": clone_foam(base),
    "write+cross": clone_foam(base),
    "write+self": clone_foam(base),
    "alternating": clone_foam(base),
}

# replay history
for step, v in enumerate(history_inputs):
    for f in foams2.values():
        f.measure(v)
    if step % CROSS_EVERY == 0:
        cross_measure(foams2["write+cross"], 1)
        self_measure(foams2["write+self"], 1)
        if (step // CROSS_EVERY) % 2 == 0:
            cross_measure(foams2["alternating"], 1)
        else:
            self_measure(foams2["alternating"], 1)

# now track spectra during future
spectra_over_time = {name: {} for name in names}

np.random.seed(1234)
future_inputs2 = [encode(s, D) for s in future_symbols]

for step, v in enumerate(future_inputs2):
    if step in checkpoints:
        for name in names:
            spectra_over_time[name][step] = sensitivity_spectrum(foams2[name], probe_inputs)

    for name in names:
        foams2[name].measure(v)

# compare spectra: do foams diverge in HOW they rank probes?
print("\nProbe ranking correlation between foam types (at each checkpoint):")
for cp in checkpoints:
    print(f"\n  step {cp}:")
    for i, n1 in enumerate(names):
        for j, n2 in enumerate(names):
            if j > i:
                s1 = spectra_over_time[n1][cp]
                s2 = spectra_over_time[n2][cp]
                corr = np.corrcoef(s1, s2)[0, 1]
                print(f"    {n1} vs {n2}: {corr:.4f}")

# does each foam's OWN spectrum change over time?
print("\nSelf-spectrum stability (correlation with own initial spectrum):")
for name in names:
    initial = spectra_over_time[name][checkpoints[0]]
    for cp in checkpoints[1:]:
        current = spectra_over_time[name][cp]
        corr = np.corrcoef(initial, current)[0, 1]
        print(f"  {name:15s} step 0 vs step {cp}: {corr:.4f}")


# --- the heirloom: does IT have a characteristic rhythm? ---
print("\n" + "=" * 60)
print("Heirloom optionality trajectory")
print("=" * 60)

from heirloom import get as get_heirloom
heirloom = get_heirloom()
h_sens = instantaneous_sensitivity(heirloom, probe_inputs)
h_spec = sensitivity_spectrum(heirloom, probe_inputs)
print(f"  L = {heirloom.boundary_cost():.4f}")
print(f"  mean sensitivity = {h_sens:.4f}")
print(f"  sensitivity CV across probes = {np.std(h_spec)/np.mean(h_spec):.4f}")

# how does the heirloom's spectrum correlate with each foam type?
# use the final checkpoint spectra
print(f"\n  Heirloom spectrum correlation with each dynamic type (final checkpoint):")
for name in names:
    final_spec = spectra_over_time[name][checkpoints[-1]]
    corr = np.corrcoef(h_spec, final_spec)[0, 1]
    print(f"    vs {name:15s}: {corr:.4f}")


report()
save()
