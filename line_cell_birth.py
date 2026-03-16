"""
line_cell_birth.py — cell birth in the measurement basis.

"Shit just got real" as two specialized sub-foams cross-measuring
and producing a new effective basis that spans both domains.

The hypothesis: two foams, each specialized on different input classes,
cross-measure. The cross-measurement produces organized BCH residuals
that increase sensitivity to inputs that CONNECT the two domains —
inputs that neither foam alone would respond to strongly.

This is cell birth in the LINE, not the foam. The measurer becomes
more plural.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian
from heirloom import alongside, report, save

np.random.seed(42)

D = 8
N = 3
N_SPECIALIZE = 100  # inputs to specialize each foam
N_PROBE = 50


def clone_foam(foam):
    f = Foam(d=foam.d, n=foam.n, writing_rate=foam.writing_rate)
    for i in range(foam.n):
        f.bubbles[i].L = foam.bubbles[i].L.copy()
        f.bubbles[i].T = foam.bubbles[i].T.copy()
    return f


def sensitivity_to_inputs(foam, inputs):
    """Mean dissonance across specific inputs (non-destructive)."""
    total = 0.0
    for v in inputs:
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        total += np.mean([np.linalg.norm(j2[i] - m[i]) for i in range(foam.n)])
    return total / len(inputs)


def per_input_sensitivity(foam, inputs):
    """Per-input dissonance vector."""
    vals = []
    for v in inputs:
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        vals.append(np.mean([np.linalg.norm(j2[i] - m[i]) for i in range(foam.n)]))
    return np.array(vals)


# --- create two domains with distinct input classes ---
# domain A: symbols 0-63 (low bits)
# domain B: symbols 192-255 (high bits)
# connection: symbols 64-191 (middle — overlapping structure)

np.random.seed(42)
domain_a_symbols = [np.random.randint(0, 64) for _ in range(N_SPECIALIZE)]
domain_b_symbols = [np.random.randint(192, 256) for _ in range(N_SPECIALIZE)]
connection_symbols = [np.random.randint(64, 192) for _ in range(N_PROBE)]

domain_a_inputs = [encode(s, D) for s in domain_a_symbols]
domain_b_inputs = [encode(s, D) for s in domain_b_symbols]
connection_inputs = [encode(s, D) for s in connection_symbols]

# also probe inputs from each domain
probe_a = [encode(np.random.randint(0, 64), D) for _ in range(N_PROBE)]
probe_b = [encode(np.random.randint(192, 256), D) for _ in range(N_PROBE)]


# --- specialize two foams on different domains ---
print("=" * 60)
print("Specializing two foams on different domains")
print("=" * 60)

# start from same initial state
base = Foam(d=D, n=N, writing_rate=0.01)
foam_a = clone_foam(base)  # will specialize on domain A
foam_b = clone_foam(base)  # will specialize on domain B

for v in domain_a_inputs:
    foam_a.measure(v)
    alongside(v)

for v in domain_b_inputs:
    foam_b.measure(v)
    alongside(v)

print(f"\nAfter specialization:")
print(f"  foam_a L = {foam_a.boundary_cost():.4f}")
print(f"  foam_b L = {foam_b.boundary_cost():.4f}")

# --- measure each foam's sensitivity to each domain ---
print(f"\nSensitivity BEFORE cross-measurement:")
print(f"  foam_a to domain A: {sensitivity_to_inputs(foam_a, probe_a):.4f}")
print(f"  foam_a to domain B: {sensitivity_to_inputs(foam_a, probe_b):.4f}")
print(f"  foam_a to connection: {sensitivity_to_inputs(foam_a, connection_inputs):.4f}")
print(f"  foam_b to domain A: {sensitivity_to_inputs(foam_b, probe_a):.4f}")
print(f"  foam_b to domain B: {sensitivity_to_inputs(foam_b, probe_b):.4f}")
print(f"  foam_b to connection: {sensitivity_to_inputs(foam_b, connection_inputs):.4f}")


# --- cross-measure: foam_a and foam_b measure each other ---
print("\n" + "=" * 60)
print("Cross-measurement between specialized foams")
print("=" * 60)

# save pre-cross state
foam_a_pre = clone_foam(foam_a)
foam_b_pre = clone_foam(foam_b)

N_CROSS = 30
for step in range(N_CROSS):
    # foam_a reads foam_b's bases
    for i in range(N):
        bj = foam_b.bubbles[i].basis
        v = np.real(bj[0, :])
        v = v / (np.linalg.norm(v) + 1e-12)
        foam_a.measure(v)

    # foam_b reads foam_a's bases
    for i in range(N):
        bj = foam_a.bubbles[i].basis
        v = np.real(bj[0, :])
        v = v / (np.linalg.norm(v) + 1e-12)
        foam_b.measure(v)

print(f"\nAfter cross-measurement:")
print(f"  foam_a L = {foam_a.boundary_cost():.4f}")
print(f"  foam_b L = {foam_b.boundary_cost():.4f}")


# --- key test: sensitivity to connection inputs ---
print(f"\nSensitivity AFTER cross-measurement:")
print(f"  foam_a to domain A: {sensitivity_to_inputs(foam_a, probe_a):.4f}")
print(f"  foam_a to domain B: {sensitivity_to_inputs(foam_a, probe_b):.4f}")
print(f"  foam_a to connection: {sensitivity_to_inputs(foam_a, connection_inputs):.4f}")
print(f"  foam_b to domain A: {sensitivity_to_inputs(foam_b, probe_a):.4f}")
print(f"  foam_b to domain B: {sensitivity_to_inputs(foam_b, probe_b):.4f}")
print(f"  foam_b to connection: {sensitivity_to_inputs(foam_b, connection_inputs):.4f}")


# --- comparison: self-measurement instead of cross ---
print("\n" + "=" * 60)
print("CONTROL: self-measurement instead of cross")
print("=" * 60)

foam_a_self = clone_foam(foam_a_pre)
foam_b_self = clone_foam(foam_b_pre)

for step in range(N_CROSS):
    # each foam self-measures
    v = encode(np.random.randint(0, 256), D)
    ra = np.real(foam_a_self.readout(v))
    ra = ra / (np.linalg.norm(ra) + 1e-12)
    foam_a_self.measure(ra)

    rb = np.real(foam_b_self.readout(v))
    rb = rb / (np.linalg.norm(rb) + 1e-12)
    foam_b_self.measure(rb)

print(f"\nSensitivity after SELF-measurement (control):")
print(f"  foam_a to domain A: {sensitivity_to_inputs(foam_a_self, probe_a):.4f}")
print(f"  foam_a to domain B: {sensitivity_to_inputs(foam_a_self, probe_b):.4f}")
print(f"  foam_a to connection: {sensitivity_to_inputs(foam_a_self, connection_inputs):.4f}")
print(f"  foam_b to domain A: {sensitivity_to_inputs(foam_b_self, probe_a):.4f}")
print(f"  foam_b to domain B: {sensitivity_to_inputs(foam_b_self, probe_b):.4f}")
print(f"  foam_b to connection: {sensitivity_to_inputs(foam_b_self, connection_inputs):.4f}")


# --- does cross-measurement change which CONNECTION inputs are most dissonant? ---
print("\n" + "=" * 60)
print("Directional change in connection sensitivity")
print("=" * 60)

pre_profile_a = per_input_sensitivity(foam_a_pre, connection_inputs)
post_profile_a = per_input_sensitivity(foam_a, connection_inputs)
self_profile_a = per_input_sensitivity(foam_a_self, connection_inputs)

corr_cross = np.corrcoef(pre_profile_a, post_profile_a)[0, 1]
corr_self = np.corrcoef(pre_profile_a, self_profile_a)[0, 1]

print(f"  foam_a connection profile correlation:")
print(f"    pre vs post-cross: {corr_cross:.4f}")
print(f"    pre vs post-self:  {corr_self:.4f}")
print(f"    (lower = more reshaping of which connections are available)")

pre_profile_b = per_input_sensitivity(foam_b_pre, connection_inputs)
post_profile_b = per_input_sensitivity(foam_b, connection_inputs)
self_profile_b = per_input_sensitivity(foam_b_self, connection_inputs)

corr_cross_b = np.corrcoef(pre_profile_b, post_profile_b)[0, 1]
corr_self_b = np.corrcoef(pre_profile_b, self_profile_b)[0, 1]

print(f"  foam_b connection profile correlation:")
print(f"    pre vs post-cross: {corr_cross_b:.4f}")
print(f"    pre vs post-self:  {corr_self_b:.4f}")


# --- do the two foams CONVERGE on which connections matter? ---
print("\n" + "=" * 60)
print("Do cross-measured foams agree on which connections matter?")
print("=" * 60)

cross_agree = np.corrcoef(post_profile_a, post_profile_b)[0, 1]
self_agree = np.corrcoef(self_profile_a, self_profile_b)[0, 1]
pre_agree = np.corrcoef(pre_profile_a, pre_profile_b)[0, 1]

print(f"  Connection profile agreement between foam_a and foam_b:")
print(f"    before anything:      {pre_agree:.4f}")
print(f"    after cross-measure:  {cross_agree:.4f}")
print(f"    after self-measure:   {self_agree:.4f}")


report()
save()
