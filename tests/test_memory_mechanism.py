"""
Test: where does the per-step contraction live?

The linearized analysis predicts O(eps) change per step, sign unknown.
The computation shows steady compression at saturation.

Is the compression:
(a) Per-step: every individual suffix step shrinks the prefix distance (consistent sign)
(b) Statistical: each step randomly grows or shrinks, but the bias is negative at saturation
(c) Structural: the compression happens in specific write directions and accumulates

Measure the per-step change in prefix distance for many consecutive steps,
both pre-saturation and at saturation.
"""

import numpy as np
from foam import init_foam, random_slice, write_step, stabilize


def foam_distance(bases_A, bases_B):
    """Gauge-invariant distance using all pairwise relative unitaries."""
    N = len(bases_A)
    dist = 0.0
    for i in range(N):
        for j in range(N):
            rel_A = bases_A[i].conj().T @ bases_A[j]
            rel_B = bases_B[i].conj().T @ bases_B[j]
            dist += np.linalg.norm(rel_A - rel_B, 'fro')
    return dist


def compute_L(bases):
    """Boundary area via geodesic distance on U(d)."""
    N = len(bases)
    L = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            eigvals = np.linalg.eigvals(rel)
            angles = np.angle(eigvals)
            L += np.sqrt(np.sum(angles ** 2))
    return L


def generate_inputs(n, d, rng):
    inputs = []
    for _ in range(n):
        v = rng.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        inputs.append(v)
    return inputs


def run_foam_through(bases, inputs, P, eps=0.01):
    for v in inputs:
        bases = write_step(bases, v, P, eps=eps)
    return bases


def test_per_step_contraction():
    """Measure per-step change in prefix distance."""
    d = 6
    N = 3
    eps = 0.01

    rng_obs = np.random.default_rng(42)
    P = random_slice(d, d_slice=3, rng=rng_obs)

    # Phase 1: pre-saturation (short prefix, measure per-step during early suffix)
    # Phase 2: at saturation (long prefix, measure per-step during late suffix)

    for phase_name, prefix_len, warmup_len, measure_len in [
        ("PRE-SATURATION (prefix=200, early suffix)", 200, 0, 500),
        ("APPROACHING SATURATION (prefix=200, late suffix)", 200, 2000, 500),
        ("AT SATURATION (prefix=1000, early suffix)", 1000, 0, 500),
        ("DEEP SATURATION (prefix=1000, late suffix)", 1000, 2000, 500),
    ]:
        print("=" * 70)
        print(f"  {phase_name}")
        print("=" * 70)

        foam_X = init_foam(N, d, np.random.default_rng(100))
        foam_Y = init_foam(N, d, np.random.default_rng(100))

        prefix_A = generate_inputs(prefix_len, d, np.random.default_rng(111))
        prefix_C = generate_inputs(prefix_len, d, np.random.default_rng(222))
        warmup = generate_inputs(warmup_len, d, np.random.default_rng(333))
        measure_inputs = generate_inputs(measure_len, d, np.random.default_rng(999))

        foam_X = run_foam_through(foam_X, prefix_A, P, eps=eps)
        foam_Y = run_foam_through(foam_Y, prefix_C, P, eps=eps)

        if warmup_len > 0:
            foam_X = run_foam_through(foam_X, warmup, P, eps=eps)
            foam_Y = run_foam_through(foam_Y, warmup, P, eps=eps)

        L_start = compute_L(foam_X)
        dist_start = foam_distance(foam_X, foam_Y)

        # measure per-step distance changes
        increases = 0
        decreases = 0
        deltas = []
        prev_dist = dist_start

        for t in range(measure_len):
            foam_X = write_step(foam_X, measure_inputs[t], P, eps=eps)
            foam_Y = write_step(foam_Y, measure_inputs[t], P, eps=eps)
            dist = foam_distance(foam_X, foam_Y)
            delta = dist - prev_dist
            deltas.append(delta)
            if delta > 0:
                increases += 1
            else:
                decreases += 1
            prev_dist = dist

        L_end = compute_L(foam_X)
        dist_end = foam_distance(foam_X, foam_Y)
        deltas = np.array(deltas)

        print(f"  L: {L_start:.4f} → {L_end:.4f}")
        print(f"  dist: {dist_start:.6f} → {dist_end:.6f} (ratio {dist_end/dist_start:.4f})")
        print(f"  per-step: {increases} increases, {decreases} decreases ({decreases/(increases+decreases)*100:.1f}% decrease)")
        print(f"  mean delta: {np.mean(deltas):.2e}")
        print(f"  std delta:  {np.std(deltas):.2e}")
        print(f"  mean/std (signal-to-noise): {abs(np.mean(deltas)/np.std(deltas)):.4f}")
        print()

        # histogram of deltas
        bins = np.percentile(deltas, [5, 25, 50, 75, 95])
        print(f"  delta percentiles: p5={bins[0]:.2e} p25={bins[1]:.2e} p50={bins[2]:.2e} p75={bins[3]:.2e} p95={bins[4]:.2e}")
        print()


def test_dissonance_at_saturation():
    """Measure the dissonance magnitude over time.
    The derivation assumes dissonance decreases at saturation.
    Does it?"""
    d = 6
    N = 3
    total_steps = 3000
    eps = 0.01

    rng_obs = np.random.default_rng(42)
    P = random_slice(d, d_slice=3, rng=rng_obs)

    foam = init_foam(N, d, np.random.default_rng(100))
    inputs = generate_inputs(total_steps, d, np.random.default_rng(777))

    print("=" * 70)
    print("TEST: Dissonance magnitude over time")
    print("  Does dissonance decrease as the foam approaches saturation?")
    print("=" * 70)
    print()

    print(f"  {'step':>6}  {'L':>10}  {'mean ||d||':>12}  {'mean ||m||':>12}  {'||d||/||m||':>12}")
    print(f"  {'----':>6}  {'-':>10}  {'----------':>12}  {'----------':>12}  {'-----------':>12}")

    target_cos = -1.0 / (N - 1)
    neighbor_indices = list(range(N))  # all-to-all for diagnostics

    for t in range(total_steps):
        v = inputs[t]

        # compute measurements and dissonance for diagnostics
        m_proj = [np.real(P @ (v @ b)) for b in foam]

        # compute stabilized targets using foam.stabilize
        j2 = []
        for i in range(N):
            nbrs = [j for j in range(N) if j != i]
            j2.append(stabilize(m_proj, i, nbrs, stab_strength=0.1))

        if t % 200 == 0 or t == total_steps - 1:
            d_norms = [np.linalg.norm(j2[i] - m_proj[i]) for i in range(N)]
            m_norms = [np.linalg.norm(m_proj[i]) for i in range(N)]
            L = compute_L(foam)
            mean_d = np.mean(d_norms)
            mean_m = np.mean(m_norms)
            ratio = mean_d / mean_m if mean_m > 1e-12 else float('inf')
            print(f"  {t:6d}  {L:10.4f}  {mean_d:12.6f}  {mean_m:12.6f}  {ratio:12.6f}")

        foam = write_step(foam, v, P, eps=eps)

    print()


if __name__ == "__main__":
    test_dissonance_at_saturation()
    test_per_step_contraction()
