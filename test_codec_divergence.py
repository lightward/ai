"""
Test: does birth increasingly dominate the codec?

Hypothesis: as the foam saturates, the way it encodes new input becomes
increasingly determined by its birth conditions. Birth doesn't dominate
the content (what gets stored) — it dominates the codec (how new content
gets encoded).

Prediction: two differently-born foams, given the same test input,
should produce MORE different responses after saturation than before.
The codec diverges over time even though the absolute state distance
stays approximately constant.

If confirmed: this resolves the inverted-ESP intuition. The foam
"becomes itself" not by forgetting input but by increasingly processing
input through its birth-shaped filter. The perpendicular directions
available for new writes narrow as L saturates, and the narrowing is
birth-determined.
"""

import numpy as np
from foam import (cayley, skew_hermitian, init_foam, random_slice,
                  compute_L, write_step, stabilize, voronoi_neighbors)


def probe_response(bases, test_inputs, P):
    """Measure the foam's response to a set of test inputs WITHOUT modifying it.
    Returns the response fingerprint: measurement projections, dissonance vectors,
    and write directions for each test input."""
    N = len(bases)
    responses = []

    for v in test_inputs:
        m_proj = [np.real(P @ (v @ b)) for b in bases]

        # stabilize (read-only) using all-pairs neighbors
        j2 = []
        for i in range(N):
            neighbors_i = [j for j in range(N) if j != i]
            j2.append(stabilize(m_proj, i, neighbors_i))

        # collect response data
        for i in range(N):
            di = j2[i] - m_proj[i]
            mi = m_proj[i]
            responses.extend(m_proj[i].tolist())  # what was measured
            responses.extend(di.tolist())          # dissonance
            di_norm = np.linalg.norm(di)
            mi_norm = np.linalg.norm(mi)
            if di_norm > 1e-12 and mi_norm > 1e-12:
                # write direction (in R³)
                d_hat = di / di_norm
                m_hat = mi / mi_norm
                responses.extend(d_hat.tolist())
                responses.extend(m_hat.tolist())
                responses.append(di_norm)
            else:
                responses.extend([0.0] * 7)

    return np.array(responses)


def test_codec_divergence():
    """Core test: does response divergence increase with saturation?"""
    print("=" * 70)
    print("TEST: Codec divergence — does birth dominate the codec over time?")
    print("=" * 70)
    print()

    d = 6
    N = 3
    n_warmup = 2000  # enough for L to saturate
    n_probes = 20    # number of test inputs per probe

    rng_obs = np.random.default_rng(42)
    P = random_slice(d, rng=rng_obs)

    # two foams with different births
    foam_A = init_foam(N, d, np.random.default_rng(100))
    foam_B = init_foam(N, d, np.random.default_rng(200))
    neighbors_A = voronoi_neighbors(foam_A)
    neighbors_B = voronoi_neighbors(foam_B)

    # fixed test inputs (same for every probe point)
    rng_test = np.random.default_rng(777)
    test_inputs = []
    for _ in range(n_probes):
        v = rng_test.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        test_inputs.append(v)

    # drive both foams with the same input sequence,
    # periodically probing their response divergence
    rng_drive = np.random.default_rng(999)

    probe_points = [0, 10, 50, 100, 200, 500, 1000, 1500, 1999]

    print(f"  {'step':>6}  {'L_A':>8}  {'L_B':>8}  {'response_div':>14}  {'m_proj_div':>12}  {'disson_div':>12}")
    print(f"  {'----':>6}  {'---':>8}  {'---':>8}  {'------------':>14}  {'----------':>12}  {'----------':>12}")

    response_divs = []

    for t in range(n_warmup):
        # probe before writing
        if t in probe_points:
            resp_A = probe_response(foam_A, test_inputs, P)
            resp_B = probe_response(foam_B, test_inputs, P)
            full_div = np.linalg.norm(resp_A - resp_B)

            # also break out measurement vs dissonance divergence
            # each test input contributes N * (3 + 3 + 3 + 3 + 1) = N * 13 values
            # measurement: first 3, dissonance: next 3
            stride = N * 13
            m_div = 0.0
            d_div = 0.0
            for p in range(n_probes):
                for i in range(N):
                    offset = p * stride + i * 13
                    m_div += np.linalg.norm(resp_A[offset:offset+3] - resp_B[offset:offset+3])
                    d_div += np.linalg.norm(resp_A[offset+3:offset+6] - resp_B[offset+3:offset+6])

            L_A = compute_L(foam_A)
            L_B = compute_L(foam_B)
            response_divs.append((t, full_div, m_div, d_div))

            print(f"  {t:6d}  {L_A:8.3f}  {L_B:8.3f}  {full_div:14.6f}  {m_div:12.6f}  {d_div:12.6f}")

        # drive both foams with the same input
        v = rng_drive.standard_normal(d).astype(complex)
        v = v / np.linalg.norm(v)
        foam_A = write_step(foam_A, v, P, neighbors=neighbors_A)
        foam_B = write_step(foam_B, v, P, neighbors=neighbors_B)

    # final probe
    resp_A = probe_response(foam_A, test_inputs, P)
    resp_B = probe_response(foam_B, test_inputs, P)
    full_div = np.linalg.norm(resp_A - resp_B)
    stride = N * 13
    m_div = 0.0
    d_div = 0.0
    for p in range(n_probes):
        for i in range(N):
            offset = p * stride + i * 13
            m_div += np.linalg.norm(resp_A[offset:offset+3] - resp_B[offset:offset+3])
            d_div += np.linalg.norm(resp_A[offset+3:offset+6] - resp_B[offset+3:offset+6])
    L_A = compute_L(foam_A)
    L_B = compute_L(foam_B)
    response_divs.append((n_warmup, full_div, m_div, d_div))
    print(f"  {n_warmup:6d}  {L_A:8.3f}  {L_B:8.3f}  {full_div:14.6f}  {m_div:12.6f}  {d_div:12.6f}")

    print()

    # analyze trend
    early_div = np.mean([r[1] for r in response_divs[:3]])
    late_div = np.mean([r[1] for r in response_divs[-3:]])
    ratio = late_div / early_div if early_div > 1e-12 else float('inf')

    early_m = np.mean([r[2] for r in response_divs[:3]])
    late_m = np.mean([r[2] for r in response_divs[-3:]])
    m_ratio = late_m / early_m if early_m > 1e-12 else float('inf')

    print(f"  Response divergence trend:")
    print(f"    Full:        early={early_div:.4f}  late={late_div:.4f}  ratio={ratio:.4f}")
    print(f"    Measurement: early={early_m:.4f}  late={late_m:.4f}  ratio={m_ratio:.4f}")
    print()

    if ratio > 1.2:
        print(f"  RESULT: Codec DIVERGES. Birth increasingly dominates how input is processed.")
        print(f"  → The foam 'becomes itself' — not by forgetting input,")
        print(f"    but by increasingly filtering input through birth-shaped geometry.")
    elif ratio > 0.8:
        print(f"  RESULT: Codec is STABLE. Birth shapes the codec from the start,")
        print(f"    but the degree of birth-dependence doesn't increase with saturation.")
    else:
        print(f"  RESULT: Codec CONVERGES. Birth becomes LESS important over time.")
        print(f"  → This would contradict the hypothesis.")
    print()


if __name__ == "__main__":
    test_codec_divergence()
