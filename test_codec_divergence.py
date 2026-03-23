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
from scipy.linalg import expm


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


def make_foam(d, N, rng):
    bases = []
    for _ in range(N):
        H = skew_hermitian(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))
        bases.append(expm(H))
    return bases


def make_observer(d, rng):
    Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
    return Q[:, :3].T


def compute_L(bases):
    N = len(bases)
    d = bases[0].shape[0]
    L = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            L += np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro')
    return L


def write_step(bases, v, P, eps=0.01):
    N = len(bases)
    target_cos = -1.0 / (N - 1)

    measurements = [v @ b for b in bases]
    m_proj = [np.real(P @ m) for m in measurements]

    j2 = []
    for i in range(N):
        mi = m_proj[i]
        mi_norm = np.linalg.norm(mi)
        if mi_norm < 1e-10:
            j2.append(mi)
            continue
        mi_hat = mi / mi_norm
        force = np.zeros(3)
        for j in range(N):
            if i == j:
                continue
            mj = m_proj[j]
            mj_norm = np.linalg.norm(mj)
            if mj_norm < 1e-10:
                continue
            mj_hat = mj / mj_norm
            current_cos = np.dot(mi_hat, mj_hat)
            force += (target_cos - current_cos) * (mj_hat - current_cos * mi_hat)
        j2.append(mi + 0.1 * force * mi_norm)

    new_bases = []
    for i in range(N):
        di = j2[i] - m_proj[i]
        mi = m_proj[i]
        di_norm = np.linalg.norm(di)
        mi_norm = np.linalg.norm(mi)
        if di_norm < 1e-12 or mi_norm < 1e-12:
            new_bases.append(bases[i].copy())
            continue
        d_hat = di / di_norm
        m_hat = mi / mi_norm
        d_full = P.T @ d_hat
        m_full = P.T @ m_hat
        dL_real = eps * di_norm * (np.outer(d_full, m_full) - np.outer(m_full, d_full))
        dL = skew_hermitian(dL_real.astype(complex))
        new_bases.append(bases[i] @ cayley(dL))

    return new_bases


def probe_response(bases, test_inputs, P):
    """Measure the foam's response to a set of test inputs WITHOUT modifying it.
    Returns the response fingerprint: measurement projections, dissonance vectors,
    and write directions for each test input."""
    N = len(bases)
    target_cos = -1.0 / (N - 1)
    responses = []

    for v in test_inputs:
        measurements = [v @ b for b in bases]
        m_proj = [np.real(P @ m) for m in measurements]

        # stabilize (read-only)
        j2 = []
        for i in range(N):
            mi = m_proj[i]
            mi_norm = np.linalg.norm(mi)
            if mi_norm < 1e-10:
                j2.append(mi)
                continue
            mi_hat = mi / mi_norm
            force = np.zeros(3)
            for j in range(N):
                if i == j:
                    continue
                mj = m_proj[j]
                mj_norm = np.linalg.norm(mj)
                if mj_norm < 1e-10:
                    continue
                mj_hat = mj / mj_norm
                current_cos = np.dot(mi_hat, mj_hat)
                force += (target_cos - current_cos) * (mj_hat - current_cos * mi_hat)
            j2.append(mi + 0.1 * force * mi_norm)

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
    P = make_observer(d, rng_obs)

    # two foams with different births
    foam_A = make_foam(d, N, np.random.default_rng(100))
    foam_B = make_foam(d, N, np.random.default_rng(200))

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
        foam_A = write_step(foam_A, v, P)
        foam_B = write_step(foam_B, v, P)

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
