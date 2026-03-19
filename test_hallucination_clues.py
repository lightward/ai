"""
Test: does a badly-oriented observer still produce useful writes?

"Hallucination" = projection onto a basis that misses most of the geometry.
"Clue" = the write still contains usable structural information.

Setup: Two observers, A (well-aligned with the input) and B (badly-aligned).
Both write to the same foam with the same input.
Question: Does B's write still move the foam in a distinguishable direction?
Does a third observer C see useful structure from B's "hallucinated" writes?

If yes: hallucination contains clues. The projection is lossy but the
write extracts structure from whatever it can see.
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


def write_step(bases, v, P, eps=0.01):
    N = len(bases)
    d = bases[0].shape[0]
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


def foam_signature(bases, P):
    """Gauge-invariant readout from observer P."""
    N = len(bases)
    readouts = [P @ b for b in bases]
    sigs = []
    for i in range(N):
        for j in range(i, N):
            inner = np.trace(readouts[i].conj().T @ readouts[j])
            sigs.append(np.real(inner))
            sigs.append(np.imag(inner))
    return np.array(sigs)


def write_magnitude(bases, v, P):
    """How much does one write step change the foam?"""
    new_bases = write_step(bases, v, P)
    # measure change in each basis
    total = 0.0
    for old, new in zip(bases, new_bases):
        total += np.linalg.norm(new - old, 'fro')
    return total


def main():
    d = 8
    N = 3
    n_writes = 50
    rng = np.random.default_rng(42)

    # Input vector — lives primarily in first 3 dimensions
    v = np.zeros(d, dtype=complex)
    v[:3] = rng.standard_normal(3)
    v = v / np.linalg.norm(v)

    # Observer A: well-aligned (slice spans dims 0-2, where input lives)
    P_A = np.zeros((3, d))
    P_A[0, 0] = 1.0
    P_A[1, 1] = 1.0
    P_A[2, 2] = 1.0

    # Observer B: badly-aligned (slice spans dims 5-7, orthogonal to input)
    P_B = np.zeros((3, d))
    P_B[0, 5] = 1.0
    P_B[1, 6] = 1.0
    P_B[2, 7] = 1.0

    # Observer C: intermediate (slice spans dims 1-3, partial overlap)
    Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
    P_C = Q[:, :3].T  # random slice

    # Check alignment of each observer with the input
    for name, P in [("A (aligned)", P_A), ("B (orthogonal)", P_B), ("C (random)", P_C)]:
        proj = np.real(P @ v)
        alignment = np.linalg.norm(proj) / np.linalg.norm(v)
        print(f"Observer {name}: input alignment = {alignment:.4f}")
    print()

    # How much does each observer's write actually change the foam?
    foam = make_foam(d, N, np.random.default_rng(0))
    for name, P in [("A (aligned)", P_A), ("B (orthogonal)", P_B), ("C (random)", P_C)]:
        mag = write_magnitude(foam, v, P)
        print(f"Observer {name}: write magnitude = {mag:.6f}")
    print()

    # Now: each observer writes independently to copies of the foam.
    # A third readout (from C) compares what each produced.
    foam_base = make_foam(d, N, np.random.default_rng(0))
    sig_base = foam_signature(foam_base, P_C)

    results = {}
    for name, P in [("A (aligned)", P_A), ("B (orthogonal)", P_B), ("C (random)", P_C)]:
        foam = [b.copy() for b in foam_base]
        sigs = [foam_signature(foam, P_C)]
        for _ in range(n_writes):
            foam = write_step(foam, v, P)
            sigs.append(foam_signature(foam, P_C))

        sigs = np.array(sigs)
        total_drift = np.linalg.norm(sigs[-1] - sigs[0])
        step_changes = [np.linalg.norm(sigs[i+1] - sigs[i]) for i in range(len(sigs)-1)]
        results[name] = {
            'drift': total_drift,
            'mean_step': np.mean(step_changes),
            'final_sig': sigs[-1]
        }
        print(f"Observer {name} writes {n_writes} times:")
        print(f"  total drift (seen by C): {total_drift:.6f}")
        print(f"  mean step change:        {np.mean(step_changes):.6f}")
        print(f"  nonzero steps:           {sum(1 for s in step_changes if s > 1e-10)}/{len(step_changes)}")
        print()

    # Key question: can C distinguish A's writes from B's writes?
    dist_AB = np.linalg.norm(results["A (aligned)"]['final_sig'] - results["B (orthogonal)"]['final_sig'])
    dist_AC = np.linalg.norm(results["A (aligned)"]['final_sig'] - results["C (random)"]['final_sig'])
    dist_BC = np.linalg.norm(results["B (orthogonal)"]['final_sig'] - results["C (random)"]['final_sig'])

    print("Can C distinguish which observer wrote?")
    print(f"  distance(A-written, B-written): {dist_AB:.6f}")
    print(f"  distance(A-written, C-written): {dist_AC:.6f}")
    print(f"  distance(B-written, C-written): {dist_BC:.6f}")
    print()

    if results["B (orthogonal)"]['drift'] > 1e-10:
        print("→ B (orthogonal to input) still produces nonzero, distinguishable writes.")
        print("  The 'hallucination' (badly-aligned projection) contains clues.")
        print(f"  B's drift is {results['B (orthogonal)']['drift']/results['A (aligned)']['drift']*100:.1f}% "
              f"of A's drift.")
    else:
        print("→ B (orthogonal to input) produces NO distinguishable writes.")
        print("  When projection misses the input entirely, there are no clues.")

    # Final check: what if input has some energy in B's dimensions?
    print("\n" + "=" * 60)
    print("Control: input with energy in all dimensions")
    print("=" * 60 + "\n")

    v_full = rng.standard_normal(d).astype(complex)
    v_full = v_full / np.linalg.norm(v_full)

    for name, P in [("A", P_A), ("B", P_B), ("C", P_C)]:
        proj = np.real(P @ v_full)
        alignment = np.linalg.norm(proj) / np.linalg.norm(v_full)
        foam = [b.copy() for b in foam_base]
        for _ in range(n_writes):
            foam = write_step(foam, v_full, P)
        drift = np.linalg.norm(foam_signature(foam, P_C) - sig_base)
        print(f"Observer {name}: alignment={alignment:.4f}, drift={drift:.6f}")


if __name__ == "__main__":
    main()
