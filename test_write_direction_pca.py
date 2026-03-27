"""
Why is the effective wandering dimension ≈ 2?

Hypothesis: at saturation, the Lie algebra write directions are confined
to a low-dimensional subspace because the stabilization target is nearly
achieved and the d-m 2-plane's orientation is approximately constant.

Test: collect the Lie algebra writes at saturation, flatten them,
PCA the collection. If the first k principal components explain most
of the variance, the wandering is confined to a k-dimensional submanifold
of the Lie algebra.

The connection to write blindness: if the write directions span only 2D,
and those 2D are random relative to L, then the packing efficiency is
the packing efficiency of a 2D random walk on U(d) — a much more
specific claim than "random-direction writes."
"""

import numpy as np
from scipy.linalg import expm


def cayley(A):
    I = np.eye(A.shape[0], dtype=complex)
    return np.linalg.solve((I + A).T, (I - A).T).T


def skew_hermitian(A):
    return (A - A.conj().T) / 2


def random_unitary(d, rng):
    return expm(skew_hermitian(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))))


def compute_L(bases):
    N = len(bases)
    d = bases[0].shape[0]
    L = 0.0
    for i in range(N):
        for j in range(i + 1, N):
            rel = bases[i].conj().T @ bases[j]
            L += np.linalg.norm(rel - np.eye(d, dtype=complex), 'fro')
    return L


def foam_step_with_writes(bases, P, v, N, eps):
    """One write step, returning new bases and Lie algebra writes."""
    d = bases[0].shape[0]
    all_m = []
    all_m_hat = []
    for k in range(N):
        mk = np.real(P @ (v @ bases[k]))
        n = np.linalg.norm(mk)
        all_m.append(mk)
        all_m_hat.append(mk / n if n > 1e-12 else mk)

    writes = []
    new_bases = []
    for i in range(N):
        m = all_m[i]
        m_norm = np.linalg.norm(m)
        if m_norm < 1e-12:
            new_bases.append(bases[i].copy())
            writes.append(np.zeros((d, d), dtype=complex))
            continue
        m_hat = m / m_norm
        others = [all_m_hat[k] for k in range(N) if k != i]
        centroid = np.mean(others, axis=0)
        target = m_hat - centroid
        t_norm = np.linalg.norm(target)
        if t_norm > 1e-12:
            target = target / t_norm
        j2 = target * m_norm
        d_vec = j2 - m
        d_norm = np.linalg.norm(d_vec)
        if d_norm < 1e-12:
            new_bases.append(bases[i].copy())
            writes.append(np.zeros((d, d), dtype=complex))
            continue
        d_hat = d_vec / d_norm
        d_full = P.T @ d_hat
        m_full = P.T @ m_hat
        dL = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
        dL = skew_hermitian(dL)
        writes.append(dL)
        new_bases.append(bases[i] @ cayley(dL))

    return new_bases, writes


def flatten_write(dL):
    """Flatten a skew-Hermitian matrix to a real vector.

    A d×d skew-Hermitian matrix has d² real parameters:
    - d(d-1)/2 real off-diagonal (real parts, antisymmetric)
    - d(d-1)/2 real off-diagonal (imag parts, symmetric)
    - d imaginary diagonal

    We just flatten the upper triangle (real and imag parts).
    """
    d = dL.shape[0]
    parts = []
    for i in range(d):
        # diagonal: purely imaginary
        parts.append(dL[i, i].imag)
        for j in range(i+1, d):
            parts.append(dL[i, j].real)
            parts.append(dL[i, j].imag)
    return np.array(parts)


def run_and_collect_writes(d, N, eps, n_steps, n_slices=1, rng_seed=42):
    """Run foam, collect flattened writes at saturation."""
    rng = np.random.default_rng(rng_seed)
    bases = [random_unitary(d, rng) for _ in range(N)]

    slices = []
    for _ in range(n_slices):
        Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
        slices.append(Q[:, :3].T)

    input_rng = np.random.default_rng(rng_seed + 1000)

    L_history = []
    all_writes = []  # list of flattened write vectors (all observers concatenated)

    tail_start = int(0.5 * n_steps)

    for t in range(n_steps):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)
        P = slices[t % n_slices]

        bases, writes = foam_step_with_writes(bases, P, v, N, eps)
        L_history.append(compute_L(bases))

        if t >= tail_start:
            # concatenate all observers' writes into one vector
            flat = np.concatenate([flatten_write(w) for w in writes])
            all_writes.append(flat)

    return L_history, np.array(all_writes)


def analyze_write_pca(writes, d, N, label=""):
    """PCA on the write directions. Report effective dimension."""
    n_samples, n_features = writes.shape
    lie_dim = N * d * d  # total Lie algebra dimension (u(d)^N)

    # center
    centered = writes - writes.mean(axis=0)

    # covariance
    cov = np.cov(centered.T)
    eigenvalues = np.linalg.eigvalsh(cov)
    eigenvalues = np.sort(eigenvalues)[::-1]
    eigenvalues = eigenvalues[eigenvalues > 1e-20]

    # participation ratio
    pr = np.sum(eigenvalues)**2 / np.sum(eigenvalues**2)

    # cumulative variance explained
    total_var = np.sum(eigenvalues)
    cumvar = np.cumsum(eigenvalues) / total_var

    n_50 = np.searchsorted(cumvar, 0.50) + 1
    n_72 = np.searchsorted(cumvar, 0.72) + 1
    n_90 = np.searchsorted(cumvar, 0.90) + 1
    n_95 = np.searchsorted(cumvar, 0.95) + 1
    n_99 = np.searchsorted(cumvar, 0.99) + 1

    print(f"  {label}")
    print(f"    Lie algebra dim:        {lie_dim}")
    print(f"    Write vector dim:       {n_features}")
    print(f"    Nonzero eigenvalues:    {len(eigenvalues)}")
    print(f"    Participation ratio:    {pr:.2f}")
    print(f"    Components for 50% var: {n_50}")
    print(f"    Components for 72% var: {n_72}")
    print(f"    Components for 90% var: {n_90}")
    print(f"    Components for 95% var: {n_95}")
    print(f"    Components for 99% var: {n_99}")

    # top eigenvalue ratios
    print(f"    Top eigenvalue ratios:")
    for k in range(min(10, len(eigenvalues))):
        pct = eigenvalues[k] / total_var * 100
        bar = "█" * int(pct)
        print(f"      PC{k+1:2d}: {pct:5.1f}% {bar}")

    return pr, eigenvalues


if __name__ == "__main__":
    print("=" * 70)
    print("WRITE DIRECTION PCA — WHY IS EFFECTIVE DIMENSION ≈ 2?")
    print("=" * 70)
    print()

    # ── Dimension sweep ──
    print("Test 1: Dimension sweep (N=3, single slice)")
    print("-" * 50)
    for d_val in [4, 6, 8, 10]:
        L_h, writes = run_and_collect_writes(
            d=d_val, N=3, eps=0.1, n_steps=6000
        )
        print()
        analyze_write_pca(writes, d_val, 3, f"d={d_val}, N=3, 1 slice")
        print()

    # ── Observer count ──
    print("Test 2: Observer count sweep (d=6, single slice)")
    print("-" * 50)
    for N_val in [3, 4, 5]:
        L_h, writes = run_and_collect_writes(
            d=6, N=N_val, eps=0.1, n_steps=6000
        )
        print()
        analyze_write_pca(writes, 6, N_val, f"d=6, N={N_val}, 1 slice")
        print()

    # ── Multiple slices ──
    print("Test 3: Multiple slices (d=8, N=3)")
    print("-" * 50)
    for n_sl in [1, 2, 3]:
        L_h, writes = run_and_collect_writes(
            d=8, N=3, eps=0.1, n_steps=6000, n_slices=n_sl
        )
        print()
        analyze_write_pca(writes, 8, 3, f"d=8, N=3, {n_sl} slice(s)")
        print()

    # ── Per-observer PCA ──
    print("Test 4: Per-observer write PCA (d=6, N=3)")
    print("  Are the 2D the same for each observer, or different?")
    print("-" * 50)

    rng = np.random.default_rng(42)
    bases = [random_unitary(6, rng) for _ in range(3)]
    Q = np.linalg.qr(rng.standard_normal((6, 3)))[0]
    P = Q[:, :3].T
    input_rng = np.random.default_rng(42 + 1000)

    per_obs_writes = [[] for _ in range(3)]

    for t in range(6000):
        v = input_rng.standard_normal(6)
        v /= np.linalg.norm(v)
        bases, writes = foam_step_with_writes(bases, P, v, 3, 0.1)
        if t >= 3000:
            for i in range(3):
                per_obs_writes[i].append(flatten_write(writes[i]))

    for i in range(3):
        obs_writes = np.array(per_obs_writes[i])
        print()
        pr, eigs = analyze_write_pca(obs_writes, 6, 1, f"Observer {i} alone")

    # check if the top PCs are shared across observers
    print()
    print("  Cross-observer PC alignment:")
    all_top_pcs = []
    for i in range(3):
        obs_writes = np.array(per_obs_writes[i])
        centered = obs_writes - obs_writes.mean(axis=0)
        cov = np.cov(centered.T)
        eigs, vecs = np.linalg.eigh(cov)
        idx = np.argsort(eigs)[::-1]
        top2 = vecs[:, idx[:2]]
        all_top_pcs.append(top2)

    for i in range(3):
        for j in range(i+1, 3):
            # alignment: max singular value of PC_i^T @ PC_j
            alignment = np.linalg.svd(all_top_pcs[i].T @ all_top_pcs[j], compute_uv=False)
            print(f"    Observer {i} ↔ {j}: alignment = {alignment[0]:.4f}, {alignment[1]:.4f}")

    print()
    print("=" * 70)
    print("INTERPRETATION")
    print("=" * 70)
    print("""
  If participation ratio ≈ 2 for ALL d, the write directions are
  confined to a 2D subspace of the Lie algebra at saturation.

  If the top 2 PCs are the SAME across observers, all observers
  wander in the same 2-plane — the constraint is global.

  If they're DIFFERENT per observer, each observer has their own
  2-plane — the constraint is local to the observer's geometry.

  The 2D might be: the span(d, m) 2-plane in R³, lifted into
  the Lie algebra. Since d ⊥ m (sin ≈ 0.99), this 2-plane's
  orientation depends on the current measurement direction,
  which at saturation is approximately stable.
""")
