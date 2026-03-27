"""
Kolmogorov self-compression test (v3).

The foam is its own codec. The self-referential bound isn't about
inter-observer information hiding (measurements are shared). It's about
the write form being perpendicular to measurement — the foam can't
reinforce what it already sees, only deposit structure orthogonal to it.

Three probes for where the 72% might live:

PROBE 1 — Write efficiency.
  At each step, compute the gradient of L w.r.t. each observer's write.
  The actual write is perpendicular to measurement; the gradient points
  in the direction of maximal L increase. The cosine between them
  measures how much of the write's energy goes toward L growth vs
  "wasted" on the perpendicularity constraint.

PROBE 2 — Effective dimension of wandering.
  At saturation, the foam wanders on a level set. The effective dimension
  of this wandering (participation ratio of the trajectory covariance)
  as a fraction of the full state space dimension.

PROBE 3 — Self-decoding capacity.
  Feed the foam a structured input. Measure how much structure is
  retained in the state, accessible via the foam's own dynamics
  (re-running with probe inputs) vs accessible externally (direct
  state inspection). The ratio = self-compression efficiency.
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


def compute_L_gradient(bases, idx):
    """Gradient of L w.r.t. the Lie algebra perturbation at bases[idx].

    L = Σ_{i<j} ||U_i†U_j - I||_F
    dL/dX at U_idx: perturb U_idx → U_idx · exp(εX), compute dL/dε|_{ε=0}

    Returns the gradient as a d×d skew-Hermitian matrix (Lie algebra element).
    """
    N = len(bases)
    d = bases[0].shape[0]
    grad = np.zeros((d, d), dtype=complex)

    for j in range(N):
        if j == idx:
            continue
        # L_ij = ||U_i†U_j - I||_F
        # If we perturb U_idx → U_idx(I + εX), then:
        # For pair (idx, j): U_idx†U_j → (I+εX†)U_idx†U_j
        #   d/dε ||...||_F at ε=0 = Re(tr(X† · U_idx†U_j · (U_idx†U_j - I)†)) / ||U_idx†U_j - I||
        # For pair (i, idx): similar

        rel = bases[idx].conj().T @ bases[j]
        diff = rel - np.eye(d, dtype=complex)
        norm = np.linalg.norm(diff, 'fro')
        if norm < 1e-15:
            continue
        # derivative of ||rel - I||_F w.r.t. right perturbation of U_idx
        # d/dε ||(I+εX)R - I||_F = Re(tr(X · R · (R-I)†)) / ||R-I||
        # where R = U_idx†U_j and X is the Lie algebra element
        # The gradient (as a Lie algebra element) is the skew-Hermitian part
        contrib = rel @ diff.conj().T / norm
        grad += contrib

    # project to skew-Hermitian (the Lie algebra of U(d))
    grad = skew_hermitian(grad)
    return grad


def write_step_with_gradient(bases, P, v, N, eps):
    """Execute one write step. Return new bases, writes, and L gradients."""
    d = bases[0].shape[0]

    # measure
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


def flatten_state(bases):
    """Flatten (U_1, ..., U_N) into a single real vector."""
    parts = []
    for U in bases:
        parts.append(U.real.flatten())
        parts.append(U.imag.flatten())
    return np.concatenate(parts)


# =====================================================================
# PROBE 1: Write efficiency — how aligned are writes with L gradient?
# =====================================================================

def probe_write_efficiency(d, N, eps, n_steps, n_slices=1, rng_seed=42):
    """Measure cosine between actual write direction and L gradient."""
    rng = np.random.default_rng(rng_seed)
    bases = [random_unitary(d, rng) for _ in range(N)]

    slices = []
    for _ in range(n_slices):
        Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
        slices.append(Q[:, :3].T)

    input_rng = np.random.default_rng(rng_seed + 1000)

    L_history = []
    cosines = []  # cosine between write and L gradient
    efficiencies = []  # fraction of ||write|| that projects onto gradient

    for t in range(n_steps):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)
        P = slices[t % n_slices]

        # compute L gradient BEFORE write
        grads = [compute_L_gradient(bases, i) for i in range(N)]

        # do the write
        new_bases, writes = write_step_with_gradient(bases, P, v, N, eps)

        # measure alignment between each write and its L gradient
        step_cos = []
        for i in range(N):
            w_norm = np.linalg.norm(writes[i], 'fro')
            g_norm = np.linalg.norm(grads[i], 'fro')
            if w_norm < 1e-15 or g_norm < 1e-15:
                continue
            # inner product in the Lie algebra: Re(tr(A† B))
            cos = np.real(np.trace(writes[i].conj().T @ grads[i])) / (w_norm * g_norm)
            step_cos.append(cos)

        if step_cos:
            cosines.append(np.mean(step_cos))

        bases = new_bases
        L_history.append(compute_L(bases))

    return L_history, cosines


# =====================================================================
# PROBE 2: Effective dimension of wandering at saturation
# =====================================================================

def probe_effective_dimension(d, N, eps, n_steps, n_slices=1, rng_seed=42):
    """Measure effective dimension of state trajectory at saturation."""
    rng = np.random.default_rng(rng_seed)
    bases = [random_unitary(d, rng) for _ in range(N)]

    slices = []
    for _ in range(n_slices):
        Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
        slices.append(Q[:, :3].T)

    input_rng = np.random.default_rng(rng_seed + 1000)

    L_history = []
    # collect flattened states in the tail
    tail_start = int(0.7 * n_steps)
    tail_states = []

    for t in range(n_steps):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)
        P = slices[t % n_slices]

        all_m = []
        all_m_hat = []
        for k in range(N):
            mk = np.real(P @ (v @ bases[k]))
            n_val = np.linalg.norm(mk)
            all_m.append(mk)
            all_m_hat.append(mk / n_val if n_val > 1e-12 else mk)

        for i in range(N):
            m = all_m[i]
            m_norm = np.linalg.norm(m)
            if m_norm < 1e-12:
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
                continue
            d_hat = d_vec / d_norm
            d_full = P.T @ d_hat
            m_full = P.T @ m_hat
            dL = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
            dL = skew_hermitian(dL)
            bases[i] = bases[i] @ cayley(dL)

        L_history.append(compute_L(bases))

        if t >= tail_start:
            tail_states.append(flatten_state(bases))

    # compute effective dimension via participation ratio
    states_matrix = np.array(tail_states)
    states_centered = states_matrix - states_matrix.mean(axis=0)
    cov = np.cov(states_centered.T)
    eigenvalues = np.linalg.eigvalsh(cov)
    eigenvalues = eigenvalues[eigenvalues > 1e-20]  # remove numerical zeros

    # participation ratio: (Σλ)² / Σλ²
    pr = np.sum(eigenvalues)**2 / np.sum(eigenvalues**2)
    full_dim = 2 * N * d * d  # real dimensions of U(d)^N
    lie_dim = N * d * d  # dimension of the Lie algebra u(d)^N

    return L_history, pr, full_dim, lie_dim, eigenvalues


# =====================================================================
# PROBE 3: Self-decoding — can the foam decode its own input history?
# =====================================================================

def probe_self_decoding(d, N, eps, n_steps, n_slices=1, rng_seed=42):
    """Feed structured inputs, measure how much structure is decodable.

    Use two distinct input directions. Feed a known binary sequence.
    From the final state, measure how distinguishable the two input
    populations are — from inside (one observer's measurements) vs
    from outside (full pairwise distances).
    """
    rng = np.random.default_rng(rng_seed)
    bases = [random_unitary(d, rng) for _ in range(N)]

    slices = []
    for _ in range(n_slices):
        Q = np.linalg.qr(rng.standard_normal((d, 3)))[0]
        slices.append(Q[:, :3].T)

    # two fixed input directions
    v0 = rng.standard_normal(d)
    v0 /= np.linalg.norm(v0)
    v1 = rng.standard_normal(d)
    v1 /= np.linalg.norm(v1)

    # run to saturation with random inputs first
    input_rng = np.random.default_rng(rng_seed + 1000)
    warmup = int(0.7 * n_steps)
    for t in range(warmup):
        v = input_rng.standard_normal(d)
        v /= np.linalg.norm(v)
        P = slices[t % n_slices]

        all_m = []
        all_m_hat = []
        for k in range(N):
            mk = np.real(P @ (v @ bases[k]))
            n_val = np.linalg.norm(mk)
            all_m.append(mk)
            all_m_hat.append(mk / n_val if n_val > 1e-12 else mk)

        for i in range(N):
            m = all_m[i]
            m_norm = np.linalg.norm(m)
            if m_norm < 1e-12:
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
                continue
            d_hat = d_vec / d_norm
            d_full = P.T @ d_hat
            m_full = P.T @ m_hat
            dL_val = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
            dL_val = skew_hermitian(dL_val)
            bases[i] = bases[i] @ cayley(dL_val)

    # now feed structured inputs and record measurements
    n_test = n_steps - warmup
    bits = input_rng.integers(0, 2, size=n_test)
    m_after_0 = []  # measurements after a 0-input
    m_after_1 = []  # measurements after a 1-input

    for t in range(n_test):
        v = v0 if bits[t] == 0 else v1
        P = slices[(warmup + t) % n_slices]

        all_m = []
        all_m_hat = []
        for k in range(N):
            mk = np.real(P @ (v @ bases[k]))
            n_val = np.linalg.norm(mk)
            all_m.append(mk)
            all_m_hat.append(mk / n_val if n_val > 1e-12 else mk)

        # record observer 0's measurement before write
        if bits[t] == 0:
            m_after_0.append(all_m[0].copy())
        else:
            m_after_1.append(all_m[0].copy())

        for i in range(N):
            m = all_m[i]
            m_norm = np.linalg.norm(m)
            if m_norm < 1e-12:
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
                continue
            d_hat = d_vec / d_norm
            d_full = P.T @ d_hat
            m_full = P.T @ m_hat
            dL_val = eps * d_norm * (np.outer(d_full, m_full.conj()) - np.outer(m_full, d_full.conj()))
            dL_val = skew_hermitian(dL_val)
            bases[i] = bases[i] @ cayley(dL_val)

    # measure distinguishability of 0-inputs vs 1-inputs
    # from observer 0's perspective (internal)
    mean_0 = np.mean(m_after_0, axis=0)
    mean_1 = np.mean(m_after_1, axis=0)
    separation = np.linalg.norm(mean_1 - mean_0)

    # within-class variance
    var_0 = np.mean([np.linalg.norm(m - mean_0)**2 for m in m_after_0])
    var_1 = np.mean([np.linalg.norm(m - mean_1)**2 for m in m_after_1])
    avg_var = (var_0 + var_1) / 2

    # Fisher discriminant (separation² / variance)
    fisher = separation**2 / avg_var if avg_var > 1e-15 else float('inf')

    return fisher, separation, avg_var


# =====================================================================
# RUN ALL PROBES
# =====================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("KOLMOGOROV SELF-COMPRESSION TEST (v3)")
    print("Three probes for the self-referential bound")
    print("=" * 70)
    print()

    # ── PROBE 1: Write efficiency ──
    print("PROBE 1: Write-gradient alignment")
    print("  Cosine between actual write and L-gradient direction")
    print("  If perpendicularity constrains L growth, cosine < 1")
    print("-" * 50)

    for d_val in [4, 6, 8]:
        L_h, cosines = probe_write_efficiency(d=d_val, N=3, eps=0.1, n_steps=2000)
        n = len(cosines)
        tail = int(0.7 * n)
        early_cos = np.mean(cosines[:int(0.2*n)]) if int(0.2*n) > 0 else float('nan')
        sat_cos = np.mean(cosines[tail:])
        sat_std = np.std(cosines[tail:])
        print(f"  d={d_val}, N=3:  early={early_cos:+.4f}  sat={sat_cos:+.4f} ± {sat_std:.4f}  cos²={sat_cos**2:.4f}")
    print()

    # ── PROBE 2: Effective dimension ──
    print("PROBE 2: Effective dimension of wandering at saturation")
    print("  Participation ratio / full state dimension")
    print("-" * 50)

    for d_val in [4, 6, 8]:
        L_h, pr, full_dim, lie_dim, eigs = probe_effective_dimension(
            d=d_val, N=3, eps=0.1, n_steps=3000
        )
        print(f"  d={d_val}, N=3:")
        print(f"    Full state dim:     {full_dim}")
        print(f"    Lie algebra dim:    {lie_dim}")
        print(f"    Participation ratio: {pr:.1f}")
        print(f"    PR / full_dim:      {pr/full_dim:.4f}")
        print(f"    PR / lie_dim:       {pr/lie_dim:.4f}")
        # show spectrum
        top_k = min(10, len(eigs))
        eigs_sorted = np.sort(eigs)[::-1]
        cumvar = np.cumsum(eigs_sorted) / np.sum(eigs_sorted)
        # how many components for 72% of variance?
        n_72 = np.searchsorted(cumvar, 0.72) + 1
        n_90 = np.searchsorted(cumvar, 0.90) + 1
        print(f"    Components for 72% var: {n_72} ({n_72/lie_dim:.4f} of lie dim)")
        print(f"    Components for 90% var: {n_90} ({n_90/lie_dim:.4f} of lie dim)")
    print()

    # ── PROBE 3: Self-decoding ──
    print("PROBE 3: Self-decoding (Fisher discriminant for binary inputs)")
    print("  How distinguishable are two input classes from observer's measurements?")
    print("-" * 50)

    for d_val in [4, 6, 8]:
        fisher, sep, var = probe_self_decoding(
            d=d_val, N=3, eps=0.1, n_steps=3000
        )
        print(f"  d={d_val}, N=3:  Fisher={fisher:.4f}  separation={sep:.4f}  variance={var:.4f}")
    print()

    print("=" * 70)
    print("LOOKING FOR 0.72 (or its complement 0.28) IN ANY PROBE")
    print("=" * 70)
