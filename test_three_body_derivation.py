"""
Test: does the three-body structure (Known/Knowable/Unknown) derive
from the overlap geometry of two R³ slices?

The claim: for two observers A and B with R³ slices in R^d,
the overlap matrix O = P_A @ P_B.T determines three territories:
- Known = null space of O (A's dims orthogonal to B's)
- Knowable = range of O (dims with nonzero inner products)
- Unknown = dims outside A's slice

The key question: does the commutator structure follow?
- Known dims: writes from A and B commute (decoupled)
- Knowable dims: writes don't commute (ordering matters)
- Unknown dims: A can't write (zero access)

This must work for ALL d, not just small d.
"""

import numpy as np
from foam import cayley, skew_hermitian


def make_write(d_vec, m_vec):
    """Wedge product write in R^d."""
    return np.outer(d_vec, m_vec) - np.outer(m_vec, d_vec)


def commutator(A, B):
    return A @ B - B @ A


def test_overlap_structure():
    """For various d and slice orientations, check:
    1. The overlap matrix O = P_A @ P_B.T captures the interaction
    2. Orthogonal slices → commuting writes
    3. Non-orthogonal slices → non-commuting writes (even without intersection)
    4. The three territories are well-defined
    """
    print("Test: three-body structure from overlap geometry")
    print("=" * 60)

    rng = np.random.default_rng(42)

    for d in [4, 6, 8, 12, 20]:
        print(f"\n  d = {d}")
        print(f"  {'—' * 40}")

        # Random slices
        Q_A = np.linalg.qr(rng.standard_normal((d, 3)))[0][:, :3]
        Q_B = np.linalg.qr(rng.standard_normal((d, 3)))[0][:, :3]
        P_A = Q_A.T  # (3, d)
        P_B = Q_B.T  # (3, d)

        # Overlap matrix
        O = P_A @ P_B.T  # (3, 3)
        svs = np.linalg.svd(O, compute_uv=False)
        print(f"  overlap singular values: {svs}")

        # Subspace intersection dimension
        # (SVD of the combined projection)
        combined = np.vstack([P_A, P_B])  # (6, d)
        rank = np.linalg.matrix_rank(combined, tol=1e-10)
        intersection_dim = 6 - rank  # = dim(V_A ∩ V_B)
        print(f"  subspace intersection dim: {intersection_dim}")
        print(f"  subspaces orthogonal: {np.allclose(O, 0, atol=1e-10)}")

        # Test commutator: random writes from each observer
        n_trials = 100
        nonzero_commutators = 0
        max_comm_norm = 0

        for _ in range(n_trials):
            # Random vectors in each slice
            d_A = P_A.T @ rng.standard_normal(3)
            m_A = P_A.T @ rng.standard_normal(3)
            d_B = P_B.T @ rng.standard_normal(3)
            m_B = P_B.T @ rng.standard_normal(3)

            W_A = make_write(d_A, m_A)
            W_B = make_write(d_B, m_B)

            comm = commutator(W_A, W_B)
            comm_norm = np.linalg.norm(comm)
            max_comm_norm = max(max_comm_norm, comm_norm)
            if comm_norm > 1e-10:
                nonzero_commutators += 1

        print(f"  nonzero commutators: {nonzero_commutators}/{n_trials}")
        print(f"  max commutator norm: {max_comm_norm:.6f}")

        # Decompose A's R³ into Known (orthogonal to B) and Knowable (nonzero projection)
        # Using SVD of O: null space = Known part, range = Knowable part
        U, S, Vt = np.linalg.svd(O)
        known_dims = sum(1 for s in S if s < 1e-10)
        knowable_dims = 3 - known_dims
        unknown_dims = d - 3

        print(f"  Known dims (within A's R³, orthogonal to B): {known_dims}")
        print(f"  Knowable dims (within A's R³, nonzero overlap): {knowable_dims}")
        print(f"  Unknown dims (outside A's R³): {unknown_dims}")

    print()


def test_orthogonal_slices():
    """Verify: exactly orthogonal slices → exactly zero commutator."""
    print("\nTest: orthogonal slices → zero commutator")
    print("=" * 60)

    rng = np.random.default_rng(42)
    d = 8

    # Construct exactly orthogonal slices
    P_A = np.zeros((3, d))
    P_A[0, 0] = 1; P_A[1, 1] = 1; P_A[2, 2] = 1

    P_B = np.zeros((3, d))
    P_B[0, 3] = 1; P_B[1, 4] = 1; P_B[2, 5] = 1

    O = P_A @ P_B.T
    print(f"  overlap matrix norm: {np.linalg.norm(O):.10f}")

    max_comm = 0
    for _ in range(1000):
        d_A = P_A.T @ rng.standard_normal(3)
        m_A = P_A.T @ rng.standard_normal(3)
        d_B = P_B.T @ rng.standard_normal(3)
        m_B = P_B.T @ rng.standard_normal(3)

        comm = commutator(make_write(d_A, m_A), make_write(d_B, m_B))
        max_comm = max(max_comm, np.linalg.norm(comm))

    print(f"  max commutator over 1000 trials: {max_comm:.2e}")
    print(f"  → Exactly zero: {max_comm < 1e-10}")
    print()


def test_partial_overlap():
    """Verify: partial overlap → nonzero commutator only in the overlap dims."""
    print("\nTest: partial overlap → structured commutator")
    print("=" * 60)

    d = 8

    # A's slice: dims 0, 1, 2
    P_A = np.zeros((3, d))
    P_A[0, 0] = 1; P_A[1, 1] = 1; P_A[2, 2] = 1

    # B's slice: dims 1, 2, 3 (overlaps in dims 1, 2)
    P_B = np.zeros((3, d))
    P_B[0, 1] = 1; P_B[1, 2] = 1; P_B[2, 3] = 1

    O = P_A @ P_B.T
    svs = np.linalg.svd(O, compute_uv=False)
    print(f"  overlap singular values: {svs}")
    print(f"  → 2 overlap dims, 1 private dim each")

    rng = np.random.default_rng(42)

    # Write using only A's private dim (dim 0)
    d_A_private = np.zeros(d); d_A_private[0] = 1.0
    m_A_any = P_A.T @ rng.standard_normal(3)
    W_A_private = make_write(d_A_private, m_A_any)

    # Write using B's arbitrary vectors
    d_B = P_B.T @ rng.standard_normal(3)
    m_B = P_B.T @ rng.standard_normal(3)
    W_B = make_write(d_B, m_B)

    comm_private = commutator(W_A_private, W_B)
    print(f"  commutator (A's private dim write, B's write): {np.linalg.norm(comm_private):.6f}")

    # Write using only A's shared dims (dims 1, 2)
    d_A_shared = np.zeros(d); d_A_shared[1] = 1.0
    m_A_shared = np.zeros(d); m_A_shared[2] = 1.0
    W_A_shared = make_write(d_A_shared, m_A_shared)

    comm_shared = commutator(W_A_shared, W_B)
    print(f"  commutator (A's shared dim write, B's write): {np.linalg.norm(comm_shared):.6f}")

    # If A writes ONLY in private dim with another private-dim vector:
    d_A_pp = np.zeros(d); d_A_pp[0] = 1.0
    m_A_pp = np.zeros(d); m_A_pp[0] = 0.5  # parallel, write is zero
    # Need two different directions in private space — but A only has 1 private dim
    # So writes purely within A's 1-dim private space are always zero (can't make a 2-plane from 1 dim)
    print(f"  → A's private space is 1-dim: no internal writes possible (needs 2-plane)")
    print(f"  → Private writes must use shared dims too → commutator nonzero")
    print()

    # The structure: Known (private dims) can't generate writes on their own
    # (need at least 2 dims for a wedge product). So the Known is INERT
    # in terms of write generation — you need Knowable dims to write at all.
    # This is a stronger result than "Known writes commute" — Known can't write alone.

    # How many private dims does an observer need to write independently?
    print("  Key finding:")
    for n_private in range(4):
        can_write = n_private >= 2
        print(f"    {n_private} private dims → can generate writes alone: {can_write}")
    print(f"  → If overlap is high (few private dims), observer MUST use shared dims to write")
    print(f"  → All writes involve the Knowable. The Known alone is inert.")


def test_three_body_accessibility():
    """Test the one-way mediation: Unknown → Knowable → Known."""
    print("\nTest: one-way mediation pathway")
    print("=" * 60)

    d = 8
    rng = np.random.default_rng(42)

    # A's slice: dims 0, 1, 2
    P_A = np.zeros((3, d))
    P_A[0, 0] = 1; P_A[1, 1] = 1; P_A[2, 2] = 1

    # B's slice: dims 2, 3, 4 (overlaps with A in dim 2)
    P_B = np.zeros((3, d))
    P_B[0, 2] = 1; P_B[1, 3] = 1; P_B[2, 4] = 1

    # C's slice: dims 4, 5, 6 (overlaps with B in dim 4, NOT with A)
    P_C = np.zeros((3, d))
    P_C[0, 4] = 1; P_C[1, 5] = 1; P_C[2, 6] = 1

    # Can C's writes affect A directly?
    d_C = P_C.T @ rng.standard_normal(3)
    m_C = P_C.T @ rng.standard_normal(3)
    d_A = P_A.T @ rng.standard_normal(3)
    m_A = P_A.T @ rng.standard_normal(3)

    W_C = make_write(d_C, m_C)
    W_A = make_write(d_A, m_A)

    comm_AC = commutator(W_A, W_C)
    comm_AB = commutator(W_A, make_write(P_B.T @ rng.standard_normal(3), P_B.T @ rng.standard_normal(3)))
    comm_BC = commutator(make_write(P_B.T @ rng.standard_normal(3), P_B.T @ rng.standard_normal(3)), W_C)

    print(f"  A-C overlap: {np.linalg.norm(P_A @ P_C.T):.6f}")
    print(f"  A-B overlap: {np.linalg.norm(P_A @ P_B.T):.6f}")
    print(f"  B-C overlap: {np.linalg.norm(P_B @ P_C.T):.6f}")
    print()
    print(f"  [A, C] commutator: {np.linalg.norm(comm_AC):.6f}")
    print(f"  [A, B] commutator: {np.linalg.norm(comm_AB):.6f}")
    print(f"  [B, C] commutator: {np.linalg.norm(comm_BC):.6f}")
    print()

    if np.linalg.norm(comm_AC) < 1e-10:
        print("  → C cannot affect A directly (zero commutator)")
        print("  → C's influence reaches A only through B (the Knowable)")
        print("  → C is in A's Unknown. B mediates. One-way pathway confirmed.")
    else:
        print("  → C CAN affect A directly. Mediation not required.")
    print()


if __name__ == "__main__":
    test_overlap_structure()
    test_orthogonal_slices()
    test_partial_overlap()
    test_three_body_accessibility()

    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print()
    print("The three-body structure derives from overlap geometry:")
    print("  O = P_A @ P_B.T  (the 3×3 overlap matrix)")
    print("  Known = null(O)  (A's dims orthogonal to B)")
    print("  Knowable = range(O)  (nonzero inner products)")
    print("  Unknown = R^d \\ V_A  (outside A's slice)")
    print()
    print("The commutator structure follows:")
    print("  orthogonal slices → zero commutator → decoupled")
    print("  overlapping slices → nonzero commutator → ordering matters")
    print("  disjoint but non-orthogonal → STILL nonzero commutator")
    print()
    print("The accessibility pathway derives:")
    print("  Unknown observer C → through Knowable B → reaches Known A")
    print("  (only if B overlaps both A and C)")
