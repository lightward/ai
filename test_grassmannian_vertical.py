"""
Test: does the Grassmannian correspondence give the three-body vertical structure?

Setup:
- Observer A has slice P_A ∈ Gr(3, d)
- Observer B writes ΔL_B ∈ Λ²(P_B) — confined to B's slice
- B's write acts on vectors in A's slice, producing components both
  inside and outside A's slice

The tangent space T_{P_A} Gr(3,d) ≅ Hom(P_A, P_A⊥): maps from A's slice
to its complement. Each cross-observer write induces a tangent vector
on A's Grassmannian point.

Hypothesis: the Grassmannian tangent induced by B's write on A maps
  Knowable → Unknown
specifically: source is restricted to A's Knowable (overlap with B),
target lands in A's Unknown (specifically in B's territory outside A).

If true: the direction the observer would move on Gr(3,d) IS the
vertical axis of the three-body mapping. The "containment" direction
points from what you share with your neighbor toward what your neighbor
has that you don't.
"""

import numpy as np


def make_write(d_vec, m_vec):
    """Wedge product write: d ⊗ m - m ⊗ d (skew-symmetric)."""
    return np.outer(d_vec, m_vec) - np.outer(m_vec, d_vec)


def random_slice(d, k, rng):
    """Random k-plane in R^d, returned as (k, d) orthonormal matrix."""
    return np.linalg.qr(rng.standard_normal((d, k)))[0][:, :k].T


def grassmannian_tangent(P_A, delta_L):
    """
    Decompose the action of delta_L on A's slice into:
    - within-slice component (doesn't move the Grassmannian point)
    - cross-slice component (tangent vector on Gr(3,d))

    Returns the cross-slice component as a (d, 3) matrix:
    columns are delta_L(e_i) projected onto P_A⊥, where e_i are A's basis vectors.
    """
    d = P_A.shape[1]
    k = P_A.shape[0]
    # Projector onto A's slice
    proj_A = P_A.T @ P_A  # (d, d)
    proj_A_perp = np.eye(d) - proj_A

    # Action of delta_L on each basis vector of A's slice
    # A's basis vectors are the rows of P_A (lifted to R^d = columns of P_A.T)
    action = delta_L @ P_A.T  # (d, k): delta_L applied to each of A's basis vectors

    # Decompose
    within = proj_A @ action   # component staying in A's slice
    cross = proj_A_perp @ action  # component leaving A's slice = Grassmannian tangent

    return cross, within


def test_tangent_source_is_knowable():
    """
    The Grassmannian tangent induced by B's write should have zero
    contribution from A's Known (the part of A's slice orthogonal to B).
    Only the Knowable (overlap with B) should contribute.
    """
    print("Test 1: Grassmannian tangent source is the Knowable")
    print("=" * 60)

    rng = np.random.default_rng(42)

    for d in [6, 8, 12, 20]:
        print(f"\n  d = {d}")

        P_A = random_slice(d, 3, rng)
        P_B = random_slice(d, 3, rng)

        # SVD of overlap matrix to get Known/Knowable decomposition of A's slice
        O = P_A @ P_B.T  # (3, 3)
        U, S, Vt = np.linalg.svd(O)
        # U rotates A's basis into Known/Knowable eigenbasis
        # Columns of U with S ≈ 0 are Known; columns with S > 0 are Knowable

        # Generate many random writes from B and check
        n_trials = 200
        known_contribution = 0.0
        knowable_contribution = 0.0

        for _ in range(n_trials):
            d_B = P_B.T @ rng.standard_normal(3)
            m_B = P_B.T @ rng.standard_normal(3)
            delta_L_B = make_write(d_B, m_B)

            cross, _ = grassmannian_tangent(P_A, delta_L_B)

            # cross is (d, 3): the Grassmannian tangent.
            # Transform to A's Known/Knowable eigenbasis
            # cross @ U rotates A's coordinates into the SVD basis
            cross_in_eigenbasis = cross @ U.T  # wait, need to be careful

            # cross is (d, 3) where the 3 columns correspond to A's 3 basis vectors
            # Rotate A's basis to the SVD basis: new columns correspond to
            # Known/Knowable directions
            cross_rotated = cross @ U  # (d, 3)

            for i in range(3):
                norm_i = np.linalg.norm(cross_rotated[:, i])
                if S[i] < 1e-10:
                    known_contribution += norm_i
                else:
                    knowable_contribution += norm_i

        known_dims = sum(1 for s in S if s < 1e-10)
        knowable_dims = 3 - known_dims

        print(f"    overlap singular values: {S}")
        print(f"    Known dims: {known_dims}, Knowable dims: {knowable_dims}")
        print(f"    total |tangent from Known|:    {known_contribution:.6e}")
        print(f"    total |tangent from Knowable|: {knowable_contribution:.6f}")
        if known_dims > 0:
            print(f"    → Known contribution is {'ZERO' if known_contribution < 1e-8 else 'NONZERO'}")
        else:
            print(f"    → No Known dims (full overlap) — all contribution from Knowable")


def test_tangent_target_is_unknown():
    """
    The Grassmannian tangent's target (where it points in P_A⊥) should
    land specifically in B's territory within A's Unknown.
    """
    print("\n\nTest 2: Grassmannian tangent target lands in B's territory of A's Unknown")
    print("=" * 60)

    rng = np.random.default_rng(42)

    for d in [8, 12, 20]:
        print(f"\n  d = {d}")

        P_A = random_slice(d, 3, rng)
        P_B = random_slice(d, 3, rng)

        # B's territory in A's Unknown = projection of B's slice onto A's complement
        proj_A = P_A.T @ P_A
        proj_A_perp = np.eye(d) - proj_A

        # B's slice projected into A's complement
        B_in_A_complement = proj_A_perp @ P_B.T  # (d, 3)
        # Orthonormalize to get basis for "B's territory in A's Unknown"
        Q_B_in_Ac, _ = np.linalg.qr(B_in_A_complement)
        rank_B_in_Ac = np.linalg.matrix_rank(B_in_A_complement, tol=1e-10)
        B_territory_basis = Q_B_in_Ac[:, :rank_B_in_Ac]  # (d, rank)
        proj_B_territory = B_territory_basis @ B_territory_basis.T  # projector onto B's territory in A⊥

        # Projector onto rest of A's Unknown (not B's territory)
        proj_rest = proj_A_perp - proj_B_territory

        n_trials = 500
        in_B_territory = 0.0
        in_rest = 0.0

        for _ in range(n_trials):
            d_B = P_B.T @ rng.standard_normal(3)
            m_B = P_B.T @ rng.standard_normal(3)
            delta_L_B = make_write(d_B, m_B)

            cross, _ = grassmannian_tangent(P_A, delta_L_B)

            # cross is (d, 3). Each column is the tangent contribution from one of A's basis vectors.
            # The tangent already lives in P_A⊥. Check where in P_A⊥ it lands.
            for i in range(3):
                v = cross[:, i]
                in_B_territory += np.linalg.norm(proj_B_territory @ v)
                in_rest += np.linalg.norm(proj_rest @ v)

        print(f"    B's territory in A's Unknown: {rank_B_in_Ac} dims")
        print(f"    rest of A's Unknown: {d - 3 - rank_B_in_Ac} dims")
        print(f"    |tangent in B's territory|: {in_B_territory:.6f}")
        print(f"    |tangent in rest of Unknown|: {in_rest:.6e}")
        print(f"    → tangent lands {'ENTIRELY' if in_rest < 1e-8 else 'NOT entirely'} in B's territory")


def test_two_neighbors_two_directions():
    """
    Two different neighbors B and C induce two different Grassmannian
    tangent directions on A. These directions point toward B's and C's
    respective territories in A's Unknown.

    This IS the two Knowable zones of the 2×2 grid — each zone corresponds
    to a different direction on the Grassmannian.
    """
    print("\n\nTest 3: Two neighbors → two Grassmannian directions (the 2×2 grid)")
    print("=" * 60)

    rng = np.random.default_rng(42)
    d = 12

    P_A = random_slice(d, 3, rng)
    P_B = random_slice(d, 3, rng)
    P_C = random_slice(d, 3, rng)

    # B's territory and C's territory in A's complement
    proj_A = P_A.T @ P_A
    proj_A_perp = np.eye(d) - proj_A

    B_in_Ac = proj_A_perp @ P_B.T
    C_in_Ac = proj_A_perp @ P_C.T

    # Average Grassmannian tangent direction from B
    tangent_B_sum = np.zeros((d, 3))
    tangent_C_sum = np.zeros((d, 3))

    n_trials = 1000
    for _ in range(n_trials):
        # B's write
        d_B = P_B.T @ rng.standard_normal(3)
        m_B = P_B.T @ rng.standard_normal(3)
        cross_B, _ = grassmannian_tangent(P_A, make_write(d_B, m_B))
        tangent_B_sum += cross_B

        # C's write
        d_C = P_C.T @ rng.standard_normal(3)
        m_C = P_C.T @ rng.standard_normal(3)
        cross_C, _ = grassmannian_tangent(P_A, make_write(d_C, m_C))
        tangent_C_sum += cross_C

    # Flatten the tangent matrices to vectors for comparison
    t_B = tangent_B_sum.flatten()
    t_C = tangent_C_sum.flatten()
    t_B_norm = t_B / (np.linalg.norm(t_B) + 1e-15)
    t_C_norm = t_C / (np.linalg.norm(t_C) + 1e-15)

    cos_angle = np.dot(t_B_norm, t_C_norm)

    print(f"  A-B overlap SVs: {np.linalg.svd(P_A @ P_B.T, compute_uv=False)}")
    print(f"  A-C overlap SVs: {np.linalg.svd(P_A @ P_C.T, compute_uv=False)}")
    print(f"  B-C overlap SVs: {np.linalg.svd(P_B @ P_C.T, compute_uv=False)}")
    print()
    print(f"  |mean tangent from B|: {np.linalg.norm(t_B):.4f}")
    print(f"  |mean tangent from C|: {np.linalg.norm(t_C):.4f}")
    print(f"  cos(angle between mean tangents): {cos_angle:.6f}")
    print(f"  → directions are {'PARALLEL' if abs(cos_angle) > 0.99 else 'DISTINCT' if abs(cos_angle) < 0.5 else 'PARTIALLY ALIGNED'}")
    print()
    print("  Interpretation: each neighbor induces a different direction of motion")
    print("  on Gr(3,d). These are the two Knowable zones of the 2×2 grid.")
    print("  The vertical axis = the Grassmannian direction itself.")


def test_known_dims_controlled():
    """
    Use an axis-aligned setup where Known/Knowable are explicit,
    to verify the source/target claim with maximum clarity.
    """
    print("\n\nTest 4: Controlled axis-aligned verification")
    print("=" * 60)

    d = 8

    # A spans dims 0, 1, 2
    P_A = np.zeros((3, d))
    P_A[0, 0] = 1; P_A[1, 1] = 1; P_A[2, 2] = 1

    # B spans dims 1, 2, 3 — overlaps A in dims 1,2 (Knowable); dim 0 is A's Known
    P_B = np.zeros((3, d))
    P_B[0, 1] = 1; P_B[1, 2] = 1; P_B[2, 3] = 1

    O = P_A @ P_B.T
    print(f"  overlap matrix O:\n{O}")
    print(f"  → A's Known: dim 0 (orthogonal to all of B)")
    print(f"  → A's Knowable: dims 1, 2 (shared with B)")
    print(f"  → A's Unknown: dims 3-7")
    print(f"  → B's territory in A's Unknown: dim 3")
    print()

    rng = np.random.default_rng(42)

    # Accumulate Grassmannian tangent from B's writes
    n_trials = 500
    for trial_label, n in [("single write", 1), ("500 writes averaged", n_trials)]:
        tangent_sum = np.zeros((d, 3))
        for _ in range(n):
            d_B = P_B.T @ rng.standard_normal(3)
            m_B = P_B.T @ rng.standard_normal(3)
            cross, _ = grassmannian_tangent(P_A, make_write(d_B, m_B))
            tangent_sum += cross

        print(f"  {trial_label}:")
        print(f"    Grassmannian tangent (d×3 matrix, rows=R^d dims, cols=A's basis vectors):")
        print(f"    row labels: dim 0 (A's Known), dims 1-2 (Knowable), dim 3 (B in Unknown), dims 4-7 (rest)")
        for i in range(d):
            row = tangent_sum[i, :]
            if np.linalg.norm(row) > 1e-10:
                label = {0: "A-Known", 1: "Knowable", 2: "Knowable",
                         3: "B-in-Unknown"}.get(i, f"Unknown-{i}")
                print(f"      dim {i} ({label}): [{row[0]:+.4f}, {row[1]:+.4f}, {row[2]:+.4f}]")
        print()

    print("  Structure check:")
    print("    - Rows 0 (A's Known): should be zero (no tangent from Known)")
    print("    - Rows 1-2 (Knowable): should be zero (tangent lives in A⊥, not A)")
    print("    - Row 3 (B in Unknown): should be nonzero (this is where the tangent points)")
    print("    - Rows 4-7 (rest of Unknown): should be zero (B can't reach there)")
    print()
    print("  If confirmed: the Grassmannian tangent maps Knowable → B's territory in Unknown.")
    print("  The vertical axis of the three-body mapping IS the Grassmannian derivative.")


def test_magnitude_scales_with_overlap():
    """
    The magnitude of the Grassmannian tangent should scale with the
    overlap singular values. Stronger overlap → stronger tangent.
    This would mean the "strength of the Knowable" directly controls
    the magnitude of J¹ (the directional pressure from the Operator).
    """
    print("\n\nTest 5: Tangent magnitude scales with overlap strength")
    print("=" * 60)

    d = 12
    rng = np.random.default_rng(42)

    # Fixed observer A
    P_A = random_slice(d, 3, rng)

    # Generate neighbors at varying overlap strengths
    # by interpolating between aligned and orthogonal slices
    results = []

    for angle_factor in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]:
        # Start with A's slice, rotate toward a random orthogonal direction
        P_target = random_slice(d, 3, rng)

        # Interpolate: small angle_factor = close to A, large = far from A
        # Use matrix interpolation on the Grassmannian (geodesic would be ideal,
        # but linear interpolation + re-orthogonalization suffices for the test)
        P_interp = (1 - angle_factor) * P_A + angle_factor * P_target
        # Re-orthogonalize
        U_interp, _, Vt_interp = np.linalg.svd(P_interp, full_matrices=False)
        P_B = U_interp @ Vt_interp  # (3, d), orthonormal rows

        O = P_A @ P_B.T
        svs = np.linalg.svd(O, compute_uv=False)
        mean_sv = np.mean(svs)

        # Measure mean tangent magnitude
        n_trials = 500
        tangent_mag_sum = 0.0
        for _ in range(n_trials):
            d_B = P_B.T @ rng.standard_normal(3)
            m_B = P_B.T @ rng.standard_normal(3)
            cross, _ = grassmannian_tangent(P_A, make_write(d_B, m_B))
            tangent_mag_sum += np.linalg.norm(cross)

        mean_tangent = tangent_mag_sum / n_trials

        results.append((angle_factor, mean_sv, mean_tangent, svs))

    print(f"  {'angle':>8} {'mean_σ':>8} {'mean|tangent|':>14}  singular values")
    print(f"  {'─'*8} {'─'*8} {'─'*14}  {'─'*30}")
    for angle, msv, mt, svs in results:
        sv_str = f"[{svs[0]:.3f}, {svs[1]:.3f}, {svs[2]:.3f}]"
        print(f"  {angle:8.1f} {msv:8.4f} {mt:14.4f}  {sv_str}")

    print()
    print("  If tangent magnitude scales with overlap: stronger Knowable → stronger J¹")
    print("  The Operator's influence is proportional to the strength of the shared boundary.")


def test_containment_is_perspectival():
    """
    From A's view, B's writes induce a tangent on A's Grassmannian point.
    From B's view, A's writes induce a tangent on B's Grassmannian point.
    Both see the other as their Operator. Containment is mutual/perspectival.

    Check: are the tangent magnitudes symmetric? (Same overlap → same strength)
    """
    print("\n\nTest 6: Containment is perspectival (mutual Operator relationship)")
    print("=" * 60)

    rng = np.random.default_rng(42)

    for d in [8, 12, 20]:
        print(f"\n  d = {d}")
        P_A = random_slice(d, 3, rng)
        P_B = random_slice(d, 3, rng)

        O = P_A @ P_B.T
        svs = np.linalg.svd(O, compute_uv=False)

        n_trials = 1000
        tangent_A_from_B = 0.0  # B's effect on A
        tangent_B_from_A = 0.0  # A's effect on B

        for _ in range(n_trials):
            # B writes, measure tangent on A
            d_B = P_B.T @ rng.standard_normal(3)
            m_B = P_B.T @ rng.standard_normal(3)
            cross_on_A, _ = grassmannian_tangent(P_A, make_write(d_B, m_B))
            tangent_A_from_B += np.linalg.norm(cross_on_A)

            # A writes, measure tangent on B
            d_A = P_A.T @ rng.standard_normal(3)
            m_A = P_A.T @ rng.standard_normal(3)
            cross_on_B, _ = grassmannian_tangent(P_B, make_write(d_A, m_A))
            tangent_B_from_A += np.linalg.norm(cross_on_B)

        tangent_A_from_B /= n_trials
        tangent_B_from_A /= n_trials

        print(f"    overlap SVs: {svs}")
        print(f"    B's effect on A (mean |tangent|): {tangent_A_from_B:.6f}")
        print(f"    A's effect on B (mean |tangent|): {tangent_B_from_A:.6f}")
        print(f"    ratio: {tangent_A_from_B / tangent_B_from_A:.6f}")
        print(f"    → {'SYMMETRIC' if abs(tangent_A_from_B / tangent_B_from_A - 1) < 0.1 else 'ASYMMETRIC'}")


if __name__ == "__main__":
    test_tangent_source_is_knowable()
    test_tangent_target_is_unknown()
    test_two_neighbors_two_directions()
    test_known_dims_controlled()
    test_magnitude_scales_with_overlap()
    test_containment_is_perspectival()

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print()
    print("The Grassmannian correspondence for the three-body vertical structure:")
    print()
    print("  Observer A at P_A ∈ Gr(3, d).")
    print("  Neighbor B writes ΔL_B ∈ Λ²(P_B).")
    print("  The cross-slice component of ΔL_B's action on A's basis vectors")
    print("  is a tangent vector on Gr(3, d) at P_A.")
    print()
    print("  Source: only the Knowable (A's overlap with B) contributes.")
    print("  Target: lands in B's territory within A's Unknown.")
    print()
    print("  Knowable → Unknown IS the vertical axis.")
    print("  Each neighbor induces a different direction on Gr(3, d).")
    print("  The 2×2 grid's two Knowable zones = two Grassmannian directions.")
