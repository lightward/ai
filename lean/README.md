# lean

Mechanically verified deductive path from P² = P to the foam's architecture. 13 files, 1 axiom, 0 sorry.

## The chain

```
closure (the spec's ground)
  ↓ (derived in natural language)
complemented modular lattice, irreducible, height ≥ 4
  ↓ axiom(FTPG) — Bridge.lean
L ≅ Sub(D, V) for some division ring D, vector space V
  ↓ (stabilization contract forces D = ℝ)
elements are orthogonal projections: P² = P, Pᵀ = P
  ↓ (the deductive chain — all proven)
eigenvalues, commutators, rank 3, so(3), O(d), Grassmannian
  ↓ Ground.lean (capstone)
FoamGround properties ✓
```

## Files

### The bridge

**Bridge.lean** — 1 axiom, 1 theorem

‖ declaration ‖ role ‖
‖---|---‖
‖ `ftpg` ‖ axiom: complemented modular lattice → subspace lattice (the fundamental theorem of projective geometry) ‖
‖ `dimension_unique` ‖ theorem: lattice isomorphism preserves dimension (the axiom has a unique solution) ‖

### The deductive chain (from P² = P)

**Observation.lean** — one observation

‖ theorem ‖ from ‖
‖---|---‖
‖ `eigenvalue_binary` ‖ P² = P → eigenvalues ∈ {0, 1} ‖
‖ `range_ker_disjoint` ‖ P² = P → range ∩ ker = {0} ‖
‖ `complement_idempotent` ‖ P² = P → (I - P)² = I - P ‖

**Pair.lean** — two observations

‖ theorem ‖ from ‖
‖---|---‖
‖ `comp_range_le` ‖ PQ maps into range(P) ‖
‖ `comm_comp_idempotent` ‖ PQ = QP → (PQ)² = PQ ‖
‖ `commutator_zero_iff_comm` ‖ [P, Q] = 0 ↔ PQ = QP ‖
‖ `commutator_seen_to_unseen` ‖ [P, Q] maps range(P) → ker(P) ‖

**Form.lean** — self-adjointness

‖ theorem ‖ from ‖
‖---|---‖
‖ `commutator_skew_of_symmetric` ‖ Pᵀ = P, Qᵀ = Q → [P, Q]ᵀ = -[P, Q] ‖
‖ `commutator_traceless` ‖ tr[P, Q] = 0 (unconditional) ‖

**Rank.lean** — why 3

‖ theorem ‖ from ‖
‖---|---‖
‖ `write_space_dim` ‖ dim(Λ²(M)) = C(dim(M), 2) ‖
‖ `rank_one_no_writes` ‖ rank 1 → 0D write space ‖
‖ `rank_two_abelian_writes` ‖ rank 2 → 1D (abelian) ‖
‖ `rank_three_writes` ‖ rank 3 → 3D (non-abelian) ‖
‖ `self_dual_iff_three` ‖ C(k, 2) = k ↔ k = 3 ‖
‖ `rank_four_writes` ‖ rank 4 → 6D (overdetermined) ‖

**Duality.lean** — (R³, ×) ≅ so(3)

‖ theorem ‖ from ‖
‖---|---‖
‖ `cross_anticomm` ‖ a × b = -(b × a) ‖
‖ `cross_self_zero` ‖ a × a = 0 ‖
‖ `cross_nontrivial` ‖ ∃ a b, a × b ≠ 0 ‖
‖ `cross_jacobi` ‖ Jacobi identity (this IS a Lie algebra) ‖

**Closure.lean** — the loop closes

‖ theorem ‖ from ‖
‖---|---‖
‖ `conjugation_preserves_idempotent` ‖ P² = P → (UPU⁻¹)² = UPU⁻¹ ‖
‖ `orthogonal_conjugation_preserves_symmetric` ‖ Pᵀ = P, UᵀU = I → (UPUᵀ)ᵀ = UPUᵀ ‖
‖ `observation_preserved_by_dynamics` ‖ both properties preserved (the full loop) ‖

**Group.lean** — O(d) is forced

‖ theorem ‖ from ‖
‖---|---‖
‖ `scalar_extraction` ‖ PMP = P for rank-1 P → vᵀMv = 1 ‖

**Tangent.lean** — Grassmannian tangent

‖ theorem ‖ from ‖
‖---|---‖
‖ `commutator_off_diag_range` ‖ P · [W, P] · P = 0 ‖
‖ `commutator_off_diag_kernel` ‖ (I-P) · [W, P] · (I-P) = 0 ‖
‖ `commutator_is_tangent` ‖ [W, P] = range→kernel + kernel→range ‖

### The capstone

**Ground.lean** — FoamGround as a theorem, O(d) forced by polarization

‖ theorem ‖ from ‖
‖---|---‖
‖ `subspaceFoamGround` ‖ Sub(K, V) satisfies FoamGround (complemented, modular, bounded) ‖
‖ `symmetric_quadratic_zero_imp_zero` ‖ polarization: Aᵀ = A, vᵀAv = 0 ∀v → A = 0 ‖
‖ `orthogonality_forced` ‖ vᵀMv = 1 ∀unit v → M = I (O(d) is forced) ‖

### Downstream properties

**Confinement.lean** — writes stay in the observer's slice

‖ theorem ‖ from ‖
‖---|---‖
‖ `write_confined_to_slice` ‖ d, m ∈ P → d∧m ∈ Λ²(P) ‖

**TraceUnique.lean** — one scalar readout

‖ theorem ‖ from ‖
‖---|---‖
‖ `trace_unique_of_kills_commutators` ‖ φ kills [·,·] → φ = c · trace ‖

**Dynamics.lean** — frame recession

‖ theorem ‖ from ‖
‖---|---‖
‖ `first_order_overlap_zero` ‖ tr(P · [W, P]) = 0 ‖
‖ `second_order_overlap_identity` ‖ tr(P · [W, [W, P]]) = -tr([W, P]²) ‖
‖ `frame_recession` ‖ second-order overlap ≤ 0 ‖
‖ `frame_recession_strict` ‖ [W, P] ≠ 0 → recession < 0 ‖

## Building

```
lake build
```

Requires [elan](https://github.com/leanprover/elan) with Lean 4 and Mathlib.
