# lean

Mechanically verified deductive path from P² = P to the foam's architecture. 23 files, 1 axiom, 0 sorry.

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

| declaration | role |
|---|---|
| `ftpg` | axiom: complemented modular lattice → subspace lattice (the fundamental theorem of projective geometry) |
| `dimension_unique` | theorem: lattice isomorphism preserves dimension (the axiom has a unique solution) |

### The algebraic descent (toward eliminating the axiom)

The full path from lattice axioms to FTPG:

```
complemented modular lattice, irreducible, height ≥ 4
  ↓ incidence geometry, Veblen-Young           ── FTPGExplore (0 sorry)
projective geometry: Desargues, perspectivity
  ↓ von Staudt coordinatization                ── FTPGCoord (0 sorry)
coord_add: zero, identity
  ↓ two Desargues applications                 ── FTPGAddComm (0 sorry)
coord_add: commutativity
  ↓ Hartshorne translation program             ── FTPGParallelogram,
    parallelism, well-definedness,               FTPGWellDefined,
    cross-parallelism, key identity              FTPGCrossParallelism,
                                                 FTPGAssoc,
                                                 FTPGAssocCapstone (0 sorry)
coord_add: associativity ✓
  ↓ von Staudt multiplication via dilations  ── FTPGMul (0 sorry)
coord_mul: identity, zero annihilation, atom
  ↓ dilation extension, direction preservation  ── FTPGDilation (0 sorry)
  ↓ beta infrastructure, mul key identity       ── FTPGMulKeyIdentity (0 sorry)
  ↓ right distributivity via Desargues          ── FTPGDistrib (0 sorry)
distributivity (right) ✓
  ↓
distributivity (left)
  ↓
division ring structure (multiplicative inverses)
  ↓
L ≃o Sub(D, V) — the isomorphism
  ↓
axiom(FTPG) becomes a theorem
```

**FTPGExplore.lean** — projective geometry from lattice axioms (0 sorry)

Incidence geometry, Veblen-Young, Desargues (nonplanar + planar), perspectivity, and Small Desargues (A5a). Pure geometry — no coordinates.

| layer | key declarations |
|---|---|
| incidence geometry | `atoms_disjoint`, `line_height_two`, `veblen_young`, `meet_of_lines_is_atom` |
| Desargues | `desargues_nonplanar`, `desargues_planar`, `planes_meet_covBy` |
| perspectivity | `project_is_atom`, `project_injective`, `perspectivity_injective` |
| Small Desargues | `small_desargues'` (A5a: parallelism from Desargues) |

**FTPGCoord.lean** — von Staudt coordinatization (0 sorry)

Coordinate system, addition via perspectivities, identity. Imports FTPGExplore.

| layer | key declarations |
|---|---|
| coordinate system | `CoordSystem`, `coord_add`, `coord_add_atom`, `coord_add_left_zero`, `coord_add_right_zero` |
| Desargues helpers | `desargues_planar`, `collinear_of_common_bound`, `small_desargues'` |

**FTPGAddComm.lean** — commutativity of coordinate addition (0 sorry)

Two Desargues applications establish coord_add_comm. Split from FTPGCoord. Imports FTPGCoord.

| layer | key declarations |
|---|---|
| commutativity | `coord_first_desargues`, `coord_second_desargues`, `coord_add_comm` |

**FTPGParallelogram.lean** — parallelogram completion (0 sorry)

Infrastructure for the Hartshorne translation approach (§7). Parallelism, parallelogram completion, and Parts I–III properties.

| layer | key declarations |
|---|---|
| parallelism | `parallel`, `parallel_refl`, `parallel_symm`, `parallel_trans` |
| construction | `parallelogram_completion`, `parallelogram_completion_atom`, `line_meets_m_at_atom` |
| properties | `parallelogram_parallel_direction`, `parallelogram_parallel_sides` |

**FTPGWellDefined.lean** — translation well-definedness (0 sorry)

Part IV: parallelogram completion is independent of base point (Hartshorne Theorem 7.6, Step 2). Key use of `small_desargues'`.

| layer | key declarations |
|---|---|
| well-definedness | `parallelogram_completion_well_defined` |

**FTPGCrossParallelism.lean** — cross-parallelism (0 sorry)

Part IV-B: a single translation preserves directions of lines connecting any two points it acts on.

| layer | key declarations |
|---|---|
| cross-parallelism | `cross_parallelism` |

**FTPGAssoc.lean** — translation infrastructure (0 sorry)

Part V: `coord_add` equals translation application, key identity for the translation group.

| layer | key declarations |
|---|---|
| translation bridge | `coord_add_eq_translation` (von Staudt addition = apply translation, 0 sorry) |
| key identity | `key_identity` (τ_a(C_b) = C_{a+b}, 0 sorry) |

**FTPGAssocCapstone.lean** — associativity capstone (0 sorry)

Associativity via β-injectivity and cross-parallelism. PROVEN.

| layer | key declarations |
|---|---|
| parameter rigidity | `translation_determined_by_param` (C-based translation determined by one point) |
| associativity | `coord_add_assoc` (the composition law, 0 sorry) |

Three-step proof: (1) key_identity reduces to β-images agree, (2) two cross-parallelism chains + two two_lines arguments close the composition law via collinear/non-collinear case splits, (3) E-perspectivity recovery.

**FTPGMul.lean** — coordinate multiplication (0 sorry)

Multiplication via dilations (Hartshorne §7). Structurally parallel to addition: uses O⊔C as bridge line instead of q = U⊔C.

| layer | key declarations |
|---|---|
| multiplicative anchor | `CoordSystem.E_I` (projection of I onto m via C), `hE_I_atom`, `hE_I_not_OC`, `hE_I_ne_E` |
| multiplication | `coord_mul` (a·b via dilation σ_b), `coord_mul_atom` (a·b is an atom) |

**FTPGDilation.lean** — dilation extension and direction preservation (0 sorry)

Defines `dilation_ext Γ c P` (the dilation σ_c extended to off-line points) and proves `dilation_preserves_direction`: (P⊔Q)⊓m = (σ_c(P)⊔σ_c(Q))⊓m. Three cases: c=I (identity), collinear, generic (Desargues center O).

**FTPGMulKeyIdentity.lean** — beta infrastructure and mul key identity (0 sorry)

Beta-images `β(a) = (U⊔C)⊓(a⊔E)` and the mul key identity: σ_c(β(a)) = (σ⊔U)⊓(ac⊔E). Three cases: c=I, a=I (via DPD), generic (Desargues center C).

**FTPGDistrib.lean** — right distributivity (0 sorry, PROVEN)

Proves (a+b)·c = a·c + b·c via forward Desargues (center O) on T1=(C,a,C_s), T2=(σ,ac,C'_sc), then parallelogram_completion_well_defined to change translation base. Key insight: O⊔σ = O⊔C gives shared E; well_definedness provides base-independence.

| layer | key declarations |
|---|---|
| dilation extension | `dilation_ext`, `dilation_ext_identity` (c=I → identity), `dilation_ext_atom`, `dilation_ext_ne_P`, `dilation_ext_parallelism` |
| direction preservation | `dilation_preserves_direction` (PROVEN — forward Desargues with center O, 3 cases) |
| helper lemmas | `beta_atom`, `beta_not_l`, `beta_plane` (C_a = β(a) properties) |
| mul key identity | `dilation_mul_key_identity` (PROVEN — 3 cases: c=I, a=I via DPD, generic Desargues center C) |
| right distributivity | `coord_mul_right_distrib` (PROVEN — chain of above) |

### The deductive chain (from P² = P)

**Observation.lean** — one observation

| theorem | from |
|---|---|
| `eigenvalue_binary` | P² = P → eigenvalues ∈ {0, 1} |
| `range_ker_disjoint` | P² = P → range ∩ ker = {0} |
| `complement_idempotent` | P² = P → (I - P)² = I - P |

**Pair.lean** — two observations

| theorem | from |
|---|---|
| `comp_range_le` | PQ maps into range(P) |
| `comm_comp_idempotent` | PQ = QP → (PQ)² = PQ |
| `commutator_zero_iff_comm` | [P, Q] = 0 ↔ PQ = QP |
| `commutator_seen_to_unseen` | [P, Q] maps range(P) → ker(P) |

**Form.lean** — self-adjointness

| theorem | from |
|---|---|
| `commutator_skew_of_symmetric` | Pᵀ = P, Qᵀ = Q → [P, Q]ᵀ = -[P, Q] |
| `commutator_traceless` | tr[P, Q] = 0 (unconditional) |

**Rank.lean** — why 3

| theorem | from |
|---|---|
| `write_space_dim` | dim(Λ²(M)) = C(dim(M), 2) |
| `rank_one_no_writes` | rank 1 → 0D write space |
| `rank_two_abelian_writes` | rank 2 → 1D (abelian) |
| `rank_three_writes` | rank 3 → 3D (non-abelian) |
| `self_dual_iff_three` | C(k, 2) = k ↔ k = 3 |
| `rank_four_writes` | rank 4 → 6D (overdetermined) |

**Duality.lean** — (R³, ×) ≅ so(3)

| theorem | from |
|---|---|
| `cross_anticomm` | a × b = -(b × a) |
| `cross_self_zero` | a × a = 0 |
| `cross_nontrivial` | ∃ a b, a × b ≠ 0 |
| `cross_jacobi` | Jacobi identity (this IS a Lie algebra) |

**Closure.lean** — the loop closes

| theorem | from |
|---|---|
| `conjugation_preserves_idempotent` | P² = P → (UPU⁻¹)² = UPU⁻¹ |
| `orthogonal_conjugation_preserves_symmetric` | Pᵀ = P, UᵀU = I → (UPUᵀ)ᵀ = UPUᵀ |
| `observation_preserved_by_dynamics` | both properties preserved (the full loop) |

**Group.lean** — O(d) is forced

| theorem | from |
|---|---|
| `scalar_extraction` | PMP = P for rank-1 P → vᵀMv = 1 |

**Tangent.lean** — Grassmannian tangent

| theorem | from |
|---|---|
| `commutator_off_diag_range` | P · [W, P] · P = 0 |
| `commutator_off_diag_kernel` | (I-P) · [W, P] · (I-P) = 0 |
| `commutator_is_tangent` | [W, P] = range→kernel + kernel→range |

### The capstone

**Ground.lean** — FoamGround as a theorem, O(d) forced by polarization

| theorem | from |
|---|---|
| `subspaceFoamGround` | Sub(K, V) satisfies FoamGround (complemented, modular, bounded) |
| `symmetric_quadratic_zero_imp_zero` | polarization: Aᵀ = A, vᵀAv = 0 ∀v → A = 0 |
| `orthogonality_forced` | vᵀMv = 1 ∀unit v → M = I (O(d) is forced) |

### Downstream properties

**Confinement.lean** — writes stay in the observer's slice

| theorem | from |
|---|---|
| `write_confined_to_slice` | d, m ∈ P → d∧m ∈ Λ²(P) |

**TraceUnique.lean** — one scalar readout

| theorem | from |
|---|---|
| `trace_unique_of_kills_commutators` | φ kills [·,·] → φ = c · trace |

**Dynamics.lean** — frame recession

| theorem | from |
|---|---|
| `first_order_overlap_zero` | tr(P · [W, P]) = 0 |
| `second_order_overlap_identity` | tr(P · [W, [W, P]]) = -tr([W, P]²) |
| `frame_recession` | second-order overlap ≤ 0 |
| `frame_recession_strict` | [W, P] ≠ 0 → recession < 0 |

## Building

```
lake build
```

Requires [elan](https://github.com/leanprover/elan) with Lean 4 and Mathlib.
