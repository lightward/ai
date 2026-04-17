# the writing map

## constraints

this derivation claims only what follows from these results.

### from lean (proven)

- **commutator_skew_of_symmetric** (Form.lean): if P and Q are self-adjoint, [P, Q] is skew-symmetric.
- **commutator_traceless** (Form.lean): tr[P, Q] = 0.
- **self_dual_iff_three** (Rank.lean): C(k, 2) = k iff k = 3.
- **rank_three_writes** (Rank.lean): dim(Λ²(ℝ³)) = 3.
- **cross_anticomm, cross_self_zero, cross_jacobi, cross_nontrivial** (Duality.lean): (ℝ³, ×) is a non-abelian Lie algebra (so(3)).
- **write_confined_to_slice** (Confinement.lean): if d and m lie in the observer's subspace P, then d ∧ m lies in Λ²(P).
- **commutator_seen_to_unseen** (Pair.lean): [P, Q] maps range(P) into ker(P).
- **observation_preserved_by_dynamics** (Closure.lean): orthogonal conjugation preserves P² = P and Pᵀ = P.

### from mathematics (cited, not proven in lean)

- **Taylor's theorem** (Jean Taylor, 1976): classification of stable junction configurations in ℝ³ — 120° triple junctions (k = 3) and tetrahedral vertices (k = 4). hypotheses: codimension-1 boundaries, locally area-minimizing, flat ambient space.

## derivation

**the write form.** given an observer with self-adjoint rank-3 projection P measuring input v ∈ ℝᵈ:

1. projection: m = Pv (the measurement, in P's slice).
2. a stabilization target j₂ (see below). dissonance: d = j₂ − m.
3. write direction: d ∧ m. write magnitude: f(d, m), a positive scalar function — a modeling choice (see below).

the write direction d ∧ m = d ⊗ m − m ⊗ d is determined up to sign:
- skew-symmetric (`commutator_skew_of_symmetric`).
- confined to Λ²(P) (`write_confined_to_slice`).
- confined to span{d, m}: d and m are the only vectors available from one measurement step.
- Λ²(2-plane) is 1-dimensional (from `rank_three_writes`: Λ²(ℝ³) has dim 3; a 2-plane within it contributes dim 1). the direction is unique up to sign.

the magnitude f(d, m) is not determined by this derivation. none of the downstream results below depend on its specific form: Haar convergence (geometry.md) depends on controllability of write *directions*, not magnitudes; the 1/√2 ceiling is combinatorial; frame recession is non-positive regardless of magnitude.

**perpendicularity.** the wedge product vanishes on parallel arguments (`cross_self_zero`: a × a = 0) and is maximal on orthogonal ones. this follows from the form.

**stabilization target.** this derivation takes the stabilization target as input from stabilization.md. within the stipulated ℝ³ slice and Taylor's classification, the target j₂ is the regular-simplex cosine −1/(k − 1) for local coordination number k ∈ {3, 4}. everything upstream of this paragraph — the wedge form, its confinement, skew-symmetry — is independent of the stabilization choice.

**flat/curved separation.** writes land in U(d) (curved: sectional curvature K(X, Y) = ¼‖[X, Y]‖²). the stabilization classification (Taylor) is stated over flat ℝ³. `observation_preserved_by_dynamics` shows the write (orthogonal conjugation) preserves the projection structure, so the ℝ³ slice persists under write. the classification in ℝ³ and the dynamics in U(d) therefore operate on different geometric objects by construction.

**confinement.** both d and m lie in the observer's slice. `write_confined_to_slice` gives d ∧ m ∈ Λ²(P). an observer's write cannot have components outside P. cross-observer effects come through `commutator_seen_to_unseen` (the commutator [W, P_A] has nonzero components mapping A's range to A's kernel), not through direct action on A's complement.

**two-argument signature.** the write is a function of (foam_state, input). foam_state determines P and j₂; input determines v. both are needed to form d = j₂ − Pv.

## status

**proven** (in lean, 0 sorry):
- skew-symmetry of the write form
- tracelessness of [P, Q]
- rank 3 as the unique dimension with Λ²(ℝ³) ≅ ℝ³ (self_dual_iff_three)
- confinement to observer's slice
- dynamics preserve the ground

**derived** (in this file):
- d ∧ m as the unique (up to sign) write direction, from skew + confinement + 1D of Λ²(2-plane)
- perpendicularity as a property of the wedge form
- flat/curved separation as a consequence of observation_preserved_by_dynamics plus the stabilization classification being stated in flat ℝ³

**modeling choices** (not forced):
- the magnitude scaling f(d, m). no downstream result uses its specific form.
- the stabilization target. taken as input from stabilization.md; stated there as dependent on the D = ℝ + Taylor stipulation.

**cited** (external mathematics):
- Taylor's classification of stable junctions in ℝ³

**observed in simulation** (not derived):
- perpendicular writes are the unique navigable constraint under the simulated dynamics (distinguishability + stability)
- the perpendicularity cost mechanism (write blindness) in simulation runs
- within-slice variance departs from isotropy in simulation (45:30:25 rather than 33:33:33)
