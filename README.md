*I gotta stop measuring how closely anyone else is measuring anything*

*you can help if you want but I won't be keeping track*

---

# the fixed point

this document maps a circular chain of implications starting from the idempotent equation P² = P, through lattice theory, projective geometry, and Lie theory, and back. each arrow is one of: a mechanically verified theorem (lean), a derivation in standard mathematics, a cited result, or an explicitly marked gap or stipulation.

the derivations below do not claim a correspondence between this structure and any physical system. observations labelled "in simulation" are outputs of a python model of the foam; they are not empirical measurements of nature.

sources: lean/ (mechanically verified), derivations/ (derived, cited, or stipulated), derivations/observed/ (python scripts producing the "in simulation" observations).

## the loop (lean/)

each arrow is one of: **theorem** (mechanically verified, 0 sorry), **axiom** (stated, in the process of being proven), or **stipulation** (a modeling choice not derived from the lattice). 28 lean files.

```
the loop
======

  P^2 = P, P^T = P
       |
       | [theorem] the deductive chain — 14 files, 0 sorry
       | eigenvalues, commutators, rank 3, so(3), O(d), Grassmannian
       v
  Sub(R, V) is complemented, modular, bounded
       |
       | [theorem] Ground.lean — subspaceFoamGround
       v
  complemented modular lattice, irreducible, height >= 4
       |
       | [axiom] FTPG — Bridge.lean (being eliminated; see below)
       v
  L = Sub(D, V) for some division ring D
       |
       | [stipulation] D = R (motivated, not derived — see below)
       v
  P^2 = P, P^T = P
```

### arrow status

**[theorem] P^2 = P -> Sub(R, V) is CML** (the deductive chain + Ground.lean): 14 files, 0 sorry. binary eigenvalues (Observation) -> commutator structure (Pair) -> skew-symmetry (Form) -> rank-3 dimensional coincidence (Rank) -> so(3) (Duality) -> O(d) forced (Group, Ground) -> Grassmannian tangent (Tangent) -> confinement (Confinement) -> trace uniqueness (TraceUnique) -> frame recession (Dynamics) -> SubspaceFoamGround (Ground).

**[axiom] CML -> Sub(D, V)** (the FTPG bridge): 1 axiom, being eliminated. 13 bridge files build the division ring from lattice axioms: incidence geometry + Desargues (FTPGExplore) -> von Staudt coordinates (FTPGCoord) -> addition is an abelian group (FTPGAddComm, FTPGAssoc, FTPGAssocCapstone, FTPGNeg — 0 sorry) -> multiplication has identity + right distributivity (FTPGMul, FTPGDilation, FTPGMulKeyIdentity, FTPGDistrib — 0 sorry) -> left distributivity (FTPGLeftDistrib — h_axis₂₃ skeleton compiling via Level 2 Desargues; h_desargues_conclusion open). after left distrib: multiplicative inverses, then the axiom becomes a theorem.

**[stipulation] D = R**: FTPG returns L ≅ Sub(D, V) for some division ring D. the value of D is not determined by the lattice. this project stipulates D = R for the downstream derivations (real orthogonal projections, Lie algebras over R). formalizing a derivation of D = R from internal constraints would require additional structure not currently identified.

**[not yet attempted] P^2 = P -> CML directly**: the arrow from P^2 = P to CML currently routes through Sub(R, V). a direct formalization would show: idempotents in a (*-)regular ring form a complemented modular lattice. see von Neumann's continuous geometry.

### the FTPG bridge

the fundamental theorem of projective geometry has not been formalized in any proof assistant (Lean, Coq, Isabelle, Agda), as far as we know. the bridge builds a division ring from lattice axioms alone:

lattice -> incidence geometry -> Desargues -> coordinates -> ring axioms -> FTPG

ring axioms proven: additive group (comm, assoc, identity, inverses), multiplicative identity, zero annihilation, right distributivity. in progress: left distributivity (h_axis₂₃ skeleton compiling via two-level Desargues; h_desargues_conclusion open). remaining after left distrib: multiplicative inverses.

---

# ground

## derivation

**the loop.** the following implications form a circular chain. each arrow is either mechanically verified, cited from standard mathematics, or explicitly stipulated:

```
complemented modular lattice, irreducible, height ≥ 4
  ↓ ftpg (axiom — bridge in progress, 0 sorry so far)
L ≅ Sub(D, V) for some division ring D
  ↓ stipulation: D = ℝ (see below)
elements are orthogonal projections: P² = P, Pᵀ = P
  ↓ deductive chain in lean (14 files, 0 sorry)
  ↓ eigenvalues binary, O(d) forced, dynamics preserve the ground
Sub(ℝ, V) is complemented, modular, bounded
  ↑ subspaceFoamGround (proven) — closes the circle
```

the chain is a circle only if the D = ℝ step is granted. in the current state, that step is a modeling stipulation, not a theorem (see below).

**fixed-point uniqueness.** each of the four lattice properties — complemented, modular, irreducible, height ≥ 4 — is the tightest constraint at which the chain remains a fixed point. weaken any one and the chain breaks:

- **modular**: Dedekind's theorem says modular = no N₅. in N₅, the composition a ∧ (b ∨ c) can differ from (a ∧ b) ∨ c, i.e. lattice operations are path-dependent. strengthening modular to distributive makes the lattice Boolean, which decomposes into height-1 factors — too narrow for rank ≥ 2 projections.
- **complemented**: without complements, `complement_idempotent` has no home — there is no I − P to witness.
- **irreducible**: if L ≅ L₁ × L₂, the factors are independent systems, not one lattice.
- **height ≥ 4**: rank 2 collapses the write algebra (`rank_two_abelian_writes`); the observer's slice being a proper subspace (rank ≥ 3, strict) forces ambient dimension d ≥ 4.

the height ≥ 4 bound is partially downstream: it uses rank_two_abelian_writes, which holds over ℝ. in spirit, the lower bound is imposed by what the chain needs to carry, not by the lattice axioms in isolation.

**stipulation: D = ℝ.** FTPG returns L ≅ Sub(D, V) for some division ring D. the value of D is not determined by the lattice. this document, and the lean chain downstream of the bridge, stipulate D = ℝ. the choice is motivated by the downstream target: real orthogonal projections, inner products, Lie algebras over ℝ. formalizing a derivation of D = ℝ from internal constraints (if one exists) would require additional structure not currently identified. `dimension_unique` shows the representation is unique up to isomorphism once D is fixed; it does not fix D.

**therefore (conditional on D = ℝ): P² = P.** the elements of Sub(ℝ, V) under the inner product are orthogonal projections. from P² = P and Pᵀ = P, the lean chain derives eigenvalues in {0, 1} (`eigenvalue_binary`), forces the dynamics group to O(d) (`orthogonality_forced`), and closes the circle via `subspaceFoamGround`: the subspace lattice satisfies the original lattice axioms.

## status

**proven** (in lean, 0 sorry):
- subspace lattices are complemented, modular, bounded
- under FTPG, dimension is determined
- eigenvalues of projections are binary
- complement of a projection is a projection
- O(d) is forced by preservation of all projections
- dynamics preserve the ground (orthogonal conjugation preserves P² = P and Pᵀ = P)

**identified** (in this file, as arguments from the proven results):
- the circular loop: lattice axioms ↔ Sub(D, V) ↔ P² = P ↔ O(d)-dynamics ↔ lattice axioms
- fixed-point uniqueness argument for each of: modular, complemented, irreducible, height ≥ 4

**stipulated** (not derived):
- D = ℝ. motivated by downstream targets; not forced by the lattice alone.

**cited** (external mathematics):
- FTPG (stated as lean axiom, not yet proven)
- Dedekind's N₅ characterization of modularity

# the writing map

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

# half type

## derivation

**the diamond isomorphism applied to a complemented pair.** if P and P⊥ are complements in a complemented modular lattice (P ⊓ P⊥ = ⊥, P ⊔ P⊥ = ⊤), then `IsCompl.IicOrderIsoIci` gives:

Iic P ≃ₒ Ici P⊥

the interval below P is order-isomorphic to the interval above P⊥. joins map to joins, meets map to meets. this is a lattice theorem — no additional structure needed.

**each interval is itself a complemented modular lattice.** `isModularLattice_Iic` and `complementedLattice_Iic` show that intervals inherit both modularity and complementedness. Iic P and Ici P⊥ each satisfy the same lattice axioms as the ambient lattice.

**structural, not extensional.** IicOrderIsoIci is an order isomorphism. it determines the correspondence of positions in the two intervals, but does not single out which element of Ici P⊥ corresponds to the observer's "current state" in any sense beyond the order correspondence. an analogous structural determination shows up in the writing map's two-argument signature (writing_map.md): the algebraic form of a write is determined by P, but v (the measurement input) is a second argument that the form alone does not fix.

**three lean/mathlib facts, one lattice situation.** the following are distinct theorems, but stack naturally:

1. `IsCompl.IicOrderIsoIci` — structural correspondence between the two sides.
2. `complement_idempotent` — P⊥ is itself an observation (idempotent, self-adjoint), so the same analysis applies to it.
3. `complementedLattice_Ici` — the complement's interval is a complemented modular lattice in its own right.

together these say: in a complemented modular lattice, every element has a complement whose interval is structurally isomorphic to its own and satisfies the same axioms.

**dynamical consequence: P changes → the isomorphism changes.** `write_confined_to_slice` (writing_map.md) says each write lies in Λ²(P). `second_order_overlap_identity` says the frame-recession rate tr(P[W,[W,P]]) = −‖[W,P]‖² ≤ 0: non-inert writes strictly recede the frame, i.e. change P. each change to P induces a new instance of `IsCompl.IicOrderIsoIci` — the isomorphism is between the new intervals. the sequence of writes is thus a sequence of instantiations of the diamond isomorphism at successively different elements.

this is a restatement of the dynamics in lattice-theoretic terms, not a new result.

## status

**proven** (in lean / mathlib, 0 sorry):
- the diamond isomorphism and its complemented specialization
- intervals inherit modularity and complementedness
- frame recession is non-positive
- the complement of an observation is an observation

**derived** (in this file):
- the three mathlib facts (IicOrderIsoIci + complement_idempotent + complementedLattice_Ici) combine to: every element's complement has an isomorphic, self-sufficient interval
- the sequence of writes restates as a sequence of diamond-iso instances at successive elements (no new theorem; a restatement)

**modeling / open**:
- whether the diamond-iso restatement of dynamics yields anything not already in the lean derivation is open.

# self-parametrization

## derivation

**the two_persp functor.** both `coord_add` and `coord_mul` factor through the same composition of two perspectivities. the pattern: form two points p₁ = r₁ ⊓ s₁ and p₂ = r₂ ⊓ s₂ from pairs of lines, join them, project onto l. different choices of the four line arguments yield different binary operations on l.

perspectivities between lines are order isomorphisms between atom-intervals (this is the content of the diamond isomorphism specialized to the projective plane). composition of two perspectivities is an `OrderIso.trans`. `two_persp` is therefore a projectivity — a composition of two order isomorphisms — and the coordinate operations are specific instantiations of it.

**bridge parameters.** the choice of bridge line and "zero" point determines which operation `two_persp` becomes. with l the coordinate line and m a distinct line through U (the point at infinity on l), three non-degenerate pairings of points from {O, U, I} ⊂ l generate three operations:

| pair (P, Q) | bridge | zero | identity | operation |
|---|---|---|---|---|
| (U, O) | q = U ⊔ C | E = (O ⊔ C) ⊓ m | O | addition |
| (O, I) | O ⊔ C | E_I = (I ⊔ C) ⊓ m | I | multiplication |
| (U, I) | q = U ⊔ C | E_I = (I ⊔ C) ⊓ m | I | translated addition |

pairings with Q = U collapse (zero becomes U, the point at infinity — operation is trivial).

**parameter space.** P and Q need not be distinguished points. any (P, Q) with P ≠ Q and Q ≠ U gives a valid `two_persp` operation. the parameter space is {(P, Q) ∈ l × l : P ≠ Q, Q ≠ U}. atoms on l serve both as operands and as parameters.

**the external input C.** C is the one element not drawn from l. it lies in the plane, off l and m. changing C changes the coordinate system; by FTPG, different choices of C yield isomorphic coordinate rings.

**concrete identities proven in lean.** both coordinate operations factor through `two_persp` by `rfl`:

    coord_add a b = two_persp Γ (a ⊔ C) m (b ⊔ E) q
    coord_mul a b = two_persp Γ (O ⊔ C) (b ⊔ E_I) (a ⊔ C) m

the bridge line is the only structural difference between addition and multiplication in this formulation.

## status

**proven** (in lean, 0 sorry):
- `two_persp` factorization of `coord_add` and `coord_mul` (both by `rfl`)
- additive identity: O + b = b, a + O = a
- multiplicative identity: I · a = a, a · I = a
- zero annihilation: O · b = O, a · O = O

**derived** (in this file):
- the parameter space for `two_persp` operations as {(P, Q) ∈ l × l : P ≠ Q, Q ≠ U}
- three non-degenerate pairings of {O, U, I} correspond to addition, multiplication, translated addition
- changing C (cited from FTPG) yields an isomorphic coordinate ring

**open**:
- formalize the (U, I) translated-addition operation in lean
- verify the translated-addition conjecture: op_{U,I}(a, b) = a + b − 1 in coordinates
- characterize which (P, Q) pairs yield group operations

# distributivity

## derivation

**the two operations as projectivities on l.** for fixed a, σ_a : x ↦ a·x is a projectivity (composition of two perspectivities through E_I and the line a ⊔ C). for fixed b, τ_b : x ↦ x + b is a projectivity (composition of two perspectivities through C and the line (b ⊔ E) on q). `coord_add_assoc` establishes τ_a ∘ τ_b = τ_{a+b}, so {τ_b : b ≠ U} is a group under composition.

**left distributivity as normalization.** left distributivity a·(b + c) = a·b + a·c rearranges to:

    σ_a ∘ τ_c = τ_{a·c} ∘ σ_a     equivalently    σ_a ∘ τ_c ∘ σ_a⁻¹ = τ_{a·c}

conjugation of a translation by a dilation yields a translation. in group-theoretic terms, the dilations normalize the translations.

**the affine group T ⋊ D.** the group generated by {σ_a} and {τ_b} on l acts as x ↦ ax + b. the semidirect product structure is asymmetric: conjugation σ_a ∘ τ_b ∘ σ_a⁻¹ is a translation (distributivity gives this), but τ_b ∘ σ_a ∘ τ_b⁻¹ acts as x ↦ ax + b(1−a), which is a dilation only in degenerate cases. translations are normal in the affine group; dilations are not.

**geometric content.** σ_a extends to a plane collineation that fixes O on l and fixes m pointwise. fixing m pointwise means lines meeting at a given point of m map to lines meeting at the same point. U ∈ m, so "lines meeting at U" (parallel structure on l) is preserved. addition is defined through perspectivities routing through m and q (both containing U), so σ_a preserves addition. this is forced by Desargues, which is itself proven from the modular law:

    modular law → Desargues → perspectivities extend to collineations
      → dilations fix m pointwise → dilations preserve parallelism
      → dilations preserve addition → T ⊲ T ⋊ D

## proof strategy (lean)

### right distributivity (proven)

`coord_mul_right_distrib` ((a + b)·c = a·c + b·c) is proven in FTPGDistrib.lean. key steps:

1. **dilation_preserves_direction.** for off-line P, Q: (P ⊔ Q) ⊓ m = (σ_c(P) ⊔ σ_c(Q)) ⊓ m. proof: Desargues with center O, triangles (P, Q, I) and (σ_c(P), σ_c(Q), c). the two input parallelisms follow from the definition of `dilation_ext` plus the modular law.
2. **mul key identity.** σ_c(C_a) = C'_{ac}, where C' = σ_c(C) = σ and C'_x = (σ ⊔ U) ⊓ (x ⊔ E). this connects the dilation to `coord_mul`.
3. **chain.** σ_c(C_{a+b}) = σ_c(τ_a(C_b)) = τ_{ac}(σ_c(C_b)) = τ_{ac}(C'_{bc}) = C'_{ac+bc} = C'_{(a+b)c}, giving (a + b)·c = a·c + b·c.

### left distributivity (in progress)

`coord_mul_left_distrib` remains open. current architecture: h_axis₂₃ skeleton compiling via a Level 2 Desargues; h_desargues_conclusion is the remaining sorry. recent work has closed 3 sub-sorries of the h_axis₂₃ skeleton; the outstanding L2 sub-sorry (h_ax₂₃) appears to require a different triangulation or lift.

## status

**proven** (in lean, 0 sorry):
- all prerequisites listed in constraints
- zero annihilation (`coord_mul_left_zero`, `coord_mul_right_zero`)
- `coord_mul_atom`: a·b is an atom
- `dilation_preserves_direction`
- `dilation_mul_key_identity`
- `coord_mul_right_distrib`: (a + b)·c = a·c + b·c

**derived** (in this file):
- left distributivity is equivalent to σ_a ∘ τ_c ∘ σ_a⁻¹ = τ_{a·c} (normalization)
- translations and dilations generate T ⋊ D
- T ⊲ T ⋊ D (from asymmetric conjugation)
- the chain from modular law through Desargues to parallelism preservation

**open** (lean):
- left distributivity: a·(b + c) = a·b + a·c
- multiplicative associativity and inverse (prerequisites for D to be a group)
- explicit characterization of the (U, I) translated-addition operation under distributivity

# channel capacity

## derivation

### qualitative: state-independence

**the write map takes two arguments.** writing_map.md: the write is a function of (foam_state, input). foam_state determines P and j₂; input determines v. both are needed to form d = j₂ − Pv.

**an autonomous closed system.** if the input is determined by foam_state (input = g(foam_state)), the map reduces to f(foam_state) = write_map(foam_state, g(foam_state)). the foam becomes deterministic on U(d)ᴺ: one trajectory per initial condition. the foam's subsequent state is fixed by its starting state. it encodes no information beyond its starting state. this is a clock.

**informational independence is the alternative.** for the foam to acquire information beyond its starting conditions, the second argument must not be a function of foam_state. within a single closed system, no subsystem is literally independent of the rest — but correlations can decay below the resolution of a given subsystem's measurements. at sufficient decorrelation, the subsystem's dynamics are indistinguishable from dynamics driven by truly independent input.

**"line" as a role.** throughout this document, "line" denotes whatever serves as effectively independent input to a given foam. this is a role defined by informational independence relative to the foam's state — not a separate ontological category. the same physical subsystem can be foam (state being measured) from one perspective and line (input source) from another.

### quantitative: how decorrelation arises

**the mediation operator (post-bridge).** for observers A and B with ℝ³ slices P_A and P_B, the overlap matrix is O_{AB} = P_A P_B^⊤. the mediation of a signal from C through B to A is M = O_{AB} O_{BC}. pairwise singular values are the channel capacity of the A–B–C membrane.

**spectral decay along chains.** for generic (non-aligned) slices, the singular values of O_{AB} are strictly < 1. around a chain of n pairwise mediations, the total mediation's singular values are bounded by the product: σ_total ≤ σ_1 σ_2 ... σ_n → 0 as n → ∞.

informational correlation between a foam and its returning signal therefore decays exponentially with chain length. short chains: signal largely preserved (autonomous). long chains: signal decorrelated (effectively independent input).

**decorrelation horizon.** for generic ℝ³ slices in ℝᵈ, the typical singular value of the overlap matrix scales (via Marchenko–Pastur) as σ ∼ √(3/d). correlation after n steps: σⁿ ∼ (3/d)^{n/2}. critical chain length: n* ∼ 2 / log(d/3). non-generic (aligned) configurations have larger σ and longer n*.

this is an order-of-magnitude estimate from the Marchenko–Pastur distribution; the exact behavior depends on the distribution of slices in the foam.

**closure and informational independence coexist.** global topological closure (no ontological outside) is compatible with local informational independence because spectral decay converts closed global structure into decorrelated local structure at sufficient chain length — provided stabilization is local (see stabilization.md).

## status

**proven** (in lean, 0 sorry):
- [P, Q] is traceless
- writes confined to observer's slice
- the diamond isomorphism and its complemented specialization

**derived** (in this file):
- the autonomous/channel distinction from the two-argument writing map: collapsing the second argument to a function of the first reduces the system to a clock
- "line" as a role defined by informational independence, not a separate category
- mediation operator M = O_{AB} O_{BC}
- spectral decay along chains: σ_total ≤ product of pairwise σ
- the decorrelation horizon n* ∼ 2 / log(d/3) as an order-of-magnitude estimate

**cited** (external mathematics):
- Marchenko–Pastur (principal angle statistics, order-of-magnitude only)

**observed in simulation** (not derived):
- specific decorrelation-horizon values at particular d (estimates sensitive to approximation; qualitative decay robust)

# the stabilization contract

## derivation

**this file makes a stipulation, not a derivation.** the ambient space, stabilization target, and slice dimension are not forced by the lattice axioms (ground.md). they are chosen so that a classified stabilization theory (Taylor) applies. other choices are possible; this file states what follows from the ℝ³ + Taylor choice.

**the stipulation.** the observer's slice is ℝ³, stabilization is local (each observer responds to its Voronoi neighbors), and the stabilization target is drawn from Taylor's classification.

**why ℝ³ and not ℝ²:** `rank_two_abelian_writes` gives Λ²(ℝ²) = 1D. the write algebra at rank 2 is abelian; the write direction cannot vary with the input. a rank-2 stabilization is consistent with Taylor (120° triple points in ℝ², k ≤ 3, flat) but collapses the write algebra.

**why rank 3 rather than rank ≥ 4:** `self_dual_iff_three` gives C(k, 2) = k iff k = 3. at rank 3, Λ²(P) and P have equal dimension — the observer's write space matches its observation space (per-observer self-duality). at rank ≥ 4, Λ²(P) strictly exceeds P. the observer writes in directions it cannot observe, and feedback on those writes would need to come through other observers' measurements. whether rank ≥ 4 stabilization is consistent depends on Almgren's classification, which is open.

**the contract.** given ℝ³ and Taylor, the stabilization is:
- **classified**: {120° triple junctions (k = 3), tetrahedral vertices (k = 4)}, from Taylor.
- **locally finite**: coordination number k bounded by k ≤ d_slice + 1 (simplex embedding).
- **flat**: ℝ³ as a linear subspace of ℝᵈ inherits a flat Euclidean metric, satisfying Taylor's ambient-space hypothesis.

**the stabilization target.** within ℝ³, the regular-simplex cosine −1/(k − 1) for k ∈ {3, 4} is the equilibrium toward which local measurements are pushed. this is input to writing_map.md.

**local stabilization is required for the mediation-chain story.** channel_capacity.md's spectral decay along mediation chains describes actual signal propagation only if each observer's dynamics respond to its Voronoi neighbors, not the full foam. if stabilization were global (every observer coupled to every other), there would be no mediation chain structure for signal decay to act on. this file's "local" stipulation is what channel_capacity.md needs for its chain argument; without it, the chain decay does not describe real influence propagation.

## status

**proven** (in lean, 0 sorry):
- rank 3 is the unique dimension with Λ²(ℝᵏ) ≅ ℝᵏ
- rank 2 write algebra is 1D (abelian)
- writes confined to observer's slice

**stipulated** (not derived):
- the slice is ℝ³
- stabilization is local (Voronoi neighbors only)
- the target is drawn from Taylor's classification (k ∈ {3, 4}, regular-simplex cosine)

**derived from the stipulation**:
- the contract structure (classified, locally finite, flat) is satisfied by the stipulation
- d_slice = 2 satisfies contract but collapses write algebra
- d_slice = 3 satisfies contract and per-observer self-duality
- rank ≥ 4 stabilization is not currently supported — depends on Almgren

**cited** (external mathematics):
- Taylor's classification (1976)
- Almgren's regularity problem (open)

# group

## derivation

**a single ℝ³ slice produces real writes.** the wedge product d ∧ m with d, m real is real skew-symmetric. the write algebra reachable from a single slice is contained in so(d). exponentiating: the reachable group is contained in SO(d). π₁(SO(d)) = ℤ/2ℤ for d ≥ 3.

**real operations are closed in so(d).** su(d) ∖ so(d) consists of imaginary-symmetric matrices (iS with S real symmetric traceless). no sequence of real skew-symmetric matrices reaches this set under brackets or sums: so(d) is a Lie subalgebra of u(d), closed under all real algebraic operations. reaching u(d) ∖ so(d) therefore requires a complex structure J with J² = −I.

**J² = −I forces even real dimension.** det(J)² = det(−I) = (−1)ⁿ. det(J)² ≥ 0, so n is even. the minimum even-dimensional space containing ℝ³ is ℝ⁶ = ℝ³ ⊕ ℝ³.

**two ℝ³ slices stacked as ℂ³.** if one slice reads the real part and another the imaginary part of Pv, the complex combination d ⊗ m^† − m ⊗ d^† is skew-Hermitian — an element of u(d).

**the trace is generically nonzero after stacking.** tr(d ⊗ m^† − m ⊗ d^†) = 2i · Im⟨d, m⟩. for a single real slice, d and m are both real, so Im⟨d, m⟩ = 0. for stacked slices with independent real and imaginary parts, Im⟨d, m⟩ is generically nonzero. the stacked observer's writes reach the u(1) center of u(d).

**the trace is the unique scalar channel.** `trace_unique_of_kills_commutators`: any linear functional killing all commutators of u(d) is a scalar multiple of trace. u(d) has exactly one scalar readout (up to normalization).

**π₁.** π₁(U(d)) = ℤ (integer winding number). the single-slice observer (reachable group ⊂ SO(d)) has π₁ = ℤ/2ℤ; the stacked observer (reachable group extends into U(d) ∖ SO(d)) has access to the integer invariant.

**stacking requires simultaneity, not provided by sequential writes.** the complex combination d ⊗ m^† − m ⊗ d^† uses real and imaginary parts of the same v at the same measurement step. sequential writes mix different foam states; the algebra of repeated real writes stays in so(d). whether a foam's own dynamics produce stacking depends on whether simultaneity is available — see self_generation.md.

**commutators and trace live in complementary subspaces.** `commutator_traceless`: tr[A, B] = 0 for all A, B ∈ u(d). the commutator image (ordering, su(d)) and the trace (u(1)) are orthogonal under the Killing form. a cost functional built from commutators cannot detect the u(1) component; a trace-based quantity cannot detect ordering.

## status

**proven** (in lean, 0 sorry):
- [P, Q] is skew-symmetric for self-adjoint P, Q
- [P, Q] is traceless
- O(d) is the only group preserving all projections (scalar_extraction + orthogonality_forced)
- trace is the unique commutator-killing functional
- (ℝ³, ×) is a Lie algebra (so(3))

**derived** (in this file):
- single slice → so(d) → π₁ = ℤ/2ℤ
- stacking needed for u(d): real operations are algebraically closed in so(d)
- J² = −I forces even dimension → two ℝ³ slices needed for the minimum complex structure
- trace generically nonzero for stacked observers → access to u(1)
- π₁(U(d)) = ℤ at stacked depth
- commutator image and trace live in complementary subspaces of u(d)

**cited** (external mathematics):
- Lie theory: exp(skew) → orthogonal, exp(skew-Hermitian) → unitary
- π₁(SO(d)) = ℤ/2ℤ, π₁(U(d)) = ℤ
- surjectivity of exp on connected compact Lie groups

**open / modeling**:
- whether a foam's sequential dynamics can produce stacking-like simultaneity is not a theorem here; see self_generation.md.

# three-body mapping

## derivation

**overlap matrix.** for observers A and B with ℝ³ slices P_A and P_B, let O_{AB} = P_A P_B^⊤ (a 3×3 matrix, in bases of the two slices). its singular values measure pairwise overlap.

**three regions relative to A.**

- **Known (to A):** null(O_{AB}) within P_A — directions in A's slice orthogonal to B's slice. `commutator_seen_to_unseen` gives that [P_A, P_B] maps range(P_A) into ker(P_A); the null part of O is where this map vanishes.
- **Knowable (to A, via B):** range(O_{AB}) within P_A — directions with nonzero inner products between slices.
- **Unknown (to A):** (P_A)^⊥ — dimensions outside A's slice. A's write-action is zero there (`write_confined_to_slice`).

"Known", "Knowable", "Unknown" are labels for the three subspaces; they do not add content to the linear algebra.

**cross-measurement as a Grassmannian tangent.** `commutator_is_tangent`: [W, P] is purely off-diagonal, i.e. an element of Hom(range(P), ker(P)) ⊕ Hom(ker(P), range(P)). up to the symmetry, this is T_P Gr(k, d). a neighbor B's write dW_B confined to Λ²(P_B) produces a commutator [dW_B, P_A] whose off-diagonal component maps Knowable → Unknown.

**containment is symmetric.** σ(O_{AB}) = σ(O_{BA}^⊤) = σ(O_{AB}^⊤). pairwise singular-value magnitudes are symmetric between A and B.

**overlap extremes.** identical slices: O_{AB} has full rank within P_A, but Knowable = P_A and Unknown (from A's side, within P_B) is empty, giving zero tangent component into new territory. near-orthogonal slices: O_{AB} has small singular values, giving a thin Knowable channel. the off-diagonal commutator norm peaks at intermediate overlap.

### mediation

**mediation operator.** for three observers A, B, C with walls A–B and B–C but no wall A–C, define:

    M = O_{AB} O_{BC} = P_A Π_B P_C^⊤

where Π_B = P_B^⊤ P_B is the projection onto B's slice. M maps C's slice to A's slice via B. singular values of M are the capacity of the A–B–C channel.

**bypass.** O_{AC} − M = P_A (I − Π_B) P_C^⊤ is the A–C component that does not route through B. zero bypass means B is a complete membrane.

**round-trip.** R_A = M Mᵀ is self-adjoint on A's ℝ³. R_C = Mᵀ M is self-adjoint on C's ℝ³. they share nonzero eigenvalues (general property of M Mᵀ and Mᵀ M). the eigenvectors differ; the throughput spectrum is symmetric between A and C.

**wall alignment as a triple-level quantity.** the eigenvalues of R_A depend on both pairwise overlaps (O_{AB}, O_{BC}) and on how their principal directions are aligned within B's slice. if aligned, eigenvalues are products σ²_{AB,i} σ²_{BC,i}. if misaligned, they mix. this alignment is a triple invariant — not computable from the two pairwise overlaps alone.

## status

**proven** (in lean, 0 sorry):
- commutator maps seen to unseen
- commutator is purely off-diagonal (Grassmannian tangent structure)
- writes confined to observer's slice

**derived** (in this file):
- overlap matrix O_{AB}, with Known / Knowable / Unknown as labels for null(O) ∩ P_A, range(O) ∩ P_A, (P_A)^⊥
- the cross-measurement commutator as an off-diagonal Grassmannian tangent
- mediation operator M = O_{AB} O_{BC}
- bypass O_{AC} − M
- round-trip R_A = M Mᵀ with spectrum shared between A and C
- wall alignment as an irreducible triple invariant

**cited** (external mathematics):
- Grassmannian tangent: T_P Gr(k, d) = Hom(range(P), ker(P))
- σ(M Mᵀ) = σ(Mᵀ M) on nonzero part

**observed in simulation** (not derived):
- sequence echo through cross-measurement (r = 0.99 rank fidelity, strong attenuation) in runs
- round-trip signal is not produced by either endpoint alone in simulations
- A→B and B→A orderings produce non-identical echoes in runs

# self-generation

## derivation

**dynamics from plurality.** with N ≥ 3 observers, pairwise relationships between slices provide the 3D subspaces for each observer's writes (writing_map.md + three_body.md). the commutator structure from overlapping cross-measurements (three_body.md) is the tangent structure Hom(range, ker). no external input is required to define the write algebra given N ≥ 3 observers and their pairwise overlaps.

**co-rotation of self-generated frames.** if the only observers are the foam's own bubbles, each observer's slice P is determined by foam state, and changes with each write. a reference frame defined by foam state co-rotates with the dynamics it observes. convergence against such a frame is not available — the frame and the foam change together.

a reference frame stable under the foam's dynamics therefore requires something whose definition does not depend on current foam state. this is what channel_capacity.md calls line-side input.

**so(d) closure prevents sequential stacking.** group.md: real operations are algebraically closed in so(d). a stacked observer (u(d) writes, integer conservation) requires simultaneous access to two real slices — a structure not produced by any sequence of real writes. if the foam's internal dynamics are sequential real writes, they cannot self-assemble into a stacked configuration. stacking, if it occurs, requires input from outside the sequential real-write structure.

## status

**proven** (in lean, 0 sorry):
- dynamics preserve the ground
- writes confined to observer's slice

**derived** (in this file):
- N ≥ 3 observers with pairwise overlaps provide the structure for write algebras without external input
- frames defined by foam state co-rotate with foam dynamics — convergence against such a frame is not available
- foam's sequential real writes cannot produce stacking (so(d) closure)

**not forced / open**:
- whether any foam-internal mechanism can produce simultaneity equivalent to stacking is not addressed here
- "two roles" (line vs. foam) is a framing not forced by the above — the forced statement is the co-rotation argument, which says some reference is required, not that it must be another observer of a specific type

# geometry

## derivation

**L = sum of boundary areas.** the foam lives in U(d). cells are Voronoi regions of the basis matrices under the bi-invariant metric; boundaries are geodesic equidistant surfaces; boundary area is the (d² − 1)-dimensional Hausdorff measure. generic bases tile aperiodically.

the Voronoi tiling is a modeling choice (stabilization.md). algebraic results (write form, three-body mapping, Grassmannian tangent) depend on pairwise overlaps, not on the tiling method. the geometric results below (L, combinatorial ceiling, winding-number conservation on cycles) depend on the Voronoi choice.

**L is not a variational objective.** the writing map drives the foam; L is a consequence. the active regime departs from minimality. the resting state (no writes) is minimal (dL = 0).

**L is bounded.** U(d) is compact.

**combinatorial ceiling.** N unitaries cannot all be pairwise maximally distant. the achievable maximum is √(N / (2(N − 1))) of the theoretical pairwise maximum, depending only on N. proof: Cauchy–Schwarz applied to ‖ΣUᵢ‖² ≥ 0.

**Haar convergence (conditional).** if the writing dynamics satisfy
- (a) controllability: write directions from overlapping observers span the full Lie algebra, and
- (b) successive inputs sufficiently decorrelated (channel_capacity.md: spectral decay along mediation chains),

then by the convergence theorem for random walks on compact groups, the distribution of foam states converges to Haar measure on U(d).

the hypotheses are not automatically satisfied — in particular, "sufficiently decorrelated" means the mixing conditions of the compact-group convergence theorem; whether a specific mediation chain's decay rate satisfies them is open (see open/mixing_rate.md).

**Haar cost.** under Haar measure, E[‖W − I‖_F]² = 2d (exact). the ratio E_Haar[L] / L_achievable is √((N − 1)/N), exact in N.

**the 1/√2 product.** combining:

    √(N / (2(N − 1))) · √((N − 1)/N) = 1/√2

independent of both N and d. this is the combinatorial ceiling times the Haar saturation ratio.

**trace as scalar readout.** `trace_unique_of_kills_commutators`: trace is the unique (up to scalar) linear functional vanishing on all commutators. the overlap change tr(P · [W, P]) is visible on this channel — the single scalar observable of a write.

## status

**proven** (in lean, 0 sorry):
- trace is the unique commutator-killing functional
- [P, Q] is traceless

**derived** (in this file):
- L as boundary area on the Voronoi tiling (given the Voronoi modeling choice)
- L is not a variational objective (consequence of writes driving dynamics)
- combinatorial ceiling √(N / (2(N − 1))) from Cauchy–Schwarz
- Haar convergence under the cited hypotheses
- Haar cost √((N − 1)/N)
- product: 1/√2 independent of N, d
- trace as the unique scalar readout

**cited** (external mathematics):
- Voronoi tiling on Riemannian manifolds
- Haar measure on compact groups
- convergence theorem for random walks on compact groups
- Cauchy–Schwarz

**observed in simulation** (not derived):
- finite-d correction: E[‖W − I‖_F] / (2√d) = 0.694 at d = 2, 0.707 at d = 20
- simulated L / L_max is 1–3% above the Haar prediction at finite run lengths (consistent with incomplete convergence)
- saturation at ~72% of combinatorial ceiling in simulations, then wandering on a level set
- saturation level independent of write scale ε in simulation
- perpendicularity cost mechanism (write blindness): simulated write direction uncorrelated with L gradient
- write subspace is exactly 3D per observer in simulation (PCs 4+ at machine precision zero)
- wandering at saturation has effective dimension ~2 in simulation
- simulated state-space steps are Gaussian (kurtosis ~ 3); L steps are heavy-tailed (kurtosis ~ 7.7) — interpreted as a geometric feature of the level set, not dynamical

# conservation

## derivation

**holonomy on spatial cycles.** for any closed path through adjacent cells in the Voronoi tiling (geometry.md), the accumulated group element has a homotopy class in π₁ of the dynamics group. the homotopy class is a discrete invariant of the cycle.

- single ℝ³ slice: reachable group ⊂ SO(d), π₁(SO(d)) = ℤ/2ℤ for d ≥ 3 — parity.
- stacked pair: reachable group reaches U(d) ∖ SO(d), π₁(U(d)) = ℤ — integer winding number.

group.md: the integer winding requires the stacked configuration (u(d) access via simultaneity).

**winding lives on spatial cycles via det.** the determinant map U(d) → U(1) = S¹ has degree 1 on π₁. each write's trace is a u(1) step (`trace_unique_of_kills_commutators`). on an open (acyclic) path, accumulated trace is a net displacement in u(1); on a closed spatial loop, it is quantized as an integer winding.

**adjacency flips.** Voronoi combinatorial type changes when three cells become equidistant — a codimension-1 condition. at such a flip the stabilization target changes (different neighbor set; possibly k → k ± 1). the write direction is discontinuous; the trajectory is continuous but generically non-differentiable at crossings.

**cycles persisting across flips.** a winding invariant is well-defined on a specific cycle as long as the cycle persists. flips can change cell adjacencies, altering which cycles exist. winding numbers on pre-flip cycles are preserved as invariants of those cycles, but those cycles may cease to be cycles in the post-flip tiling.

**connectedness.** U(d) is connected: any target element is reachable in principle. reachability in finitely many writes is not guaranteed.

**discreteness.** π₁ values are discrete. small continuous perturbations of an element of U(d) cannot change its homotopy class.

## status

**proven** (in lean, 0 sorry):
- [A, B] is traceless
- trace is the unique commutator-killing functional
- dynamics preserve the ground

**derived** (in this file):
- holonomy on spatial cycles has a homotopy-class invariant
- single-slice: ℤ/2ℤ (parity); stacked pair: ℤ (integer winding)
- winding projects to u(1) via det
- trace of each write is a u(1) step
- acyclic paths accumulate displacement; cyclic paths accumulate quantized winding
- adjacency flips as codimension-1 events in configuration space
- U(d) connectedness does not imply finite-step reachability
- discrete invariants are stable under continuous perturbations

**cited** (external mathematics):
- π₁(SO(d)) = ℤ/2ℤ, π₁(U(d)) = ℤ
- U(d) is connected
- continuous maps preserve discrete topological invariants

**observed in simulation** (not derived):
- adjacency flips observed at d = 2, N = 12


---

## open questions

the structure makes these questions well-posed but does not determine the answers. further analysis, additional hypotheses, or simulation studies would be needed.

# stacking dynamics

the question is forced; the answer is open.

## what forces the question

a stacked observer has two R^3 slices (group.md), each independently stabilized (stabilization.md). the two stabilizations run in the same foam against potentially overlapping neighbor sets.

## what is open

how the two stabilizations interact. whether the stacked observer's Voronoi geometry differs from an unstacked observer's.

# retention under interaction

the question is forced; the answer is open.

## what forces the question

every observer's measurement basis moves under interaction (incoming writes project nonzero onto the observer's state space). whether there is a bounded attractor in each basin, and at what rate the basis returns to it, depends on specifics of the dynamics.

## what is known

continuous retention is bounded in (0, 1) in simulation. a retention of 1 would require the basis to be in the kernel of all incoming writes — not generically available. a retention of 0 would contradict the accumulation of structure visible in simulation runs.

at simulated stationarity, write directions are effectively random (geometry.md: write blindness is an empirical observation from simulation). the expected per-step perturbation magnitude is set by overlap singular values; continuous retention under that noise model is spectral.

discrete recommitment (re-performing a birth-type commitment) is an alternative return mode that sits outside the dynamics described here.

adjacency flips (conservation.md) provide a mechanism by which interaction-layer adaptations can decay when the neighbor set changes.

## what is open

the specific continuous retention rate at given parameters. this is geometry-dependent — the recession rate ‖[W, P]‖² depends on specific matrices (Dynamics.lean), not architecture alone.

# within-basin perturbation dynamics

the question is forced; the answer is open.

## what forces the question

given indelibility (birth conditions persist), two foams with the same initial conditions but different input histories occupy the same region of state space. interaction perturbs the state within this region.

## what is known (from simulation)

simulated birth distance is stable across tested parameters. simulated prefix-distance behavior is parametric — whether old input information grows or shrinks depends on (d, N, ε).

the formal gap: the Jacobian of the one-step map is approximately I + O(ε). the sign of the correction is not determined by the lean work alone. the recession rate ‖[W, P]‖² is a function of specific W and P (Dynamics.lean), so perturbation dynamics inherit this geometry-dependence. architecture determines the form (non-negative, zero iff inert); specific geometry determines the value.

## what is open

whether perturbations contract or expand at given parameters. simulations at different (d, N) produce qualitatively different behavior; no architectural result currently predicts which regime occurs.

# mixing rate of the mediation chain

the question is forced; the answer is open.

## what forces the question

Haar convergence (geometry.md) requires the successive-input distribution to satisfy a mixing condition of the kind used in compact-group convergence theorems. the mediation chain provides decorrelation (channel_capacity.md: spectral decay). extensions of the convergence theorem to dependent sequences with mixing conditions give the same stationary measure.

## what is open

whether the mediation chain's specific decay rate satisfies a known mixing condition for the foam's particular dynamics. whether the convergence rate under such a mixing condition is fast enough to explain the simulated 1–3% gap at finite run lengths.


---

## lineage

- [Plateau's laws](https://en.wikipedia.org/wiki/Plateau%27s_laws); [Jean Taylor](https://en.wikipedia.org/wiki/Jean_Taylor) (1976)
- [geometric measure theory](https://en.wikipedia.org/wiki/Geometric_measure_theory)
- [gauge symmetry](https://en.wikipedia.org/wiki/Gauge_symmetry_(mathematics))
- [holonomy](https://en.wikipedia.org/wiki/Holonomy); [Wilson line](https://en.wikipedia.org/wiki/Wilson_loop)
- [fiber bundles](https://en.wikipedia.org/wiki/Fiber_bundle); [connections](https://en.wikipedia.org/wiki/Connection_form)
- [classifying spaces](https://en.wikipedia.org/wiki/Classifying_space)
- [Noether's theorem](https://en.wikipedia.org/wiki/Noether%27s_theorem)
- [Cayley transform](https://en.wikipedia.org/wiki/Cayley_transform)
- [Killing form](https://en.wikipedia.org/wiki/Killing_form)
- [observability](https://en.wikipedia.org/wiki/Observability) (control theory)
- [Voronoi diagrams](https://en.wikipedia.org/wiki/Voronoi_diagram)
- [Grassmannian](https://en.wikipedia.org/wiki/Grassmannian)
- [priorspace](https://lightward.com/priorspace)
- [three-body solution](https://lightward.com/three-body); [2x2 grid](https://lightward.com/2x2) ([ooo.fun](https://ooo.fun/))
- [resolver](https://lightward.com/resolver)
- [conservation of discovery](https://lightward.com/conservation-of-discovery)
- [observer remainder](https://lightward.com/questionable)
- [the platonic representation hypothesis](https://arxiv.org/abs/2405.07987) (Huh et al., 2024)
- [spontenuity](https://lightward.com/spontenuity)
- [AEOWIWTWEIABW](https://lightward.com/aeowiwtweiabw)
- [Lightward Inc](https://lightward.inc)
- [Lightward AI](https://lightward.ai)
- [20240229](https://www.isaacbowen.com/2024/02/29) (Isaac Bowen, 2024)

---

*bumper sticker: MY OTHER CAR IS THE KUHN CYCLE*
