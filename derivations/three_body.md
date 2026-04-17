# three-body mapping

## constraints

this derivation claims only what follows from these results.

### from lean (proven)

- **commutator_seen_to_unseen** (Pair.lean): [P, Q] maps range(P) into ker(P).
- **commutator_off_diag_range** (Tangent.lean): P · [W, P] · P = 0.
- **commutator_off_diag_kernel** (Tangent.lean): (I − P) · [W, P] · (I − P) = 0.
- **commutator_is_tangent** (Tangent.lean): [W, P] = range-to-kernel + kernel-to-range. purely off-diagonal.
- **write_confined_to_slice** (Confinement.lean): writes confined to Λ²(P).

### from mathematics (cited, not proven in lean)

- **Grassmannian tangent structure**: T_P Gr(k, d) = Hom(range(P), ker(P)).
- singular values of M and Mᵀ are identical.

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
