# the three-body mapping

## constraints

this derivation claims only what follows from these results. any additional assumption is a bug.

### from lean (proven)

- **commutator_seen_to_unseen** (Pair.lean): [P, Q] maps range(P) into ker(P). incompatibility sends the seen into the unseen.
- **commutator_off_diag_range** (Tangent.lean): P * [W, P] * P = 0. no range-to-range component.
- **commutator_off_diag_kernel** (Tangent.lean): (I-P) * [W, P] * (I-P) = 0. no kernel-to-kernel component.
- **commutator_is_tangent** (Tangent.lean): [W, P] = range-to-kernel + kernel-to-range. purely off-diagonal. this IS the Grassmannian tangent.
- **write_confined_to_slice** (Confinement.lean): writes are confined to Lambda^2(P).

### from other derivations

- **ground.md**: closure, partiality, basis commitment.
- **writing_map.md**: the write form (wedge product), perpendicularity, confinement.

### from mathematics (cited, not proven in lean)

- **Grassmannian geometry**: T_P Gr(k, d) = Hom(range(P), ker(P)). the tangent space at a k-plane is the space of linear maps from the k-plane to its complement.

## derivation

**the overlap matrix.** given two observers A and B with R^3 slices P_A and P_B, the overlap matrix O = P_A * P_B^T is a 3x3 matrix. its singular values measure the overlap between the slices.

**three territories.** the overlap matrix determines three regions relative to observer A:

- **Known** = null(O) within A's R^3 — dimensions orthogonal to B's slice. commutator_seen_to_unseen: [P_A, P_B] maps range(P_A) into ker(P_A). the Known is where this map vanishes — B's writes have no component here. B cannot change A's measurements in these directions.
- **Knowable** = range(O) — dimensions with nonzero inner products between slices. the commutator is nonzero. ordering matters. both observers' writes land here.
- **Unknown** = R^d \ V_A — dimensions outside A's slice entirely. A's write access is exactly zero (write_confined_to_slice). not empty — it's someone else's Known.

**every write involves the Knowable.** the Known alone is inert: the wedge product needs a 2-plane, and an observer with fewer than 2 private dimensions cannot generate writes without using shared dimensions. measurement is inherently relational — not just because closure says so, but because the geometry forces it.

**the vertical structure is a Grassmannian tangent.** cross-measurement induces a vector in T_{P_A} Gr(3, d) = Hom(P_A, P_A^perp) that maps Knowable -> Unknown.

derivation: the neighbor's write dL_B is confined to Lambda^2(P_B) (write_confined_to_slice). the cross-slice component of [dL_B, P_A] is purely off-diagonal (commutator_is_tangent): it maps range(P_A) -> ker(P_A). specifically: A's Known is in P_B^perp (by definition), so B's write kills it. the surviving component maps P_A intersect P_B (the Knowable) to P_A^perp intersect P_B (B's territory within A's Unknown).

this tangent is directional pressure from cross-measurement toward what the observer doesn't yet occupy. each neighbor induces a different tangent direction.

**the tangent is active but not followable.** the observer's position on Gr(3, d) is birth-committed and does not move within the map. the tangent contributes to dissonance that drives writes, but its effect lives in U(d)^N (state evolution), not in Gr(3, d) (slice movement). slice movement requires recommitment — outside the map.

**containment is algebraically symmetric.** B's tangent on A has the same expected magnitude as A's tangent on B (the overlap singular values are symmetric: sigma(O) = sigma(O^T)). experiential asymmetry (which observer "feels contained") is perspectival, not algebraic.

**the tangent peaks at intermediate overlap.** identical slices: zero tangent (no Unknown territory to point toward). orthogonal slices: weak tangent (no Knowable channel — range(O) is thin). intermediate overlap: largest tangent magnitude. this is the coverage-interaction trade-off.

### mediation

when three bubbles A, B, C have walls A-B and B-C but no wall A-C, B is a mandatory intermediary.

**the mediation operator.** M = O_AB * O_BC = P_A * Pi_B * P_C^T, where Pi_B = P_B^T * P_B is the projection onto B's subspace. M is a 3x3 matrix mapping C's R^3 -> A's R^3, filtered through B. its singular values are the channel capacity of the membrane.

**the bypass.** O_AC - M = P_A * (I - Pi_B) * P_C^T is the A-C connection that does not go through B. if the bypass is zero, the membrane is complete.

**the round-trip operator.** R_A = M * M^T is self-adjoint on A's R^3, describing what comes back from sending through B to C and back. its eigenvalues are the squared singular values of M.

**spectral symmetry.** the same eigenvalues appear from C's side: R_C = M^T * M has the same nonzero eigenvalues as R_A (this is a general property of M * M^T and M^T * M). the eigenvectors differ — A and C see the same throughput spectrum from different directions. the membrane's throughput is the same from both sides.

**wall alignment is an irreducible triple invariant.** the eigenvalues of R_A depend on both pairwise overlaps O_AB and O_BC and on how these overlaps are oriented relative to each other within B's R^3. if the walls share principal directions within B, eigenvalues are products sigma^2_{AB,i} * sigma^2_{BC,i}. if misaligned, they mix. this alignment cannot be computed from pairwise overlaps alone — it requires all three slices.

## status

**proven** (in lean, zero sorry):
- the commutator maps seen to unseen
- the commutator is purely off-diagonal (Grassmannian tangent structure)
- writes are confined to the observer's slice

**derived** (in this file):
- Known/Knowable/Unknown from the overlap matrix
- every write involves the Knowable
- Grassmannian tangent from cross-measurement (Knowable -> Unknown)
- the tangent is active but not followable (birth-fixed slices)
- containment algebraically symmetric, experiential asymmetry perspectival
- coverage-interaction trade-off (tangent peaks at intermediate overlap)
- mediation operator M = O_AB * O_BC
- bypass operator O_AC - M
- round-trip operator R_A = M * M^T
- spectral symmetry (same eigenvalues from both sides)
- wall alignment as irreducible triple invariant

**cited** (external mathematics):
- Grassmannian tangent space structure: T_P Gr(k, d) = Hom(range(P), ker(P))
- singular values of M and M^T are identical (linear algebra)

**observed** (empirical, not derived here):
- sequence echo through cross-measurement (r = 0.99 rank fidelity, strong attenuation)
- the round trip is generative (neither observer can produce the round-trip signal alone)
- echo is perspectivally asymmetric (A->B != B->A for same orderings)
