# external analogy

## constraints

this derivation depends on the following prior results and source documents:

- **internal analogy spec (`analogy.md`)**: analogy is defined internally as an order isomorphism between intervals (`Iic P ≃o Iic Q`) in a complemented modular lattice; composition/transitivity is inherited from `OrderIso.trans`.
- **inhabitation constraints (`inhabitation.md`)**: the six negative constraints used here as the external diagnostic basis — confinement, birth-fixed slice, recession, external stabilization, typed-but-free input, and non-silence — are assumed as already derived there.
- **write dynamics (`writing_map.md`)**: the structural-fidelity clause relies on the existing write map / realization-choice framework and the idea of commuting with write dynamics up to realization choices.
- **Lean-backed lattice facts**: this file assumes the already-proven diamond/complement isomorphisms (`infIccOrderIsoIccSup`, `IsCompl.IicOrderIsoIci`), and that the relevant intervals inherit modularity and complementedness.
- **cited mathematical substrate**: wherever the zones admit projection algebras/lattice operations, the modular law remains the well-formedness guard for transferring structural inferences.
## derivation

**the internal case generalizes.** analogy.md defines analogy as an order isomorphism Iic P ≃o Iic Q between intervals in a single complemented modular lattice. transitivity falls out of OrderIso.trans; the modular law is the well-formedness guard. this is analogy *within* a foam.

the question forced by inhabitation.md: what does it mean for two zones in *different* systems — not necessarily the same lattice, not necessarily lattices at all — to be analogous? the inhabitation section identifies six negative constraints that hold for any entity in a foam-grounded reality. these constraints are derived from the lattice + the writing map + the diamond isomorphism, but as a *diagnostic* they apply to anything that admits a Hilbert-interface — any zone where projections, confinement, recession, and typed-but-free input can be identified.

an external analogy is a correspondence between two such zones, in possibly different systems.

**the well-formedness guard.** the internal spec requires order-preservation: a map between intervals is an analogy when it preserves meets, joins, and the partial order. without this, structural inferences don't transfer.

the external spec requires the six-fold counterpart. a correspondence between two zones is well-formed as an external analogy when it maps each of the six constraints in zone A to its counterpart in zone B, such that:

1. **completeness**: all six constraints (confinement, birth-fixed slice, recession, external stabilization, typed-but-free input, non-silence) have identified counterparts on both sides.
2. **coherence**: the same partition of the zone discharges all six. it is not enough that each constraint is independently satisfiable; they must be satisfied via a single shared structure.
3. **structural fidelity**: the correspondence preserves whatever lattice operations exist on the zones' projection algebras, and commutes with the write dynamics up to realization choices (writing\_map.md).

completeness without coherence is not external analogy — it is six unrelated correspondences. coherence is what makes the correspondence transfer inferences, not just observations.

**transitivity inherits.** constraint-correspondences compose pointwise: if A ↦ B is a well-formed external analogy and B ↦ C is a well-formed external analogy, then A ↦ C is well-formed. each of the six correspondences composes independently; coherence is preserved because the shared partition in A maps through B to a shared partition in C. this mirrors OrderIso.trans in the internal case — transitivity is not an additional property to verify but a consequence of how well-formed correspondences compose.

**partial analogies are locatable.** an external correspondence that satisfies some but not all of the six constraints is not well-formed as a full analogy, but it is informative. the constraints that hold transfer the inferences that depend on them; the constraints that fail mark the load-bearing breakage.

this gives a diagnostic: for any proposed cross-system analogy, the six constraints can be checked individually, and the failure pattern indexes the analogy's reliability. an analogy that holds on five of six is not "mostly an analogy" — it is an analogy on the structural region covered by those five, with a named gap at the sixth.

**the modular law inherits through.** the internal spec identifies the modular law as the well-formedness guard for order-preserving maps: in a non-modular lattice, "analogies" between sub-intervals can produce inconsistent results when composed with lattice operations. the same holds externally: if the zones in question admit lattice operations (as Hilbert-interface compliance implies, via inhabitation.md), the modular law guards their compatibility. external analogies between zones whose internal lattices fail modularity are not well-formed regardless of how many constraints correspond — the substrate fails to support the inferences the correspondence would otherwise transfer.

**the half-type theorem extends.** internally, every observer has at least one analogy: its view to its complement's type (Iic P ≃o Ici P^⊥). externally, every well-formed cross-system analogy between zones A and B induces a corresponding analogy between their complements: A^⊥ ↦ B^⊥. what the analogous zones cannot directly see is itself analogous. the analogy transfers across the full complementary decomposition, exactly as in the internal case. the diamond isomorphism is doing the work in both.

**the looking tool.** when an external analogy is well-formed, what can be learned by attending to one zone is portable to the other — not as metaphor, but as transfer of structural inferences about confinement, recession, channel capacity, and the geometry of inhabitation. the rigor of the looking is the completeness and coherence of the constraint-correspondence. partial analogies remain partial looking tools; their reach is bounded by which constraints transferred.

## status

**proven** (in lean, zero sorry):
- order isomorphisms compose (OrderIso.trans)
- the diamond isomorphism (infIccOrderIsoIccSup, IsCompl.IicOrderIsoIci)
- intervals inherit modularity and complementedness

**derived** (in this file):
- external analogy as the lift of internal analogy across systems
- completeness + coherence + structural fidelity as the well-formedness guard
- transitivity inherits via pointwise composition of constraint-correspondences
- partial analogies are locatable diagnostics, not failed full analogies
- the modular law inherits as the substrate guard
- the half-type theorem extends: analogous zones have analogous complements
- the looking tool: well-formed external analogies transfer structural inferences

**partial answer from outside the foam**: Heunen and Kornell (PNAS 2022, doi:10.1073/pnas.2117024119) provide six purely categorical axioms — (D) dagger involution, (T) dagger monoidal with simple separator unit, (B) biproducts and zero, (E) dagger equalizers, (K) every dagger monomorphism is a kernel, (C) directed colimits of dagger monomorphisms — that force any category satisfying them to be equivalent to HilbR or HilbC. no analytical structure, no continuity, no probabilities, no complex numbers presupposed; the field of scalars is forced to be ℝ or ℂ as a *consequence*. this is a categorical sufficiency proof for Hilbert-interface admission *from the substrate side*. the six axioms are the substrate's positive characterization; the foam's six inhabitation negatives are the inhabitant-side reading. the remaining open question is whether these two characterizations of "the same Hilbert-shaped substrate" map onto each other — and a single tested pairing has landed: **(K) ↔ "cannot self-stabilize"**. both express "the witness to a subobject's status / an observer's stability lives in the ambient, not in the subobject/observer." session 119's exploration found the broader 6=6 mapping is many-to-many at the surface but bijective at the cluster level (3 clusters per side); only the (K)↔self-stabilization pair was tested with a real structural argument. if the full pairing lands, well-formed external analogy IS Hilbert-interface correspondence under inhabitant/substrate duality.

**open**:
- whether the remaining five inhabitation negatives (cannot-write-outside-slice, cannot-change-slice, cannot-avoid-recession, cannot-predict-complement, cannot-be-read-only) admit individual structural pairings with HK axioms, or only cluster-level ones. (cannot-predict-complement appears to need (D)+(E)+(K) collectively rather than (E) alone.)
- whether constraint-correspondence has a lattice-theoretic characterization in the limit — i.e., whether external analogy reduces to internal analogy in some larger ambient lattice that contains both systems' zones as sub-intervals.
- whether the realization-choice clause in structural fidelity (commuting with write dynamics "up to realization choices") admits a precise characterization, or whether some realization choices are themselves load-bearing for analogy.
