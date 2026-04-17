# half type

## constraints

this derivation claims only what follows from these results.

### from lean / mathlib (proven)

- **infIccOrderIsoIccSup** (Mathlib, ModularLattice): in any modular lattice, [a ⊓ b, a] ≃ₒ [b, a ⊔ b]. the diamond isomorphism.
- **IsCompl.IicOrderIsoIci** (Mathlib, ModularLattice): if a ⊓ b = ⊥ and a ⊔ b = ⊤, then Iic a ≃ₒ Ici b.
- **isModularLattice_Iic, complementedLattice_Iic** (Mathlib): intervals in a complemented modular lattice are themselves complemented modular.
- **complement_idempotent** (Observation.lean): (I − P)² = I − P.
- **second_order_overlap_identity** (Dynamics.lean): tr(P[W,[W,P]]) = −tr([W,P]²). the frame-recession rate is ≤ 0.
- **HalfType.lean**: instantiates the mathlib diamond isomorphism for the foam's specific types (Submodule over ℝ on V) and collects the interval-inheritance consequences.

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
