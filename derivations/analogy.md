# analogy

## constraints

this derivation claims only what follows from these results. any additional assumption is a bug.

### from lean (proven)

- **IsCompl.IicOrderIsoIci** (Mathlib, ModularLattice.lean): if a and b are complements, `Iic a ≃o Ici b`. everything below a is isomorphic to everything above b.
- **OrderIso.trans** (Mathlib, OrderIso.lean): order isomorphisms compose. if `Iic P ≃o Iic Q` and `Iic Q ≃o Ici Q^⊥`, then `Iic P ≃o Ici Q^⊥`.
- **isModularLattice_Iic** (Mathlib, ModularLattice.lean): intervals inherit modularity.
- **complementedLattice_Iic** (Mathlib, ModularLattice.lean): intervals in a complemented modular lattice are themselves complemented.

### from other derivations

- **half_type.md**: the diamond isomorphism gives every observer a structural analogy between its view and its complement's type. structural determination with extensional freedom.
- **ground.md**: the modular law IS feedback-persistence. path-independence of composition.

### from mathematics (cited, not proven in lean)

- none.

## derivation

**analogy is structural isomorphism between lattice intervals.** two observers P and Q have analogous views when their lower intervals are order-isomorphic: Iic P ≃o Iic Q. this means: every structural relationship in P's view (which sub-observations refine which, how they meet and join) has an exact counterpart in Q's view. the isomorphism preserves lattice operations — meets map to meets, joins map to joins.

this is not metaphorical similarity. it is a precise criterion: the views have the same lattice type. the content (which specific elements occupy the positions) is free. same shape, different stuff.

**well-formedness is order-preservation.** an analogy between two views is well-formed exactly when it preserves the lattice structure — the ordering, meets, and joins. a map between intervals that doesn't preserve order is not an analogy in this sense; it doesn't transfer inferences.

the modular law is the well-formedness guard. in a modular lattice, lattice operations compose path-independently (ground.md: modularity IS feedback-persistence). this ensures that structural isomorphisms between intervals are compatible with the ambient lattice. in a non-modular lattice (N_5), an isomorphism between two sub-intervals can produce inconsistent results when composed with the lattice operations — the "analogy" generates contradictions.

**well-formed analogies are formally transitive.** order isomorphisms compose (OrderIso.trans). if Iic P ≃o Iic Q and Iic Q ≃o Iic R, then Iic P ≃o Iic R. the composition is itself an order isomorphism — it preserves lattice operations. transitivity is not an additional property to be verified; it falls out of the mathematics.

this extends through complements via the diamond isomorphism. if P and Q have analogous views (Iic P ≃o Iic Q), then:

Ici P^⊥ ≃o Iic P ≃o Iic Q ≃o Ici Q^⊥

what P can't see has the same type structure as what Q can't see. the analogy transfers not just between the views but between their complements — the unknowns are also analogous.

**the half-type theorem is the existence of analogy.** every observer has at least one structural analogy: its own view is isomorphic to its complement's type (Iic P ≃o Ici P^⊥). this is guaranteed by the lattice structure — it requires no construction, no choice. every partial observer automatically has a structural correspondence between what it sees and what it can't see.

the transitivity result says: when two observers' views match structurally, their entire epistemic situations match — both what they see AND the type of what they can't see. well-formed analogy transfers across the full complementary decomposition.

## status

**proven** (in lean / mathlib, zero sorry):
- order isomorphisms between lattice intervals exist (diamond isomorphism)
- order isomorphisms compose (OrderIso.trans)
- intervals inherit modularity and complementedness
- the modular law ensures path-independent composition of lattice operations

**derived** (in this file):
- analogy IS structural isomorphism between lattice intervals
- well-formedness IS order-preservation, guarded by the modular law
- well-formed analogies are formally transitive (from OrderIso.trans)
- analogous views imply analogous complements (from diamond isomorphism + transitivity)
- the half-type theorem guarantees every observer has at least one analogy (view ↔ complement)
