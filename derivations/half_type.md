# half type

## constraints

this derivation claims only what follows from these results. any additional assumption is a bug.

### from lean (proven)

- **infIccOrderIsoIccSup** (Mathlib, ModularLattice.lean): in any modular lattice, `[a ⊓ b, a] ≃o [b, a ⊔ b]`. the diamond isomorphism. the interval below one element, measured from the meet, is order-isomorphic to the interval above the other, measured to the join.
- **IsCompl.IicOrderIsoIci** (Mathlib, ModularLattice.lean): if a and b are complements (a ⊓ b = ⊥, a ⊔ b = ⊤), then `Iic a ≃o Ici b`. everything below a is isomorphic to everything above b.
- **isModularLattice_Iic, isModularLattice_Ici** (Mathlib, ModularLattice.lean): intervals inherit modularity. the sub-lattice below (or above) any element is itself modular.
- **complementedLattice_Iic, complementedLattice_Ici** (Mathlib, ModularLattice.lean): intervals in a complemented modular lattice are themselves complemented.
- **write_confined_to_slice** (Confinement.lean): writes are confined to Λ²(P).
- **complement_idempotent** (Observation.lean): (I - P)² = I - P. the complement of an observation is an observation.
- **second_order_overlap_identity** (Dynamics.lean): tr(P[W,[W,P]]) = -tr([W,P]²). frame recession rate is non-positive.

### from other derivations

- **ground.md**: closure, partiality, indelibility. the modular law IS feedback-persistence.
- **writing_map.md**: the write is a function of (foam_state, input) — two arguments. form is algebraically determined; content requires state-independent input.
- **channel_capacity.md**: the decorrelation horizon σ ~ √(3/d) (quantitative, post-bridge).

### from mathematics (cited, not proven in lean)

- none.

## derivation

**the diamond isomorphism is the half-type theorem.** in the foam's complemented modular lattice, every observation P has a complement P^⊥ with P ⊓ P^⊥ = ⊥ and P ⊔ P^⊥ = ⊤. the diamond isomorphism (infIccOrderIsoIccSup) and its complemented specialization (IsCompl.IicOrderIsoIci) give:

Iic P ≃o Ici P^⊥

everything the observer can see (the lattice below P) is order-isomorphic to everything above the complement. the isomorphism preserves lattice operations: joins map to joins, meets map to meets. the complement isn't unstructured absence — it carries exactly the type structure of the observer's perspective, reflected.

**each half is self-sufficient.** isModularLattice_Iic and complementedLattice_Iic prove that the interval below any element is itself a complemented modular lattice — it satisfies the foam ground conditions independently. the observer's view is a complete foam in miniature. the same holds for the complement's interval (Ici). neither half needs the other to be well-formed. each is a valid ground on its own.

**the isomorphism is structural, not extensional.** IicOrderIsoIci is an order isomorphism — it preserves the lattice structure (which elements are above or below which others). it does not determine which specific element of Ici P^⊥ corresponds to the observer's current state. the observer knows the *type* of what can arrive from the complement (the lattice structure is determined) but not *which value* will arrive (the specific element is free). structural determination with extensional freedom IS state-independence (channel_capacity.md). the complement's type is fixed; its content is the channel.

**three results compress to one.** the writing map's two-argument type signature (channel_capacity.md), complement_idempotent (Observation.lean), and the state-independence requirement for channel capacity (channel_capacity.md) are three expressions of the diamond isomorphism:

1. two arguments: the direct decomposition P ⊔ P^⊥ = ⊤ gives two components, each carrying the other's type structure.
2. complement is an observation: the complement's interval is a complemented modular lattice (complementedLattice_Ici), so P^⊥ is a valid ground for observation.
3. state-independence: the isomorphism fixes structure but not content. what arrives from the complement is typed but free.

the single statement: **in a complemented modular lattice, every element's complement is a structurally isomorphic, self-sufficient ground whose content is undetermined.** the three results are three readings of this one fact.

**the dependent clock.** write_confined_to_slice says each write lives in Λ²(P). second_order_overlap_identity says the frame can only recede: the overlap change is -‖[W,P]‖², non-positive. indelibility (ground.md) says writes cannot be undone. combining:

each write may change P. each change to P changes the diamond isomorphism — the map Iic P ≃o Ici P^⊥ updates. the *type* of what can arrive from the complement changes with each tick. the space of legal next-writes (confined to Λ²(P_new)) depends on all prior writes. this is a dependent telescope: each tick's type is determined by the accumulated history of ticks.

the guard is the modular law. path-independence of composition (ground.md: modularity IS feedback-persistence) ensures that the telescope is well-typed regardless of evaluation order. the modular law doesn't just check types — it IS the type-checking rule for the dependent clock.

**frame recession enriches the complement.** as P recedes (shrinks), Iic P contracts — the observer's direct view narrows. but IicOrderIsoIci means Ici P^⊥ expands in lockstep — the typed structure of the complement grows. the observer sees less; the type-richness of what can arrive from outside increases.

this is the mechanism behind σ ~ √(3/d). higher ambient dimension means P is a smaller fraction of the whole, which means Ici P^⊥ is richer, which means the complement carries more typed structure, which means decorrelation is faster (more independent directions available), which means more channel capacity. the scaling law is the diamond isomorphism applied to a receding frame.

**type-narrowing of self produces type-enrichment of input.** this is not a trade-off — it is a single operation (the diamond isomorphism) read from two sides. the observer's loss of direct scope and the channel's gain of typed capacity are the same lattice-theoretic event. the half-type theorem says they cannot come apart.

## status

**proven** (in lean / mathlib, zero sorry):
- the diamond isomorphism (infIccOrderIsoIccSup)
- the complemented specialization (IsCompl.IicOrderIsoIci)
- intervals inherit modularity and complementedness
- writes confined to observer's slice
- complement of an observation is an observation
- frame recession is non-positive

**derived** (in this file):
- the diamond isomorphism IS the half-type theorem
- each half is a self-sufficient foam ground
- structural determination with extensional freedom IS state-independence
- three results (two-argument signature, complement-as-observation, state-independence) compress to one
- the dependent clock: confinement + recession + indelibility form a dependent telescope
- the modular law IS the type-checking rule for the dependent clock
- frame recession enriches the complement (the mechanism behind σ ~ √(3/d))
- type-narrowing and channel-enrichment are one operation read from two sides
