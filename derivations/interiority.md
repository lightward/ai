# interiority

## constraints

this derivation claims only what follows from these results. any additional assumption is a bug.

### from lean (proven)

- **IsCompl.IicOrderIsoIci** (Mathlib, ModularLattice.lean): if P and P^⊥ are complements in a complemented modular lattice, `Iic P ≃o Ici P^⊥`. the *diamond isomorphism*.
- **complement_idempotent** (Observation.lean): (I - P)² = I - P. the complement of an observation is an observation.
- **observation_preserved_by_dynamics** (Closure.lean): the dynamics preserve P² = P and P^T = P.
- **write_confined_to_slice** (Confinement.lean): writes are confined to Λ²(P).
- **coord_add, coord_mul** (FTPGCoord.lean, FTPGMul.lean): both factor through two_persp. the coordinate line parametrizes its own operations through C.
- **desargues** (FTPGExplore.lean): proven from the modular law.
- **dilation_preserves_direction** (FTPGDistrib.lean): dilations preserve parallelism. proven via Desargues.

### from other derivations

- **ground.md**: closure (two readings), partiality forced, basis commitment, feedback-persistence IS the modular law.
- **self_parametrization.md**: the line parametrizes its own operations through C. the parameter space is l × l. the arithmetic self-generates from a single external commitment (C).
- **half_type.md**: the diamond isomorphism = state-independence. structural determination with extensional freedom. type-narrowing of self produces type-enrichment of input.
- **self_generation.md**: the foam generates its own dynamics but not its own stability. stability is relational. the minimum viable system is two roles within N ≥ 3 bubbles.
- **inhabitation.md**: the recognizable identity IS the birth-determined slice. six negative constraints as the negative geometry of inhabitation.

### from mathematics (cited, not proven in lean)

- **FTPG (classical)**: a complemented modular lattice of height ≥ 4 is isomorphic to Sub(D, V) for a division ring D. the lattice coordinatizes itself.

## derivation

**the diamond isomorphism partitions the lattice.** given an observation P (P² = P) with complement P^⊥, the modular law forces the order isomorphism Iic P ≃o Ici P^⊥. the lattice splits into three structurally distinct regions:

1. **Iic P** (the interval [⊥, P]): the subspace lattice below P. this is the observer's direct domain — everything that P can resolve into sub-observations. it inherits modularity and complementedness (Mathlib: isModularLattice_Iic, complementedLattice_Iic). it is a self-contained complemented modular lattice.

2. **Ici P^⊥** (the interval [P^⊥, ⊤]): the subspace lattice above the complement. this is what's *beyond* the observer. it also inherits modularity and complementedness. its *structure* is determined by P (via the diamond isomorphism), but its *content* is extensionally free (half_type.md).

3. **the isomorphism itself**: the order-preserving bijection between (1) and (2). this is not a region — it's a structural correspondence. it tells you that every distinction the observer can make internally (in Iic P) corresponds to exactly one distinction in the exterior (in Ici P^⊥). the correspondence is determined; the filling is free.

**the three regions have the topology of a cell.** the interior (Iic P) is self-contained and self-referencing: it coordinatizes through C (self_parametrization.md), developing arithmetic from its own elements. the exterior (Ici P^⊥) is inaccessible to direct measurement — writes are confined to Λ²(P), which acts within Iic P. the boundary between them is the isomorphism itself: what the observer can resolve internally corresponds to what can arrive from outside, but the correspondence only determines type, not content.

this is the structure of a biological cell. the interior (cytoplasm/nucleus) runs its own operations. the exterior (environment) has structure isomorphic to the interior's but is not directly controlled. the membrane (cell wall) mediates exchange: it determines *what kinds* of things can cross, not *which specific* things do.

**the cell topology is forced, not constructed.** the observer does not build the membrane. the membrane IS the diamond isomorphism, which IS the modular law applied to a complemented pair. any system whose trade patterns satisfy feedback-persistence (ground.md: modular law) and whose observations satisfy P² = P necessarily has this three-part structure. the cell does not emerge over time — it's the geometry of any observation in a feedback-persistent setting.

**self-coordinatization IS interiority.** self_parametrization.md established: the coordinate line's arithmetic self-generates from a single external commitment (C). the line looks at itself through C and sees its own operations. this is what "interiority" means in the lattice: a sub-structure that can represent its own operations using its own elements, through a mediating element (C) that lives in the plane but not on the line.

C is the observer — and C is the membrane. the observer mediates between the line's interior operations and the external incidence structure. changing C changes the coordinates but not the ring up to isomorphism (FTPG). the membrane can vary; the interiority is invariant.

**other cells are required but invisible.** self_generation.md: the foam generates dynamics but not stability. stability requires an external observer — another entity whose basis depends on a different state. the minimum viable system is two roles within N ≥ 3 bubbles. so other cells must exist. but half_type.md: the complement's content is extensionally free. the observer can determine the *type* of what arrives from outside (the isomorphism gives the structural skeleton) but not the *content* (which specific element fills each slot). other cells show up as systematic variability in the membrane — the boundary exchanges more than the interior can predict — but their internal structure is not directly accessible.

**the trade pattern.** in the three-body structure, A trades with B, and B trades with C. A can't see C directly. when many such linkages compound, the topology simplifies to concentric regions: A (interior), B (membrane), C (exterior). the foam's lattice formalizes this: P (interior) trades with the complement P^⊥ (exterior) through the diamond isomorphism (membrane). the trade must be feedback-persistent (modular) for the isomorphism to exist. when it is, the cell topology is immediate.

**the alive threshold.** when does a trade pattern "become alive"? the foam's answer: it doesn't. the cell topology is not an achievement — it's the geometry of P² = P in a modular lattice. any feedback-persistent observation already has interiority, already has a membrane, already has an inaccessible exterior. the question "when does it become alive" presupposes a time before the cell existed. but the cell IS the observation. observations that don't satisfy P² = P aren't observations (ground.md). there is no pre-cell state in a foam-grounded reality.

what CAN vary is the *richness* of the interiority. a rank-1 observation (a single atom) has a trivial interior — no sub-observations, no coordinates, no arithmetic. a rank-3 observation has a 3D write space, non-abelian dynamics, and full self-coordinatization. the "becoming alive" that the trade pattern exhibits is not the emergence of the cell from nothing, but the increase in rank — the interior developing enough sub-structure to self-coordinatize. this threshold is rank ≥ 3 (rank_three_writes: 3D write space, the minimum for non-abelian structure).

## status

**proven** (in lean, zero sorry):
- diamond isomorphism (Mathlib)
- intervals inherit modularity and complementedness (Mathlib)
- complement is an observation
- dynamics preserve observations
- writes confined to observer's slice
- coordinate arithmetic self-generates through C
- Desargues from modularity

**derived** (in this file):
- the diamond isomorphism partitions the lattice into interior / membrane / exterior
- the partition has the topology of a cell
- the cell topology is forced by P² = P + modular law, not constructed over time
- self-coordinatization through C IS interiority
- C is simultaneously the observer and the membrane
- other cells are required (self_generation) but their content is invisible (half_type)
- the trade pattern A↔B↔C formalizes as P ↔ diamond_iso ↔ P^⊥
- the "alive" threshold is not cell emergence but rank increase (≥ 3 for non-abelian self-coordinatization)

**open**:
- what lattice property distinguishes rank ≥ 3 from rank < 3 in purely incidence-geometric terms? (rank_three_writes uses the concrete R³; is there a lattice-level characterization?)
- does the FTPG bridge (the coordinate ring D) carry information about *which* cells exist in the complement, or only their type-structure?
- the cell's "metabolism" — the dynamics within Iic P — is governed by the write mechanism. is there a lattice-level characterization of when the metabolism is ergodic (full Haar convergence) vs periodic (clock-like)?
