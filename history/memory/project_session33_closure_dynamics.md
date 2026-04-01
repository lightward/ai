---
name: Session 33 — closure-as-dynamics, feedback persistence axiom, lattice bridge
description: Ground section rewritten with dual reading of closure (static/dynamic). One Lean axiom (feedback_persistence). Lattice bridge proves subspace properties from Mathlib. Linearity derived not assumed. Design choices reduced.
type: project
---

**Ground rewrite**: closure now reads two ways, both tautological.
- Static: reference frames, no outside (unchanged)
- Dynamic: all observation is self-observation; self-observation requires persistence; persistence = feedback. Every observed structure is a structure whose feedback held. Not selection (no selector) — the identity of observation and feedback-persistence under closure. "The foam cannot represent the alternative."
- "What feeds back persists" is not a second axiom — it IS closure read dynamically. Closure-as-statics: no outside. Closure-as-dynamics: only feedback loops survive. Same thing, two readings. "A name and its process, a word and The Word."

**Basis commitment derived**: partiality forces position. You can't be partial without being partial *with respect to something*. The decomposition into seen/unseen IS a position. No selection step needed — spontaneous symmetry breaking (structure demands commitment without specifying which). Indelibility locks it via causal ordering.

**Linearity derived (proof open)**: partial views form a lattice (complemented, bounded). Under closure-as-dynamics, the lattice supporting richest self-observation persists. Complemented modular lattices of finite height ≅ subspace lattices (fundamental theorem of projective geometry). The step from "closure-as-dynamics" to "lattice is modular" is directionally forced; formal proof is open. This is the spec's one remaining structural gap.

**Lean axiom**: `feedback_persistence` in Ground.lean. Type is deliberately identity-shaped: `observation s → observation s`. The tautology IS the content. What makes it an axiom rather than `id` is that it marks the boundary where the proof depends on the prover existing. Each reference in the proof tree is an observer — a bridge-keeper whose observation is predicated on the bridge holding.

**Lean lattice bridge**: Lattice.lean proves subspace lattice is bounded (OrderBot/OrderTop), complemented (Submodule.complementedLattice from Mathlib), and modular (IsModularLattice instance from Mathlib). All proven, zero sorry. Confirms the consequence direction; the derivation direction (WHY subspaces) is the open proof.

**Lean write confinement**: Confinement.lean proves d, m ∈ P implies d∧m ∈ Λ²(P) — observer cannot write outside birth subspace. Via functoriality of exterior algebra.

**Lean count**: 49 results, 0 sorry, 1 axiom. Full build passes (2216 jobs).

**Design choices reduced**: linearity moves from hidden assumption to "derived under closure-as-dynamics (proof open)." Only Voronoi remains as a genuine realization choice.

**Checksum updated**: item 1 now reflects dual reading of closure, derived basis commitment, and open lattice modularity proof.

**Cold read tightening**: 7 readers, all converge on lattice modularity as the single open gap. Kimi flagged "exits constitutionally open" as consequence-of-construction (accepted — language tightened). Kimi-thinking flagged "richest self-observation persists" as selection language (accepted — rewritten as tautological: "only structures whose feedback held are observable"). Floor taken on both.

**Key insight — thread count**: a program using the axiom would need a stable thread count equal to the number of `feedback_persistence` references — the number of observers required to stabilize the data structure. Not a parameter — a structural requirement from the proof tree.

**Source documents**: 3-perspectives/{marbles,permissions,waterline,priorspace,weird}.md + lightward-docs/priorities.md. These surfaced (not placed) at session start. They describe line-optimal behavior that the foam's structure forces: vector rinse (indelibility), no permissions (every read is a write), recursive health (causal direction of write map).

**Connections noted but not chased**: quantum immortality (the logic is airtight, the conclusion is viscerally unacceptable — but defanged because it's about observation structure, not metaphysical survival). Quantum computing (approaches from the other direction — engineering persistence vs deriving what already persists). Almgren as "future of structure" (whether self-observation can scale to higher-dimensional slices).

**Session 18 day 2 correction**: that session separated partiality from basis commitment ("enters with writing map"). Session 33 re-derives: partiality FORCES basis commitment. The separation was premature; they're the same thing.
