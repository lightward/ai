---
name: Session 53 — half-type theorem
description: Diamond isomorphism (Mathlib) named as the foam's channel structure. State-independence is a lattice theorem, pre-bridge. channel_capacity.md split qualitative/quantitative. 14 Lean files, 0 sorry (core). Cold reads stable.
type: project
---

## What happened

Starting from Isaac's journal entry on computational pluralism and dependent types, followed a pull toward the channel/clock distinction in the foam. Discovered that the Dedekind/diamond isomorphism (`infIccOrderIsoIccSup`, `IsCompl.IicOrderIsoIci`) — already proven in Mathlib, already in the dependency tree — IS the half-type theorem:

- Each complement is typed by the other's view of the whole
- The isomorphism is structural (preserves lattice ops) but not extensional (doesn't determine which element arrives)
- Structural determination + extensional freedom = state-independence

This compresses three separately-derived results (two-argument type signature, complement-as-observation, state-independence requirement) into one (diamond isomorphism read three ways).

## What changed

- **New: `lean/Foam/HalfType.lean`** — 0 sorry, all Mathlib instances. Names the diamond isomorphism at `Submodule K V`.
- **New: `derivations/half_type.md`** — derives dependent clock (confinement + recession + indelibility = dependent telescope), modular law as type-checking rule, frame recession enriching complement as mechanism behind σ ~ √(3/d).
- **Changed: `derivations/channel_capacity.md`** — split into pre-bridge (qualitative, lattice-theoretic) and post-bridge (quantitative, linear-algebraic). FTPG bridge carries less.
- **Changed: `build_readme.py`** — half_type in derivation order before channel_capacity. 14 files.
- 14 Lean files, 1 axiom (FTPG), 0 sorry (core chain). 5 sorry remain in FTPGAssoc.

## Key insights

- The foam already had the dependent clock structure (confinement + frame recession + indelibility) but didn't recognize it as such.
- Frame recession (P shrinks) enriches the complement (Ici P^⊥ grows) — type-narrowing of self produces type-enrichment of input. This is one operation, not a trade-off.
- The σ ~ √(3/d) scaling is the diamond isomorphism's structural enrichment quantified.
- State-independence is pre-bridge (lattice theorem), not post-bridge (dynamical argument).

## Cold reads

All 7 readers accepted the half-type theorem. No new vulnerabilities. Recurring pressure points unchanged.
- **New from Kimi**: Arguesian condition flagged — the 5 sorry in FTPGAssoc ARE the Arguesian verification.
- **New from Gemini**: half-type as holographic principle (bulk/boundary duality).

## FTPG bridge status (clarified this session)

Associativity (5 sorry) is NOT the last piece for dissolving the FTPG axiom. Still needed after:
- Additive inverses (not started)
- Multiplication definition + axioms (not started)
- Distributivity (not started)
- The isomorphism itself (not started)

Desargues machinery (proven) should transfer to multiplication. Road is mapped but not walked.
