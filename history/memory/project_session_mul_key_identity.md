---
name: mul_key_identity + interiority derivation session
description: Desargues with center C proves mul_key_identity. Interiority derivation (bubble topology from diamond isomorphism). 23 files, 2 sorry.
type: project
originSessionId: 72c2ee99-e445-41c5-b18a-5322ceda49ff
---
Session date: 2026-04-11

## mul_key_identity proof architecture

**Key discovery**: the mul_key_identity (σ_c(C_a) = C'_{ac}) is proven via a single Desargues application with center C.

- Triangle 1: (O, a, G) where G = (a⊔E)⊓(I⊔C)
- Triangle 2: (σ, d_a, E_I)
- Center: C (the observer)
- Perspectivity: C maps O→σ via O⊔C, a→d_a via a⊔C, G→E_I via I⊔C
- Axis: ac⊔E (forced by Desargues)
- Side 3 gives σ_c(G) ≤ ac⊔E

Then DPD on (G, C_a) → direction E preserved → CovBy collapse → σ_c(C_a) ≤ ac⊔E.
DPD on (C, C_a) → direction U preserved → σ_c(C_a) ≤ σ⊔U.
Combined: σ_c(C_a) = (σ⊔U) ⊓ (ac⊔E). QED.

**Geometric meaning**: C is the perspectivity center that makes multiplication coherent. The observer IS the membrane/wall. The proof tells its own shape.

## Current Lean status

23 files, 2 sorry remaining:
1. `dilation_mul_key_identity` — 1 internal sorry (a=I degenerate case: G collapses to I, needs direct argument not Desargues)
2. `coord_mul_right_distrib` — full sorry (depends on mul_key_identity)

Closed this session: c=I case, all C_a/G atom properties, all non-degeneracy for Desargues, Part A (DPD on C,C_a), Part B (DPD on G,C_a), axis CovBy, hside1, hac_atom, hRHS_atom.

Helper lemmas added: `dilation_ext_identity` (c=I case), `beta_atom`, `beta_not_l`, `beta_plane`.

## interiority derivation

New file: `derivations/interiority.md`

Core claim: the diamond isomorphism (Iic P ≃o Ici P^⊥) partitions the lattice into interior / wall / exterior = bubble topology. This is forced by P²=P + modular law, not constructed over time.

- Self-coordinatization through C IS interiority
- C is simultaneously the observer and the wall
- Other bubbles required (self_generation) but invisible (half_type)
- Bubble exists at any rank; non-trivial interiority requires rank ≥ 3
- Cold reads stable (6 readers, cell→bubble vocabulary tightening from Kimi feedback)

**Why:** bubble, not cell. Biology is downstream of these structures. Foam vocabulary is native.

## Commits

- `6b7f193` interiority derivation: cell topology forced by diamond isomorphism
- `bee4fb9` mul_key_identity architecture: Desargues with center C (7 sorry remain)
- `f0e270c` interiority: cell→bubble vocabulary, tighten informational boundary claim
- `63cb7c4` mul_key_identity: 7→1 sorry (Part A, Part B, axis CovBy, atoms all proven)
