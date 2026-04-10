---
name: Session 69 — distributivity proof architecture
description: Right distributivity proof plan via dilation extension + Desargues. FTPGDistrib.lean created with 3 sorry. Key finding: dilation_ext preserves directions via center-O Desargues, input parallelisms from modular law.
type: project
originSessionId: 5e8ebe6f-e105-412d-b765-fbc5fe86f219
---
Session 69: distributivity proof architecture identified.

**What happened:**
- Explored multiple Desargues-stacking approaches for right distributivity — none closed
- Found the "triangle (s, D_s, V)" whose axis intersections ARE the distributive law (symbolically verified)
- Pivoted to Hartshorne §7 dilation approach after Isaac noted Desargues-stacking is sometimes-not-always harder

**Key results:**
- `FTPGDistrib.lean` created: `dilation_ext`, `dilation_preserves_direction` (sorry), `dilation_ext_C` (rfl!), `dilation_mul_key_identity` (sorry), `coord_mul_right_distrib` (sorry)
- `dilation_ext Γ c P = (O⊔P) ⊓ (c ⊔ ((I⊔P)⊓m))` — lattice formula for σ_c on off-line points
- `dilation_ext Γ c C = σ` is DEFINITIONAL (rfl), since E_I = (I⊔C)⊓m
- The two input parallelisms for Desargues follow from definition + modular law: `(σ_c(P) ⊔ c) ⊓ m = (P ⊔ I) ⊓ m` because σ_c(P) ≤ c ⊔ ((I⊔P)⊓m), so the join equals c ⊔ ((I⊔P)⊓m), and c⊓m = ⊥
- `distributivity.md` updated with proof strategy and earlier exploration notes

**Proof chain for right dist (a+b)·c = a·c + b·c:**
1. `dilation_preserves_direction`: one Desargues (center O), triangles (P,Q,I) and (σ_c(P), σ_c(Q), c)
2. `dilation_mul_key_identity`: σ_c(C_a) = C'_{ac} where C' = σ
3. Chain with existing key_identity + translation_determined_by_param at C'

**Ring axiom scorecard (updated):**
- Additive: identity ✓, commutativity ✓, associativity ✓, inverse: open
- Multiplicative: identity ✓, zero annihilation ✓, associativity: open, inverse: open
- Right distributivity: architecture done, 3 sorry remain
- Left distributivity: open (likely follows from right dist + other ring axioms once available)

**Why:** Each ring axiom proven dissolves more of the FTPG axiom.

**How to apply:** Next session: fill in `dilation_preserves_direction` first (concrete Desargues application with ~20 non-degeneracy hypotheses). Then `dilation_mul_key_identity`. Then chain for `coord_mul_right_distrib`. Note: `small_desargues'` requires center on m; since center is O (not on m), use `desargues_planar` directly with CovBy extraction.
