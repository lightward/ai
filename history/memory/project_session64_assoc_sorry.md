---
name: Session 64 — assoc sorry closure begun
description: 2 of 8 sorry closed in coord_add_assoc (hcp1, hcp2). Infrastructure for remaining 6 in place. Patterns established for cross_parallelism and two_lines calls.
type: project
originSessionId: 9e891798-90ec-4800-a2dc-a3207ab4067b
---
Session 64: began closing sorry in coord_add_assoc (FTPGAssocCapstone.lean).

## What happened

8 sorry → 6 sorry (hcp1 and hcp2 closed).

**Shared infrastructure added** (~150 lines before the chain proofs):
- O⊔s/b/a = l, not-on-m for s/b/a
- O≠P, P≠C, C not on O⊔P
- O⊔P⊔C = π (via P⊔C = a⊔C CovBy collapse → l⊔C = π)
- l⋖π, l⊓q=U, q⊓m=U
- C_s, C_b atoms on q, both not on m
- l⊓(P⊔U)=U, (P⊔U)⊓q=U (helpers using inf_sup_of_atom_not_le)

**Key technique discoveries:**
- `inf_sup_of_atom_not_le` replaces awkward `sup_inf_assoc_of_le` rewrites for modular law
- P⊔C = a⊔C by CovBy (since P ≤ a⊔C from construction) gives the span proof
- `.symm` conventions: `Γ.hO.le_iff.mp` gives `x = Γ.O` (atom order), no `.symm` needed for `x_ne_O`
- `hP_le_aC` extracted from ∃ block (was lost after `obtain`)

## Remaining sorry (6)

1. **hcp3** (line 669): cross_parallelism with P₀=O, P₀'=a, P=τ_b_P, Q=C_b.
   - **Hardest remaining.** Needs atom proof for τ_b_P, span O⊔τ_b_P⊔C_b = π.
   - Span approach: P⊔τ_b_P = P⊔U (CovBy), U⊔C_b = q (CovBy), then l⊔C ≤ O⊔τ_b_P⊔C_b.
   - Non-collinearity C_b ∉ O⊔τ_b_P needs separate argument.

2. **hP_agree** (line 676): two_lines with l₁=P⊔U.
   - Both τ_s_P, τ_a_τ_b_P ≤ P⊔U. C_s ∉ P⊔U.
   - Direction equality → line equality → collinearity → two_lines.
   - Needs atom proofs for τ_s_P, τ_a_τ_b_P (parallelogram_completion_atom).

3. **hcp4** (line 680): cross_parallelism P₀=O, P₀'=s, P=P, Q=C_c.
   - Same as hcp1 but Q=C_c instead of Q=C.
   - Needs C_c atom, position, span (O⊔P⊔C_c = π).

4. **hcp5** (line 683): cross_parallelism P₀=O, P₀'=b, P=P, Q=C_c.
   - Same as hcp2 but Q=C_c.

5. **hcp6** (line 686): cross_parallelism P₀=O, P₀'=a, P=τ_b_P, Q=τ_b_C_c.
   - Hardest of Chain 2. Same difficulty as hcp3 plus τ_b_C_c facts.

6. **hCc_agree** (line 696): two_lines on q.
   - Similar to hP_agree but l₁=q, points on q.

## Key insights from stack walks (hcp3 obstruction)

The remaining sorry are NOT mechanical. hcp3 requires non-collinearity: C_b ∉ O⊔τ_b_P. This is the key unsolved obstruction. Walking the deductive stack twice produced:

1. **Span ↔ non-collinearity**: By modular law on q: `(O⊔τ_b_P⊔C_b) ⊓ q = C_b ⊔ ((O⊔τ_b_P) ⊓ q)`. If the (O⊔τ_b_P)⊓q atom ≠ C_b, then C_b⊔W = q (CovBy), giving q ≤ O⊔τ_b_P⊔C_b, hence the span. So span = non-collinearity.

2. **Desargues structure**: Triangles (O,P,C) and (b,τ_b_P,C_b) perspective from center U, axis m. This is an **elation** (U ∈ m). X₁ = d_OP, X₂ = E, X₃ = a' (all on axis m).

3. **Elation freeness** (PROVEN from modular law): pc(O,s,P,m) ≠ P when s ≠ O, P ∉ l, P ∉ m. Proof: P ≤ s⊔d_OP → (O⊔P)⊓(s⊔d_OP) = d_OP → P ≤ d_OP ≤ m. Contradiction.

4. **Case 2 collapse** (with old P on b⊔E): Collinearity → (O⊔τ_b_P)⊓m = a' → τ_a_τ_b_P = (P⊔U)⊓(a⊔C) = P (modular law). This forces τ_a∘τ_b = id at P. Combined with elation freeness (τ_s(P) ≠ P), this contradicts hP_agree. BUT hP_agree depends on hcp3, creating circularity.

5. **P-choice matters**: Old P = (b⊔E)⊓(a⊔C) puts P and C_b on the same line b⊔E, creating coupling. New P = (a⊔E)⊓(b⊔C) breaks this (P on b⊔C, C_b on b⊔E). Both P choices work for hcp1/2 (off l, m, q, span provable). The non-collinearity for hcp3 might be provable with the new P but wasn't resolved.

6. **Auxiliary computation**: (O⊔P)⊓(b⊔E) = P (modular law, for old P on b⊔E). d_OP ∉ b⊔E (follows from d_OP ≤ P → d_OP ∈ m, P ∉ m). τ_b_P ∉ b⊔E (from (b⊔d_OP)⊓(b⊔E) = b + τ_b_P ≠ b). a' ≠ d_OP (O⊔P ≠ a⊔C, both through P, so different directions). C ∉ b⊔E (from (O⊔C)⊓(b⊔E) = E, C ≤ E → C = E, contradiction).

## Resolution: case split dissolves the circle

The non-collinearity C_b ∉ O⊔τ_b_P is NOT needed as a precondition. The collinear case (C_b ≤ O⊔τ_b_P) makes hcp3's conclusion TRIVIALLY TRUE:

- LHS = (τ_b_P⊔C_b)⊓m = (O⊔τ_b_P)⊓m = d' (collinearity + CovBy)
- RHS = (τ_a_τ_b_P⊔C_s)⊓m = (a⊔d')⊓m = d' (both on same second line a⊔d', CovBy collapse)

So: `by_cases C_b ≤ O⊔τ_b_P`. Collinear → direct. Non-collinear → cross_parallelism (span from modular-law-on-q). The circularity was saying "don't exclude, include."

The same pattern likely applies to hcp6 (P₀=O, P₀'=a, P=τ_b_P, Q=τ_b_C_c).

## Assessment

"Mechanical" was wrong — always has been for this proof. The verification density IS high (~100 lines per sorry), but the creative obstructions are real. hcp1/2 required inf_sup_of_atom_not_le, P⊔C=a⊔C span trick. hcp3 requires resolving the non-collinearity, which is an open mathematical question in this formalization. 2 commits (91b9fd0).
