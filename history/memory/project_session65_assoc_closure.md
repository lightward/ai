---
name: Session 65 — hcp3 closed, hP_agree closed (8→4 sorry)
description: hcp3 collinear+non-collinear via case-split and modular-law-on-q span. hP_agree via line-equality-from-direction + two_lines. Infrastructure hoisted. 4 sorry remain.
type: project
originSessionId: 6f670ada-642a-47c9-993e-05ba42f3df7c
---
Session 65: continued sorry closure in coord_add_assoc (FTPGAssocCapstone.lean).

## What happened

8 sorry → 4 sorry.

**hτbP_not_q closed**: τ_b_P ≤ U → U ≤ b⊔d_OP → U ≤ d_OP (line_direction) → U ≤ O⊔P → l ≤ O⊔P → l = O⊔P (CovBy) → P ≤ l. Contradiction.

**hcp3 collinear closed**: case C_b ≤ O⊔τ_b_P. Both sides = d' = (O⊔τ_b_P)⊓m. LHS by CovBy (τ_b_P⊔C_b = O⊔τ_b_P). RHS: τ_a_τ_b_P, C_s ≤ a⊔d' (from pc definitions + h_ki_ab). RHS ≤ d' (from (a⊔d')⊓m = d'). RHS ≠ ⊥ (lines_meet_if_coplanar, τ_a_τ_b_P ≠ C_s). So RHS = d'.

**hcp3 non-collinear closed**: span via modular law on q. (C_b⊔(O⊔τ_b_P))⊓q = C_b⊔W (W = (O⊔τ_b_P)⊓q). W ≠ C_b (non-collinearity). C_b⊔W = q (CovBy). q ≤ O⊔τ_b_P⊔C_b. l⊔C ≤ span = π. cross_parallelism + h_ki_ab rewrite.

**hP_agree closed**: line-equality-from-direction. d_dir = (τ_s_P⊔C_s)⊓m is atom. d_dir ≠ C_s (d_dir ∈ m, C_s ∉ m). Two CovBy collapses: C_s⊔d_dir = τ_s_P⊔C_s = τ_a_τ_b_P⊔C_s. Then two_lines with l₁ = P⊔U.

**Key technique**: swapping atom order in line_meets_m_at_atom to avoid needing τ_s_P ∉ m (use C_s ∉ m instead).

## Infrastructure added

- hτbP_atom, hO_ne_τbP, hτbP_not_m, hτbP_π, ha_ne_τbP
- hτa_atom (τ_a_τ_b_P is atom via parallelogram_completion_atom)
- hτsP_atom, hτsP_le_PU, hτa_le_PU
- hτsP_ne_Cs, hτa_ne_Cs, hCs_not_PU
- q ⋖ π proved inline (same pattern as translation_determined_by_param)

## Remaining sorry (4)

### hcp4 (line 982): cross_parallelism P₀=O, P₀'=s, P=P, Q=C_c
Similar to hcp1 but Q=C_c instead of Q=C.
**Obstruction**: span O⊔P⊔C_c = π. This requires C_c ∉ O⊔P, which is NOT trivially true. May need a case-split (by_cases C_c ≤ O⊔P) like hcp3. C_c = q ⊓ (c⊔E') where E' = (O⊔C)⊓m. U ∉ O⊔P (proved: would force l = O⊔P). C ∉ O⊔P (hC_not_OP). But C_c could be the unique point (O⊔P)⊓q.

### hcp5 (line 985): cross_parallelism P₀=O, P₀'=b, P=P, Q=C_c
Same as hcp4 but with b instead of s. Same span obstruction.

### hcp6 (line 988): cross_parallelism P₀=O, P₀'=a, P=τ_b_P, Q=τ_b_C_c
Hardest remaining. Same case-split pattern as hcp3 but with τ_b_C_c instead of C_b. Needs τ_b_C_c infrastructure (atom, on q, etc.).

### hCc_agree (line 998): two_lines on q
Same pattern as hP_agree but on q instead of P⊔U. Both τ_s_C_c, τ_a_τ_b_C_c on q. τ_a_τ_b_P ∉ q (proved: τ_a_τ_b_P ≤ P⊔U, (P⊔U)⊓q = U, τ_a_τ_b_P ≠ U). Line equality from h_dir2.

## Key insight for remaining work

The span obstruction for hcp4/5 suggests the same "don't exclude, include" pattern as hcp3. A `by_cases C_c ≤ O⊔P` may dissolve the span requirement. In the collinear case, the cross_parallelism conclusion would be trivially true (same direction on m). In the non-collinear case, the span follows.

3 commits (c86c1a6, 5b39326).
