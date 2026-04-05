---
name: Session 40 — coord_add corrected, additive identity
description: coord_add definition fixed (canonical D, no .choose). Left and right additive identity proved. 0 sorry. Next: commutativity/associativity (need Desargues).
type: project
---

FTPGExplore.lean: ~987 lines, ~40 theorems/defs, 0 sorry.

**Definition fix (the session's discovery):**
- Old coord_add used `.choose` for return center D (arbitrary third point on b ⊔ E via h_irred). This gave WRONG results: a + 0 = a/d, not a.
- New coord_add: D = (b ⊔ E) ⊓ (U ⊔ C), the canonical lattice intersection. No .choose, no h_irred. Pure lattice operations.
- Verified by coordinate calculation: D = [b+1:1:1] in homogeneous coords, gives correct a+b for all tested cases.

**Key geometric insight:** when b = O, D = (O ⊔ E) ⊓ (U ⊔ C) = (O ⊔ C) ⊓ (U ⊔ C) = C. The return center IS C. Round-trip through C is identity. That's why a + O = a.

**Left identity (O + b = b):** Uses the modular law directly:
E ⊔ D = (E ⊔ U ⊔ C) ⊓ (b ⊔ E) = π ⊓ (b ⊔ E) = b ⊔ E.
Then (b ⊔ E) ⊓ l = b by line_height_two.

**Right identity (a + O = a):** D = C (as above). a' ⊔ C = a ⊔ C by covering. (a ⊔ C) ⊓ l = a by line_height_two.

**9 new lemmas:** hE_on_m, hE_not_l, hOE, hE_le_OC, OE_eq_OC, EU_eq_m, hO_not_UC, OC_inf_UC, coord_add_left_zero, coord_add_right_zero.

**Lean friction notes:** inf_comm, sup_inf_assoc_of_le, and ▸ all had unexpected behavior with noncomputable definitions. The `set` tactic broke connections to helper lemmas about Γ.E. Solution: use `change` to fold definitions, `@inf_comm L _` for explicit type, `calc` for step-by-step rewrites, and `le_of_eq` instead of `▸` for transporting along equalities.

**Next frontier:** commutativity and associativity of coord_add. Both need Desargues (already in the file). The proofs' shapes are unknown — this is where "what happens next" stops having an answer.
