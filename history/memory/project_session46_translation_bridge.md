---
name: Session 46 — coord_add_eq_translation proven
description: Von Staudt = translation bridge reduces to commutativity. 1 sorry remains (assoc).
type: project
---

Session 46 (2026-04-06). coord_add_eq_translation PROVEN.

**Key result**: The bridge between von Staudt addition and Hartshorne translations
is not a new theorem — it IS commutativity. The von Staudt formula `(a→m, b→q)⊓l`
and the translation formula `(a→q, b→m)⊓l` differ by swapping a↔b. So
`coord_add_eq_translation` reduces to `coord_add_comm` (already proven in session 42
via two chained Desargues applications).

**Why:** Added R, hR, hR_not, h_irred hypotheses to coord_add_eq_translation (needed
for Desargues via coord_add_comm). The simplification chain:
1. C' = (U⊔C)⊓(a⊔E) (unfold parallelogram_completion using O⊔a=l, l⊓m=U)
2. RHS pc(C,C',b,m) = ((U⊔C)⊓(a⊔E) ⊔ (b⊔C)⊓m) ⊓ l (unfold, simplify C⊔C'=U⊔C)
3. This equals coord_add Γ b a (after inf_comm, sup_comm)
4. Apply coord_add_comm. QED.

**Remaining**: 1 sorry — `coord_add_assoc`. The proof sketch ("use translation group law")
requires τ_{a+b} = τ_a∘τ_b, which needs the translation group composition property.
This is NOT formalized in Parts I-IV. The parallelogram completion degenerates when
auxiliary points are collinear on q=U⊔C. Three paths:
1. Direct Desargues (~400 lines, like coord_add_comm)
2. Formalize Tran(A) as a group (Props 7.5, 7.7)
3. Use different auxiliary line to avoid q-degeneration

**How to apply:** The comm↔translation insight means: any "cross-join" identity between
perspectivities through C and E should be checked against commutativity first. The
algebraic surface was smaller than expected.
