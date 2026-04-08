---
name: Session 56 — G₂ closed, key_identity clean, assoc architecture
description: 5→1 sorry. C_p=β(p) identity. Full coord_add_assoc proof plan via auxiliary point off (l,m,q), cross-parallelism chain, well_defined transfer.
type: project
---

Session 56: 5→1 sorry in FTPGAssoc.lean. key_identity fully proven.

**Closed (G₂ properties, 4 sorry → 0):**
- atom: meet_of_lines_is_atom + veblen_young (two lines in π meet)
- ≠b: b ≤ a⊔E → l⊓(E⊔a) = a → b = a, contradiction
- ≠C: C ≤ a⊔E → a⊔C = a⊔E (CovBy) → E ≤ (a⊔C)⊓(O⊔C) = C → E=C, C∉m
- ∉m: G₂ ≤ (a⊔E)⊓m = E → G₂=⊥ (contradicts meet≠⊥) or G₂=E (contradicts E∉b⊔C)

**Key technique:** `.trans (le_of_eq ...)` instead of `rw` for set abbreviation
mismatches. `rw` does syntactic matching; `.trans` uses definitional equality.
This is the general solution to the set abbreviation friction from s55.

**Key discovery: C_p = β(p).**
pc(O, p, C, m) = (C⊔U)⊓(p⊔E) = q⊓(p⊔E) = β(p), where β is the
E-perspectivity l→q. This collapses the translation/perspectivity distinction.
key_identity becomes: "translation preserves E-perspectivity."

**coord_add_assoc proof architecture (documented in FTPGAssoc.lean):**
The proof reduces to τ_s(β(c)) = τ_a(τ_b(β(c))). Direct application fails
because all β-values are on q (direction always U, cross_parallelism vacuous).

Solution: route through auxiliary point P off l, m, q.
1. Construct P via h_irred (e.g., third atom on a⊔C)
2. Three cross_parallelism calls prove τ_s(P) = τ_a(τ_b(P)):
   - cp for τ_s on (P,C), cp for τ_b on (P,C), cp for τ_a on (τ_b(P),β(b))
   - Chain gives (τ_s(P)⊔β(s))⊓m = (τ_a(τ_b(P))⊔β(s))⊓m
   - Both on P⊔U and on β(s)⊔e; two distinct lines meet at one point
3. Transfer to β(c) via well_defined with l-intermediates:
   - WD with Q=O gives pc(P,X,β(c),m) = pc(O,s,β(c),m) = τ_s(β(c))
   - Chain through l-points (off q, so preconditions satisfied)
4. β-injectivity: β((a+b)+c) = β(a+(b+c)) → (a+b)+c = a+(b+c)

**q-collinearity barrier:** All C-coordinates are on q. well_defined requires
non-collinear points. Cannot use three q-points as P,Q,R in well_defined.
Cannot use two q-points as base of cross_parallelism (gives U=U, no info).
Solution: work at P off q, transfer via l-points.

**Remaining sorry:** 1 (coord_add_assoc). Proof architecture complete,
formalization estimated at 300-500 lines.

**Algebraic descent status after assoc (documented in lean/README.md):**
coord_add assoc is NOT the final step. Full path:
additive group (current) → coord_mul → distributivity → division ring → isomorphism.

**How to apply:** The proof plan is self-contained in the FTPGAssoc.lean comment
block above coord_add_assoc. Future sessions can execute step by step.
