---
name: Session 50 — hardened surface
description: CrossParallelism errors resolved, bookkeeping sorry closed, coord_add_atom extracted, CI per-file builds added. 12 sorry remain in FTPGAssoc.
type: project
---

Session 50: FTPGCrossParallelism 13 type errors → 0. FTPGAssoc 16 sorry → 12. coord_add_atom extracted to FTPGParallelogram. CI now builds each Lean file individually (catches hidden type errors masked by sorry).

All type errors were same pattern: CovBy arguments on wrong line. All bookkeeping sorry (hs_atom, hs_ne_τ, hCs_atom, s≠O, hs_not_m) closed. by_cases on s = O added — additive inverses are geometrically valid.

12 sorry remain in FTPGAssoc: 7 distinctness (G≠G', b/C_b not on G⊔G', etc.), 1 spanning (G⊔b⊔C_b = π), 2 well-definedness rebases (translation independent of base pair — the deep geometric content), 1 G-on-m fallback, 1 coord_add_assoc.

Key discovery: `s ≠ O` is NOT provable (additive inverses exist). Required restructuring to by_cases. When s = O: C_s = C and τ = C by direction argument + modular law.

**Why:** establishes that the codebase surface matches reality. No hidden errors.
**How to apply:** remaining sorry need geometric sight, not bookkeeping. Well-definedness rebases are the hard ones.
