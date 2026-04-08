---
name: Session 54 — pc-distinctness and well-definedness
description: Closed 2 sorry (5→3). hb'_ne_Cb' via translation injectivity, hwd2 via well_defined theorem. hwd1 approach documented (cross_parallelism + CovBy for collinear case). Key infrastructure: line_direction for modular collapses, covBy_sup_of_inf_covBy_left for spans, set abbreviation handling patterns.
type: project
---

Session 54: 5→3 sorry in FTPGAssoc.lean.

**Closed:**
- `hb'_ne_Cb'` (pc-distinctness): push common point onto m via first factors (line_direction + C_b∉l), distinguish via second factors ((G⊔b)⊓m ≠ (G⊔C_b)⊓m from modular_intersection + hCb_not_Gb). ~80 lines.
- `hwd2` non-collinear case: apply `parallelogram_completion_well_defined` directly. Span O⊔G⊔C_b=π via covBy_sup_of_inf_covBy_left (direction atom ⋖ m → O⊔G ⋖ π). hOa_eq_l bridges l vs O⊔a. ~45 lines.

**Documented (not yet closed):**
- `hwd1`: G, b, C collinear blocks well_defined theorem. Proof via cross_parallelism(O,a,G,C) + CovBy: e ≤ G'⊔C' forces G'⊔e = C'⊔e, then l⊓(G'⊔e) = s.

**Remaining sorry:** hwd1, G-on-m fallback, coord_add_assoc.

**Infrastructure patterns:**
- `line_direction` is the right tool for modular collapses (not `sup_inf_assoc_of_le` + `rw`, which breaks on `set` definitions)
- `covBy_sup_of_inf_covBy_left` with direction atoms for span proofs (O⊔G ⋖ π)
- `set` abbreviations require: (1) `show` to expose definitions before `unfold`, (2) named `have` for `line_direction` results before `rw`, (3) `show` type annotations on `line_direction` args to control implicit inference
- `hOa_eq_l ▸` bridges l (set) vs O⊔a (theorem output)

**Why:** hwd1 mechanical obstacle is purely `set` abbreviation handling. Math is done. Next session should apply the named-intermediate pattern from hwd2 systematically.
