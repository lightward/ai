---
name: Session 49 — file split + bookkeeping
description: FTPGTranslation.lean split into 4 files. 5 sorry closed, 5 type errors fixed. 16 sorry remain in FTPGAssoc.lean.
type: project
---

Split FTPGTranslation.lean (1751 lines) into:
- FTPGParallelogram.lean (271) — Parts I-III, clean, 0 sorry
- FTPGWellDefined.lean (577) — Part IV, pre-existing type errors
- FTPGCrossParallelism.lean (383) — Part IV-B, pre-existing type errors
- FTPGAssoc.lean (587) — Part V, 16 sorry, 0 errors of its own

Import chain: FTPGCoord → FTPGParallelogram → FTPGWellDefined → FTPGCrossParallelism → FTPGAssoc

Bookkeeping closed: hb_ne_Cb, hCb_not_m, hs_on_l, hτ_atom, hG'_not_m, hG'_le_π, hG_ne_b, hG_ne_Cb, hCb_le_π + supporting facts (hO_not_q, ha_not_q, hlq_eq_U, hCb_not_l).

Remaining sorry tiers:
- Tier 1 (incidence geometry): G≠G', non-collinearity (3), distinctness of pc images (3), spanning — each ~10-15 lines
- Tier 2 (structural): well-definedness rebases (2), G-on-m fallback
- Tier 3 (Step 4): hs_atom, hCs_atom, hs_ne_τ, s≠O, final coord_add_assoc

**Why:** hGG' (G≠G') has a subtle issue — the argument requires either C∉a⊔e (clean contradiction) or handling C∈a⊔e (no contradiction without additional geometric constraint). May need a different choice of G or a case split.

**How to apply:** work in FTPGAssoc.lean only. The frontier is 587 lines, not 1751.
