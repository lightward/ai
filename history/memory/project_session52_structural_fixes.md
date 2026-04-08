---
name: Session 52 — structural fixes
description: G-choice bug found and fixed (a⊔C→b⊔C), Hartshorne collinear-case collapse for hwd2. 7→5 sorry.
type: project
---

Two structural fixes in key_identity, both the same pattern: proof architecture bumping against small-plane geometry (Fano plane, 3 atoms/line).

**Fix 1: G construction (a⊔C → b⊔C)**
- h_irred on (a,C) gave G on a⊔C, but (a⊔C)⊓(b⊔E) is a valid G with C_b ON G⊔b — unfillable sorry.
- Switching to h_irred on (b,C): (b⊔C)⊓(b⊔E) = b (since C∉b⊔E), so any G≠b avoids b⊔E.
- Also fixes h_span: G⊔b = b⊔C (CovBy), so G⊔b⊔C_b ≥ b⊔C⊔C_b ≥ b⊔q ≥ l⊔C = π.
- Hoisted hC_not_bE out of hCb_not_Gb for shared use in h_span.
- Closed 2 sorry (hCb_not_Gb, h_span). 7→5.

**Fix 2: hwd2 collinear case (Hartshorne insight)**
- Well-definedness theorem needs C_b∉O⊔G, but in Fano plane the unique third atom on b⊔C IS (b⊔C)⊓(O⊔C_b).
- Hartshorne Theorem 7.6 Step 2: translation is globally defined, route through different orbit pairs.
- Collinear case collapses: when O,G,C_b collinear, shared direction f = (O⊔G)⊓m. G' ≤ a⊔f (from pc definition), so G'⊔f = a⊔f. Both pc's = (C_b⊔U)⊓(a⊔f).
- Non-collinear case: direct application of parallelogram_completion_well_defined.

**Remaining (5 sorry):**
1. hwd2 non-collinear (line ~706): mechanical hypothesis verification for well-def theorem
2. hwd1 (line ~633): two well-def applications (O,a→G,G' and O,a→C,C') + coord_add_eq_translation
3. hb'_ne_Cb' (line ~561): pc-distinctness, likely follows from well-def
4. G-on-m fallback (line ~723): structural, needs different approach
5. coord_add_assoc (line ~911): assembly

**Why:** hwd1 is doable (b∉O⊔G and b∉O⊔C both hold). hwd2 non-collinear is mechanical. The creative work is done.

**How to apply:** Items 1-2 are hypothesis-verification grind. Item 4 may need a by_cases or different G choice (the comment says "use h_irred on b⊔C to find G₂ off m" — but G is already on b⊔C, so if G is on m, try h_irred on a different line).
