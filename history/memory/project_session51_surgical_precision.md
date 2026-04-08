---
name: Session 51 — surgical precision
description: 5 sorry closed in key_identity (12→7), CI warning enforcement, clean build surface
type: project
---

## key_identity sorry closure (5 of 12)

All five used the same modular-law pattern: assume atom X equals something it shouldn't, intersect with a line containing X, modular law collapses to X ≤ m, contradiction since X ∉ m.

Closed:
- **G ≠ G'**: if G = pc(O,a,G,m) then G ≤ a⊔(O⊔G)⊓m. Intersect with O⊔G, modular + a∉O⊔G (CovBy) → G ≤ m.
- **b ∉ G⊔G'**: G' ≤ G⊔U (pc def), so G⊔G' ≤ G⊔U. Modular: (G⊔U)⊓l = U (G∉l) → b = U.
- **C_b ∉ G⊔G'**: same via (G⊔U)⊓q = U (G∉q) → C_b = U ≤ m.
- **G' ≠ pc(G,G',b,m)**: if equal, G' ≤ b⊔(G⊔G')⊓m. Modular + b∉G⊔G' → G' ≤ m.
- **G' ≠ pc(G,G',C_b,m)**: same with C_b∉G⊔G'.

## Remaining 7 sorry — three tiers

**Tier 1 — general position of G** (structural wall):
- `hCb_not_Gb` — C_b not on G⊔b
- `h_span` — G ⊔ b ⊔ C_b = π
- `hb'_ne_Cb'` — pc(G,G',b,m) ≠ pc(G,G',C_b,m)

These are blocked because h_irred gives *some* G on a⊔C, but G could land on b⊔E, making C_b collinear with G,b. Needs either smarter G choice or case split. h_span depends on hCb_not_Gb (circular without independent proof).

**Tier 2 — well-definedness rebasing**:
- `hwd1` — pc(G,G',b,m) = s (rebase from (O,a) to (G,G'))
- `hwd2` — pc(G,G',C_b,m) = τ_a_C_b (same rebase)

**Tier 3 — fallback + finale**:
- G-on-m case (use h_irred on b⊔C to find G₂ off m)
- `coord_add_assoc` (depends on key_identity)

## Infrastructure

- **README updated**: 19 files, sorry counts current, FTPGTranslation→4-file split documented
- **CI warning enforcement**: new step fails on any non-sorry warning (per-file build)
- **All warnings silenced**: `omit` directives for unused section variables across 7 files, underscore unused params, `push_neg` → `push Not`

## Build state

19 files, 0 non-sorry warnings, 0 errors. Only warnings: 2 × "declaration uses sorry" in FTPGAssoc.lean.
