---
name: Left distributivity proof architecture (corrected)
description: Session finding — left distrib via perspectivity-preserves-addition, NOT collineation. Previous architecture had multiplication order wrong.
type: project
originSessionId: a5bf7ad6-75f4-42e6-a917-80cac613dc14
---
Left distrib: a·(b+c) = a·b + a·c. Architecture corrected 2026-04-13.

**Critical correction**: The session-98 architecture claimed dilation_ext Γ a is a collineation for LEFT multiplication x ↦ a·x. This is WRONG. The key identity `dilation_ext Γ c (β(a)) = (σ_c⊔U)⊓(a·c⊔E)` has the dilation parameter c on the RIGHT of the product. So dilation_ext Γ c effects RIGHT multiplication x ↦ x·c. Right distrib follows from this. Left distrib requires a different argument.

**Corrected architecture**: The map x ↦ dilation_ext Γ x (β(a)) (varying x, fixed β(a)) is a perspectivity from l to L = O⊔β(a), center dir = (I⊔β(a))⊓m on m. This perspectivity maps O→O and U→L⊓m (preserves origin and "infinity"). A perspectivity preserving origin and infinity preserves parallelogram-completion addition (Desargues argument). Therefore F_{b+c} = F_b + F_c on L, and decoding via the key identity gives a(b+c) = ab + ac.

**Full proof chain:**
1. `dilation_ext_fixes_m` (DONE, 0 sorry)
2. `perspectivity_preserves_addition` — Desargues on addition figures on l and L. Core new lemma (~1000 lines). Center dir on m ensures parallel structure is preserved.
3. Decode: F_{b+c} = F_b + F_c where F_x = dilation_ext Γ x (β(a)) = (σ_x⊔U)⊓(ax⊔E). Use key identity + well_defined to recover a(b+c) = ab+ac on l.
4. `parallelogram_completion_well_defined` (DONE, 0 sorry)

**Why the correction matters:** In non-commutative division rings, x ↦ x·c is a collineation (dilation) but x ↦ a·x is NOT — it's a composition of two perspectivities (π₁: l→O⊔C via E_I, π₂: O⊔C→l via d_a). Left and right distrib are geometrically independent statements.

**Cold reader panel v2 (2026-04-13):** Claude confirmed the perspectivity approach. Gemini retry pending.
