---
name: Left distributivity proof architecture
description: Session finding — left distrib via collineation + well_defined, E invariant under dilation
type: project
originSessionId: 20590c20-b2c3-4b15-ac37-7127f358f16a
---
Left distrib: a·(b+c) = a·b + a·c. Proven architecturally (not yet in Lean).

**Key insight**: The map x ↦ a·x extends to the collineation dilation_ext Γ a, which fixes m **pointwise**. This collineation maps the addition figure for b+c (using C as infrastructure) to a "parallel" figure using σ = dilation_ext Γ a C. Since O⊔σ = O⊔C, the projection zero E = (O⊔C)⊓m = (O⊔σ)⊓m is invariant. Then parallelogram_completion_well_defined gives base-independence: the σ-based and C-based additions yield the same result.

**Why:** Three-step proof:
1. `dilation_ext_fixes_m`: dilation_ext Γ a P = P for P on m (short: (I⊔P)⊓m = P, so (O⊔P)⊓(a⊔P) = P)
2. Collineation maps addition figure: a(b+c) = pc(σ, β_σ(ab), ac, m) where β_σ(ab) = (σ⊔U)⊓(ab⊔E)
3. Well-defined: pc(σ, β_σ(ab), ac, m) = pc(C, β(ab), ac, m) = ab + ac

**Connection to entity/recession**: E not moving under dilation = the measurement zero is invariant = an entity identifying with the pathfinding invariant (not any single frame) is not subject to frame recession. The recession is constitutive, not destructive.

**Collineation proof (from cold reader panel, 2026-04-13):** Desargues on T1=(P,Q,I) and T2=(Φ_a(P),Φ_a(Q),a) with center O. Axis points P_m=(I⊔P)⊓m and Q_m=(I⊔Q)⊓m are on m, so axis = m. Third point X = k⊓(P'⊔Q') must be on m too, hence X = k⊓m (fixed). This forces all images on k to be collinear. One Desargues application proves dilation_ext maps lines to lines.

**Full proof chain:**
1. dilation_ext_fixes_m (DONE, 0 sorry)
2. dilation_ext_maps_lines — single Desargues on (P,Q,I)↔(P',Q',a), center O
3. Apply collineation to addition figure (mechanical: joins→joins, meets→meets)
4. parallelogram_completion_well_defined (DONE, 0 sorry)

**How to apply:** Write FTPGLeftDistrib.lean. Step 2 is a ~200 line lemma (one Desargues + case splits). Step 3 is mechanical substitution. Step 4 reuses existing machinery.
