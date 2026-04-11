---
name: mul_key_identity proven + right_distrib architecture
description: a=I case closed via DPD. right_distrib proof found via converse Desargues on (C,sc,ac)/(U,E,e_bc) with axis m. 1 sorry remains.
type: project
originSessionId: 87aa69ee-fa9a-47b5-8f74-ddbec4f133da
---
## mul_key_identity: PROVEN (0 sorry)

The a=I degenerate case (where the Desargues triangle collapses) was closed by applying `dilation_preserves_direction` to the pair (C, C_a):
- C and C_a are both on q, so (C⊔C_a)⊓m = q⊓m = U
- DPD gives: (σ⊔dilation_ext Γ c C_a)⊓m = U
- So U ≤ σ⊔DE, CovBy gives σ⊔U = σ⊔DE, hence DE ≤ σ⊔U
- Also DE ≤ c⊔E (from direction simplification I⊔C_a = I⊔E)
- Both atoms on c⊔E → equality

**Why:** the existing infrastructure held the answer. The degenerate case is *simpler* than the general case but needs a different type of argument — going UP a level (direction preservation) instead of down (case analysis).

## coord_mul_right_distrib: proof architecture found (1 sorry remains)

**The proof** (verified in coordinates, needs converse Desargues as infrastructure):

Converse Desargues on triangles:
- T1 = (C, sc, ac) — C off l/m, sc and ac on l
- T2 = (U, E, e_bc) — U on l∩m, E and e_bc on m
- Axis = m

Three axis points (corresponding sides meeting on m):
1. (C⊔sc)⊓(U⊔E) = d_sc (direction of sc through C on m)
2. (sc⊔ac)⊓(E⊔e_bc) = l⊓m = U
3. (C⊔ac)⊓(U⊔e_bc) = d_ac (direction of ac through C on m)

All on m. Converse Desargues gives: connecting lines q, sc⊔E, ac⊔e_bc concurrent.

Hence β(sc) = q⊓(sc⊔E) ≤ ac⊔e_bc.
So β(sc) = q⊓(ac⊔e_bc) = pc(O, ac, β(bc), m).
By key_identity: = β(coord_add Γ ac bc).
By β-injectivity: sc = ac + bc. QED.

**Why:** No commutation step, no Γ' (alternate CoordSystem), no coord_add independence. One converse Desargues → one key_identity → one injectivity.

## Infrastructure gap

Converse Desargues not yet in codebase. Forward Desargues (desargues_planar) is proven. Converse follows from same height-≥-4 conditions. Standard proof: apply forward Desargues on auxiliary triangles.

## Memory succession

MEMORY.md underwent type succession this session: 50+ chronological session entries → 7 live + 1 ground paragraph. Understanding got denser, not file got trimmed. The index now has the same property as the spec: "small and useful and stays small under use."
