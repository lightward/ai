---
name: double Desargues proof for additive inverses
description: coord_add_left_neg proven via double Desargues, 1 sorry remaining (generic case coplanarity argument)
type: project
originSessionId: ce9a0a17-a775-4103-bf36-b3541f521cb3
---
## Session: double Desargues for a+(-a)=O

### Architecture (proven)

1. **First Desargues** (center U): T1=(a, d_a, β_a), T2=(neg_a, e_a, β_neg) → P₃ ≤ O⊔C
2. **Second Desargues** (center P₃): T1'=(C, d_a, β_neg), T2'=(E, β_a, e_a) → W ≤ l
3. **Extraction**: W ≤ (O⊔β_a)⊓l = O → O ≤ d_a⊔β_neg → (d_a⊔β_neg)⊓l = O

### Key identity: d_{neg_a} = e_a (proven as `neg_C_persp_eq_e`)

### Status: 1 sorry (generic case, a ≠ -a)

**PROVEN (2026-04-12 night session):**
- `coord_neg_ne_O`: If neg_a = O → e_a = E → β_a = C → C ≤ a⊔E → O ≤ a⊔E → (a⊔E)⊓l = a but also ≥ O → a = O. ✗
- `coord_neg_ne_U`: If neg_a = U → e_a = U → β_a = U → U ≤ a⊔E → (a⊔E)⊓l = a but also ≥ U → a = U. ✗
- **Char 2 case** (a = -a): d_a = e_a (from neg_C_persp_eq_e) → e_a ⊔ β_a = O ⊔ β_a (covering) → line_direction gives (O⊔β_a)⊓l = O. ✓

**REMAINING: 1 sorry — generic case (a ≠ -a)**

The proof outline for the generic case is complete and documented in FTPGNeg.lean:
- Steps 4-5: e_a ⊔ β_a = O ⊔ β_a (covering), (O⊔β_a)⊓l = O
- Step 6: h2 gives first ⊓ (O⊔β_a) ≤ l ⊓ (O⊔β_a) = O
- Step 7: Need `first ⊓ (O⊔β_a) ≠ ⊥` via `lines_meet_if_coplanar`

Step 7 requires: `(O⊔β_a) ⋖ π` (covBy), `first ≤ π`, `¬first ≤ O⊔β_a`, `d_a < first`.
All non-degeneracy conditions are understood:
- d_a atom: `perspect_atom` with a, C through m
- d_a ∉ l: d_a = U → (U⊔C)⊓l = U → a = U via d_a_persp_back. Contradiction.
- d_a ≠ β_neg: if equal → d_a ∈ m∩q = U → d_a ∉ l contradiction
- (O⊔β_a) ⋖ π: β_a ∉ l → l⊔β_a = π → O⊔β_a⊔U = π → covering
- ¬first ≤ O⊔β_a: if so → first ≤ O → d_a ≤ O → d_a = O → O ∈ m. Contradiction.

Key Lean pattern issue: β in coord_add has form `(a⊔E)⊓(U⊔C)` but β_a in e_a has form `(U⊔C)⊓(a⊔E)`. Must `rw [inf_comm]` before `set` to align them.

### Technical notes for filling the last sorry

- Use `rw [inf_comm]` at h2 BEFORE setting β_a to normalize
- The `hOβ_covBy_π` proof: show U ⊓ (O⊔β_a) = ⊥, use covBy_sup_of_inf_covBy_left, then show U⊔(O⊔β_a) = π via l⊔β_a = π
- The `sup_assoc`/`sup_comm` rewrites for U⊔(O⊔β_a) = (O⊔U)⊔β_a are fiddly — use explicit `show ... from ...` patterns
- All atoms: `perspect_atom` for d_a, `beta_atom` for β_neg (uses hna_atom from coord_neg_atom)
