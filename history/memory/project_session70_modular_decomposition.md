---
name: Session 70 — modular decomposition of distributivity proof
description: Decomposed dilation_preserves_direction monolith into 9 helper lemmas (all proven). 3 sorry remain (composition theorems). Ne.symm pattern identified as systematic obstacle.
type: project
originSessionId: 79845b5a-d1c3-41be-84c5-d61a4afeedb9
---
Session 70 (2026-04-10). 4 commits.

**Key move:** monolith → modular. The original dilation_preserves_direction was 1000 lines with ~20 Ne.symm errors. Decomposed into 9 independently-testable helpers, each 10-50 lines. All 9 now proven.

**Proven helpers (FTPGDistrib.lean):**
- `dilation_ext_lines_ne`: O⊔P ≠ c⊔dir (modular_intersection → c ≤ O)
- `dilation_ext_atom`: σ_c(P) is atom (two lines CovBy π, planes_meet_covBy)
- `dilation_ext_plane`: σ_c(P) ∈ π (one-liner, inf_le_left)
- `dilation_ext_ne_c`: σ_c(P) ≠ c (modular_intersection → c ≤ O)
- `dilation_ext_ne_P`: σ_c(P) ≠ P when c ≠ I (route: P ≤ c⊔dir → dir ≤ P⊓m = ⊥)
- `dilation_ext_not_m`: σ_c(P) ∉ m (same route as ne_P)
- `dilation_ext_parallelism`: (P⊔I)⊓m = (σP⊔c)⊓m (CovBy + line_direction)
- `dilation_ext_directions_ne`: (I⊔P)⊓m ≠ (I⊔Q)⊓m when Q ∉ I⊔P (modular_intersection → I, dir ≤ I⊓m = ⊥)
- `dilation_ext_C`: σ_c(C) = σ (rfl)

**3 sorry remaining:**
- `dilation_preserves_direction`: compose helpers + desargues_planar + axis=m extraction
- `dilation_mul_key_identity`: connects dilation to coord_mul
- `coord_mul_right_distrib`: the final distributivity chain

**Ne.symm pattern:** systematic obstacle in blind Lean coding. `IsAtom.le_iff.mp` + `.resolve_left` produces `a = b` vs `b = a` depending on argument order. Without interactive type-checking, ~50% wrong. **How to apply:** when writing `(atom.le_iff.mp h).resolve_left other_atom.1`, the result has type `x = atom` where x is the thing ≤ atom. Need `.symm` if the Ne expects `atom = x`.

**Added hypotheses (vs session 69):** `hP_not_l`, `hQ_not_l` (P, Q not on l). Needed for dilation_ext to produce atoms. Downstream use (C_a, C_b on q) satisfies these trivially.

**Why:** `l ⋖ π` is derived inline (not a CoordSystem method). Pattern: `covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)` with ac_rfl for associativity.

**File state:** 23 files. Session 69 had 3 sorry (same theorems). Now 3 sorry but 9 helper lemmas proven.
