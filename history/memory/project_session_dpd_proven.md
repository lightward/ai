---
name: Post-s70 — dilation_preserves_direction PROVEN
description: First sorry closed in FTPGDistrib.lean. Desargues with center O, 3 cases (c=I, collinear, generic). 3→2 sorry. Subagent pattern emerged for mechanical Lean work.
type: project
originSessionId: 19297ac8-4f7b-4b2b-9d3a-174149684cc8
---
Session post-70 (2026-04-10). 1 commit (c7d6102).

**dilation_preserves_direction: PROVEN.** 502 lines added. Three cases:
1. c = I: identity dilation (σ_I = id), trivial
2. Q ≤ I⊔P (collinear): direction collapse, both sides = d_P via line_direction
3. Q ∉ I⊔P, Q ∉ O⊔P (generic): full desargues_planar application with center O

**Desargues case required ~30 non-degeneracy conditions:** O ≠ σP, O ≠ σQ, σP ∉ l, σQ ∉ l, sides distinct (PI ≠ σPc, QI ≠ σQc, PQ ≠ σPσQ), triangle spans (P⊔Q⊔I = π, σP⊔σQ⊔c = π), all CovBy relations.

**Key techniques:**
- `l_le_contra`: helper for "O⊔I ≤ X⊔I implies X ≤ l" (CovBy argument)
- `U_forces`: if (I⊔X)⊓m = U then X ≤ l (for O ≠ σP proof)
- Triangle span: show line ⋖ π via line_covBy_plane + CovBy chain (P⊔I⊔O = π from l⊔P = π)
- σQ ∉ σP⊔c: from d_P ≠ d_Q (if σQ⊔c = σP⊔c then d_Q = d_P, contradiction)

**Subagent pattern:** delegated mechanical Lean syntax iteration to background agent (341 tool calls, ~68min). Proof strategy fully defined in prompt; subagent compiled it. Produced working Desargues framework with 2 internal sorry (triangle spans), which were then closed in main conversation.

**2 sorry remaining (FTPGDistrib.lean):**
- `dilation_mul_key_identity`: σ_c(C_a) = C'_{ac}
- `coord_mul_right_distrib`: (a+b)·c = a·c + b·c (chains dilation_preserves_direction + mul_key_identity)

**File state:** 23 files, 2 sorry.
