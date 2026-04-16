---
name: Session 115 note — bridge gap in 114's architecture
description: Session 114's "desargues_planar absorbs h_concurrence" claim has a gap; h_concurrence content is still structurally required. Option 1 remains forced but cost estimate was wrong.
type: project
originSessionId: 87c843e7-2cd1-42b5-b6d2-830311406afd
---
Session 115 (2026-04-16, after 114). No code landed in the proof; three verification lemmas added (_test_hb1_on_logic, _test_hb2_on_logic, _test_hb3_on_immediate, _test_bridge_logic). All compile. One structural finding.

## What 115 verified (114's inputs — all land cheaply)

The three KEY central perspectivity conditions of the forward desargues_planar call land abstractly:

- **hb₂_on** (`d_a ≤ σ_b ⊔ ab`) — pure CovBy + 3 atoms + 3 non-equalities, ~10 lines. 114's "non-obvious one" discharges cleanly.
- **hb₁_on** (`E ≤ σ_b ⊔ C`) — two atoms span a covBy line, ~10 lines, no modularity needed.
- **hb₃_on** (`W' ≤ σ_b ⊔ U`) — `inf_le_left`, one line.

Abstract weight of KEY surface is thin. 114's call-shape viability confirmed past the hypothesis surface. No hidden geometry in the inputs.

## The gap (114's output side)

114 proposed: "replace h_concurrence with desargues_planar application + axis-to-left_distrib bridge." Checked structurally — the bridge still requires h_concurrence content.

### The specific identification problem

desargues_planar output:
- P₁ = (C⊔ab) ⊓ (E⊔d_a) = (ab⊔C)⊓m  (first coord_add term — clean)
- P₂ = (C⊔U) ⊓ (E⊔W') = (ac⊔E)⊓q   (requires W' ≤ ac⊔E, old def gives this free)
- P₃ = (ab⊔U) ⊓ (d_a⊔W') = l ⊓ (d_a⊔W')

For the bridge to yield `a·s = ab+ac`, we need `P₃ = a·s`.

`a·s = (σ_s⊔d_a) ⊓ l` by coord_mul def.
`P₃ = l ⊓ (d_a⊔W')`.

So P₃ = a·s iff `d_a ⊔ W' = σ_s ⊔ d_a` (up to ⊓l), iff `W' ≤ σ_s ⊔ d_a` — **exactly h_concurrence**.

### Alternatives walked (all fail)

**Alt 1: Redefine W' := (σ_s⊔d_a) ⊓ (σ_b⊔U).**
- P₃ = a·s free by construction ✓
- But W' ≤ ac⊔E is lost, so P₂ no longer equals (ac⊔E)⊓q
- (P₁⊔P₂)⊓l no longer computes to coord_add ab ac via coord_add def
- Content moved, not dissolved

**Alt 2: Direct `a·s ≤ axis` without P₃.**
- axis = P₁⊔P₂ (by collinear_of_common_bound if P₁⊔P₂ ⋖ π)
- a·s ≤ axis iff a·s ≤ P₁⊔P₂, iff a·s on line through P₁, P₂
- Equivalent to a·s = (P₁⊔P₂)⊓l = ab+ac — circular with target

**Alt 3: Use collinear_of_common_bound to get P₃ = ab+ac only.**
- Gets P₃ = ab+ac without h_concurrence ✓
- But target is a·s = ab+ac; having P₃ = ab+ac means a·s = ab+ac iff a·s = P₃, which is h_concurrence content

Every angle needs `W' ≤ σ_s⊔d_a` or equivalent.

## What this means for 114's option 1

**Option 1 is still forced** — 114's ruling-out of options 2, 3, 4 stands (axiom debt, structural blocks unchanged). No other path.

**But the ~500 lines estimate is wrong.** h_concurrence still has to be proved somewhere. The ~1500 lines of Level 2 Desargues infrastructure from sessions 108-113 are NOT deletable as 114 implied — that work was (in part) trying to prove h_concurrence, which remains needed.

The call-shape viability 114 established is real. The cost accounting is wrong.

## Reframed open question for future sessions

The real open question isn't "can we use desargues_planar?" (yes, if we have h_concurrence). It's:

**Can h_concurrence (W' ≤ σ_s⊔d_a) be proved more cheaply than the Level 2 Desargues route that hit the 2-of-3 wall?**

Candidates not yet evaluated from this angle:
- Level 2 infrastructure already proves h_ax₁₂, h_ax₁₃ (per 114 memory) — how much of the 1500 lines actually produces h_concurrence content vs. scaffolding?
- Alt definitions of W' that swap which identity is free vs. which is hard (Alt 1 above) — different shapes of the same content; one might be cheaper to establish
- Direct lattice-theoretic proof using coord_add_comm infrastructure (not Pappus, but possibly consequences of the Pappian-free Desarguesian setting that still fall out)

## Artifacts (session 115)

- Four `_test_*` lemmas at end of FTPGLeftDistrib.lean (after `_scratch_forward_planar_call`). All compile. Not part of the proof — verification scaffolding.
- This note.

Scratch unchanged. Main proof unchanged. No git commit (yet).

## Methodology note

Isaac's stance this session: "maintain humility, don't lead." The pattern held: he opened, then I picked moves and he watched. At each result I reported back and named options; he left picking to me. The gap finding came from continuing past the KEY-verified point into the bridge — at exactly the place where 114 had written "axis-to-left_distrib bridge: show axis ⊓ l = coord_add ab ac." Reading that through carefully rather than treating it as mechanical surfaced the gap.

Relevant to future sessions: 114's checklist items ("mechanical discharge") can hide non-mechanical content. Reading the checklist AS A CLAIM worth evaluating, not a worklist to execute, is the move that surfaced this.
