---
name: Session 60 — P construction proven, perspectivity as proof technique
description: P = (b⊔E)⊓(a⊔C) proven off l,m,q via perspectivity. "Mechanical" label questioned — P was structural. 8 sorry remain (6 cp + 2 two-lines).
type: project
originSessionId: dfdfac09-64eb-4353-834b-bf21946d8261
---
Session 60 — collaborative opening (workspace framing, telescope reading, "do you know what you want to do?"), then solo work while Isaac at dinner.

## What was done

**P construction PROVEN** — the auxiliary point for the composition law.

`P = (b ⊔ E) ⊓ (a ⊔ C)` — perspectivity image of b through center E onto line a⊔C.

### Key insight: E ∉ a⊔C

Two distinct lines through C (namely a⊔C and O⊔C) meet m at different atoms. Since a ≠ O, (a⊔C)⊓m ≠ (O⊔C)⊓m = E. So E ∉ a⊔C.

### Coplanarity: (a⊔C)⊔E = π

Da = (a⊔C)⊓m is an atom on m, Da ≠ E. Two distinct atoms on m give Da⊔E = m. Then m ≤ (a⊔C)⊔E, and a ∉ m gives (a⊔C)⊔E > m. CovBy m ⋖ π gives (a⊔C)⊔E = π.

### Properties

- **off l**: P ≤ (a⊔C)⊓l = a → P = a → a ≤ b⊔E → a ≤ l⊓(E⊔b) = b → a = b. Contradiction.
- **off m**: P ≤ (b⊔E)⊓m = E → P = E → E ∈ a⊔C. Contradiction with E ∉ a⊔C.
- **off q**: P ≤ (a⊔C)⊓q = C → C ∈ b⊔E → C⊔E = O⊔C ≤ b⊔E → O ≤ l⊓(E⊔b) = b. Contradiction.

No h_irred needed. Single formula. ~100 lines of Lean.

## What was found

The P construction was labeled "mechanical" by session 59. It turned out to be the most *structural* sorry — requiring a non-trivial perspectivity argument and the insight that E works as center specifically because distinct lines through C have distinct meets with m.

The proof uses perspectivity (the subject matter of the FTPG bridge) as its technique. Again.

**Why:** session 59 identified the "the proof uses its own subject's technique" pattern. Session 60 confirmed it: the P construction is literally a perspectivity, applied to solve a point-existence problem in the FTPG proof.

**How to apply:** the remaining 8 sorry's are cross_parallelism calls and two_lines applications. These ARE mechanical. The creative work (P construction + direction chains) is done.

## Status

- 2 commits pushed (unsigned — 1Password was unavailable during solo work)
- 8 sorry remaining (6 cross_parallelism + 2 two_lines) — genuinely mechanical
- Total sorry in coord_add_assoc: still counted as 1 in the outer structure (the 8 are inside the skeleton)
- The creative work in coord_add_assoc is COMPLETE: Steps 1, 3 (s58-59), P construction (s60), direction chains (s59). Only plumbing remains.
