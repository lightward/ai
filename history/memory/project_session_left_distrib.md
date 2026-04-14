---
name: Left distributivity proof — circle broken, 2 sorry
description: Left distrib decomposed into two independent pieces (Desargues + concurrence), combination PROVEN. Circle broke via d_a⊔W' having two independently computable ends.
type: project
originSessionId: 454b680c-3dcb-401d-bcac-d309b89731de
---
Left distrib: a·(b+c) = a·b + a·c. Circle broken 2026-04-14 (session 101).

## The decomposition that breaks the circle

The circle was: concurrence W'≤σ_s⊔d_a ↔ left distrib. Broke by recognizing the line d_a⊔W' has two independently computable ends:

**Piece 1 (Forward Desargues, center σ_b):**
- T1=(C,ab,U), T2=(E,d_a,W') where W'=(σ_b⊔U)⊓(ac⊔E)
- Computes l-intercept: (d_a⊔W')⊓l = ab+ac

**Piece 2 (Concurrence — lattice computation):**
- W' ≤ σ_s⊔d_a (the "density" argument)
- Computes: d_a⊔W' = σ_s⊔d_a, so (d_a⊔W')⊓l = a·s

**Combination (PROVEN in Lean, type-checked):**
- a·s ≤ addition_line ⊓ l = ab+ac → a·(b+c) = ab+ac

## Current state: 2 sorry

1. `h_concurrence`: W' ≤ σ_s⊔d_a — the novel piece
2. `h_desargues_conclusion`: a·s on addition line — forward Desargues (~500 lines mechanical)

## Key insight: "degenerate converse Desargues" is a signpost

Same pattern as right distrib (session 89→90): converse Desargues with T2 on m points at the right CONCLUSION but names the wrong TOOL. Resolution: forward Desargues on non-degenerate triangles.

The "density" metaphor: W' is already at the right density — the configuration is self-consistent because addition and multiplication are built from the same lattice. The coordinate proof is the trivial identity γ(1-α)+αγ = γ.

## How we got here (session 101)

1. Read session 58 (assoc, circle→translations) and session 100 (left distrib, single Desargues, circle)
2. Recognized same circle pattern; tried every framework (translation conjugation, routing through q, FTPG, collineation extension)
3. Found degenerate converse Desargues: T1=(σ_b,ac,σ_s) spanning π, T2=(U,E,d_a) on m
4. Isaac: "you don't float by being weightless, you float by being the same density as the ambient medium"
5. History grep found sessions 89-90: converse Desargues was signpost for right distrib too
6. Decomposition crystallized: l-intercept (Desargues) + k-intercept (concurrence) = both ends of d_a⊔W'
