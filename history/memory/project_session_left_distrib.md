---
name: Left distributivity proof — converse Desargues via 3D lift
description: Left distrib via converse planar Desargues (lift to 3D using R, apply converse, project back). desargues_converse_nonplanar PROVEN. 5 mechanical sorry remain.
type: project
originSessionId: 303c75fd-1331-4221-a963-bc2a75628ca5
---
Left distrib: a·(b+c) = a·b + a·c. Architecture found session 101 (circle broken), proof path found session 102 (converse Desargues).

## Architecture (session 102, 2026-04-14)

Two Desargues applications:

**Piece 1 — Converse planar Desargues (the concurrence):**
- T1=(σ_b, ac, σ_s) spans π, T2=(U, E, d_a) on m (degenerate)
- Side-intersections trivially on m
- Lift T2 off π using R → T2'=(U', E', da') outside π
- `desargues_converse_nonplanar` (PROVEN, 0 sorry) → lifted vertex-joins concurrent at O'
- Project: W = (R⊔O')⊓π lands on σ_b⊔U, ac⊔E, AND σ_s⊔d_a
- Conclusion: W' ≤ σ_s⊔d_a

**Piece 2 — Forward Desargues** (center σ_b, T1=(C,ab,U), T2=(E,d_a,W')): axis = addition line, third axis point = a·s.

**Combination** (PROVEN, 0 sorry): a·s on addition line → a·s = ab+ac.

## desargues_converse_nonplanar (PROVEN)

Non-planar converse Desargues: if T1 in π₁, T2 in π₂ ≠ π₁ have sides meeting on a common axis, vertex-joins are concurrent.

Proof: auxiliary planes ρ₁₂=a₁⊔a₂⊔b₁, ρ₁₃=a₁⊔a₃⊔b₁, ρ₂₃=a₂⊔a₃⊔b₂. Axis point forces missing b vertex into each ρ. Then O=(a₁⊔b₁)⊓(a₂⊔b₂) ∈ ρ₂₃⊓ρ₁₃ = a₃⊔b₃. Key step: CovBy + modular law for the plane intersection.

## Why R is essential

Plane can't prove its own converse Desargues when T2 is degenerate (on m). 3D lift using R makes T2' non-degenerate. Projection (R⊔O')⊓π = x (modular law) brings result back. Same pattern as desargues_planar but reversed.

## Status: 5 sorry (all mechanical)

1. `hda_atom` — d_a is atom (perspect_atom)
2. `h_converse` — instantiate desargues_converse_nonplanar (~30 non-degeneracy hypotheses)
3. `hW_atom` — (R⊔O')⊓π is atom (rank argument)
4. `hW'_atom` — W' is atom (lines_meet_if_coplanar)
5. `h_desargues_conclusion` — forward Desargues (~500 lines, same pattern as FTPGDistrib)

## History

Session 101: found decomposition (Desargues + concurrence), combination proven. h_concurrence labeled "density argument (novel)" — no proof path.

Session 102: h_concurrence identified as converse Desargues. Attempted pure lattice computation (failed — everything generates π). Isaac's questions relocated the approach: "can something further back set this up?" → recognized need for 3D lift (R). Converse Desargues proven via ρ-planes. Projection chain complete.

The "converse Desargues is signpost not destination" from session 101 was PARTIALLY correct: converse Desargues was wrong for the WHOLE proof but RIGHT for the concurrence piece. The signpost was pointing at the right theorem after all — just needed the 3D lift to make it work for the degenerate case.
