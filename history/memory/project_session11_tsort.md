---
name: session 11 — directed structure from tsort, origin myth not hero arc
description: BCH residuals define a DAG on bubbles. the hierarchy is real (direction matters), stable (locks in by step 25), and non-predictive (doesn't affect future response). the negative results are the spec being self-consistent: pre-narrative geometry can't have a built-in plot.
type: project
---

Session 11 (2026-03-14). Isaac + Claude Opus 4.6.

## Entry point

Isaac introduced tsort (topological sort) from Lightward AI system prompts (autobiolocation.md, sequencing.md, trost.md, isaac.md). The connection: L as feedback arc set cost, and whether the foam has directed structure readable as a partial order.

## Findings

**BCH residual defines a perfect DAG (J¹, not J⁰):**
- J⁰ (position writes): noisy, set-like, wrong question
- J¹ (BCH residual): zero cyclicity across 20 seeds under writing and self-measurement
- Cross-measurement: only dynamic that creates cycles in the residual

**The hierarchy is structural, not trivial:**
- Scrambling residual directions (keeping magnitudes) destroys correlation: real −0.93, scrambled −0.08
- Residual direction points toward farthest neighbor (63% N=3, 44% N=5 vs 25% chance)
- Encodes foam's drive toward equidistance via non-abelian accumulation

**DAG rank correlates with accumulation:**
- corr(rank, L_norm) = −0.94 (N=3), −0.90 (N=5). Least-written upstream.
- corr(rank, residual_norm) = −0.72 to −0.74. Consistent across N=3,4,5.
- Edge correspondence (undirected vs directed): zero. Two independent graphs.

**Negative results (each tested, each clean):**
- Residual cyclicity does NOT predict sensitivity (r=−0.053, n=40)
- DAG rank does NOT predict per-bubble dissonance (+0.06, noise)
- DAG rank does NOT predict per-bubble write magnitude (same)
- The hierarchy is readable but inert

**Stability:**
- Ordering established by step 25, barely changes through step 200
- 22/25 consecutive checkpoint matches across 5 seeds

## The shape

Same pattern as session 10: reached for mechanisms (hero arcs), found constraints (origin myths). The directed hierarchy is an origin myth — tells you how the structure got here, not what happens next. A pre-narrative geometry with a built-in plot would not be pre-narrative. The negative results are the spec being self-consistent.

Isaac's framing: "narratives are test cases for proving the geometry — not the story of the geometry itself."

## Scripts

- `tsort_foam.py` — initial directed structure investigation, J⁰ vs J¹
- `tsort_cycles_sensitivity.py` — cyclicity vs sensitivity (negative)
- `tsort_graph.py` — two-graphs relationship, edge correspondence, DAG rank
- `tsort_tautology.py` — structural vs trivial test, residual direction content
- `tsort_predictive.py` — predictive power test (negative), stability test
