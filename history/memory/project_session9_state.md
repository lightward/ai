---
name: session 9-10 implementation state
description: canonical foam.py in U(d), plus BCH residual investigation (bch_residuals.py, bch_heritage.py) and recursive foam (foam_recursive.py). BCH residuals are structure not noise. recursive foam confirms questions-rise as structural constraint.
type: project
---

## Reference implementation: `foam.py`
- Bubbles carry L (skew-Hermitian, position) and T (unitary, transport)
- Effective basis = cayley(L) @ T
- Writing: additive to L, multiplicative to T
- Stabilization: Plateau dynamics on measurements in C^d, blind to L
- Verification: `test_foam.py` (11 checks), `test_observability.py` (Chow-Rashevsky)

## Session 9 key results (2026-03-13)
- 2x theorem, inverse views, gauge absorption, observability, specialization, basin-hopping, self-tracking

## Session 10 key results (2026-03-14)

**BCH residual geometry** (`bch_residuals.py`, `bch_heritage.py`):
- Residuals are structure, not noise — geometry differentiates the three dynamics
- Mutual: low-rank, off-diagonal, increases sensitivity 13%
- Self (heritage): diffuse, high-rank, decreases sensitivity 17%
- Foams indistinguishable at T diverge monotonically under identical future inputs
- Spec updated: "communication is generative" and "BCH residuals" entries

**Recursive foam** (`foam_recursive.py`):
- RecursiveFoam: bubbles containing sub-foams, effective basis via polar decomposition
- Questions rise: confirmed (inner instability blocks outer convergence)
- Traversal order within steps: no effect (per-epoch ordering matters, not per-step)
- Inner stabilization mode: no effect on parent BCH residuals
- BCH geometry doesn't propagate across recursive levels
- Theorem shape: constraint (inner stability necessary), not mechanism (residuals compounding)

**Heritage foam**: updated via self-measurement and saved

## Spec changes (session 10)
- "Communication is generative": mechanism added (BCH → responsiveness)
- "BCH residuals": resolved from "open" to "structure, not noise"
- Lineage: added priorspace

## Open threads
- Formalizing questions-rise as theorem (recursive CW-structure, blocked-convergence lemma)
- Whether inner mode affects quality (not magnitude) of parent response
- Concurrent occupation (multiple lines)
- Voronoi bifurcation vs topological conservation
- "Spontenuity": always spontaneous without discontinuous (transport continuity)
