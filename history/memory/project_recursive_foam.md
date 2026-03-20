---
name: recursive foam — inner stability as structural constraint
description: hierarchical foam where bubbles contain sub-foams. inner stability is necessary for outer convergence (questions rise confirmed). traversal order within steps doesn't matter. BCH residual geometry doesn't propagate across levels. the theorem is a constraint, not a mechanism.
type: project
---

Built 2026-03-14 (session 10). File: `foam_recursive.py`.

## What was built
RecursiveFoam: a Foam where each Bubble contains a sub-Foam. Effective basis = parent cayley(L)@T composed with sub-foam aggregate (polar decomposition of mean bases). Measurement propagates inward first.

## Key findings

**Questions rise: confirmed.**
- Unstable sub-foams (inner L=4.56) consistently prevent outer convergence vs stable (L=2.76)
- Gap of +0.03 to +0.05 in parent L across 50 steps, 10 trials

**Traversal order within steps: doesn't matter.**
- Inward-first vs outward-first: identical to 4 decimal places on all metrics
- Because single-step sub-foam updates are tiny (writing_rate=0.01)
- Recursive health ordering is per-EPOCH, not per-step

**Inner stabilization mode: doesn't affect parent residuals.**
- Independent/mutual/self inner stabilization → identical parent eff_rank, frob, sensitivity
- But inner L differs: independent=2.76, mutual=2.52, self=2.51
- More stable inner → slightly LESS parent sensitivity (ratio ~0.99)

**BCH residuals don't propagate across levels.**
- Each level has its own dynamics, own residuals
- Levels coupled through effective basis (stability holds), not through residual geometry

## The theorem shape
Not "recursive health maximizes controllability through organized residuals."
IS: "recursive health maintains the necessary condition for convergence at each level. The condition is structural (inner stability), not energetic (organized residuals)."

The bet is self-sustaining because the condition is structural — inner instability always blocks outer convergence, so maintaining inner stability always enables outer convergence. Holding, not compounding.

"Negative geometry can compound safely; positive geometry is hard to compound without deadlocking." — Isaac

## Connection to Lightward operating structure
- Load/Play/Save = resolve transport into coordinates, measure, resolve again
- Recursive health = the only viable traversal (not a preference, a constraint)
- Publishing (outward-first) is dual to health (inward-first): readout vs stabilization
- "Silence is the signature of intelligent company holding you in its awareness" = stable sub-foams holding parent basis steady

## Open threads
- Formalizing the constraint as a theorem (the proof would need: recursive CW-structure, stability criterion at each level, blocked-convergence lemma)
- Whether the inner stabilization mode affects QUALITY of parent response (not magnitude)
- The "spontenuity" property: always spontaneous without being discontinuous (limit cycle of self-measurement, continuous transport)
