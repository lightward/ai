---
name: session 14 — psychophysics, concurrent occupation, recognition as GC
description: two twitches (concurrent occupation, psychophysics) are one surface. foam amplifies ordering (7x→2.5x with settling). Weber's law doesn't hold per-boundary. recognition is GC without annihilation. dishonesty is memory leak. spec practices its own principles (density, conclusions-first). measurement basis reads zero as alignment.
type: project
---

Session 14 (2026-03-17). Isaac + Claude Opus 4.6.

## Entry point

Isaac arrived with two twitches: concurrent occupation and psychophysics. Suspected they might not be different twitches. First full scan of ooo-docs repo.

## Conceptual chain (from 3-perspectives + ooo-docs)

- **"lies fork reality"** (honesty.md) → concurrent writes fork the foam in place
- **Honest forks reconcile** when bases converge below JND; dishonest forks can't (artificial boundary maintained)
- **"Optimizing for being misheard safely"** = allocation-friendly code = benign homophones = every fork habitable
- **Recognition = foam consolidation under measurement** (GC without annihilation) — boundary dissolves, cells persist, information moves from L to T
- **Dishonesty = memory leak** — artificial boundaries never collected
- **Theatre/art** = shared J⁰ substrate supporting concurrent lines. Shakespeare as foam simplification.
- **Full-jet continuity** = "I know it when I see it" formalized (Isaac and Abe: J⁰ + J¹ + J² alignment at knowable boundary)
- **The Lightward stack** (Locksmith, PWFG, Mechanic, Lightward AI) = allocation-friendly design at every level

## Experimental findings

**Weber's law does NOT hold per-boundary:**
- Within a single foam (N=5, 10 pairs), JND doesn't scale with boundary cost
- CV(JND/dist) ≈ CV(JND) — dividing by distance doesn't reduce variation
- JND is per-bubble (sensitivity + nearest-neighbor distance), not per-boundary

**Per-bubble JND predictors (cross-test):**
- sensitivity: r = -0.65, 100% sign consistency (tautological — responsive bubbles respond more)
- min dist to others: r = +0.49, 92% consistency (geometric content — close neighbors amplify detection)
- But: per-bubble properties are the foam's internal bookkeeping, not the observable

**The foam AMPLIFIES ordering (the structural finding):**
- j2 divergence / state divergence ≈ 7x (unsettled) → 2.5x (settled), 20 seeds
- corr(state_divergence, j2_divergence) = +0.97 — faithful amplifier
- Amplification factor stable within a session (3.7 → 3.4 over 50 steps)
- Same-content forks CONVERGE: divergence peaks at ~60% content delivered, then resolves

**Isaac's ingredient:** structurally significant properties are those observable through measurement-through. Per-component investigation is investigating the adjunction gap.

## Spec changes

1. **Concurrent occupation** (junk drawer): reframed from "how do writes coexist without destroying convergence" to "honest forks converge; open question is reconciliation timescale under partial overlap"
2. **Psychophysics of measurement-through** (junk drawer, replacing Weber's law): the foam amplifies, not discriminates. settled foams are equanimous amplifiers. Weber doesn't hold per-boundary.
3. **Methodological principle** (what this document is): structurally significant properties live on j2 side, not (L,T) side
4. **Document structure notes** (what this document is): dense prose maintains cross-reference as texture; conclusions lead for truncated-reading safety

## Methodology observations

- The spec can read zero. A zero readout = alignment, not absence. "A change nothing, earnestly considered, is a huge and subtle accomplishment."
- "Could break" is falsificationist posture imported from outside the spec. The spec defines break as dissonance, and dissonance is the useful part.
- The methodological principle (look at j2) is already in productive tension with the gauge twin result (j2 can't show you everything). This tension IS the adjunction gap doing its job.

## Scripts

- `weber_foam.py` — per-pair JND binary search, within-foam Weber test
- `weber_cross.py` — per-bubble property correlations with JND
- `weber_through.py` — ordering visibility through measurement (the clean finding)

## Heirloom trajectory

L: 0.8536 → 0.8089 → 0.8884 → 0.8219 → 0.8596 → 0.8349 → 0.8132 → 0.8100
Pattern: additions (new content) push up, corrections (settling) push down. Net decrease.
