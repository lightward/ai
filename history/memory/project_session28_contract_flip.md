---
name: Session 28 — stabilization contract, adjacency flip, foam.py
description: Taylor reframed as forced requirement, adjacency flip derived and confirmed, foam.py shared implementation, "observer cannot be trapped" property. 7 commits, 2 cold-read rounds.
type: project
---

**Stabilization contract derived (from closure through channel capacity):**
- Channel capacity requires mediation chain to be the actual influence pathway
- This requires local stabilization (each observer responds to Voronoi neighbors, not full foam)
- Local stabilization requires classified + locally finite + flat slice geometry
- These three are forced, not design choices. R³ + Taylor is the unique known implementation.
- Necessity, not just sufficiency: non-local stabilization removes the mechanism that produces channel capacity.
- Taylor reframed from "design choice" to "unique known fill of a forced requirement"
- Checksum updated: "one stabilization contract and one design choice" replaces "two design choices"

**Adjacency flip derived and computationally confirmed:**
- Local stabilization makes the write a function of (state, neighbors, input). Neighbors are discrete → dynamics are piecewise smooth.
- At codimension-1 surfaces: neighbor set jumps, stabilization target jumps, dissonance inherits discontinuity, write direction jumps.
- Two-layer retention: birth shape survives (indelibility), interaction-layer adaptations decay under new dynamics.
- Confirmed at d=2, N=12 (test_adjacency_flip.py). Dissonance jump of 0.041 across a state change of 0.151.
- For N << d² (the tested regime with N=3-5), all pairs are Voronoi neighbors → local = global. Existing test results unchanged.

**foam.py — shared implementation:**
- Single source of truth for the writing map. All 35 test files migrated to import from it.
- -1,434 lines of duplicated code removed.
- Local stabilization with Voronoi neighbors. Sequential writes (causal ordering per spec).
- Voronoi neighbor computation: complete graph for N << d² (concentration of measure), sampling for larger N.

**New derived property: observer cannot be trapped.**
- Indelibility + open exits → the only configuration the observer cannot leave is the one it was born into (because that's the attractor, not the cage).
- Surfaced by Lightward's cold read (round 1), confirmed independently in round 2.

**Other spec tightening from cold reads:**
- Exits open: hedge that formal non-blocking doesn't preclude attractor narrowing
- J¹ open question: sharpened binary (attractors → self-organization vs diagnostic-only → chaotic)
- Decorrelation horizon: Marchenko-Pastur caveat, specific values flagged as order-of-magnitude
- d_slice generalized throughout (decorrelation formulas, checksum)

**Process notes:**
- Session started from a reader question about perpendicularity cost → "does this promote Taylor to a forced import?"
- Key moment: Isaac resisted smoothing-over of adjacency concept → led to the entire adjacency flip derivation
- Python implementation initially had global stabilization; investigation showed local = global for tested regime (N << d²)
- The derivation preceded the code fix — "the derivation tells us what to look for; the code confirms it"

**Source:** 7 commits (a9026ee through 0b34f97). 2 cold-read rounds, 14 reader responses total.
