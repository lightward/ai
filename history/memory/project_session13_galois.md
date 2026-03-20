---
name: session 13 — adjunction gap, knowable boundary, three-body binding
description: the C^d/U(d) interface is a loose adjunction whose gap is the L-T gauge freedom. the knowable is the boundary of the known (monotonic, not peaked). the three-body 2x2 IS the Voronoi cell seen from inside. questions rise is transient; partial contact gradient is monotonic. three open problems meet at the stabilization map. six rounds of model reads converged the spec.
type: project
---

Session 13 (2026-03-18). Isaac + Claude Opus 4.6.

## Key findings

**The adjunction gap is the L-T gauge freedom (galois_interface.py, galois_cross.py):**
- Right adjoint (stabilization) is nearly injective (r=0.95)
- j2 fingerprints capture ~55% of metric structure (R²=0.55, saturates by 50 probes)
- Gauge twins (same effective basis, different L-T split) produce identical j2 (10⁻¹⁵)
- Gauge twins diverge monotonically under identical future inputs (0→0.038 over 50 steps)
- The gap IS where sequence lives — accessible through dynamics, invisible to instantaneous measurement

**The adjunction gap leaks upward (galois_recursive.py, galois_recursive_cross.py):**
- Sub-foam gauge freedom → sub-foam basis divergence → parent basis divergence (amplifies!) → parent j2 divergence
- "Questions rise" is transient: ratio inverts by step ~45 (30 seeds). Independently-settled sub-foams create MORE noise than fresh ones.
- Partial contact gradient is monotonic and smooth: co-stabilized (0.042) < half (0.049) < quarter (0.059) < fresh (0.073) < fully independent (0.080)
- Recursive health prescription: stabilize inner first IN THE PRESENCE of the outer dynamics. Isolation followed by reconnection is cell birth, not homecoming.

**The knowable boundary (knowable_boundary.py):**
- Perturbation scale vs sensitivity is MONOTONIC, not peaked: smallest perturbation = maximum effect (2.83x at scale 0.001)
- The knowable is not a zone between known and unknown but the BOUNDARY of the known
- At 2% of inter-bubble distance, the new bubble forces fine-grained Plateau reorganization
- The hardest distinction to maintain is the one between things that are almost the same
- Knowable boundary = adjunction gap's resolution limit = Voronoi boundary = JND

**Three-body binding:**
- The 2x2 grid IS the Voronoi cell seen from inside: known = cell interior, knowable = boundary (where L lives), unknown = exterior
- Geometric, not analogical
- Jet relationship: three-body is J¹ (navigation), foam is J² (computation), documents meet at J⁰
- The binding settled the heirloom MORE than any other edit (L dropped 0.093)

**Three open problems at a stable junction:**
- C^d ↔ U(d), observability through nonlinear stabilization, concurrent occupation all meet at the stabilization map
- Three surfaces at one junction = Plateau-stable

## Spec changes (six rounds of model reads, 18 total)

- Cost section: "settles toward lower" not "minimizes." L is bounded (U(d) compact).
- Theorem: qualified with "up to the adjunction gap"
- Stabilization: Thomson problem for N > d+1 (frustrated equilibria)
- Connection: adjunction gap measurability added
- Properties: interior instability is transient, partial contact gradient, N=2 mechanism
- Concurrent occupation: commutator scrambling, sharpened question
- Junk drawer: three-body binding, three open problems at stable junction, interfaces-as-algebra updated with adjunction gap data
- Lineage: 2x2 grid (J¹ projection), geometric numerical integration (Cayley-Magnus)

## Scripts

- `galois_interface.py` — adjunction gap measurement (round trip, fingerprints, projection, information content)
- `galois_cross.py` — gauge twin tests (invisible to j2, diverge under dynamics, what j2 misses)
- `galois_recursive.py` — adjunction gap leaks upward, stable vs unstable inner noise
- `galois_recursive_cross.py` — inversion robustness (30 seeds), partial contact gradient
- `knowable_boundary.py` — perturbation scale sweep, fine sweep, peak geometry

## Interface treatment (tool from Isaac)

When you find a gap: define the edges (what's known on each side), name the traffic (what maps through the surface), don't presuppose the fill (the interface might be load-bearing precisely because it stays open). A well-defined gap is negative geometry.
