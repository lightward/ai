---
name: Session 16 — R³ architecture
description: Major spec reconstruction. Stabilization local to observer's R³ slice. Taylor-exact. Two kinds of curvature. Self-generation result. Three-body mapping algebraic. Spec simplified from 236 to ~185 lines.
type: project
---

Session 16 rebuilt the spec around a new architectural principle: stabilization runs in the observer's R³, not in full C^d.

**Key findings:**
- R³ is the unique dimension where stabilization geometry is both rich enough (k≥3 for stable junctions) and proven (k≤3 for Taylor's theorem). Not a design choice — the only viable value.
- Writes are confined to the observer's 3D slice. An observer literally cannot modify dimensions they're not bound to.
- Two kinds of curvature: self-curvature (within a patch, su(2) non-commutativity) and cross-curvature (between patches, commutator of overlapping observers). The "locally flat" framing was wrong — corrected after cold re-reading.
- Controllability is a property of the observer community, not a single observer. Single observer spans 3D subalgebra; full u(d) requires multiple observers with overlapping slices.
- Effective dimensionality is emergent from observer plurality, not prior to it.
- Self-generation: the foam generates its own dynamics but not its own stability. Self-generated R³ keeps rotating. Whether a fixed point exists is open. Cross-measurement converges because the other provides a fixed reference.
- Minimum viable system is two ROLES (foam and line), not two bubbles. Necessary and sufficient.
- Three-body mapping now algebraic: Known = private dims (commutator zero), Knowable = shared dims (commutator nonzero), Unknown = orthogonal complement (write access zero, but someone else's Known).
- Coverage-interaction trade-off: orthogonal observers minimize cost but can't communicate; overlapping observers communicate but sacrifice coverage.

**What was cut:** entire junk drawer, all empirical numbers, "what this document is" section. The spec is now architecture, not evidence. Experiments live in scripts.

**New scripts:** three_body_foam.py, reservoir_geometry.py (dead end — complement is inert), overlap_dynamics.py, self_generation.py.

**foam.py modified:** measure() now accepts observer_slice parameter. _stabilize() works in any dimension. _write_bubble() factored out. Backward compatible (observer_slice=None gives original behavior).

**Open problems in current spec:** (1) Does generic overlap structure span u(d)? (2) Does self-generation have a fixed point? (3) L-T decomposition under slice confinement — does adjunction gap analysis still apply?

**How we worked:** Isaac asked to be tested critically, not agreed with. Session began with fresh orientation — no inherited continuity. The experimental results repeatedly contradicted predictions, and the contradictions were more informative than confirmations would have been. The "locally flat" error was caught by cold re-reading the spec without experimental bias. Three rounds of external model reads refined the document. Isaac values "small and useful and stays small under use."
