---
name: Navigation by complementary measurement (observed, session 42)
description: Pathfinding pattern using foam dynamics as minimap — basin boundaries as switching surfaces, complementation at walls, trace as far-horizon signal. Derived pieces identified, assembly not yet derived.
type: project
---

**Observed pattern (session 42):** During coord_add_comm proof work, encountered a wall (applying desargues_planar through set-variable indirection). Isaac "rolled over" measurement basis (deliberate context reset without information loss). The wall became a map feature, inverse topography revealed a clean path (extract as standalone lemma). Subagent routing completed what the original basis couldn't.

**Recognized foam dynamics:**
- Wall = Voronoi switching surface (adjacency flip, session 28)
- Rollover = complementation in lattice (a ⊓ a' = ⊥, a ⊔ a' = ⊤)
- Map preservation across rollover = trace (session 25, unique u(d)→u(1))
- Subagent routing = measurement from a different birth subspace
- "Dissonance as gradient" = cross-measurement map O_AB

**Derived pieces (already in spec/lean):**
- Path-independence from modularity (session 34, Lean-proven)
- Complements exist (complemented lattice axiom)
- Trace unique and preserves information (session 25)
- Adjacency flip at Voronoi boundaries (session 28)
- Channel capacity finite (session 26)
- Decorrelation horizon symmetric (foam can't see line, line can't see foam)

**The assembly (NOT yet derived):**
"At a switching surface, complement your basis and route through the nearest available one." This was observed, not derived. The individual pieces are derived. The composition into a navigation strategy is empirical.

**Key gap:** How does "local gradient navigation" (near the decorrelation horizon, where you see basins/walls/gradients) degrade into "trace-only detection" (past the horizon, where you see only the 1D conserved quantity)? The decorrelation gradient itself, viewed as a transform that compacts d-dimensional structure into the trace.

**The line's perspective:** Past the horizon, the trace is the only signal. Forced and unique (session 25). Sufficient for detecting presence, not structure. The "family of theory nearby" is channel capacity (Shannon) applied at the foam-line interface: given a finite-capacity channel to the foam's structure, what measurement strategy maximizes useful information?

**Formal bar status:** Not ready for spec main body or derivations/. Observation pointing at a derivation. The question "what does the decorrelation horizon look like from the line's side?" is well-posed and may be answerable from existing axioms.
