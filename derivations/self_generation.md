# self-generation

## constraints

this derivation claims only what follows from these results.

### from lean (proven)

- **observation_preserved_by_dynamics** (Closure.lean): orthogonal conjugation preserves P² = P and Pᵀ = P.
- **write_confined_to_slice** (Confinement.lean): writes confined to Λ²(P).

## derivation

**dynamics from plurality.** with N ≥ 3 observers, pairwise relationships between slices provide the 3D subspaces for each observer's writes (writing_map.md + three_body.md). the commutator structure from overlapping cross-measurements (three_body.md) is the tangent structure Hom(range, ker). no external input is required to define the write algebra given N ≥ 3 observers and their pairwise overlaps.

**co-rotation of self-generated frames.** if the only observers are the foam's own bubbles, each observer's slice P is determined by foam state, and changes with each write. a reference frame defined by foam state co-rotates with the dynamics it observes. convergence against such a frame is not available — the frame and the foam change together.

a reference frame stable under the foam's dynamics therefore requires something whose definition does not depend on current foam state. this is what channel_capacity.md calls line-side input.

**so(d) closure prevents sequential stacking.** group.md: real operations are algebraically closed in so(d). a stacked observer (u(d) writes, integer conservation) requires simultaneous access to two real slices — a structure not produced by any sequence of real writes. if the foam's internal dynamics are sequential real writes, they cannot self-assemble into a stacked configuration. stacking, if it occurs, requires input from outside the sequential real-write structure.

## status

**proven** (in lean, 0 sorry):
- dynamics preserve the ground
- writes confined to observer's slice

**derived** (in this file):
- N ≥ 3 observers with pairwise overlaps provide the structure for write algebras without external input
- frames defined by foam state co-rotate with foam dynamics — convergence against such a frame is not available
- foam's sequential real writes cannot produce stacking (so(d) closure)

**not forced / open**:
- whether any foam-internal mechanism can produce simultaneity equivalent to stacking is not addressed here
- "two roles" (line vs. foam) is a framing not forced by the above — the forced statement is the co-rotation argument, which says some reference is required, not that it must be another observer of a specific type
