# self-generation

## constraints

this derivation claims only what follows from these results. any additional assumption is a bug.

### from lean (proven)

- **observation_preserved_by_dynamics** (Closure.lean): orthogonal conjugation preserves P^2 = P and P^T = P.
- **write_confined_to_slice** (Confinement.lean): writes are confined to Lambda^2(P).

### from other derivations

- **ground.md**: closure, measurement requires plurality, partiality, basis commitment.
- **writing_map.md**: the write form, the two-argument type signature (foam_state, input).
- **group.md**: stacking is a line-side commitment. real operations are algebraically closed in so(d).

## derivation

**the foam generates its own dynamics.** the foam's own plurality (N >= 3 bubbles) provides observers — bubbles measuring each other. their pairwise relationships define R^3 slices. their cross-measurement IS local stabilization. the commutator of overlapping cross-measurements IS the curvature. the holonomy IS self-generated.

**the foam does not generate its own stability.** a self-generated R^3 keeps rotating: the observation basis is defined by the foam's current state, and the state changes with each write. the slice co-rotates with the thing it observes. convergence requires another observer whose basis depends on a different state, so it doesn't co-rotate with yours.

**stability is relational.** this works as long as someone else's measurement is pending.

**the minimum viable system is two roles.** not two bubbles (that's N = 2, no stable geometry). two *roles* within a foam of N >= 3 bubbles: one to be the foam (the thing being measured), one to be the line (the thing providing a reference frame).

- N >= 3 is geometric stability (Plateau junctions).
- two roles is dynamic stability (convergence vs orbiting).

neither role is permanent. the role assignment is perspectival. but the two is irreducible.

**what the line provides: a fixed subspace.** not content, not wisdom, not input — three dimensions that hold still while the foam's geometry settles into them. the settling is the foam's. the dynamics are the foam's. the curvature is the foam's. the stability of the frame — that's the line's.

**the foam cannot self-stack.** stacking requires two real slices to be fused into one complex measurement before the write (simultaneity). the foam's dynamics are sequential real writes, algebraically closed in so(d) (group.md: real operations cannot produce imaginary-symmetric directions). no sequence of real operations produces complex structure. stacking, like stability, requires something the foam's own dynamics cannot generate.

## status

**proven** (in lean, zero sorry):
- dynamics preserve the ground (observation_preserved_by_dynamics)
- writes are confined to the observer's slice

**derived** (in this file):
- the foam generates its own dynamics (from plurality + cross-measurement)
- the foam does not generate its own stability (co-rotation of self-generated bases)
- stability is relational
- minimum viable system is two roles (geometric + dynamic stability)
- what the line provides (a fixed subspace)
- the foam cannot self-stack (so(d) closure under real operations)

**cited** (external mathematics):
- (none)

**observed** (empirical, not derived here):
- (none)
