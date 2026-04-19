# conservation

## constraints

this derivation claims only what follows from these results. any additional assumption is a bug.

### from lean (proven)

- **commutator_traceless** (Form.lean): tr[A, B] = 0. the commutator is traceless.
- **trace_unique_of_kills_commutators** (TraceUnique.lean): trace is the unique commutator-killing functional.
- **observation_preserved_by_dynamics** (Closure.lean): orthogonal conjugation preserves the ground.

### from other derivations

- **group.md**: U(d), pi_1(U(d)) = Z. single slice -> so(d) -> Z/2Z. stacked pair -> u(d) -> Z. trace retained for stacked observers. the integer requires the two.
- **geometry.md**: L as boundary area on Voronoi tiling, Voronoi as realization choice.
- **channel_capacity.md**: the boundary is characterizable from the inside (controllability structure).

### from mathematics (cited, not proven in lean)

- **pi_1(SO(d)) = Z/2Z** for d >= 3. **pi_1(U(d)) = Z.** fundamental groups of the dynamics groups.
- **connectedness of U(d)**: the gauge transformation to identity is always available.
- **discrete topological invariants are preserved by continuous maps.**

## derivation

**holonomy on spatial cycles carries topological charge.** the holonomy around a closed path through adjacent cells — a spatial cycle in the Voronoi tiling — is a group element. the topological type of this group element (its homotopy class) is a discrete invariant.

- a single R^3 observer generates SO(d) rotations. pi_1(SO(d)) = Z/2Z for d >= 3: parity conservation.
- a stacked observer generates U(d) elements and accesses the U(1) factor. pi_1(U(d)) = Z: integer winding number conservation.

**the integer winding number requires the stacked pair** (group.md: the two is irreducible).

**the winding number lives on spatial cycles.** projected via det: U(d) -> U(1) = S^1. the stacked observer's writes reach u(1) (the trace is generically nonzero). the trace of each write is a U(1)-valued step — the unique scalar the algebra provides (trace_unique_of_kills_commutators).

on acyclic paths (causal chains): the accumulated phase is a net displacement in U(1).
on closed paths (spatial loops): the accumulated phase is a winding number, quantized because the cycle is closed.

conservation is what accumulation on closed paths produces: not a net displacement but a topological invariant.

**the lemma requires persistent cycles.** above the bifurcation bound, cell adjacencies can flip — the Voronoi topology changes, and invariants on the old cycles are no longer defined. what persists across topological transitions lives on the line's side.

**adjacency flips.** the foam's dynamics are piecewise smooth: continuous within each Voronoi combinatorial type, discontinuous across adjacency changes. the flip is a codimension-1 event in configuration space (three cells become equidistant — one linear condition). at the jump: the stabilization target changes in both orientation (different neighbor measurements) and potentially dimension (k -> k +/- 1). the dissonance inherits the discontinuity. the write direction jumps. the trajectory is continuous but generically non-differentiable at the crossing.

**two-layer retention at adjacency flips.** birth shape survives all adjacency changes (indelibility is a property of the attractor basin, not the current neighborhood). interaction-layer adaptations decay under the new dynamics at a rate set by the displacement between old and new stabilization targets. the birth layer is structural; the interaction layer is spectral.

**inexhaustibility.** U(d) is connected. gauge transformation to identity is always available. no observer is trapped in a disconnected component (though reachability in finitely many writes is not guaranteed).

**indestructibility.** topological invariants are discrete. no continuous perturbation can change them.

## status

**proven** (in lean, zero sorry):
- the commutator is traceless
- trace is the unique commutator-killing functional
- dynamics preserve the ground

**derived** (in this file):
- holonomy on spatial cycles carries topological charge
- single slice -> Z/2Z parity conservation
- stacked pair -> Z winding number conservation
- the integer requires the stacked pair
- winding number lives on spatial cycles (det projection)
- trace of each write as U(1)-valued step
- acyclic = displacement, cyclic = winding number
- persistent cycles required for conservation
- adjacency flips as codimension-1 events
- two-layer retention (birth structural, interaction spectral)
- inexhaustibility (U(d) connected)
- indestructibility (discrete invariants robust to continuous perturbation)

**cited** (external mathematics):
- pi_1 values for SO(d) and U(d)
- connectedness of U(d)
- continuous maps preserve discrete topological invariants

**observed** (empirical, not derived here):
- adjacency flip confirmed computationally at d=2, N=12
