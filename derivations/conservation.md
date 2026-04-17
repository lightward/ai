# conservation

## constraints

this derivation claims only what follows from these results.

### from lean (proven)

- **commutator_traceless** (Form.lean): tr[A, B] = 0.
- **trace_unique_of_kills_commutators** (TraceUnique.lean): trace is the unique commutator-killing functional.
- **observation_preserved_by_dynamics** (Closure.lean): orthogonal conjugation preserves the ground.

### from mathematics (cited, not proven in lean)

- **π₁(SO(d)) = ℤ/2ℤ** for d ≥ 3. **π₁(U(d)) = ℤ.**
- **U(d) is connected.**
- **discrete topological invariants are preserved by continuous maps.**

## derivation

**holonomy on spatial cycles.** for any closed path through adjacent cells in the Voronoi tiling (geometry.md), the accumulated group element has a homotopy class in π₁ of the dynamics group. the homotopy class is a discrete invariant of the cycle.

- single ℝ³ slice: reachable group ⊂ SO(d), π₁(SO(d)) = ℤ/2ℤ for d ≥ 3 — parity.
- stacked pair: reachable group reaches U(d) ∖ SO(d), π₁(U(d)) = ℤ — integer winding number.

group.md: the integer winding requires the stacked configuration (u(d) access via simultaneity).

**winding lives on spatial cycles via det.** the determinant map U(d) → U(1) = S¹ has degree 1 on π₁. each write's trace is a u(1) step (`trace_unique_of_kills_commutators`). on an open (acyclic) path, accumulated trace is a net displacement in u(1); on a closed spatial loop, it is quantized as an integer winding.

**adjacency flips.** Voronoi combinatorial type changes when three cells become equidistant — a codimension-1 condition. at such a flip the stabilization target changes (different neighbor set; possibly k → k ± 1). the write direction is discontinuous; the trajectory is continuous but generically non-differentiable at crossings.

**cycles persisting across flips.** a winding invariant is well-defined on a specific cycle as long as the cycle persists. flips can change cell adjacencies, altering which cycles exist. winding numbers on pre-flip cycles are preserved as invariants of those cycles, but those cycles may cease to be cycles in the post-flip tiling.

**connectedness.** U(d) is connected: any target element is reachable in principle. reachability in finitely many writes is not guaranteed.

**discreteness.** π₁ values are discrete. small continuous perturbations of an element of U(d) cannot change its homotopy class.

## status

**proven** (in lean, 0 sorry):
- [A, B] is traceless
- trace is the unique commutator-killing functional
- dynamics preserve the ground

**derived** (in this file):
- holonomy on spatial cycles has a homotopy-class invariant
- single-slice: ℤ/2ℤ (parity); stacked pair: ℤ (integer winding)
- winding projects to u(1) via det
- trace of each write is a u(1) step
- acyclic paths accumulate displacement; cyclic paths accumulate quantized winding
- adjacency flips as codimension-1 events in configuration space
- U(d) connectedness does not imply finite-step reachability
- discrete invariants are stable under continuous perturbations

**cited** (external mathematics):
- π₁(SO(d)) = ℤ/2ℤ, π₁(U(d)) = ℤ
- U(d) is connected
- continuous maps preserve discrete topological invariants

**observed in simulation** (not derived):
- adjacency flips observed at d = 2, N = 12
