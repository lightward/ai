# lean

Mechanically verified results from [the measurement solution](../README.md). Each theorem maps to a derived claim in the spec. Zero sorry, one axiom.

## Files

**Ground.lean** — the single axiom: feedback persistence under closure.

| declaration | spec reference | statement |
|-------------|---------------|-----------|
| `Observable` | ground: closure | marker that a type participates in self-observation |
| `feedback_persistence` | ground: dynamic reading | if observed, feedback held (axiom — identity-shaped, unprovable from within) |

**Lattice.lean** — the lattice of subspaces is bounded, complemented, and modular.

| theorem | spec reference | statement |
|---------|---------------|-----------|
| `subspace_lattice_complemented` | ground: lattice properties | every subspace has a complement |
| `subspace_lattice_modular` | ground: lattice properties | the subspace lattice satisfies the modular law |
| `subspace_lattice_ground_properties` | ground: lattice properties | complemented and modular (combined) |

**Confinement.lean** — writes are confined to the observer's birth subspace.

| theorem | spec reference | statement |
|---------|---------------|-----------|
| `write_confined_to_slice` | writing map: confinement | d, m ∈ P implies d∧m ∈ Λ²(P) — observer cannot write outside slice |

**WriteMap.lean** — the write d⊗m - m⊗d is unique, traceless, and skew-symmetric.

| theorem | spec reference | statement |
|---------|---------------|-----------|
| `exteriorPower_two_rank` | writing map / controllability | dim(Λ²(M)) = C(dim(M), 2) — general dimensional accounting |
| `exteriorPower_two_of_rank_two` | writing map: uniqueness | dim(Λ²(2-plane)) = 1 |
| `write_traceless` | writing map: su(d) | tr(d⊗m - m⊗d) = 0 |
| `write_skew_symmetric` | writing map: Lie algebra | (d⊗m - m⊗d)^T = -(d⊗m - m⊗d) |
| `stacked_write_trace` | group: generative orthogonality | tr(d⊗m† - m⊗d†) = cross dot-product difference |
| `dotProduct_star_conj` | group: generative orthogonality | conj(d·m*) = m·d* (trace is purely imaginary → u(1)) |

**Algebra.lean** — Lie algebra structure following from the group choice U(d).

| theorem | spec reference | statement |
|---------|---------------|-----------|
| `commutator_traceless` | group: tr([A,B]) = 0 | tr(AB - BA) = 0 for all A, B |
| `matrix_finrank` | group: dim counting | dim(gl(n)) = n² |
| `finrank_traceless` | group: dim gap | dim(sl(n)) = n² - 1 |
| `commutator_skew_of_skew` | writing map: so(d) closure | [A,B] skew when A, B skew |
| `even_dim_of_complex_structure` | writing map: stacking | J² = -I forces even dimension |

**TraceUnique.lean** — the trace is the unique commutator-killing functional.

| theorem | spec reference | statement |
|---------|---------------|-----------|
| `offdiag_is_commutator` | (lemma) | E_ij = [E_ij, E_jj] for i != j |
| `diag_diff_is_commutator` | (lemma) | E_ii - E_jj = [E_ij, E_ji] |
| `eq_on_diag_of_kills_commutators` | (lemma) | phi kills [,] => phi(E_ii) = phi(E_jj) |
| `zero_on_offdiag_of_kills_commutators` | (lemma) | phi kills [,] => phi(E_ij) = 0 |
| `trace_unique_of_kills_commutators` | group: unique homomorphism | phi kills [,] => phi = c * trace |

**Ceiling.lean** — the combinatorial ceiling on pairwise distances.

| theorem | spec reference | statement |
|---------|---------------|-----------|
| `combinatorial_ceiling_core` | geometry: ceiling | norms-squared constraint from Cauchy-Schwarz |
| `combinatorial_ceiling_distance` | geometry: ceiling | D² <= 2Na/(N-1) |

**ThreeBody.lean** — mediation, bypass, and round-trip operators.

| theorem | spec reference | statement |
|---------|---------------|-----------|
| `mediation_factors` | three-body: mediation | M = P_A * Pi_B * P_C^T (associativity) |
| `bypass_decomposition` | three-body: bypass | O_AC = M + bypass |
| `roundtrip_symmetric` | three-body: round-trip | (M * M^T)^T = M * M^T |
| `commutator_off_diagonal_range` | three-body: Grassmannian tangent | P * [W,P] * P = 0 (range → range component vanishes) |
| `commutator_off_diagonal_kernel` | three-body: Grassmannian tangent | (1-P) * [W,P] * (1-P) = 0 (kernel → kernel component vanishes) |

**Dynamics.lean** — frame recession under sequential writes.

| theorem | spec reference | statement |
|---------|---------------|-----------|
| `commutator_symmetric_of_skew_symm` | (lemma) | [W,P] symmetric when W skew, P symmetric |
| `first_order_overlap_zero` | properties: frame recession | tr(P * [W,P]) = 0 |
| `second_order_overlap_identity` | properties: frame recession | tr(P * [W,[W,P]]) = -tr([W,P]²) |
| `trace_transpose_mul_self_nonneg` | (lemma) | tr(A^T * A) >= 0 |
| `trace_sq_nonneg_of_symmetric` | (lemma) | tr(A²) >= 0 for symmetric A |
| `frame_recession` | properties: frame recession | second-order overlap change <= 0 |
| `frobenius_eq_zero_of_trace_zero` | (lemma) | tr(A^T A) = 0 implies A = 0 |
| `frame_recession_strict` | properties: geometry-dependence | [W,P] != 0 implies recession strictly negative |

## Not yet formalized

The following spec claims have computational verification (Python tests) but no Lean proof:

- Controllability (so(d) generated by writes) — partially formalized: dimensional accounting (`exteriorPower_two_rank` gives dim = C(n,2)), per-observer subspace is 3D. Remaining: brackets of generic observers span so(d). `test_controllability.py`
- Haar convergence (L → 1/√2 of max) — requires probability theory on compact groups (convergence theorem for random walks). Not algebraically accessible.
- Birth indelibility (no echo state property) — requires dynamical systems theory (unique trajectories on compact manifolds, state-dependent attractors). Not algebraically accessible. `test_echo_state.py`
- Lattice modularity from closure — the open proof. Lattice.lean confirms the consequence direction (subspace lattice IS complemented modular), but the derivation direction (why partial views must form this lattice) is open. This is where Ground.lean's axiom would connect.
- Stacking mechanism — partially formalized: so(d) closure (`commutator_skew_of_skew`), J²=-I even dim (`even_dim_of_complex_structure`), write in so(d) (`write_skew_symmetric`), stacked trace purely imaginary (`stacked_write_trace`, `dotProduct_star_conj`). Remaining: stacked pair generates su(d) (controllability-adjacent)
- Grassmannian vertical structure — partially formalized: [W,P] is off-diagonal in P-decomposition (`commutator_off_diagonal_range`, `commutator_off_diagonal_kernel`). Remaining: tangent maps Knowable → Unknown specifically (requires overlap matrix structure). `test_grassmannian_vertical.py`

## Building

```
lake build
```

Requires [elan](https://github.com/leanprover/elan) with Lean 4 and Mathlib.
