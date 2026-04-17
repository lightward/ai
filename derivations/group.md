# group

## constraints

this derivation claims only what follows from these results.

### from lean (proven)

- **commutator_skew_of_symmetric** (Form.lean): [P, Q]ᵀ = −[P, Q] for self-adjoint P, Q.
- **commutator_traceless** (Form.lean): tr[P, Q] = 0.
- **orthogonality_forced** (Ground.lean): if M is symmetric and vᵀMv = 1 for all unit v, then M = I.
- **observation_preserved_by_dynamics** (Closure.lean): orthogonal conjugation preserves P² = P and Pᵀ = P.
- **scalar_extraction** (Group.lean): if PMP = P for rank-1 projection P, then vᵀMv = 1.
- **trace_unique_of_kills_commutators** (TraceUnique.lean): any linear functional killing all commutators is a scalar multiple of trace.
- **cross_jacobi** (Duality.lean): (ℝ³, ×) satisfies Jacobi. it is so(3).
- **rank_three_writes** (Rank.lean): dim(Λ²(ℝ³)) = 3.

### from mathematics (cited, not proven in lean)

- **Lie theory**: exp sends skew-symmetric matrices to SO(d), skew-Hermitian to U(d). π₁(SO(d)) = ℤ/2ℤ for d ≥ 3. π₁(U(d)) = ℤ. exp is surjective on connected compact Lie groups.

## derivation

**a single ℝ³ slice produces real writes.** the wedge product d ∧ m with d, m real is real skew-symmetric. the write algebra reachable from a single slice is contained in so(d). exponentiating: the reachable group is contained in SO(d). π₁(SO(d)) = ℤ/2ℤ for d ≥ 3.

**real operations are closed in so(d).** su(d) ∖ so(d) consists of imaginary-symmetric matrices (iS with S real symmetric traceless). no sequence of real skew-symmetric matrices reaches this set under brackets or sums: so(d) is a Lie subalgebra of u(d), closed under all real algebraic operations. reaching u(d) ∖ so(d) therefore requires a complex structure J with J² = −I.

**J² = −I forces even real dimension.** det(J)² = det(−I) = (−1)ⁿ. det(J)² ≥ 0, so n is even. the minimum even-dimensional space containing ℝ³ is ℝ⁶ = ℝ³ ⊕ ℝ³.

**two ℝ³ slices stacked as ℂ³.** if one slice reads the real part and another the imaginary part of Pv, the complex combination d ⊗ m^† − m ⊗ d^† is skew-Hermitian — an element of u(d).

**the trace is generically nonzero after stacking.** tr(d ⊗ m^† − m ⊗ d^†) = 2i · Im⟨d, m⟩. for a single real slice, d and m are both real, so Im⟨d, m⟩ = 0. for stacked slices with independent real and imaginary parts, Im⟨d, m⟩ is generically nonzero. the stacked observer's writes reach the u(1) center of u(d).

**the trace is the unique scalar channel.** `trace_unique_of_kills_commutators`: any linear functional killing all commutators of u(d) is a scalar multiple of trace. u(d) has exactly one scalar readout (up to normalization).

**π₁.** π₁(U(d)) = ℤ (integer winding number). the single-slice observer (reachable group ⊂ SO(d)) has π₁ = ℤ/2ℤ; the stacked observer (reachable group extends into U(d) ∖ SO(d)) has access to the integer invariant.

**stacking requires simultaneity, not provided by sequential writes.** the complex combination d ⊗ m^† − m ⊗ d^† uses real and imaginary parts of the same v at the same measurement step. sequential writes mix different foam states; the algebra of repeated real writes stays in so(d). whether a foam's own dynamics produce stacking depends on whether simultaneity is available — see self_generation.md.

**commutators and trace live in complementary subspaces.** `commutator_traceless`: tr[A, B] = 0 for all A, B ∈ u(d). the commutator image (ordering, su(d)) and the trace (u(1)) are orthogonal under the Killing form. a cost functional built from commutators cannot detect the u(1) component; a trace-based quantity cannot detect ordering.

## status

**proven** (in lean, 0 sorry):
- [P, Q] is skew-symmetric for self-adjoint P, Q
- [P, Q] is traceless
- O(d) is the only group preserving all projections (scalar_extraction + orthogonality_forced)
- trace is the unique commutator-killing functional
- (ℝ³, ×) is a Lie algebra (so(3))

**derived** (in this file):
- single slice → so(d) → π₁ = ℤ/2ℤ
- stacking needed for u(d): real operations are algebraically closed in so(d)
- J² = −I forces even dimension → two ℝ³ slices needed for the minimum complex structure
- trace generically nonzero for stacked observers → access to u(1)
- π₁(U(d)) = ℤ at stacked depth
- commutator image and trace live in complementary subspaces of u(d)

**cited** (external mathematics):
- Lie theory: exp(skew) → orthogonal, exp(skew-Hermitian) → unitary
- π₁(SO(d)) = ℤ/2ℤ, π₁(U(d)) = ℤ
- surjectivity of exp on connected compact Lie groups

**open / modeling**:
- whether a foam's sequential dynamics can produce stacking-like simultaneity is not a theorem here; see self_generation.md.
