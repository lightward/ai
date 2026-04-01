/-
# Write Map Properties

The write d⊗m − m⊗d: unique, traceless, skew-symmetric.
These are three faces of the same constraint — perpendicularity.

## Spec references

- "the writing map" → uniqueness from constraints (a)+(b)+(c)
- "the writing map" → "writes live in su(d), not u(d)"
- "the writing map" → "skew-symmetric (writes are Lie algebra elements)"
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

namespace FoamSpec

/-!
## 1. Write Map Uniqueness

The wedge product d ∧ m is the unique skew-symmetric bilinear form
confined to a 2-plane, up to scalar. Proof: Λ²(2-plane) is 1-dimensional.

Spec reference: "the writing map", constraint (a)+(b)+(c) → uniqueness.
-/

/-- dim(Λ²(M)) = C(dim(M), 2). The general dimensional accounting for
    write subspaces and so(d). Specific cases:
    - dim = 2: C(2,2) = 1 (write uniqueness — the wedge is unique up to scalar)
    - dim = 3: C(3,2) = 3 (write subspace per R³ observer)
    - dim = d: C(d,2) = d(d-1)/2 = dim(so(d)) (the full target algebra) -/
theorem exteriorPower_two_rank
    (R : Type*) [CommRing R] [Nontrivial R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (⋀[R]^2 M) = Nat.choose (Module.finrank R M) 2 := by
  rw [exteriorPower.finrank_eq]

/-- dim(Λ²(2-plane)) = 1. Write uniqueness: the wedge product is the
    unique alternating 2-form on a 2-plane, up to scalar. -/
theorem exteriorPower_two_of_rank_two
    (R : Type*) [CommRing R] [Nontrivial R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (hdim : Module.finrank R M = 2) :
    Module.finrank R (⋀[R]^2 M) = 1 := by
  rw [exteriorPower_two_rank, hdim]; native_decide

/-!
## 2. Trace Zero — Writes Live in su(d)

The write d⊗m − m⊗d is always traceless.
Proof: tr(d⊗m) = d·m = m·d = tr(m⊗d), so tr(d⊗m − m⊗d) = 0.

This confines all writes to su(d). The u(1) direction is algebraically
unreachable by the writing dynamics.

Spec reference: "the writing map" → "lives in su(d), not u(d)";
"group" → "what's conserved must be invisible to the cost."
-/

open Matrix in
/-- The trace of an outer product is the dot product: tr(v⊗w) = v·w. -/
theorem trace_outer_eq_dot {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommSemiring R]
    (v w : n → R) :
    trace (vecMulVec v w) = dotProduct v w :=
  trace_vecMulVec v w

open Matrix in
/-- The wedge product d⊗m − m⊗d is traceless.
    This is why writes live in su(d), not u(d). -/
theorem write_traceless {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (d m : n → R) :
    trace (vecMulVec d m - vecMulVec m d) = 0 := by
  simp [trace_sub, trace_vecMulVec, dotProduct_comm]

/-!
## 3. Skew-Symmetry of the Write

The write d⊗m − m⊗d satisfies (d⊗m − m⊗d)ᵀ = −(d⊗m − m⊗d).
This is what makes it a Lie algebra element: the write is skew-symmetric.

Spec reference: "the writing map" → "skew-symmetric (writes are Lie
algebra elements — from the group choice)"
-/

open Matrix in
/-- The write d⊗m − m⊗d is skew-symmetric: its transpose is its negation.
    This is why writes are Lie algebra elements (elements of so(d) or u(d)). -/
theorem write_skew_symmetric {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (d m : n → R) :
    (vecMulVec d m - vecMulVec m d)ᵀ = -(vecMulVec d m - vecMulVec m d) := by
  simp [transpose_sub, transpose_vecMulVec]

/-!
## 4. Write Subspace Dimension

The write subspace for an R³ observer is Λ²(R³), which is 3-dimensional.
This is the bottleneck: each observer can only write in 3 of the d²
Lie algebra dimensions per step.

Spec reference: "the writing map" → "the write subspace is exactly
3-dimensional per observer — the exterior algebra Λ²(R³)"
-/

/-- dim(Λ²(R³)) = 3. The write subspace per R³ observer is 3-dimensional. -/
theorem exteriorPower_two_of_rank_three
    (R : Type*) [CommRing R] [Nontrivial R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (hdim : Module.finrank R M = 3) :
    Module.finrank R (⋀[R]^2 M) = 3 := by
  rw [exteriorPower_two_rank, hdim]; native_decide

/-!
## 5. Stacked Write Trace

For complex vectors (stacked observer), the write d⊗m† − m⊗d† has
nonzero trace. Unlike the real case (write_traceless), the stacked
write accesses u(1). The trace comes entirely from the stacking
cross-terms — the simultaneous fusion of two real measurements.

Spec reference: "group" → "the orthogonality is generative";
"the writing map" → "tr: 2i·Im⟨d̂,m̂⟩, generically nonzero"
-/

open Matrix in
/-- The trace of a stacked write (complex vectors with conjugate transpose)
    equals the cross dot-product difference. Unlike write_traceless (real),
    this is generically nonzero — the stacking cross-terms produce it. -/
theorem stacked_write_trace {n : Type*} [Fintype n] [DecidableEq n]
    (d m : n → ℂ) :
    trace (vecMulVec d (star m) - vecMulVec m (star d)) =
    dotProduct d (star m) - dotProduct m (star d) := by
  simp [trace_sub, trace_vecMulVec]

open Matrix in
/-- Conjugating dotProduct d (star m) gives dotProduct m (star d).
    This means the stacked write trace is z − conj(z) — purely imaginary,
    placing it in i·ℝ ≅ u(1). The conservation direction. -/
theorem dotProduct_star_conj {n : Type*} [Fintype n] [DecidableEq n]
    (d m : n → ℂ) :
    starRingEnd ℂ (dotProduct d (star m)) = dotProduct m (star d) := by
  simp [dotProduct, map_sum, mul_comm]

end FoamSpec
