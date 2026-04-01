/-
# Lie Algebra Structure

Properties that follow from the group choice U(d):
commutator tracelessness, dimensional counting,
so(d) closure, and the complex structure constraint.

## Spec references

- "group" → "tr([A, B]) = 0 for all A, B ∈ u(d)"
- "group" → "U(d) rather than SU(d) because π₁(U(d)) = ℤ"
- "the writing map" → "so(d) is a Lie subalgebra (closed under brackets)"
- "the writing map" → "J² = -I on a real vector space forces even dimensionality"
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace FoamSpec

/-!
## 1. Commutator Tracelessness

The commutator [A, B] = AB − BA of any two matrices is traceless.
Therefore accumulated brackets of writes cannot escape su(d).

Spec reference: "group" → "tr([A, B]) = 0 for all A, B ∈ u(d)"
-/

open Matrix in
/-- The commutator of any two square matrices is traceless.
    Not just for traceless matrices — this is unconditional.
    tr(AB − BA) = tr(AB) − tr(BA) = 0 by cyclicity of trace. -/
theorem commutator_traceless {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (A B : Matrix n n R) :
    trace (A * B - B * A) = 0 := by
  rw [trace_sub, trace_mul_comm]
  exact sub_self _

/-!
## 2. Dimensional Accounting

dim(u(d)) = d². The traceless matrices su(d) have dimension d² − 1.
The gap is exactly 1: the u(1) direction (scalar multiples of the identity).

The metrically invisible direction is topologically load-bearing.

Spec reference: "group" → "U(d) rather than SU(d) because π₁(U(d)) = ℤ"
-/

/-- The space of n×n matrices over a field has dimension n².
    This is dim(gl(n)) = n², and dim(u(d)) = d² in the spec's terms. -/
theorem matrix_finrank {n : ℕ}
    {K : Type*} [Field K] :
    Module.finrank K (Matrix (Fin n) (Fin n) K) = n * n := by
  simp [Module.finrank_matrix, Fintype.card_fin]

open Matrix Module in
/-- The kernel of the trace map (= traceless matrices = sl(n) = su(d) in
    the spec's notation) has dimension n² − 1.
    The gap of 1 is the u(1) direction — topologically load-bearing,
    metrically invisible. -/
theorem finrank_traceless {n : ℕ} [NeZero n]
    {K : Type*} [Field K] :
    let tr : Matrix (Fin n) (Fin n) K →ₗ[K] K := traceLinearMap (n := Fin n) (R := K) (α := K)
    finrank K (LinearMap.ker tr) = n * n - 1 := by
  intro tr
  have h_rn := LinearMap.finrank_range_add_finrank_ker tr
  have h_surj : Function.Surjective tr := fun r => trace_surjective (n := Fin n) r
  have h_range : LinearMap.range tr = ⊤ := LinearMap.range_eq_top.mpr h_surj
  simp [finrank_matrix, Fintype.card_fin, finrank_self] at h_rn
  have h_range_dim : finrank K (LinearMap.range tr) = 1 := by
    rw [h_range, finrank_top]
    exact finrank_self K
  omega

/-!
## 3. so(d) Closed Under Brackets

The commutator of two skew-symmetric matrices is skew-symmetric.
This is the algebraic core of "real operations are closed in so(d)."

Combined with: writes start in so(d), brackets stay in so(d).
Therefore a single R³ observer's entire reachable algebra is
contained in so(d). The imaginary-symmetric directions su(d) \ so(d)
are algebraically unreachable. Reaching u(d) requires stacking.

Spec reference: "the writing map" → "so(d) is a Lie subalgebra"
-/

open Matrix in
/-- The commutator of skew-symmetric matrices is skew-symmetric.
    so(d) is a Lie subalgebra: real operations can't escape to complex. -/
theorem commutator_skew_of_skew {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (A B : Matrix n n R) (hA : Aᵀ = -A) (hB : Bᵀ = -B) :
    (A * B - B * A)ᵀ = -(A * B - B * A) := by
  rw [transpose_sub, transpose_mul, transpose_mul, hA, hB]
  noncomm_ring

/-!
## 4. J² = -I Forces Even Dimension

A complex structure on a real vector space — a linear map J with J² = -I —
can only exist in even dimension. This is why the stacking requires
R⁶ = R³ ⊕ R³: the minimum even-dimensional space containing R³.

Spec reference: "the writing map" → "J² = -I on a real vector space
forces even dimensionality"
-/

open Matrix in
/-- If J² = -I for a real matrix, then the dimension is even.
    This is why reaching u(d) from so(d) requires stacking two R³ slices. -/
theorem even_dim_of_complex_structure {n : ℕ}
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J * J = -1) :
    Even n := by
  have h1 : det J ^ 2 = (-1 : ℝ) ^ n := by
    rw [sq, ← det_mul, hJ, det_neg, det_one, mul_one, Fintype.card_fin]
  have h2 : (0 : ℝ) ≤ det J ^ 2 := sq_nonneg _
  rw [h1] at h2
  have h3 : (-1 : ℝ) ^ n = 1 := by
    rcases neg_one_pow_eq_or ℝ n with h | h <;> linarith
  rwa [neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)] at h3

end FoamSpec
