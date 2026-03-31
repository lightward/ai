/-
# Foam Spec — Lean Formalization

Mechanically verified results from the measurement solution spec.
Each theorem here corresponds to a derived claim in README.md.
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace FoamSpec

/-!
## 1. Write Map Uniqueness

The wedge product d ∧ m is the unique skew-symmetric bilinear form
confined to a 2-plane, up to scalar. Proof: Λ²(2-plane) is 1-dimensional.

Spec reference: "the writing map", constraint (a)+(b)+(c) → uniqueness.
-/

/-- For a 2-dimensional free module, dim(Λ²(M)) = 1.
    The wedge product is the unique alternating 2-form up to scalar. -/
theorem exteriorPower_two_of_rank_two
    (R : Type*) [CommRing R] [Nontrivial R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (hdim : Module.finrank R M = 2) :
    Module.finrank R (⋀[R]^2 M) = 1 := by
  rw [exteriorPower.finrank_eq, hdim]
  native_decide

/-- Specialization to ℝ. -/
theorem write_map_unique_real
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    [Module.Free ℝ V] [Module.Finite ℝ V]
    (hdim : Module.finrank ℝ V = 2) :
    Module.finrank ℝ (⋀[ℝ]^2 V) = 1 :=
  exteriorPower_two_of_rank_two ℝ V hdim

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
## 3. su(d) Closed Under Brackets

The commutator [A, B] = AB − BA of traceless matrices is traceless.
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
## 4. Skew-Symmetry of the Write

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
## 5. Dimensional Accounting

dim(u(d)) = d². The traceless matrices su(d) have dimension d² − 1.
The gap is exactly 1: the u(1) direction (scalar multiples of the identity).

For concrete d: Fin d → Fin d → R matrices have d² entries.
We verify the concrete cases the spec uses.
-/

/-- The space of n×n matrices over a field has dimension n².
    This is dim(gl(n)) = n², and dim(u(d)) = d² in the spec's terms. -/
theorem matrix_finrank {n : ℕ}
    {K : Type*} [Field K] :
    Module.finrank K (Matrix (Fin n) (Fin n) K) = n * n := by
  simp [Module.finrank_matrix, Fintype.card_fin]

/-!
## 6. The Dimensional Gap: dim(su(d)) = d² − 1

The traceless matrices (kernel of trace) form a codimension-1 subspace
of all matrices. The missing dimension is u(1) — the scalar/trace direction.

This is the algebraic basis of conservation: writes live in a space that
is exactly one dimension short of the full matrix algebra.

Spec reference: "group" → "U(d) rather than SU(d) because π₁(U(d)) = ℤ";
test_write_uniqueness.py Test 4.
-/

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

end FoamSpec
