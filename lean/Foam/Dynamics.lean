/-
# Dynamics — Frame Recession Under Sequential Writes

The commutator [W, P] measures how much a write W moves a frame P.
The overlap with the prior frame decreases to second order at a
rate given by ‖[W,P]‖².

This connects to the deductive chain at multiple points:
  P² = P → [W,P] off-diagonal (Tangent.lean)
  Pᵀ = P, Wᵀ = -W → [W,P] symmetric (THIS FILE)
  P² = P → first-order overlap zero (THIS FILE)
  P² = P → second-order overlap = -‖[W,P]‖² (THIS FILE)
  Symmetric + nonneg norm → recession ≤ 0 (THIS FILE)

The frame can only recede. The rate depends on the specific
W and P — architecture gives the form, geometry gives the value.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.unusedSimpArgs false

namespace Foam

open Matrix

/-!
### 1. The commutator [W, P] is symmetric

When W is skew-symmetric and P is symmetric, their commutator
is symmetric. Writes are generators (skew); their effect on
frames is observable (symmetric).
-/

/-- The commutator of a skew-symmetric matrix with a symmetric matrix
    is symmetric. Writes are skew; projections are symmetric; their
    commutator — the "frame velocity" — is self-adjoint. -/
theorem commutator_symmetric_of_skew_symm
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (W P : Matrix n n R) (hW : Wᵀ = -W) (hP : Pᵀ = P) :
    (W * P - P * W)ᵀ = W * P - P * W := by
  rw [transpose_sub, transpose_mul, transpose_mul, hW, hP]
  noncomm_ring

/-!
### 2. First-order overlap vanishes

tr(P · [W, P]) = 0. The frame doesn't start receding immediately.
Uses only P² = P and cyclicity of trace.
-/

/-- The first-order overlap change vanishes for any projection.
    tr(P · [W, P]) = 0. The frame is stationary to first order. -/
theorem first_order_overlap_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (W P : Matrix n n R) (hP : P * P = P) :
    trace (P * (W * P - P * W)) = 0 := by
  rw [mul_sub, trace_sub]
  have h1 : trace (P * (W * P)) = trace (W * P) := by
    rw [trace_mul_comm, mul_assoc, hP]
  have h2 : trace (P * (P * W)) = trace (W * P) := by
    rw [← mul_assoc, hP, trace_mul_comm]
  rw [h1, h2, sub_self]

/-!
### 3. Second-order overlap identity

tr(P · [W, [W, P]]) = -tr([W, P]²)

Both sides reduce to 2·tr(PW²) - 2·tr(PWPW), using only P² = P
and cyclicity of trace.
-/

/-- The second-order overlap change equals the negative squared
    commutator norm. tr(P · [W, [W, P]]) = -tr([W, P]²). -/
theorem second_order_overlap_identity
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (W P : Matrix n n R) (hP : P * P = P) :
    trace (P * (W * (W * P - P * W) - (W * P - P * W) * W))
    = -trace ((W * P - P * W) * (W * P - P * W)) := by
  have expand_lhs : P * (W * (W * P - P * W) - (W * P - P * W) * W)
      = P * (W * (W * P)) - P * (W * (P * W))
        - P * (W * P * W) + P * (P * W * W) := by noncomm_ring
  have expand_rhs : (W * P - P * W) * (W * P - P * W)
      = W * P * (W * P) - W * P * (P * W)
        - P * W * (W * P) + P * W * (P * W) := by noncomm_ring
  rw [expand_lhs, expand_rhs]
  simp only [trace_sub, trace_add]
  simp only [mul_assoc]
  have h1 : trace (P * (W * (W * P))) = trace (P * (W * W)) := by
    rw [trace_mul_comm P (W * (W * P)), mul_assoc W (W * P) P,
        mul_assoc W P P, hP, ← mul_assoc W W P, trace_mul_comm]
  have h2 : trace (P * (P * (W * W))) = trace (P * (W * W)) := by
    rw [← mul_assoc P P (W * W), hP]
  have h3 : trace (W * (P * (W * P))) = trace (P * (W * (P * W))) := by
    rw [trace_mul_comm W (P * (W * P)), mul_assoc P (W * P) W, mul_assoc W P W]
  have h4 : trace (W * (P * (P * W))) = trace (P * (W * W)) := by
    rw [← mul_assoc P P W, hP, trace_mul_comm W (P * W), mul_assoc P W W]
  rw [h1, h2, h3, h4]
  ring

/-!
### 4. The prior frame can only recede

For real matrices: tr(AᵀA) = Σᵢⱼ Aᵢⱼ² ≥ 0. When A = [W, P] is
symmetric, tr(A²) = tr(AᵀA) ≥ 0.

Combined with the identity: tr(P · [W, [W, P]]) = -tr([W,P]²) ≤ 0.
-/

/-- The Frobenius norm squared tr(AᵀA) is non-negative. -/
theorem trace_transpose_mul_self_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    0 ≤ trace (Aᵀ * A) := by
  show 0 ≤ ∑ i, (Aᵀ * A) i i
  simp only [mul_apply, transpose_apply]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_self_nonneg _

/-- For symmetric real matrices, tr(A²) = tr(AᵀA) ≥ 0. -/
theorem trace_sq_nonneg_of_symmetric
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : Aᵀ = A) :
    0 ≤ trace (A * A) := by
  have : Aᵀ * A = A * A := by rw [hA]
  rw [← this]
  exact trace_transpose_mul_self_nonneg A

/-- **Frame recession.** The second-order overlap change is non-positive.
    The prior frame can only recede under a non-inert write. -/
theorem frame_recession
    {n : Type*} [Fintype n] [DecidableEq n]
    (W P : Matrix n n ℝ) (hW : Wᵀ = -W) (hP_symm : Pᵀ = P) (hP_proj : P * P = P) :
    trace (P * (W * (W * P - P * W) - (W * P - P * W) * W)) ≤ 0 := by
  have h_identity := second_order_overlap_identity W P hP_proj
  have h_symm := commutator_symmetric_of_skew_symm W P hW hP_symm
  have h_nonneg := trace_sq_nonneg_of_symmetric (W * P - P * W) h_symm
  linarith

/-!
### 5. Frobenius norm zero implies matrix zero
-/

/-- If the Frobenius norm squared is zero, every entry is zero. -/
theorem frobenius_eq_zero_of_trace_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ)
    (h : trace (Aᵀ * A) = 0) :
    A = 0 := by
  ext i j
  have h_sum : ∑ k : n, ∑ l : n, A l k * A l k = 0 := by
    convert h using 1
  have h_entry : A i j * A i j = 0 := by
    have h_all_nonneg : ∀ k l : n, 0 ≤ A l k * A l k := fun k l => mul_self_nonneg _
    have h_outer := Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      Finset.sum_nonneg (fun l _ => h_all_nonneg k l)) |>.mp h_sum j (Finset.mem_univ _)
    exact Finset.sum_eq_zero_iff_of_nonneg (fun l _ => h_all_nonneg j l)
      |>.mp h_outer i (Finset.mem_univ _)
  exact mul_self_eq_zero.mp h_entry

/-- **Frame recession is a full characterization.**
    The recession rate is zero if and only if [W, P] = 0.
    When [W, P] ≠ 0, the recession is strictly negative.

    The architecture says "recession happens or it doesn't."
    The geometry determines which. -/
theorem frame_recession_strict
    {n : Type*} [Fintype n] [DecidableEq n]
    (W P : Matrix n n ℝ) (hW : Wᵀ = -W) (hP_symm : Pᵀ = P) (hP_proj : P * P = P)
    (h_noninert : W * P - P * W ≠ 0) :
    trace (P * (W * (W * P - P * W) - (W * P - P * W) * W)) < 0 := by
  have h_identity := second_order_overlap_identity W P hP_proj
  have h_symm := commutator_symmetric_of_skew_symm W P hW hP_symm
  have h_pos : 0 < trace ((W * P - P * W) * (W * P - P * W)) := by
    suffices h : 0 < trace ((W * P - P * W)ᵀ * (W * P - P * W)) by
      rwa [h_symm] at h
    rcases (trace_transpose_mul_self_nonneg (W * P - P * W)).lt_or_eq with h | h
    · exact h
    · exact absurd (frobenius_eq_zero_of_trace_zero _ h.symm) h_noninert
  linarith

end Foam
