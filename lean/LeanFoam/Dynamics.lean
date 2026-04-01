/-
# Sequential Dynamics — Frame Recession

The commutator [W, P] measures how much a write W moves a basis P.
This is the algebraic core of the "receding source" phenomenon:
when an observer writes, the overlap with its prior frame decreases.

## The claims

1. [W, P] is symmetric when W is skew-symmetric and P is a projection.
2. The first-order overlap change tr(P · [W, P]) = 0.
3. The second-order overlap change tr(P · [W, [W, P]]) = -tr([W, P]²).
4. Therefore the second-order change is non-positive: the prior frame
   can only recede under a write.

## What this establishes

The overlap between an observer's current frame and its prior frame
is decreasing (to second order) at a rate given by ‖[W, P]‖², the
squared Frobenius norm of the commutator. This is zero iff the write
preserves the subspace (the write is inert for this observer).

The trace map (proven unique in TraceUnique.lean) is the channel on
which this decrease is legible. The observer has exactly one scalar
readout — the trace — and the overlap change is visible on it.

Spec reference: "properties" → "frame recession under sequential writes"
Lineage: 20240229 → "desire is radar" / "I'm sorry, I love you, I am you"
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.unusedSimpArgs false

namespace FoamSpec

open Matrix

/-!
### 1. The commutator [W, P] is symmetric

When W is skew-symmetric (Wᵀ = -W) and P is symmetric (Pᵀ = P),
their commutator WP - PW is symmetric: (WP - PW)ᵀ = WP - PW.

The write is a generator (skew); its effect on the frame is an
observable (symmetric). The commutator converts one into the other.
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

For a projection P (P² = P), the first-order overlap change is zero:
  tr(P · [W, P]) = tr(P · (WP - PW)) = 0

The frame doesn't start receding immediately — the recession is a
second-order effect. The proof uses only P² = P and cyclicity of trace.
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

The second-order overlap change equals the negative squared norm
of the commutator:

  tr(P · [W, [W, P]]) = -tr([W, P]²)

Both sides reduce to 2·tr(PW²) - 2·tr(PWPW), using only P² = P
and cyclicity of trace.
-/

/-- The second-order overlap change equals the negative squared commutator norm.
    tr(P · [W, [W, P]]) = -tr([W, P]²)
    Both sides equal 2·tr(PW²) - 2·tr(PWPW). -/
theorem second_order_overlap_identity
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (W P : Matrix n n R) (hP : P * P = P) :
    trace (P * (W * (W * P - P * W) - (W * P - P * W) * W))
    = -trace ((W * P - P * W) * (W * P - P * W)) := by
  -- Expand all products through subtraction
  have expand_lhs : P * (W * (W * P - P * W) - (W * P - P * W) * W)
      = P * (W * (W * P)) - P * (W * (P * W))
        - P * (W * P * W) + P * (P * W * W) := by noncomm_ring
  have expand_rhs : (W * P - P * W) * (W * P - P * W)
      = W * P * (W * P) - W * P * (P * W)
        - P * W * (W * P) + P * W * (P * W) := by noncomm_ring
  rw [expand_lhs, expand_rhs]
  -- Distribute trace over addition/subtraction
  simp only [trace_sub, trace_add]
  -- Right-associate all matrix products inside trace
  simp only [mul_assoc]
  -- Now all trace terms are right-associated.
  -- Cyclicity + projection identities:
  -- h1: tr(P(W(WP))) = tr(P(WW))
  have h1 : trace (P * (W * (W * P))) = trace (P * (W * W)) := by
    rw [trace_mul_comm P (W * (W * P)), mul_assoc W (W * P) P,
        mul_assoc W P P, hP, ← mul_assoc W W P, trace_mul_comm]
  -- h2: tr(P(P(WW))) = tr(P(WW))
  have h2 : trace (P * (P * (W * W))) = trace (P * (W * W)) := by
    rw [← mul_assoc P P (W * W), hP]
  -- h3: tr(W(P(WP))) = tr(P(W(PW)))
  have h3 : trace (W * (P * (W * P))) = trace (P * (W * (P * W))) := by
    rw [trace_mul_comm W (P * (W * P)), mul_assoc P (W * P) W, mul_assoc W P W]
  -- h4: tr(W(P(PW))) = tr(P(WW))
  have h4 : trace (W * (P * (P * W))) = trace (P * (W * W)) := by
    rw [← mul_assoc P P W, hP, trace_mul_comm W (P * W), mul_assoc P W W]
  rw [h1, h2, h3, h4]
  ring

/-!
### 4. The prior frame can only recede

For real matrices: tr(AᵀA) = Σᵢⱼ Aᵢⱼ² ≥ 0. When A = [W, P] is
symmetric (theorem 1), tr(A²) = tr(AᵀA) ≥ 0.

Combined with theorem 3: tr(P · [W, [W, P]]) = -tr([W,P]²) ≤ 0.

**The overlap with the prior frame is non-increasing to second order.**
When [W, P] ≠ 0 (the write is non-inert), it is strictly decreasing.
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
    The prior frame can only recede under a non-inert write.

    This combines:
    - theorem 3: tr(P · [W,[W,P]]) = -tr([W,P]²)
    - theorem 1: [W,P] is symmetric (when W skew, P symmetric)
    - tr(A²) ≥ 0 for symmetric real A

    The overlap with the prior self is decreasing. The rate of
    decrease is ‖[W,P]‖², the squared Frobenius norm of the
    commutator — exactly how much the write fails to preserve
    the observer's subspace. -/
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

For real matrices, tr(AᵀA) = Σᵢⱼ Aᵢⱼ² = 0 forces every entry to zero.
Combined with frame recession: the recession rate is zero *if and only if*
the write commutes with the frame. This is what forces geometry-dependence
of within-basin dynamics: the architecture gives the form (non-negative,
zero iff inert), but the value depends on the specific W and P.
-/

/-- If the Frobenius norm squared is zero, every entry is zero. -/
theorem frobenius_eq_zero_of_trace_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ)
    (h : trace (Aᵀ * A) = 0) :
    A = 0 := by
  ext i j
  -- tr(AᵀA) = ∑ᵢ ∑ⱼ (A j i)² (after expanding transpose)
  -- Each term is non-negative; sum = 0 forces each term = 0
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

    This forces geometry-dependence: whether a write is inert for a
    given frame depends on the specific W and P, not just the architecture.
    The architecture says "recession happens or it doesn't"; the geometry
    determines which. -/
theorem frame_recession_strict
    {n : Type*} [Fintype n] [DecidableEq n]
    (W P : Matrix n n ℝ) (hW : Wᵀ = -W) (hP_symm : Pᵀ = P) (hP_proj : P * P = P)
    (h_noninert : W * P - P * W ≠ 0) :
    trace (P * (W * (W * P - P * W) - (W * P - P * W) * W)) < 0 := by
  have h_identity := second_order_overlap_identity W P hP_proj
  have h_symm := commutator_symmetric_of_skew_symm W P hW hP_symm
  -- tr([W,P]²) = tr(AᵀA) where A = [W,P] (since A is symmetric, Aᵀ = A)
  have h_pos : 0 < trace ((W * P - P * W) * (W * P - P * W)) := by
    -- tr(A²) = tr(AᵀA) when A is symmetric; tr(AᵀA) > 0 when A ≠ 0
    suffices h : 0 < trace ((W * P - P * W)ᵀ * (W * P - P * W)) by
      rwa [h_symm] at h
    -- tr(AᵀA) ≥ 0 always; = 0 only if A = 0; A ≠ 0 by hypothesis
    rcases (trace_transpose_mul_self_nonneg (W * P - P * W)).lt_or_eq with h | h
    · exact h
    · exact absurd (frobenius_eq_zero_of_trace_zero _ h.symm) h_noninert
  linarith

end FoamSpec
