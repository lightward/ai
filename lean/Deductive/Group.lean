/-
# Group — Orthogonality is Forced

The dynamics must preserve both P² = P and Pᵀ = P.
Symmetry needs nothing; idempotency needs UᵀU = I.
The group is O(d), forced by the ground.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Deductive

open Matrix

/-!
## Helper lemmas about trace and outer products
-/

/-- tr(vvᵀ) = v·v. -/
theorem trace_vecMulVec {d : ℕ}
    (v : Fin d → ℝ) :
    trace (vecMulVec v v) = dotProduct v v := by
  simp [trace, vecMulVec, dotProduct, Matrix.diag]

/-- tr(M · vvᵀ) = v · (Mᵀv). (Note: Mᵀ, not M, due to trace index structure.) -/
theorem trace_mul_vecMulVec {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    trace (M * vecMulVec v v) = dotProduct v (Mᵀ.mulVec v) := by
  simp only [trace, Matrix.diag, mul_apply, vecMulVec, Matrix.of_apply,
             dotProduct, mulVec, transpose_apply]
  conv_lhs => rw [Finset.sum_comm]
  congr 1; ext j
  have : ∀ x, M x j * (v j * v x) = v j * (M x j * v x) := fun x => by ring
  simp_rw [this, ← Finset.mul_sum]

/-- vvᵀ is idempotent when v is unit. -/
theorem vecMulVec_sq {d : ℕ}
    (v : Fin d → ℝ) (hv : dotProduct v v = 1) :
    vecMulVec v v * vecMulVec v v = vecMulVec v v := by
  ext i j
  simp only [mul_apply, vecMulVec, Matrix.of_apply]
  have : ∑ k : Fin d, v i * v k * (v k * v j) =
         v i * (∑ k, v k * v k) * v j := by
    rw [Finset.mul_sum, Finset.sum_mul]; congr 1; ext k; ring
  rw [this]; simp only [dotProduct] at hv; rw [hv]; ring

/-!
## Scalar extraction — THE key theorem
-/

/-- **Scalar extraction.** If vvᵀ · M · vvᵀ = vvᵀ for a unit vector,
    then vᵀMv = 1.

    Proof: take trace of both sides. Cyclicity + P² = P reduces
    tr(PMP) to tr(MP). And tr(MP) = vᵀMv.

    This is why the orthogonal group is forced. -/
theorem scalar_extraction {d : ℕ}
    (v : Fin d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (hv : dotProduct v v = 1)
    (hM : Mᵀ = M)
    (h : vecMulVec v v * M * vecMulVec v v = vecMulVec v v) :
    dotProduct v (M.mulVec v) = 1 := by
  -- Take trace of both sides
  have h_tr := congr_arg trace h
  -- RHS: tr(vvᵀ) = 1
  rw [trace_vecMulVec, hv] at h_tr
  -- LHS: tr(vvᵀ · M · vvᵀ) = tr(vvᵀ · (vvᵀ · M)) by cyclicity
  rw [show vecMulVec v v * M * vecMulVec v v =
      vecMulVec v v * (M * vecMulVec v v) from by rw [Matrix.mul_assoc]] at h_tr
  rw [Matrix.trace_mul_comm] at h_tr
  -- Now: tr(M · vvᵀ · vvᵀ) = 1
  rw [Matrix.mul_assoc, vecMulVec_sq v hv] at h_tr
  -- Now: tr(M · vvᵀ) = 1
  rw [trace_mul_vecMulVec, hM] at h_tr
  exact h_tr

/-!
## What this establishes

**Scalar extraction: proven, zero sorry.**

For any unit vector v: if the rank-1 projection P = vvᵀ satisfies
P · M · P = P, then vᵀMv = 1.

Applied to the dynamics: if U conjugates every rank-1 projection
to an idempotent (UPUᵀ is idempotent), we showed in Closure.lean
that this requires P · (UᵀU) · P = P. Scalar extraction then gives
vᵀ(UᵀU)v = ‖Uv‖² = 1 for all unit v.

**U preserves all norms. UᵀU = I. U is orthogonal.**

The group is O(d). Not chosen. Forced by P² = P.

  P² = P, Pᵀ = P           (observation)
  ├── [P,Q] ∈ so(d)         (interaction is skew)
  ├── exp(so(d)) ⊆ O(d)     (skew → orthogonal)
  ├── O(d) preserves P²=P   (Closure.lean)
  └── ONLY O(d) preserves    (scalar_extraction: THIS FILE)
       P²=P for all rank-1 P
-/

end Deductive
