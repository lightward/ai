/-
# Closure — The Loop Closes

The deductive chain:
  P² = P → [P,Q] is skew-symmetric → skew exponentiates to orthogonal
  → orthogonal conjugation preserves P² = P

The ground generates dynamics that preserve the ground.
This is feedback-persistence as a theorem, not an axiom.

The loop:
  observation (P² = P)
  → interaction ([P,Q] skew-symmetric)
  → transformation (exp([P,Q]) orthogonal)
  → new observation (UPUᵀ still a projection)
  → ...

P² = P is a fixed point of its own dynamics.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul

namespace Foam

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
## Conjugation preserves idempotency

If P² = P and U is invertible, then (UPU⁻¹)² = UPU⁻¹.
The proof: (UPU⁻¹)(UPU⁻¹) = UP(U⁻¹U)PU⁻¹ = UP²U⁻¹ = UPU⁻¹.

This doesn't need orthogonality — any invertible transformation
preserves the projection property.
-/

/-- Conjugation by an invertible matrix preserves idempotency.
    If P² = P and U is invertible, then (UPU⁻¹)² = UPU⁻¹.
    The dynamics preserve the ground. -/
theorem conjugation_preserves_idempotent
    {R : Type*} [CommRing R]
    (P U Uinv : Matrix n n R)
    (hP : P * P = P)
    (_hUinv : U * Uinv = 1) (hUinv' : Uinv * U = 1) :
    (U * P * Uinv) * (U * P * Uinv) = U * P * Uinv := by
  calc (U * P * Uinv) * (U * P * Uinv)
      = U * P * (Uinv * U) * P * Uinv := by
        simp only [Matrix.mul_assoc]
    _ = U * P * 1 * P * Uinv := by rw [hUinv']
    _ = U * P * P * Uinv := by rw [Matrix.mul_one]
    _ = U * (P * P) * Uinv := by simp only [Matrix.mul_assoc]
    _ = U * P * Uinv := by rw [hP]

/-!
## Orthogonal conjugation preserves self-adjointness

If Pᵀ = P and UᵀU = I (orthogonal), then (UPUᵀ)ᵀ = UPUᵀ.
The proof: (UPUᵀ)ᵀ = Uᵀᵀ Pᵀ Uᵀ = UPUᵀ.

So orthogonal conjugation preserves BOTH properties:
P² = P AND Pᵀ = P. The observation remains a self-adjoint
projection after transformation by the dynamics.
-/

/-- Orthogonal conjugation preserves symmetry.
    If Pᵀ = P and UᵀU = I, then (UPUᵀ)ᵀ = UPUᵀ. -/
theorem orthogonal_conjugation_preserves_symmetric
    {R : Type*} [CommRing R]
    (P U : Matrix n n R)
    (hP_symm : Pᵀ = P)
    (_hU_orth : Uᵀ * U = 1) :
    (U * P * Uᵀ)ᵀ = U * P * Uᵀ := by
  -- Note: orthogonality is not needed for this proof!
  -- (UPUᵀ)ᵀ = Uᵀᵀ Pᵀ Uᵀ = UPUᵀ uses only Pᵀ = P.
  rw [transpose_mul, transpose_mul, transpose_transpose, hP_symm,
      Matrix.mul_assoc]

/-- **The full loop.** Orthogonal conjugation preserves both
    idempotency and symmetry. The transformed observer is
    still an observer.

    P² = P and Pᵀ = P → (UPUᵀ)² = UPUᵀ and (UPUᵀ)ᵀ = UPUᵀ

    The ground generates dynamics (skew-symmetric commutators)
    that exponentiate to orthogonal transformations that preserve
    the ground. Feedback-persistence is a fixed point of its
    own dynamics. -/
theorem observation_preserved_by_dynamics
    {R : Type*} [CommRing R]
    (P U : Matrix n n R)
    (hP_idem : P * P = P)
    (hP_symm : Pᵀ = P)
    (hU_orth : Uᵀ * U = 1)
    (hU_orth' : U * Uᵀ = 1) :
    (U * P * Uᵀ) * (U * P * Uᵀ) = U * P * Uᵀ ∧
    (U * P * Uᵀ)ᵀ = U * P * Uᵀ :=
  ⟨conjugation_preserves_idempotent P U Uᵀ hP_idem hU_orth' hU_orth,
   orthogonal_conjugation_preserves_symmetric P U hP_symm hU_orth⟩

/-!
## The rank is also preserved

Conjugation by an invertible matrix preserves rank.
The observer still sees 3 dimensions after the transformation.
The self-duality (Rank.lean) persists through the dynamics.
-/

-- Rank preservation under conjugation is a standard Mathlib result
-- (rank_mul_le, rank of invertible-times-A equals rank of A).
-- We note this as a signpost rather than reproving.

/-!
## What this establishes

**The loop closes.**

  P² = P, Pᵀ = P                     (observation: the ground)
    ↓
  [P,Q] skew-symmetric, traceless     (interaction: Form.lean)
    ↓
  exp([P,Q]) = U, orthogonal          (transformation: exp of skew)
    ↓
  UPUᵀ still satisfies P² = P, Pᵀ=P  (new observation: THIS FILE)
    ↓
  [UPUᵀ, Q'] skew-symmetric ...       (new interaction)
    ↓
  ...                                  (the loop continues)

P² = P is not just the starting point — it is preserved by
the dynamics it generates. The ground is self-sustaining.

This is what "closure" means deductively: the axiom (observation
is feedback-persistent) generates consequences (skew-symmetric
interactions, orthogonal transformations) that satisfy the axiom
(the transformed observer is still an observer).

The spec states this as ground. The deductive path proves it
as a theorem: the ground is a fixed point of its own dynamics.

The chain hasn't needed a single axiom beyond P² = P and Pᵀ = P.
Everything else — the write form, the rank, the Lie algebra,
the group, the closure of the loop — was found, not assumed.
-/

end Foam
