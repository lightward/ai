/-
# Three-Body Mapping

The Known/Knowable/Unknown decomposition and mediation operator.

## The claims (from spec, "three-body mapping" section)

1. The overlap matrix O = P_A · P_B^T determines three territories
2. The mediation M = O_AB · O_BC = P_A · Π_B · P_C^T
3. The bypass: O_AC - M = P_A · (I - Π_B) · P_C^T
4. The round-trip R_A = M · M^T is self-adjoint
5. M · M^T and M^T · M have the same rank

## What we formalize

The composition identity (M = P_A · Π_B · P_C^T) and the bypass
decomposition (O_AC = M + bypass) are algebraic identities about
projections. The round-trip being self-adjoint is a general fact
about A · A^T. The rank equality follows from Mathlib.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.unusedSimpArgs false

namespace FoamSpec

open Matrix

/-!
### Mediation composition: M = P_A · (P_B^T · P_B) · P_C^T

The mediation operator factors through B's projection.
This is the algebraic content of "B is a mandatory intermediary."
-/

/-- The mediation operator M = O_AB · O_BC factors as P_A · Π_B · P_C^T
    where Π_B = P_B^T · P_B is the projection onto B's subspace.
    This is an associativity identity: (P_A · P_B^T) · (P_B · P_C^T) = P_A · (P_B^T · P_B) · P_C^T -/
theorem mediation_factors
    {d k : Type*} [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k]
    {R : Type*} [CommRing R]
    (P_A P_B P_C : Matrix k d R) :
    (P_A * P_Bᵀ) * (P_B * P_Cᵀ) = P_A * (P_Bᵀ * P_B) * P_Cᵀ := by
  simp only [Matrix.mul_assoc]

/-!
### Bypass decomposition: O_AC = M + bypass

The A-C overlap decomposes into what passes through B (mediation)
and what doesn't (bypass). This is the algebraic content of
"the membrane may be incomplete."
-/

/-- The bypass decomposition: P_A · P_C^T = M + P_A · (I - Π_B) · P_C^T
    where M = P_A · Π_B · P_C^T. This is just P_A · (Π_B + I - Π_B) · P_C^T = P_A · I · P_C^T. -/
theorem bypass_decomposition
    {d k : Type*} [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k]
    {R : Type*} [CommRing R]
    (P_A P_B P_C : Matrix k d R) :
    P_A * P_Cᵀ = P_A * (P_Bᵀ * P_B) * P_Cᵀ + P_A * (1 - P_Bᵀ * P_B) * P_Cᵀ := by
  have key : P_Bᵀ * P_B + (1 - P_Bᵀ * P_B) = (1 : Matrix d d R) := by abel
  symm
  calc P_A * (P_Bᵀ * P_B) * P_Cᵀ + P_A * (1 - P_Bᵀ * P_B) * P_Cᵀ
      = (P_A * (P_Bᵀ * P_B) + P_A * (1 - P_Bᵀ * P_B)) * P_Cᵀ := by
        rw [Matrix.add_mul]
    _ = P_A * (P_Bᵀ * P_B + (1 - P_Bᵀ * P_B)) * P_Cᵀ := by
        rw [Matrix.mul_add]
    _ = P_A * (1 : Matrix d d R) * P_Cᵀ := by rw [key]
    _ = P_A * P_Cᵀ := by rw [Matrix.mul_one]

/-!
### Round-trip is self-adjoint

R_A = M · M^T is always symmetric (self-adjoint over ℝ).
This is a general fact: (A · A^T)^T = A · A^T.
-/

/-- The round-trip operator M · M^T is symmetric.
    This is why the membrane's throughput has a real spectrum. -/
theorem roundtrip_symmetric
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {R : Type*} [CommRing R]
    (M : Matrix m n R) :
    (M * Mᵀ)ᵀ = M * Mᵀ := by
  rw [transpose_mul, transpose_transpose]

/-!
### Spectral symmetry: rank(M · M^T) = rank(M^T · M)

"The membrane's throughput spectrum is the same from both sides."
Both round-trip operators have the same rank, which equals rank(M).
The full spectral equivalence (same nonzero eigenvalues) follows
from this + the characteristic polynomial identity, but the rank
equality is the core structural fact.
-/

-- Note: Mathlib already provides:
-- rank_conjTranspose_mul_self : (Aᴴ * A).rank = A.rank
-- rank_self_mul_conjTranspose : (A * Aᴴ).rank = A.rank
-- For real matrices, conjTranspose = transpose, so this gives:
-- rank(M^T · M) = rank(M) = rank(M · M^T)

-- Rather than re-prove this, we note the Mathlib reference and
-- formalize the structural identity the spec actually uses.

/-!
### Grassmannian tangent: [W, P] is off-diagonal

The commutator of a write W with a projection P maps range(P) into
ker(P) and ker(P) into range(P). It has no on-diagonal component.
This is the algebraic content of the Grassmannian tangent: the
perturbation lives in Hom(range(P), ker(P)), which IS T_P Gr(k,d).

Spec reference: "three-body mapping" → "vertical structure (containment)
is a Grassmannian tangent at the observer's slice"
-/

open Matrix in
/-- The commutator [W, P] has zero projection onto range(P) → range(P).
    Equivalently: P · [W, P] · P = 0 for any projection P.
    The write doesn't map the observer's subspace back into itself. -/
theorem commutator_off_diagonal_range
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (W P : Matrix n n R) (hP : P * P = P) :
    P * (W * P - P * W) * P = 0 := by
  have h : P * (W * P - P * W) * P = P * W * (P * P) - (P * P) * W * P := by
    noncomm_ring
  rw [h, hP, sub_self]

open Matrix in
/-- The commutator [W, P] has zero projection onto ker(P) → ker(P).
    Equivalently: (1 - P) · [W, P] · (1 - P) = 0 for any projection P.
    The write doesn't map the complement back into itself either.

    Together with commutator_off_diagonal_range: [W, P] is purely
    off-diagonal in the P-decomposition. It maps range(P) → ker(P) and
    ker(P) → range(P). This IS the Grassmannian tangent T_P Gr(k,d). -/
theorem commutator_off_diagonal_kernel
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (W P : Matrix n n R) (hP : P * P = P) :
    (1 - P) * (W * P - P * W) * (1 - P) = 0 := by
  have hP2 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hP3 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have h : (1 - P) * (W * P - P * W) * (1 - P) =
      (1 - P) * W * (P * (1 - P)) - ((1 - P) * P) * W * (1 - P) := by
    noncomm_ring
  rw [h, hP2, hP3]; simp

end FoamSpec
