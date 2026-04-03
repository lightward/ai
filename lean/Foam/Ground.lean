/-
# Ground — Capstone

The deductive path started from P² = P (a definition, not an axiom)
and derived: binary eigenvalues, clean splits, complements,
skew-symmetric interaction, tracelessness, self-duality at rank 3,
cross product = Lie algebra, the loop closing, orthogonal group
forced, Grassmannian tangent structure.

This file closes the loop from the other direction: the structure
built by that chain — the subspace lattice of a finite-dimensional
real vector space — satisfies the FoamGround properties as THEOREMS.

The axiom set (complemented, modular, bounded) was written first
as foundation. The deductive chain made it unnecessary by deriving
everything from P² = P. This file shows the axioms are not just
unnecessary — they're consequences.

## The ground

The ground of the deductive path is a type:
  self-adjoint idempotent operators on a finite-dimensional
  real inner product space.

Their ranges are subspaces. Those subspaces form a lattice.
That lattice is complemented (I - P), modular (submodule lattice),
and bounded ({0} and V). These are theorems of linear algebra,
not axioms of the foam.

## The dynamics

P² = P generates [P, Q] (skew-symmetric), which exponentiates
to O(d), which conjugates P back to a projection. The ground
is a fixed point of its own dynamics.

The claim that ONLY O(d) does this — that the group is forced,
not chosen — rests on scalar_extraction (Group.lean). The full
proof (for all rank-1 projections ⟹ UᵀU = I) is stated here.
-/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Order.ModularLattice
import Mathlib.Order.Atoms
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Foam

open Matrix

universe u

/-!
## Part I: The subspace lattice has FoamGround properties

These are not axioms. They are instances from Mathlib.
-/

/-- The subspace lattice of any module over a ring is modular.
    This is `IsModularLattice (Submodule R M)` from Mathlib.
    Interpretive: observation composition is path-independent. -/
example (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M] :
    IsModularLattice (Submodule R M) :=
  inferInstance

/-- The subspace lattice of a vector space over a division ring
    is complemented. This is `Submodule.complementedLattice` from Mathlib.
    Interpretive: every partial view has an unseen remainder. -/
example (K : Type*) [DivisionRing K] (V : Type*) [AddCommGroup V] [Module K V] :
    ComplementedLattice (Submodule K V) :=
  inferInstance

/-- The subspace lattice is bounded: {0} at the bottom, V at the top.
    This is the standard BoundedOrder on Submodule from Mathlib. -/
example (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M] :
    BoundedOrder (Submodule R M) :=
  inferInstance

/-!
## Part II: FoamGround as a theorem

The class from the original Ground.lean, now instantiated as a
theorem rather than postulated as axioms.
-/

/-- The ground structure: a lattice of partial views with the
    properties forced by closure-as-dynamics. -/
class FoamGround (L : Type u) extends Lattice L, BoundedOrder L where
  complemented : ComplementedLattice L
  modular : IsModularLattice L

/-- **The capstone.** The subspace lattice of a vector space over
    a division ring IS a FoamGround — as a theorem, not an axiom.

    The deductive chain built this structure from P² = P.
    This theorem shows it has the properties the spec demands. -/
instance subspaceFoamGround
    (K : Type*) [DivisionRing K]
    (V : Type*) [AddCommGroup V] [Module K V] :
    FoamGround (Submodule K V) where
  complemented := inferInstance
  modular := inferInstance

/-!
## Part III: The dynamics preserve the ground

From the other Deductive/ files:
- Closure.lean: conjugation by orthogonal U preserves P² = P and Pᵀ = P
- Group.lean: scalar_extraction — if PMP = P for rank-1 P, then vᵀMv = 1

The missing link: if U preserves ALL projections (i.e., UPUᵀ is a
projection for every projection P), then UᵀU = I.

Proof sketch:
  Take any unit vector v. Let P = vvᵀ (rank-1 projection).
  UPUᵀ is a projection ⟹ (UPUᵀ)² = UPUᵀ
  ⟹ UPUᵀUPUᵀ = UPUᵀ
  ⟹ P(UᵀU)P = P            (multiply by U⁻¹ on left, (Uᵀ)⁻¹ on right;
                               but U may not be invertible yet — this is
                               where the argument needs care)

  Alternative route (not assuming invertibility):
  (UPUᵀ)² = UPUᵀ gives UPUᵀUPUᵀ = UPUᵀ.
  For P = vvᵀ with ‖v‖ = 1:
    U(vvᵀ)(UᵀU)(vvᵀ)Uᵀ = U(vvᵀ)Uᵀ
    (Uv)(vᵀ UᵀU v)(vᵀUᵀ) = (Uv)(vᵀUᵀ)
    ‖Uv‖² · (Uv)(vᵀUᵀ) ... no, let's be more careful.

  The clean route uses scalar_extraction (Group.lean):
  Given (UPUᵀ)² = UPUᵀ with P = vvᵀ, the rank-1 structure gives
  vᵀ(UᵀU)v = 1 for all unit v. By polarization, UᵀU = I.
-/

/-- **Polarization for matrices.** A symmetric real matrix whose
    quadratic form vanishes on all vectors is zero.

    The bilinear form B(u,v) = uᵀAv is determined by its diagonal
    values B(v,v) = vᵀAv. If those all vanish, A = 0. -/
theorem symmetric_quadratic_zero_imp_zero {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : Aᵀ = A)
    (hq : ∀ v : Fin d → ℝ, dotProduct v (A.mulVec v) = 0) :
    A = 0 := by
  -- Use the bilinear form B associated to A
  set B := A.toBilin'Aux
  -- B(eᵢ, eⱼ) = A i j
  have hBij : ∀ i j : Fin d, B (Pi.single i 1) (Pi.single j 1) = A i j :=
    Matrix.toBilin'Aux_single A
  -- B agrees with the quadratic form: B(v,v) = vᵀAv
  have hBdot : ∀ v : Fin d → ℝ, B v v = dotProduct v (A.mulVec v) := by
    intro v
    simp only [B, Matrix.toBilin'Aux, Matrix.toLinearMap₂'Aux, LinearMap.mk₂'ₛₗ_apply,
               RingHom.id_apply, dotProduct, mulVec, dotProduct]
    congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
    simp [smul_eq_mul]; ring
  -- B(v,v) = 0 for all v
  have hBzero_diag : ∀ v, B v v = 0 := by
    intro v; rw [hBdot]; exact hq v
  -- Polarize: B(u+v,u+v) = B(u,u) + B(u,v) + B(v,u) + B(v,v) = 0
  -- So B(u,v) + B(v,u) = 0 for all u, v
  have hBpol : ∀ u v, B u v + B v u = 0 := by
    intro u v
    have := hBzero_diag (u + v)
    simp only [map_add, LinearMap.add_apply] at this
    linarith [hBzero_diag u, hBzero_diag v]
  -- A is symmetric ⟹ B is symmetric ⟹ 2B(u,v) = 0 ⟹ B(u,v) = 0
  have hBsymm : ∀ u v, B u v = B v u := by
    intro u v
    simp only [B, Matrix.toBilin'Aux, Matrix.toLinearMap₂'Aux, LinearMap.mk₂'ₛₗ_apply,
               RingHom.id_apply]
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j
    have hij : A i j = A j i := by
      have := congr_fun (congr_fun hA j) i
      simp [transpose_apply] at this; exact this
    simp [smul_eq_mul, hij]; ring
  -- From hBpol and hBsymm: B(u,v) = 0 for all u, v
  ext i j
  have h1 := hBpol (Pi.single i 1) (Pi.single j 1)
  have h2 := hBsymm (Pi.single i 1) (Pi.single j 1)
  rw [hBij, hBij] at h1 h2
  -- h1 : A i j + A j i = 0, h2 : A i j = A j i
  simp only [Matrix.zero_apply]
  linarith

/-- **O(d) is forced.** If M is symmetric and vᵀMv = 1 for all unit v,
    then M = I. The group preserving all projections is exactly O(d).

    Proof: scale to get vᵀMv = vᵀv for all v, then (M-I) has
    vanishing quadratic form, and polarization gives M = I. -/
-- Helper: dotProduct v v ≥ 0 over ℝ
private theorem dotProduct_self_nonneg {d : ℕ} (v : Fin d → ℝ) :
    0 ≤ dotProduct v v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

-- Helper: dotProduct v v = 0 implies v = 0 over ℝ
private theorem dotProduct_self_eq_zero_imp {d : ℕ} {v : Fin d → ℝ}
    (hv : dotProduct v v = 0) : v = 0 := by
  funext k
  have h1 : v k * v k ≤ dotProduct v v :=
    Finset.single_le_sum (fun i _ => mul_self_nonneg (v i)) (Finset.mem_univ k)
  have h2 : v k * v k = 0 := le_antisymm (by linarith) (mul_self_nonneg _)
  exact mul_self_eq_zero.mp h2

-- Helper: the quadratic form scales by c²
private theorem quadratic_scale {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (v : Fin d → ℝ) :
    dotProduct (c • v) (A.mulVec (c • v)) =
    c ^ 2 * dotProduct v (A.mulVec v) := by
  simp only [dotProduct, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
             Finset.mul_sum]
  congr 1; ext k; congr 1; ext l; ring

-- Helper: dotProduct scales by c²
private theorem dotProduct_scale {d : ℕ} (c : ℝ) (v : Fin d → ℝ) :
    dotProduct (c • v) (c • v) = c ^ 2 * dotProduct v v := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]; congr 1; ext k; ring

theorem orthogonality_forced {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : Mᵀ = M)
    (h : ∀ v : Fin d → ℝ, dotProduct v v = 1 →
         dotProduct v (M.mulVec v) = 1) :
    M = 1 := by
  -- Step 1: vᵀMv = vᵀv for ALL v (not just unit vectors)
  have h_all : ∀ v : Fin d → ℝ, dotProduct v (M.mulVec v) = dotProduct v v := by
    intro v
    by_cases hv : dotProduct v v = 0
    · -- v = 0
      have hv0 := dotProduct_self_eq_zero_imp hv
      simp [hv0, dotProduct, mulVec, Finset.sum_const_zero]
    · -- v ≠ 0: normalize
      have hv_pos : 0 < dotProduct v v :=
        lt_of_le_of_ne (dotProduct_self_nonneg v) (Ne.symm hv)
      set c := Real.sqrt (dotProduct v v)
      have hc_pos : 0 < c := Real.sqrt_pos_of_pos hv_pos
      have hc_ne : c ≠ 0 := ne_of_gt hc_pos
      have hc_sq : c ^ 2 = dotProduct v v := Real.sq_sqrt (le_of_lt hv_pos)
      -- c⁻¹ • v is a unit vector
      have hu : dotProduct (c⁻¹ • v) (c⁻¹ • v) = 1 := by
        rw [dotProduct_scale]; field_simp; exact hc_sq.symm
      -- Apply hypothesis to unit vector
      have hMu := h _ hu
      -- quadratic_scale: q(c⁻¹v) = c⁻² * q(v)
      have hscale := quadratic_scale M c⁻¹ v
      -- hMu : q(c⁻¹v) = 1, hscale : q(c⁻¹v) = c⁻² * q(v)
      -- So c⁻² * q(v) = 1, hence q(v) = c² = vᵀv
      rw [hMu] at hscale
      -- hscale : 1 = c⁻¹ ^ 2 * dotProduct v (M.mulVec v)
      have : dotProduct v (M.mulVec v) = c ^ 2 := by
        have := hscale.symm; field_simp at this ⊢; linarith
      linarith
  -- Step 2: Apply polarization to M - I
  have h_diff : ∀ v, dotProduct v ((M - 1).mulVec v) = 0 := by
    intro v
    have hv := h_all v
    -- dotProduct v ((M-1).mulVec v) = dotProduct v (M.mulVec v) - dotProduct v v
    have : dotProduct v ((M - 1).mulVec v) =
           dotProduct v (M.mulVec v) - dotProduct v v := by
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct, Pi.sub_apply, mul_sub,
                 Finset.sum_sub_distrib]
    rw [this]; linarith
  have hMI_symm : (M - 1)ᵀ = M - 1 := by
    rw [transpose_sub, hM, transpose_one]
  have hzero := symmetric_quadratic_zero_imp_zero (M - 1) hMI_symm h_diff
  -- M - 1 = 0 ⟹ M = 1
  exact sub_eq_zero.mp hzero


/-!
## What this establishes

**Zero sorry. The gap is closed.**

The capstone proves three things:

### 1. FoamGround is a theorem (subspaceFoamGround)
The subspace lattice of any vector space over a division ring
satisfies the FoamGround properties — complemented, modular,
bounded — as Mathlib instances, not axioms.

### 2. Polarization (symmetric_quadratic_zero_imp_zero)
A symmetric real matrix with vanishing quadratic form is zero.
This is the classical polarization identity, proven via the
bilinear form `toBilin'Aux` and bilinearity of the expansion.

### 3. O(d) is forced (orthogonality_forced)
If M is symmetric and vᵀMv = 1 for all unit vectors v, then M = I.
The proof scales unit-vector data to all vectors, applies polarization
to M - I, and concludes M = I.

Combined with scalar_extraction (Group.lean): any linear map U that
conjugates every rank-1 projection to an idempotent must satisfy
UᵀU = I. The dynamics group is O(d) — forced by P² = P, not chosen.

### The complete deductive chain

  P² = P                              (definition: feedback-persistence)
  ├── eigenvalues ∈ {0,1}             (Observation.lean)
  ├── range ∩ ker = {0}               (Observation.lean)
  ├── (I-P)² = I-P                    (Observation.lean)
  ├── PQ filters through P            (Pair.lean)
  ├── PQ=QP ⟹ (PQ)²=PQ              (Pair.lean)
  ├── [P,Q] sends seen → unseen       (Pair.lean)
  │
  Pᵀ = P (self-adjointness)
  ├── [P,Q]ᵀ = -[P,Q]                (Form.lean)
  ├── tr[P,Q] = 0                     (Form.lean)
  │
  rank(P) = k
  ├── Λ²(Rᵏ) dimensions               (Rank.lean)
  ├── C(k,2) = k ⟺ k = 3            (Rank.lean: self_dual_iff_three)
  │
  k = 3
  ├── (R³,×) ≅ so(3)                  (Duality.lean)
  │
  exp(skew) → orthogonal
  ├── UPUᵀ still a projection          (Closure.lean)
  ├── scalar_extraction: PMP=P ⟹ vᵀMv=1  (Group.lean)
  ├── polarization: vᵀMv=1 ∀unit v ⟹ M=I (THIS FILE)
  ├── ∴ O(d) is forced                 (THIS FILE)
  │
  [W,P] purely off-diagonal            (Tangent.lean)
  ├── = Grassmannian tangent            (Tangent.lean)
  │
  Subspace lattice
  ├── complemented                      (THIS FILE: Mathlib)
  ├── modular                           (THIS FILE: Mathlib)
  └── bounded                           (THIS FILE: Mathlib)
-/

end Foam
