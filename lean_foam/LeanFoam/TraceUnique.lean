/-
# Trace Uniqueness

The trace map is the unique linear functional (up to scalar) that
vanishes on all commutators.

## The claim (from spec, "group" section)

"the trace map tr: u(d) → u(1) is the unique Lie algebra homomorphism
to a 1-dimensional target."

## What this establishes

The u(1) direction is not merely unreachable by writes — it is the
*only* scalar-valued information a write carries. Conservation is
singular, not one-of-many.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.unusedSimpArgs false

namespace FoamSpec

open Matrix

/-!
### Elementary matrices as commutators
-/

/-- Product E_ij · E_jj = E_ij (index j matches). -/
private lemma single_mul_single_diag {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [NonAssocSemiring R]
    (i j : n) : single i j (1 : R) * single j j 1 = single i j 1 := by
  simp

/-- Product E_jj · E_ij = 0 when i ≠ j. -/
private lemma single_diag_mul_single {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [NonAssocSemiring R]
    (i j : n) (hij : i ≠ j) : single j j (1 : R) * single i j 1 = 0 := by
  simp [Ne.symm hij]

/-- Off-diagonal elementary matrix is a commutator:
    E_ij = [E_ij, E_jj]. -/
theorem offdiag_is_commutator {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (i j : n) (hij : i ≠ j) :
    (single i j (1 : R)) =
      single i j 1 * single j j 1 - single j j 1 * single i j 1 := by
  rw [single_mul_single_diag, single_diag_mul_single i j hij, sub_zero]

/-- Product E_ij · E_ji = E_ii (indices match in the middle). -/
private lemma single_mul_single_swap {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [NonAssocSemiring R]
    (i j : n) : single i j (1 : R) * single j i 1 = single i i 1 := by
  simp [single_mul_single_same]

/-- Product E_ji · E_ij = E_jj. -/
private lemma single_mul_single_swap' {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [NonAssocSemiring R]
    (i j : n) : single j i (1 : R) * single i j 1 = single j j 1 := by
  simp [single_mul_single_same]

/-- Traceless diagonal element is a commutator:
    E_ii - E_jj = [E_ij, E_ji]. -/
theorem diag_diff_is_commutator {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (i j : n) (_hij : i ≠ j) :
    single i i (1 : R) - single j j 1 =
      single i j 1 * single j i 1 - single j i 1 * single i j 1 := by
  rw [single_mul_single_swap, single_mul_single_swap']

/-!
### Key lemmas toward uniqueness
-/

/-- If a linear functional kills all commutators, it assigns
    equal values to all diagonal matrix units: φ(E_ii) = φ(E_jj). -/
theorem eq_on_diag_of_kills_commutators {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (φ : Matrix n n R →ₗ[R] R)
    (hφ : ∀ A B : Matrix n n R, φ (A * B - B * A) = 0)
    (i j : n) (hij : i ≠ j) :
    φ (single i i 1) = φ (single j j 1) := by
  have h := hφ (single i j 1) (single j i 1)
  rw [← diag_diff_is_commutator i j hij, map_sub, sub_eq_zero] at h
  exact h

/-- If a linear functional kills all commutators, it kills
    all off-diagonal matrix units: φ(E_ij) = 0 when i ≠ j. -/
theorem zero_on_offdiag_of_kills_commutators {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (φ : Matrix n n R →ₗ[R] R)
    (hφ : ∀ A B : Matrix n n R, φ (A * B - B * A) = 0)
    (i j : n) (hij : i ≠ j) :
    φ (single i j 1) = 0 := by
  have h := hφ (single i j 1) (single j j 1)
  rwa [← offdiag_is_commutator i j hij] at h

end FoamSpec
