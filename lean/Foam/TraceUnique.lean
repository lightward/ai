/-
# Trace Uniqueness — One Scalar Readout

The trace map is the unique linear functional (up to scalar) that
vanishes on all commutators.

This connects to Form.lean: the commutator [P,Q] is traceless.
Trace uniqueness says trace is the ONLY functional with this
property. Combined: there is exactly one scalar channel, and
observation interaction is invisible to it.

The deductive chain:
  P² = P → [P,Q] traceless (Form.lean)
  Matrix algebras → trace unique (THIS FILE)
  Combined: the conserved direction is singular, not one-of-many
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.unusedSimpArgs false

namespace Foam

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

/-!
### Capstone: trace uniqueness
-/

/-- Any matrix decomposes into scaled elementary matrices. -/
private lemma matrix_sum_single {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (A : Matrix n n R) :
    A = ∑ i : n, ∑ j : n, A i j • single i j (1 : R) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, single_apply, smul_eq_mul,
             mul_ite, mul_one, mul_zero]
  have inner : ∀ i : n,
      ∑ j : n, (if i = a ∧ j = b then A i j else 0) =
      if i = a then A i b else 0 := by
    intro i
    by_cases hi : i = a
    · subst hi
      simp only [true_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · simp only [hi, false_and, ite_false, Finset.sum_const_zero]
  simp_rw [inner, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Trace uniqueness.** Any linear functional killing all commutators
    is a scalar multiple of the trace. The trace is the unique such
    functional up to scalar.

    Combined with commutator_traceless (Form.lean): trace itself kills
    all commutators. So the commutator-killing functionals are exactly
    the scalar multiples of trace — a 1-dimensional space.

    There is one scalar readout. Not two. Not zero. One. -/
theorem trace_unique_of_kills_commutators
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {R : Type*} [CommRing R]
    (φ : Matrix n n R →ₗ[R] R)
    (hφ : ∀ A B : Matrix n n R, φ (A * B - B * A) = 0) :
    ∃ c : R, ∀ A : Matrix n n R, φ A = c * trace A := by
  obtain ⟨i₀⟩ := ‹Nonempty n›
  refine ⟨φ (single i₀ i₀ 1), fun A => ?_⟩
  have h_off := zero_on_offdiag_of_kills_commutators φ hφ
  have h_diag : ∀ i : n, φ (single i i 1) = φ (single i₀ i₀ 1) := by
    intro i
    by_cases h : i = i₀
    · subst h; rfl
    · exact eq_on_diag_of_kills_commutators φ hφ i i₀ h
  conv_lhs => rw [matrix_sum_single A]
  simp only [map_sum, LinearMap.map_smul, smul_eq_mul]
  have step : ∀ i : n, ∑ j : n, A i j * φ (single i j 1) =
      A i i * φ (single i₀ i₀ 1) := by
    intro i
    have : ∀ j : n, A i j * φ (single i j 1) =
        if j = i then A i i * φ (single i₀ i₀ 1) else 0 := by
      intro j
      by_cases h : j = i
      · subst h; simp [h_diag]
      · simp [h_off i j (fun e => h e.symm), h]
    simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [step]
  rw [← Finset.sum_mul, mul_comm, Matrix.trace]
  simp only [Matrix.diag_apply]

end Foam
