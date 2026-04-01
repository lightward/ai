/-
# Write Map Properties

The write d⊗m − m⊗d: unique, traceless, skew-symmetric.
These are three faces of the same constraint — perpendicularity.

## Spec references

- "the writing map" → uniqueness from constraints (a)+(b)+(c)
- "the writing map" → "writes live in su(d), not u(d)"
- "the writing map" → "skew-symmetric (writes are Lie algebra elements)"
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

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
## 3. Skew-Symmetry of the Write

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

end FoamSpec
