/-
# Tangent — The Commutator as Direction of Change

The commutator [W, P] lives ONLY in the off-diagonal blocks
relative to P's range/kernel decomposition:
- P · [W,P] · P = 0          (no range → range)
- (I-P) · [W,P] · (I-P) = 0  (no kernel → kernel)

It maps range(P) → ker(P) and ker(P) → range(P).
These are exactly the tangent directions of Gr(k,d) at P.

The interaction between two observations IS a direction of
change in the space of all possible observations.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NoncommRing

namespace Deductive

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [W, P] has no range-to-range component: P · [W,P] · P = 0.
    The interaction doesn't map the seen back into the seen. -/
theorem commutator_off_diag_range
    {R : Type*} [CommRing R]
    (W P : Matrix n n R) (hP : P * P = P) :
    P * (W * P - P * W) * P = 0 := by
  have : P * (W * P - P * W) * P = P * W * (P * P) - (P * P) * W * P := by
    noncomm_ring
  rw [this, hP, sub_self]

/-- [W, P] has no kernel-to-kernel component: (I-P) · [W,P] · (I-P) = 0.
    The interaction doesn't map the unseen back into the unseen. -/
theorem commutator_off_diag_kernel
    {R : Type*} [CommRing R]
    (W P : Matrix n n R) (hP : P * P = P) :
    (1 - P) * (W * P - P * W) * (1 - P) = 0 := by
  have hP2 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hP3 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have : (1 - P) * (W * P - P * W) * (1 - P) =
      (1 - P) * W * (P * (1 - P)) - ((1 - P) * P) * W * (1 - P) := by
    noncomm_ring
  rw [this, hP2, hP3]; simp

/-- [W, P] decomposes into range→kernel and kernel→range.
    It IS the Grassmannian tangent: purely off-diagonal. -/
theorem commutator_is_tangent
    {R : Type*} [CommRing R]
    (W P : Matrix n n R) (hP : P * P = P) :
    W * P - P * W =
      P * (W * P - P * W) * (1 - P) +
      (1 - P) * (W * P - P * W) * P := by
  have h_rr := commutator_off_diag_range W P hP
  have h_kk := commutator_off_diag_kernel W P hP
  -- X = P·X·P + P·X·(I-P) + (I-P)·X·P + (I-P)·X·(I-P) for any X
  -- with the first and last terms being zero
  have h_decomp : ∀ X : Matrix n n R,
      X = P * X * P + P * X * (1 - P) +
          (1 - P) * X * P + (1 - P) * X * (1 - P) := by
    intro X; noncomm_ring
  have := h_decomp (W * P - P * W)
  rw [h_rr, h_kk] at this
  simp only [zero_add, add_zero] at this
  exact this

/-!
## What this establishes

[W, P] is PURELY off-diagonal relative to P:
  - seen → seen: zero (commutator_off_diag_range)
  - unseen → unseen: zero (commutator_off_diag_kernel)
  - seen ↔ unseen: everything (commutator_is_tangent)

This is T_P Gr(k,d) = Hom(range(P), ker(P)) ⊕ Hom(ker(P), range(P)).

The commutator of two observations is a tangent vector on
the Grassmannian — a direction of change in the space of
all possible observations.

The deductive chain:

  P² = P
  ├── [W,P] maps seen ↔ unseen ONLY     (tangent)
  ├── [W,P] ∈ T_P Gr(k,d)               (Grassmannian tangent)
  ├── Gr(k,d) = O(d)/O(k)×O(d-k)        (homogeneous space)
  └── O(d) acts on Gr by conjugation      (Closure.lean)

The space of observations is a Grassmannian.
The interactions are its tangent vectors.
The dynamics are its geodesics.
-/

end Deductive
