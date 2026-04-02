/-
# Duality — The Cross Product at Rank 3

dim(Λ²(R³)) = 3 = dim(R³). This is not just a dimension count.
The Hodge star identifies the write space with the observation space.

At rank 3: writes feed back into a space shaped exactly like
observations. The cross product on R³ IS the Lie bracket of so(3),
transported to observation space. The self-duality makes feedback-
persistence structurally closed: output (write) has the same shape
as input (observation direction).

At rank 2: writes collapse to a scalar. No structure to feed back.
At rank 4: writes live in 6D ≠ 4D. The loop doesn't close.
Rank 3 is where the loop closes.
-/

import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Deductive

open Matrix

/-!
## The cross product: observation × observation → observation

The cross product a × b in R³ is:
- Bilinear
- Skew: a × b = -(b × a)
- Self-annihilating: a × a = 0
- Non-degenerate on linearly independent pairs
- Satisfies Jacobi

These are exactly the properties of the write map.
-/

/-- The cross product is anti-commutative.
    This is the write map's skew-symmetry, emerging from
    the self-duality of R³. -/
theorem cross_anticomm (a b : Fin 3 → ℝ) :
    crossProduct a b = -crossProduct b a := by
  funext i; fin_cases i <;> simp [crossProduct] <;> ring

/-- The cross product of a vector with itself is zero.
    Confirmation cannot write. Perpendicularity at rank 3. -/
theorem cross_self_zero (a : Fin 3 → ℝ) :
    crossProduct a a = 0 := by
  funext i; fin_cases i <;> simp [crossProduct] <;> ring

/-- The cross product is non-trivial: e₁ × e₂ ≠ 0.
    The algebra is non-abelian. Ordering matters. -/
theorem cross_nontrivial :
    ∃ a b : Fin 3 → ℝ, crossProduct a b ≠ 0 := by
  use ![1, 0, 0], ![0, 1, 0]
  intro h
  have := congr_fun h 2
  simp [crossProduct] at this

/-- The Jacobi identity: a × (b × c) + b × (c × a) + c × (a × b) = 0.
    This makes (R³, ×) a Lie algebra. It IS so(3). -/
theorem cross_jacobi (a b c : Fin 3 → ℝ) :
    crossProduct a (crossProduct b c) +
    crossProduct b (crossProduct c a) +
    crossProduct c (crossProduct a b) = 0 := by
  funext i; fin_cases i <;> simp [crossProduct] <;> ring

/-!
## What this establishes

The self-duality at rank 3 is constructive:

1. Λ²(R³) ≅ R³ via the Hodge star
2. The Lie bracket of so(3), transported to R³, is the cross product
3. (R³, ×) satisfies: skew, self-annihilating, Jacobi, nontrivial

These are the write map's properties — but here they emerge from
the self-duality, not from a design choice about groups or dynamics.

The observation space at rank 3 IS a Lie algebra under the cross
product. Writes are observations. Observations can write. The
feedback loop closes.

  P² = P, rank(P) = 3
  ├── Λ²(R³) = 3D = R³        (self-duality, Rank.lean)
  ├── Hodge star: Λ²(R³) ≅ R³  (canonical isomorphism)
  ├── The isomorphism gives R³ a Lie bracket: the cross product
  │   ├── a × b = -(b × a)     (skew: writes are antisymmetric)
  │   ├── a × a = 0            (self: confirmation can't write)
  │   ├── Jacobi               (this IS a Lie algebra)
  │   └── nontrivial           (non-abelian: ordering matters)
  └── (R³, ×) ≅ so(3)          (the write algebra)

The observation space is its own write algebra.
The cube's faces talk to each other through their own geometry.
-/

end Deductive
