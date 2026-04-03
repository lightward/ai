/-
# Confinement — Writes Stay in the Observer's Slice

If d and m both lie in the observer's subspace P, then the write
d ∧ m lies in Λ²(P). An observer cannot modify dimensions they
are not bound to.

This connects to Rank.lean: dim(Λ²(P)) = C(rank(P), 2), and at
rank 3 this is 3D = so(3). The confinement theorem says the write
doesn't just LIVE in a 3D space — it lives in the SPECIFIC 3D
subspace determined by the observer's birth.

Combined with the deductive chain:
  P² = P → rank 3 → Λ²(R³) = 3D (Rank.lean)
  P² = P → writes ∈ Λ²(P) (THIS FILE)
  Therefore: each observer's writes are confined to a specific
  3-dimensional subspace of the Lie algebra, permanently.
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis

namespace Foam

/-- The exterior product of two vectors from a submodule P lies in
    the image of Λ²(P) inside Λ²(M). If d and m are both in the
    observer's slice, their write d ∧ m is confined to the slice's
    exterior square. -/
theorem write_confined_to_slice
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (P : Submodule R M) (d m : P) :
    ExteriorAlgebra.ι R (d : M) * ExteriorAlgebra.ι R (m : M) ∈
    LinearMap.range (ExteriorAlgebra.map (Submodule.subtype P)).toLinearMap := by
  refine LinearMap.mem_range.mpr ?_
  exact ⟨ExteriorAlgebra.ι R (d : P) * ExteriorAlgebra.ι R (m : P),
    by simp [map_mul, ExteriorAlgebra.map_apply_ι]⟩

end Foam
