/-
# Write Confinement — Writes Stay in the Observer's Slice

If d and m both lie in the observer's subspace P, then the write
d ∧ m lies in Λ²(P). An observer cannot modify dimensions they
are not bound to.

This is what makes writes "birth-shaped": the birth subspace P_A
determines which 3D subspace of the Lie algebra the observer can
write in. Combined with indelibility (P_A is fixed), every write
at every step is confined to the same subspace.

## Spec references

- "the writing map" -> "both d and m lie in the observer's slice(s).
  the write is confined to the observer's subspace — an observer
  literally cannot modify dimensions they are not bound to."
- "properties" -> "the dynamics are birth expression at every step"
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis

namespace FoamSpec

/-!
## Write confinement via the exterior algebra

The exterior product of two vectors in a subspace P lands in the
image of Λ²(P) inside Λ²(M). This is the algebraic core of
write confinement: the observer's birth subspace determines the
write subspace, permanently.

We prove this using the functoriality of the exterior algebra:
a submodule inclusion P ↪ M induces Λ²(P) ↪ Λ²(M), and the
product of two elements in the image of P stays in the image.
-/

/-- The exterior product of two vectors from a submodule P lies in
    the image of Λ²(P) inside Λ²(M). In foam terms: if d and m
    are both in the observer's slice, their write d ∧ m is confined
    to the slice's exterior square.

    Spec: "the writing map" -> "the write is confined to the
    observer's subspace" -/
theorem write_confined_to_slice
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (P : Submodule R M) (d m : P) :
    ExteriorAlgebra.ι R (d : M) * ExteriorAlgebra.ι R (m : M) ∈
    LinearMap.range (ExteriorAlgebra.map (Submodule.subtype P)).toLinearMap := by
  refine LinearMap.mem_range.mpr ?_
  exact ⟨ExteriorAlgebra.ι R (d : P) * ExteriorAlgebra.ι R (m : P),
    by simp [map_mul, ExteriorAlgebra.map_apply_ι]⟩

end FoamSpec
