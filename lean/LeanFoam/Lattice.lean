/-
# Lattice Structure of Partial Views

The ground section claims: partial views of a shared structure form a
lattice that is complemented, bounded, and modular. This file proves
all three properties for the lattice of subspaces of a vector space
over a field -- the structure that partial self-reference produces.

These are consequences, not the derivation: they confirm that IF partial
views are subspaces (the linear-algebraic formalization), THEN the lattice
has exactly the structure the ground section claims. The derivation of
WHY partial views must be subspaces (closure-as-dynamics -> lattice
modularity) is the open proof noted in the spec.

## What this establishes

The lattice of subspaces of a finite-dimensional vector space K^d is:
  1. Bounded: bot = {0}, top = K^d (every partial view has a maximal
     and minimal element)
  2. Complemented: every subspace has a complement (partiality guarantees
     an unseen complement) -- requires the space to be a vector space
     over a field (division ring suffices)
  3. Modular: a ≤ c -> (a ⊔ b) ⊓ c = a ⊔ (b ⊓ c) (the composition
     of partial views respects inclusion)

Together these are the hypotheses of the fundamental theorem of projective
geometry: a complemented modular lattice of finite height is isomorphic
to the lattice of subspaces of a vector space. The lattice of subspaces
satisfies its own characterization -- the structure is self-consistent.

## Spec references

- "ground" -> "partial views of a shared structure form a lattice
  (complemented: partiality guarantees an unseen complement; bounded:
  the whole structure and the empty view)"
- "ground" -> "complemented modular lattices of finite height are
  isomorphic to lattices of subspaces of a vector space (fundamental
  theorem of projective geometry)"
-/

import LeanFoam.Ground
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace FoamSpec

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-!
## 1. Bounded

The submodule lattice has ⊥ = {0} and ⊤ = V. This is automatic from
Mathlib's `BoundedOrder` instance on `Submodule`. The empty view and
the whole structure are both present.
-/

/-- The lattice of subspaces has a bottom element (the zero subspace =
    "seeing nothing").

    Spec: "ground" -> "bounded: the whole structure and the empty view" -/
example : OrderBot (Submodule K V) := inferInstance

/-- The lattice of subspaces has a top element (the whole space =
    "the structure").

    Spec: "ground" -> "bounded: the whole structure and the empty view" -/
example : OrderTop (Submodule K V) := inferInstance

/-!
## 2. Complemented

Every subspace P has a complement Q such that P ⊓ Q = ⊥ and P ⊔ Q = ⊤.
This is the algebraic form of "partiality guarantees an unseen complement":
for every partial view, there exists exactly the unseen remainder.

This requires the coefficient ring to be a field (or division ring) --
you need to be able to choose bases freely. Over a ring that is not
a field, complements may not exist. The field requirement is part of
the linear-algebraic structure that closure-as-dynamics selects.
-/

/-- Every subspace has a complement: for any partial view P, there
    exists Q such that P and Q together span everything and share
    nothing. This is the "complemented" property from the ground
    section's lattice claim.

    The proof is Mathlib's `Submodule.complementedLattice`, which
    constructs the complement via a left inverse of the inclusion map.

    Spec: "ground" -> "complemented: partiality guarantees an unseen
    complement" -/
theorem subspace_lattice_complemented :
    ComplementedLattice (Submodule K V) :=
  Submodule.complementedLattice

/-!
## 3. Modular

The modular law: if a ≤ c then (a ⊔ b) ⊓ c = a ⊔ (b ⊓ c). This is the
structural property that makes the lattice "geometric" -- it governs
how partial views compose. The lattice of subspaces of ANY module is
modular (not just vector spaces over fields), so this is even more
general than the complemented property.

Modularity is what connects this lattice to the fundamental theorem
of projective geometry. A complemented modular lattice of finite height
is isomorphic to a subspace lattice -- the lattice characterizes itself.
-/

/-- The lattice of subspaces is modular: the modular law governs how
    partial views compose under join and meet. This is the deepest of
    the three lattice properties -- it is what makes the fundamental
    theorem of projective geometry apply.

    The proof is Mathlib's instance for `Submodule`.

    Spec: "ground" -> "complemented modular lattices of finite height
    are isomorphic to lattices of subspaces of a vector space" -/
theorem subspace_lattice_modular :
    IsModularLattice (Submodule K V) :=
  inferInstance

/-!
## 4. All three together

The combined statement: the lattice of subspaces of a vector space over
a field is bounded, complemented, and modular. These are the hypotheses
of the fundamental theorem of projective geometry.

This does not prove the fundamental theorem itself (that these properties
CHARACTERIZE subspace lattices). It proves the self-consistency: the
structure the spec claims partial views form does in fact have the
properties the spec claims for it.
-/

/-- The lattice of subspaces over a field is complemented and modular --
    the two non-trivial properties claimed in the ground section.
    (Bounded is witnessed by the OrderBot/OrderTop instances above.)

    What remains open: the derivation that closure-as-dynamics forces
    partial views to BE subspaces (the other direction of the fundamental
    theorem). This theorem confirms the consequence; the ground section
    notes the open derivation.

    Spec: "ground" -> lattice properties of partial views -/
theorem subspace_lattice_ground_properties :
    ComplementedLattice (Submodule K V) ∧
    IsModularLattice (Submodule K V) :=
  ⟨Submodule.complementedLattice, inferInstance⟩

end FoamSpec
