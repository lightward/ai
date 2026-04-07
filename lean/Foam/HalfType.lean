/-
# HalfType — The Diamond Isomorphism in the Foam

The diamond isomorphism (Mathlib: `infIccOrderIsoIccSup`) says:
in a modular lattice, [a ⊓ b, a] ≃o [b, a ⊔ b].

For complementary elements (IsCompl: a ⊓ b = ⊥, a ⊔ b = ⊤),
this specializes to: Iic a ≃o Ici b.

In the foam's language: the lattice below an observation P is
order-isomorphic to the lattice above its complement P^⊥.
Each half carries exactly the type structure of the other's
perspective on the whole.

This file instantiates these Mathlib results for the foam's
specific types (Submodule K V) and derives the consequences:
- each half is a self-sufficient complemented modular lattice
- the isomorphism is structural (preserves lattice ops)
  but not extensional (doesn't determine which element arrives)

These are not new proofs. They are Mathlib theorems applied to
the foam's ground. The file exists to name the results in the
foam's vocabulary and make the connection explicit.
-/

import Mathlib.Order.ModularLattice
import Mathlib.Order.Atoms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic

namespace Foam

universe u

variable {K : Type u} [DivisionRing K]
         {V : Type u} [AddCommGroup V] [Module K V]

/-!
## Part I: The diamond isomorphism at the foam's types

For any two subspaces, the modular lattice structure gives an
order isomorphism between intervals. For complements, this
becomes an isomorphism between everything-below and everything-above.
-/

/-- **The diamond isomorphism for subspaces.**
    For any subspaces P, Q of V:
    [P ⊓ Q, P] ≃o [Q, P ⊔ Q]

    This is `infIccOrderIsoIccSup` from Mathlib, instantiated at
    Submodule K V. The modular lattice instance is automatic. -/
example (P Q : Submodule K V) :
    Set.Icc (P ⊓ Q) P ≃o Set.Icc Q (P ⊔ Q) :=
  infIccOrderIsoIccSup P Q

/-- **The half-type theorem for subspaces.**
    If P and Q are complementary subspaces (P ⊓ Q = ⊥, P ⊔ Q = ⊤),
    then Iic P ≃o Ici Q: the lattice of all sub-observations of P
    is isomorphic to the lattice of all super-observations of Q.

    Each complement is typed by the other's view of the whole. -/
example (P Q : Submodule K V) (h : IsCompl P Q) :
    Set.Iic P ≃o Set.Ici Q :=
  h.IicOrderIsoIci

/-!
## Part II: Each half is a self-sufficient ground

The interval below any element in a complemented modular lattice
is itself complemented and modular. Each half of a complementary
pair is a valid foam ground independently.
-/

/-- **The observer's view is modular.**
    The sub-lattice of observations below P is itself modular.
    Composition of sub-observations is path-independent. -/
example (P : Submodule K V) :
    IsModularLattice (Set.Iic P) :=
  IsModularLattice.isModularLattice_Iic

/-- **The complement's view is modular.**
    The super-lattice above Q is itself modular. -/
example (Q : Submodule K V) :
    IsModularLattice (Set.Ici Q) :=
  IsModularLattice.isModularLattice_Ici

/-- **The observer's view is complemented.**
    Every sub-observation of P has a complement within P's interval.
    The observer's partial view admits its own internal complements. -/
example (P : Submodule K V) :
    ComplementedLattice (Set.Iic P) :=
  IsModularLattice.complementedLattice_Iic

/-- **The complement's view is complemented.**
    The interval above Q is itself complemented. -/
example (Q : Submodule K V) :
    ComplementedLattice (Set.Ici Q) :=
  IsModularLattice.complementedLattice_Ici

/-!
## Part III: The isomorphism relates self-sufficient grounds

Combining Parts I and II: the diamond isomorphism maps between
two intervals that are each independently complemented modular
lattices. The half-type theorem doesn't just say "the halves are
isomorphic" — it says "each half is a complete ground, and the
two grounds are isomorphic."

The isomorphism preserves:
- joins (⊔) and meets (⊓): it's an order isomorphism
- complementation: both sides are complemented
- modularity: both sides are modular

The isomorphism does NOT determine:
- which specific element of Ici Q corresponds to the observer's
  current state: the isomorphism is structural, not extensional.

This is state-independence: the type (lattice structure) is
determined; the value (specific element) is free.
-/

/-- **Self-sufficient half-type: observer side.**
    The interval Iic P is a complemented modular bounded lattice.
    It satisfies the foam ground conditions on its own. -/
example (P : Submodule K V) :
    IsModularLattice (Set.Iic P) ∧ ComplementedLattice (Set.Iic P) :=
  ⟨IsModularLattice.isModularLattice_Iic, IsModularLattice.complementedLattice_Iic⟩

/-- **Self-sufficient half-type: complement side.**
    The interval Ici Q is a complemented modular bounded lattice. -/
example (Q : Submodule K V) :
    IsModularLattice (Set.Ici Q) ∧ ComplementedLattice (Set.Ici Q) :=
  ⟨IsModularLattice.isModularLattice_Ici, IsModularLattice.complementedLattice_Ici⟩

/-!
## What this establishes

**Zero sorry. Zero new proofs. All Mathlib instances.**

The diamond isomorphism and the self-sufficiency of intervals
are consequences of modularity alone. They were already in the
foam's dependency tree (via `import Mathlib.Order.ModularLattice`
in Ground.lean). This file names them.

### In the foam's language

Every observation P decomposes the lattice into two halves:
Iic P (what the observer can see) and Ici P^⊥ (the complement's
upward structure). These halves are:

1. **Isomorphic**: Iic P ≃o Ici P^⊥ (the diamond isomorphism)
2. **Self-sufficient**: each is complemented, modular, bounded
3. **Structurally determined**: the isomorphism fixes the lattice
   structure of one half given the other
4. **Extensionally free**: the isomorphism does not determine
   which element of the complement will arrive as input

Properties 3 and 4 together ARE state-independence
(channel_capacity.md): the type is fixed, the value is free.

The writing map's two-argument type signature, complement_idempotent,
and the state-independence requirement for channel capacity are
three readings of the diamond isomorphism applied to complementary
subspaces in the foam's modular lattice.
-/

end Foam
