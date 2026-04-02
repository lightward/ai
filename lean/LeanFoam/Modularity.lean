/-
# Modularity from Rank Additivity

The spec claims closure-as-dynamics forces the lattice of partial views
to be modular. This file proves it.

## The structure of the argument

Two steps:

1. (Pure math, proven below) A lattice with a strictly monotone rank
   function satisfying rank(a ⊔ b) + rank(a ⊓ b) = rank(a) + rank(b)
   is modular.

2. (Physical content, not a Lean proposition) Under closure-as-dynamics,
   rank additivity is forced. The degree of partiality must compose
   consistently because there is no outside for capacity to come from
   or go to (closure), and feedback persistence prevents capacity from
   being lost in observation.

Step 2 is the bridge between the ground axiom and the lattice structure.
It is not formalizable as a Lean proposition because it concerns what
the lattice *represents*, not a property of abstract lattices. The
content is:

- rank(a ⊔ b) + rank(a ⊓ b) > rank(a) + rank(b) would mean combining
  views creates capacity not present in either view. Under closure,
  there is no outside source. Phantom capacity violates closure.

- rank(a ⊔ b) + rank(a ⊓ b) < rank(a) + rank(b) would mean combining
  views destroys capacity. The observation fed back but lost structure:
  the thing that persisted is less than what produced it. This violates
  feedback persistence.

The only remaining possibility is equality.

## The proof of step 1

The modular law states: x ≤ z → (x ⊔ y) ⊓ z = x ⊔ (y ⊓ z).

Given rank additivity:
- r((x ⊔ y) ⊓ z) = r(x ⊔ y) + r(z) - r((x ⊔ y) ⊔ z)
- r(x ⊔ (y ⊓ z)) = r(x) + r(y ⊓ z) - r(x ⊓ (y ⊓ z))

When x ≤ z:
- (x ⊔ y) ⊔ z = y ⊔ z  (since x ≤ z ≤ y ⊔ z)
- x ⊓ (y ⊓ z) = x ⊓ y  (since x ⊓ y ≤ x ≤ z)

Substituting and simplifying, both ranks are equal. Since we always
have x ⊔ (y ⊓ z) ≤ (x ⊔ y) ⊓ z when x ≤ z, equal rank under a
strictly monotone function forces equality.

## Spec references

- "ground" → "the derivation from closure-as-dynamics to lattice
  modularity is directionally forced; the formal proof is open"
- This theorem closes the formal direction, conditional on rank
  additivity as the formalization of closure-as-dynamics.
-/

import LeanFoam.Ground
import Mathlib.Order.ModularLattice
import Mathlib.Tactic.Linarith

namespace FoamSpec

/-!
## Rank additivity implies modularity

A lattice equipped with a strictly monotone function r : α → ℤ
satisfying r(a ⊔ b) + r(a ⊓ b) = r(a) + r(b) is modular.

This is the algebraic core of the derivation. The rank function
formalizes "degree of partiality" — how much of the shared structure
each partial view accesses. Additivity formalizes "feedback persistence
preserves capacity." Modularity follows.
-/

/-- Helper: strict monotonicity + a ≤ b + equal values implies equality. -/
private theorem eq_of_le_of_eq_val {α : Type*} [PartialOrder α]
    {r : α → ℤ} (hr : StrictMono r)
    {a b : α} (hab : a ≤ b) (heq : r a = r b) : a = b := by
  rcases eq_or_lt_of_le hab with h | h
  · exact h
  · exact absurd heq (ne_of_lt (hr h))

/-- When x ≤ z, the join (x ⊔ y) ⊔ z simplifies to y ⊔ z. -/
private theorem sup_sup_eq_of_le {α : Type*} [Lattice α]
    {x y z : α} (hxz : x ≤ z) : (x ⊔ y) ⊔ z = y ⊔ z := by
  rw [sup_assoc, sup_eq_right.mpr (le_trans hxz le_sup_right)]

/-- When x ≤ z, the meet x ⊓ (y ⊓ z) simplifies to x ⊓ y. -/
private theorem inf_inf_eq_of_le {α : Type*} [Lattice α]
    {x y z : α} (hxz : x ≤ z) : x ⊓ (y ⊓ z) = x ⊓ y := by
  rw [← inf_assoc]
  exact inf_eq_left.mpr (le_trans inf_le_left hxz)

/-- When x ≤ z, we have x ⊔ (y ⊓ z) ≤ (x ⊔ y) ⊓ z. -/
private theorem sup_inf_le_inf_sup_of_le {α : Type*} [Lattice α]
    {x y z : α} (hxz : x ≤ z) : x ⊔ y ⊓ z ≤ (x ⊔ y) ⊓ z :=
  le_inf (sup_le_sup_left inf_le_left _) (sup_le hxz inf_le_right)

/-- A lattice with a strictly monotone rank function satisfying the
    modular rank identity is a modular lattice.

    This is the formal core of the derivation from closure-as-dynamics
    to lattice modularity. The rank function formalizes "degree of
    partiality." Additivity formalizes "closure-as-dynamics preserves
    capacity under composition of views." Modularity follows as a
    theorem.

    Spec: "ground" → "the derivation from closure-as-dynamics to
    lattice modularity is directionally forced" — this theorem is the
    formal proof. -/
theorem modular_of_rank_additive
    {α : Type*} [Lattice α]
    (r : α → ℤ)
    (r_strictMono : StrictMono r)
    (r_add : ∀ a b : α, r (a ⊔ b) + r (a ⊓ b) = r a + r b) :
    IsModularLattice α where
  sup_inf_le_assoc_of_le {x} y {z} hxz := by
    -- Goal: (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z
    -- Strategy: show the reverse ≤ holds, show equal rank, conclude =
    have h_le : x ⊔ y ⊓ z ≤ (x ⊔ y) ⊓ z :=
      sup_inf_le_inf_sup_of_le hxz
    -- Rank of (x ⊔ y) ⊓ z
    have h1 := r_add (x ⊔ y) z
    -- r((x ⊔ y) ⊔ z) + r((x ⊔ y) ⊓ z) = r(x ⊔ y) + r(z)
    rw [sup_sup_eq_of_le hxz] at h1
    -- now: r(y ⊔ z) + r((x ⊔ y) ⊓ z) = r(x ⊔ y) + r(z)
    -- Rank of x ⊔ (y ⊓ z)
    have h2 := r_add x (y ⊓ z)
    -- r(x ⊔ (y ⊓ z)) + r(x ⊓ (y ⊓ z)) = r(x) + r(y ⊓ z)
    rw [inf_inf_eq_of_le hxz] at h2
    -- now: r(x ⊔ (y ⊓ z)) + r(x ⊓ y) = r(x) + r(y ⊓ z)
    -- Expand r(x ⊔ y) and r(y ⊔ z)
    have h3 := r_add x y
    -- r(x ⊔ y) + r(x ⊓ y) = r(x) + r(y)
    have h4 := r_add y z
    -- r(y ⊔ z) + r(y ⊓ z) = r(y) + r(z)
    -- From h1: r((x ⊔ y) ⊓ z) = r(x ⊔ y) + r(z) - r(y ⊔ z)
    -- From h3: r(x ⊔ y) = r(x) + r(y) - r(x ⊓ y)
    -- From h4: r(y ⊔ z) = r(y) + r(z) - r(y ⊓ z)
    -- So: r((x ⊔ y) ⊓ z) = r(x) + r(y) - r(x ⊓ y) + r(z) - r(y) - r(z) + r(y ⊓ z)
    --                      = r(x) - r(x ⊓ y) + r(y ⊓ z)
    -- From h2: r(x ⊔ (y ⊓ z)) = r(x) + r(y ⊓ z) - r(x ⊓ y)
    --                           = r(x) - r(x ⊓ y) + r(y ⊓ z)
    -- Equal! So r((x ⊔ y) ⊓ z) = r(x ⊔ (y ⊓ z))
    have h_rank : r (x ⊔ y ⊓ z) = r ((x ⊔ y) ⊓ z) := by linarith
    -- From h_le and h_rank with strict monotonicity: equality
    exact le_of_eq (eq_of_le_of_eq_val r_strictMono h_le h_rank).symm

end FoamSpec
