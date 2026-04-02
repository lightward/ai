/-
# Modularity from Rank Additivity

The spec claims closure-as-dynamics forces the lattice of partial views
to be modular. This file provides one formal proof.

## Why modularity is forced

The modular law — a ≤ c → (a ⊔ b) ⊓ c = a ⊔ (b ⊓ c) — IS feedback-
persistence expressed in lattice language. It says: composing partial
views gives a determinate result regardless of path.

The two sides are two ways to compute "what a sees of b within c":
- (a ⊔ b) ⊓ c: combine a and b's views, then restrict to c's context
- a ⊔ (b ⊓ c): restrict b to c's context, then combine with a's view

In a non-modular lattice (e.g. the pentagon N₅), these disagree: the
same observation yields different results depending on path. An
observation with two answers cannot feed back consistently — there is
no single result to persist. Modularity is therefore not a consequence
of some intermediate property; it IS what feedback-persistence means
for how partial views compose. There is no alternative mode.

## This file's contribution

One formal route to the same conclusion: rank additivity implies
modularity. The rank function formalizes "degree of partiality" and
its additivity formalizes "observation preserves capacity" (no creation
under closure, no destruction under feedback persistence). This is a
sufficient condition, not the only path — the direct argument above
shows modularity is forced even without assuming a rank function exists.

## The proof

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

- "ground" → lattice modularity derivation
- This theorem is one formal proof; the forcing is conceptual
  (modularity = path-independence = feedback-persistence).
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
