/-
# Associativity capstone (Part V-B)

The final sorry: coord_add_assoc.

## Proof architecture (session 57)

The proof routes through q via β-injectivity. Instead of proving the
composition law directly on l (where all tools degenerate), we:

1. Apply key_identity three times to reduce the goal to an O-based
   composition on a q-point: pc(O, s, C_c, m) = pc(O, a, pc(O, b, C_c, m), m).
   Here C_c = β(c) is on q but OFF l — so O-based translations work.

2. Prove the O-based composition at C_c via a cross-parallelism chain:
   - Pick auxiliary P off l, m, q.
   - Three cross_parallelism calls: τ_s, τ_b, τ_a applied to (P, C_c).
   - The chain gives: (X⊔β(LHS))⊓m = (X'⊔β(RHS))⊓m where X = τ_s(P),
     X' = τ_a(τ_b(P)).
   - From the (P, Γ.C) chain: X = X' (the composition agrees at P).
   - Two-lines argument: X⊔e is a single line, β(LHS) and β(RHS) both
     on this line AND on q → β(LHS) = β(RHS).

3. perspectivity_injective: β(LHS) = β(RHS) → LHS = RHS.

## Key lemma

`translation_determined_by_param`: if pc(C, C₁, P, m) = pc(C, C₂, P, m)
for P off q and m, then C₁ = C₂. Pure lattice argument (no Desargues):
if C₁ ≠ C₂, lines C₁⊔e_P and C₂⊔e_P share only e_P, forcing e_P ∈ P⊔U,
hence e_P = U, contradicting P ∉ q.

## Status

1 sorry: coord_add_assoc. Proof architecture complete, implementation in progress.
-/

import Foam.FTPGAssoc

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-- **A C-based translation is determined by its parameter.**

    If pc(C, C₁, P, m) = pc(C, C₂, P, m) for some P off q and m,
    then C₁ = C₂.

    Proof: both sides are on P⊔U and on C_i⊔e_P. If C₁ ≠ C₂:
    the lines C₁⊔e_P and C₂⊔e_P meet only at e_P (modular_intersection).
    So the common value = e_P ∈ P⊔U, giving e_P = (P⊔U)⊓m = U.
    But e_P = (C⊔P)⊓m ≠ U since P ∉ q. Contradiction. -/
theorem translation_determined_by_param (Γ : CoordSystem L)
    {C₁ C₂ P : L} (hC₁ : IsAtom C₁) (hC₂ : IsAtom C₂) (hP : IsAtom P)
    (hC₁_on_q : C₁ ≤ Γ.U ⊔ Γ.C) (hC₂_on_q : C₂ ≤ Γ.U ⊔ Γ.C)
    (hC₁_ne_C : C₁ ≠ Γ.C) (hC₂_ne_C : C₂ ≠ Γ.C)
    (hP_not_q : ¬ P ≤ Γ.U ⊔ Γ.C) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (h_agree : parallelogram_completion Γ.C C₁ P (Γ.U ⊔ Γ.V) =
               parallelogram_completion Γ.C C₂ P (Γ.U ⊔ Γ.V)) :
    C₁ = C₂ := by
  set q := Γ.U ⊔ Γ.C
  set m := Γ.U ⊔ Γ.V
  set e_P := (Γ.C ⊔ P) ⊓ m
  -- Y := pc(C, C₁, P, m) = pc(C, C₂, P, m)
  -- Y ≤ C_i ⊔ e_P (from second factor of parallelogram_completion)
  have hY_le_C₁e : parallelogram_completion Γ.C C₁ P m ≤ C₁ ⊔ e_P := by
    unfold parallelogram_completion; exact inf_le_right
  have hY_le_C₂e : parallelogram_completion Γ.C C₂ P m ≤ C₂ ⊔ e_P := by
    unfold parallelogram_completion; exact inf_le_right
  -- If C₁ ≠ C₂: lines C₁⊔e_P and C₂⊔e_P share only e_P
  -- → Y ≤ e_P → Y ∈ P⊔U → e_P = U → P ∈ q, contradiction
  by_contra h_ne
  sorry

/-- **Associativity of coordinate addition.**

    (a + b) + c = a + (b + c)

    Proof strategy (session 57): route through q via β-injectivity.

    1. key_identity reduces goal to O-based composition at C_c (off l):
       pc(O, s, C_c, m) = pc(O, a, pc(O, b, C_c, m), m)

    2. Cross-parallelism chain at (P, Γ.C) gives X = τ_a(τ_b(P)) = τ_s(P).
       Cross-parallelism chain at (P, C_c) gives β(LHS) = β(RHS)
       via the two-lines argument.

    3. perspectivity_injective finishes. -/
theorem coord_add_assoc (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ (coord_add Γ a b) c = coord_add Γ a (coord_add Γ b c) := by
  set l := Γ.O ⊔ Γ.U
  set m := Γ.U ⊔ Γ.V
  set q := Γ.U ⊔ Γ.C
  set s := coord_add Γ a b
  set t := coord_add Γ b c
  -- ═══ Step 0: Setup ═══
  have hs_atom : IsAtom s := coord_add_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
  have ht_atom : IsAtom t := coord_add_atom Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U
  have hs_on : s ≤ l := by show coord_add Γ a b ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have ht_on : t ≤ l := by show coord_add Γ b c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  -- ═══ Step 1: Reduce to O-based composition at C_c via key_identity ═══
  -- β(LHS) = pc(O, s, C_c, m) by key_identity for (s, c)
  -- β(RHS) = pc(O, a, pc(O, b, C_c, m), m) by key_identity for (a, t) and (b, c)
  -- Goal becomes: pc(O, s, C_c, m) = pc(O, a, pc(O, b, C_c, m), m)
  -- where C_c = pc(O, c, C, m) is on q, OFF l.
  -- ═══ Step 2: Cross-parallelism chain → β(LHS) = β(RHS) ═══
  -- Three cp calls at (P, C_c) using X = X' from the (P, C) chain.
  -- Two-lines argument: both β(LHS) and β(RHS) on q ∩ (X⊔e), unique atom.
  -- ═══ Step 3: perspectivity_injective → LHS = RHS ═══
  sorry

end Foam.FTPGExplore
