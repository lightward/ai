/-
# Left distributivity (Part VII-D)
a · (b + c) = a·b + a·c

## Proof architecture (corrected 2026-04-13)

Left multiplication x ↦ a·x is a composition of two perspectivities:
  π₁: l → O⊔C (center E_I on m): x ↦ (O⊔C)⊓(x⊔E_I)
  π₂: O⊔C → l (center d_a on m): P ↦ (P⊔d_a)⊓l

Both perspectivities have center on m, map origin O→O, and map the
m-intercept of the source to the m-intercept of the target.

Key Lemma: A perspectivity between lines through O, with center on m,
mapping the m-intercept to the m-intercept, preserves the parallelogram-
completion addition with respect to m.

Proof: By Desargues (converse → forward), showing the addition figure
on the source line maps to the addition figure on the target line.

Then: a·(b+c) = π₂(π₁(b+c)) = π₂(π₁(b) + π₁(c)) = π₂(π₁(b)) + π₂(π₁(c))
     = a·b + a·c.

## Note on multiplication order

The dilation_ext Γ c is a collineation for RIGHT multiplication x↦x·c.
Left multiplication x↦a·x is NOT a single collineation in the non-
commutative case. This is why left distrib requires a different proof
from right distrib (which used collineation directly).

## Status
In progress. 1 sorry (main theorem). dilation_ext_fixes_m proven.
-/
import Foam.FTPGNeg

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-! ## Step 1: Dilation fixes m pointwise -/

/-- The dilation σ_a fixes points on m: for P on m with P ∉ l,
    dilation_ext Γ a P = P. Proof: (I⊔P)⊓m = P by line_direction
    (I ∉ m, P ≤ m). Then dilation_ext = (O⊔P) ⊓ (a⊔P) = P by
    modular_intersection (a ∉ O⊔P since P ∉ l). -/
theorem dilation_ext_fixes_m (Γ : CoordSystem L)
    {a P : L} (ha : IsAtom a) (hP : IsAtom P)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hP_on_m : P ≤ Γ.U ⊔ Γ.V)
    (ha_ne_O : a ≠ Γ.O) (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) :
    dilation_ext Γ a P = P := by
  unfold dilation_ext
  -- Step 1: (I⊔P)⊓m = P by line_direction (I ∉ m, P ≤ m)
  have hIP_inf_m : (Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V) = P :=
    line_direction Γ.hI Γ.hI_not_m hP_on_m
  rw [hIP_inf_m]
  -- Goal: (O⊔P) ⊓ (a⊔P) = P
  -- By modular_intersection: (P⊔O)⊓(P⊔a) = P when ¬ a ≤ P⊔O
  rw [show Γ.O ⊔ P = P ⊔ Γ.O from sup_comm _ _, show a ⊔ P = P ⊔ a from sup_comm _ _]
  have hO_ne_P : Γ.O ≠ P := fun h => hP_not_l (h ▸ le_sup_left)
  have ha_ne_P : a ≠ P := fun h => hP_not_l (h ▸ ha_on)
  have ha_not_PO : ¬ a ≤ P ⊔ Γ.O := by
    intro h
    -- a ≤ P⊔O and a ≤ l = O⊔U. So a ≤ l ⊓ (P⊔O).
    -- P ∉ l, O ≤ l, O ≤ P⊔O, so l ⊓ (P⊔O) = O by modular_intersection.
    -- Hence a ≤ O, so a = O. Contradiction.
    have hU_ne_P : Γ.U ≠ P := fun h' => hP_not_l (h' ▸ le_sup_right)
    have h_int : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ P) = Γ.O :=
      modular_intersection Γ.hO Γ.hU hP Γ.hOU hO_ne_P hU_ne_P hP_not_l
    have ha_le_O : a ≤ Γ.O := by
      have h' : a ≤ Γ.O ⊔ P := (sup_comm P Γ.O) ▸ h
      exact (le_inf ha_on h').trans h_int.le
    exact ha_ne_O ((Γ.hO.le_iff.mp ha_le_O).resolve_left ha.1)
  exact modular_intersection hP Γ.hO ha hO_ne_P.symm ha_ne_P.symm
    (Ne.symm ha_ne_O) ha_not_PO

/-! ## The left distributivity theorem -/

/-- **Left distributivity: a · (b + c) = a·b + a·c.**

Proof architecture: left multiplication x ↦ a·x decomposes as π₂ ∘ π₁ where
  π₁: l → O⊔C (center E_I on m, maps O→O, U→E)
  π₂: O⊔C → l (center d_a on m, maps O→O, E→U)
Both perspectivities preserve parallelogram-completion addition (Key Lemma),
so a·(b+c) = π₂(π₁(b+c)) = π₂(π₁(b)+π₁(c)) = π₂(π₁(b))+π₂(π₁(c)) = a·b+a·c. -/
theorem coord_mul_left_distrib (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hbc : b ≠ c)
    -- Non-degeneracy conditions for the sum and products
    (hs_ne_O : coord_add Γ b c ≠ Γ.O) (hs_ne_U : coord_add Γ b c ≠ Γ.U)
    (hab_ne_O : coord_mul Γ a b ≠ Γ.O) (hab_ne_U : coord_mul Γ a b ≠ Γ.U)
    (hac_ne_O : coord_mul Γ a c ≠ Γ.O) (hac_ne_U : coord_mul Γ a c ≠ Γ.U)
    (hab_ne_ac : coord_mul Γ a b ≠ coord_mul Γ a c)
    (has_ne_O : coord_mul Γ a (coord_add Γ b c) ≠ Γ.O)
    (has_ne_U : coord_mul Γ a (coord_add Γ b c) ≠ Γ.U)
    (habac_ne_O : coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) ≠ Γ.O)
    (habac_ne_U : coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_mul Γ a (coord_add Γ b c) =
      coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) := by
  -- ═══ Setup ═══
  set l := Γ.O ⊔ Γ.U with hl_def
  set m := Γ.U ⊔ Γ.V with hm_def
  set k := Γ.O ⊔ Γ.C with hk_def  -- the "bridge" line O⊔C
  set s := coord_add Γ b c with hs_def
  set ab := coord_mul Γ a b with hab_def
  set ac := coord_mul Γ a c with hac_def
  -- Key intermediate atoms on the bridge k = O⊔C
  set σ_b := (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) with hσb_def  -- π₁(b)
  set σ_c := (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) with hσc_def  -- π₁(c)
  set σ_s := (Γ.O ⊔ Γ.C) ⊓ (s ⊔ Γ.E_I) with hσs_def  -- π₁(b+c)
  set d_a := (a ⊔ Γ.C) ⊓ m with hda_def                 -- π₂ center
  -- ═══ The proof decomposes into: ═══
  -- 1. coord_mul Γ a x = (σ_x ⊔ d_a) ⊓ l  [multiplication = π₂(π₁(x))]
  -- 2. π₁ preserves addition: σ_s = σ_b +_k σ_c on k = O⊔C
  -- 3. π₂ preserves addition: π₂(σ_s) = π₂(σ_b) + π₂(σ_c) on l
  -- 4. Combined: a·(b+c) = a·b + a·c
  sorry

end Foam.FTPGExplore
