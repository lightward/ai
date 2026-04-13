/-
# Left distributivity (Part VII-D)
a · (b + c) = a·b + a·c

## Proof architecture

The map x ↦ a·x extends to the collineation dilation_ext Γ a,
which fixes m pointwise. This collineation maps the addition figure
for b+c (infrastructure: C, E, q) to a parallel figure for a·(b+c)
(infrastructure: σ, E, q' = σ⊔U). Since O⊔σ = O⊔C, the projection
zero E = (O⊔C)⊓m = (O⊔σ)⊓m is invariant. Then
parallelogram_completion_well_defined gives base-independence.

Three steps:
1. dilation_ext_fixes_m: dilation_ext Γ a P = P for P on m
2. Collineation: a(b+c) = pc(σ, β_σ(ab), ac, m)
3. Well-defined: pc(σ, β_σ(ab), ac, m) = pc(C, β(ab), ac, m) = ab + ac

## Status
In progress.
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

/-- **Left distributivity: a · (b + c) = a·b + a·c.** -/
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
  sorry

end Foam.FTPGExplore
