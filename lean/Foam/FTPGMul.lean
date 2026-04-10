/-
# Coordinate multiplication (Part VI)

Multiplication on the coordinate line via dilations.

## Definition

a · b is a two-step perspectivity implementing the dilation σ_b:
1. σ_b(C) = (O⊔C) ⊓ (b ⊔ E_I) on the line O⊔C
2. a · b = (σ_b(C) ⊔ d_a) ⊓ l where d_a = (a⊔C)⊓m

## Status

Definition, E_I infrastructure, 0 sorry.
-/

import Foam.FTPGCoord
import Foam.FTPGParallelogram

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-- E_I: projection of I onto m through center C. -/
noncomputable def CoordSystem.E_I (Γ : CoordSystem L) : L := (Γ.I ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)

variable (Γ : CoordSystem L)

theorem CoordSystem.hI_not_m : ¬ Γ.I ≤ Γ.U ⊔ Γ.V :=
  fun h => Γ.hUI (Γ.atom_on_both_eq_U Γ.hI Γ.hI_on h).symm

theorem CoordSystem.hE_I_atom : IsAtom Γ.E_I :=
  line_meets_m_at_atom Γ.hI Γ.hC (fun h => Γ.hC_not_l (h ▸ Γ.hI_on))
    (sup_le (Γ.hI_on.trans le_sup_left) Γ.hC_plane)
    (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    Γ.m_covBy_π Γ.hI_not_m

theorem CoordSystem.hE_I_on_m : Γ.E_I ≤ Γ.U ⊔ Γ.V := inf_le_right

theorem CoordSystem.hE_I_le_IC : Γ.E_I ≤ Γ.I ⊔ Γ.C := inf_le_left

/-- E_I is not on O⊔C. Proof: E_I ≤ O⊔C → E_I = E → directions agree →
    I⊔C = O⊔C → I ≤ O⊔C → l⊓(O⊔C) = O → I = O. -/
theorem CoordSystem.hE_I_not_OC : ¬ Γ.E_I ≤ Γ.O ⊔ Γ.C := by
  intro h
  have hIC : Γ.I ≠ Γ.C := fun h' => Γ.hC_not_l (h' ▸ Γ.hI_on)
  have hOC : Γ.O ≠ Γ.C := fun h' => Γ.hC_not_l (h' ▸ le_sup_left)
  have hEI_ne_C : Γ.E_I ≠ Γ.C := fun h' => Γ.hC_not_m (h' ▸ Γ.hE_I_on_m)
  -- E_I ≤ (O⊔C)⊓m = E, so E_I = E
  have hEI_eq_E : Γ.E_I = Γ.E :=
    (Γ.hE_atom.le_iff.mp (le_inf h Γ.hE_I_on_m)).resolve_left Γ.hE_I_atom.1
  -- C⊔E_I = I⊔C (CovBy: C < C⊔E_I ≤ I⊔C, C ⋖ I⊔C)
  have hCEI_eq_IC : Γ.C ⊔ Γ.E_I = Γ.I ⊔ Γ.C :=
    ((sup_comm Γ.C Γ.I ▸ atom_covBy_join Γ.hC Γ.hI hIC.symm).eq_or_eq
      (lt_of_le_of_ne le_sup_left (fun h' => hEI_ne_C
        ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_I_atom.1))).le
      (sup_le le_sup_right Γ.hE_I_le_IC)).resolve_left
      (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h' => hEI_ne_C
        ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_I_atom.1))))
  -- C⊔E = O⊔C (CovBy: C < C⊔E ≤ O⊔C, C ⋖ O⊔C)
  have hE_ne_C : Γ.E ≠ Γ.C := fun h' => Γ.hC_not_m (h' ▸ CoordSystem.hE_on_m)
  have hCE_eq_OC : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C :=
    ((sup_comm Γ.C Γ.O ▸ atom_covBy_join Γ.hC Γ.hO hOC.symm).eq_or_eq
      (lt_of_le_of_ne le_sup_left (fun h' => hE_ne_C
        ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_atom.1))).le
      (sup_le le_sup_right CoordSystem.hE_le_OC)).resolve_left
      (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h' => hE_ne_C
        ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_atom.1))))
  -- I⊔C = C⊔E_I = C⊔E = O⊔C, so I ≤ O⊔C
  have hI_le : Γ.I ≤ Γ.O ⊔ Γ.C := by
    have : Γ.I ⊔ Γ.C = Γ.O ⊔ Γ.C := by rw [← hCEI_eq_IC, hEI_eq_E, hCE_eq_OC]
    exact le_sup_left.trans this.le
  -- l ⊓ (O⊔C) = O (inf_sup_of_atom_not_le, after sup_comm)
  have h_lOC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm Γ.O Γ.C]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l le_sup_left
  exact Γ.hOI.symm ((Γ.hO.le_iff.mp ((le_inf Γ.hI_on hI_le).trans h_lOC.le)).resolve_left
    Γ.hI.1)

theorem CoordSystem.hE_I_ne_E : Γ.E_I ≠ Γ.E :=
  fun h => Γ.hE_I_not_OC (h ▸ CoordSystem.hE_le_OC)

theorem CoordSystem.hE_I_not_l : ¬ Γ.E_I ≤ Γ.O ⊔ Γ.U := by
  intro h
  have : Γ.E_I ≤ Γ.U := (le_inf h Γ.hE_I_on_m).trans Γ.l_inf_m_eq_U.le
  have hEI_eq_U : Γ.E_I = Γ.U :=
    (Γ.hU.le_iff.mp this).resolve_left Γ.hE_I_atom.1
  -- E_I ≤ I⊔C. U ≤ I⊔C. l ⊓ (I⊔C) = I (since C ∉ l). U ≤ I. U = I.
  have hI_eq_U : Γ.I = Γ.U := by
    have hU_le_IC : Γ.U ≤ Γ.I ⊔ Γ.C := hEI_eq_U ▸ Γ.hE_I_le_IC
    have h_lIC := inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (Γ.hI_on : Γ.I ≤ Γ.O ⊔ Γ.U)
    -- h_lIC : (O⊔U) ⊓ (C⊔I) = I. Need (O⊔U) ⊓ (I⊔C).
    rw [sup_comm Γ.C Γ.I] at h_lIC
    exact ((Γ.hI.le_iff.mp ((le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hU_le_IC).trans
      h_lIC.le)).resolve_left Γ.hU.1).symm
  exact Γ.hUI hI_eq_U.symm

/-!
## Coordinate multiplication
-/

/-- **Coordinate multiplication: a · b.** -/
noncomputable def coord_mul (Γ : CoordSystem L) (a b : L) : L :=
  ((Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ Γ.U)

/-- Multiplication factors through the two-perspectivity pattern.
    Bridge: O⊔C (via center E_I, return via C on m). -/
theorem coord_mul_eq_two_persp (Γ : CoordSystem L) (a b : L) :
    coord_mul Γ a b = two_persp Γ (Γ.O ⊔ Γ.C) (b ⊔ Γ.E_I) (a ⊔ Γ.C) (Γ.U ⊔ Γ.V) := rfl

/-!
## Multiplicative identity
-/

/-- E_I ⊔ (O⊔C) = π: E_I is not on O⊔C, so their join is the plane. -/
private theorem EI_sup_OC_eq_π : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
  have h_lt : Γ.O ⊔ Γ.C < Γ.E_I ⊔ (Γ.O ⊔ Γ.C) :=
    lt_of_le_of_ne le_sup_right (fun h => Γ.hE_I_not_OC (h ▸ le_sup_left))
  have h_le : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (Γ.hE_I_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
      (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane)
  exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)

/-- I is a left multiplicative identity: I · a = a.

    With the first argument = I, the second perspectivity output is E_I
    (by definition of E_I = (I⊔C)⊓m). The modular law gives
    σ ⊔ E_I = a ⊔ E_I (using E_I ⊔ (O⊔C) = π), and projection
    onto l recovers a. Same pattern as coord_add_left_zero. -/
theorem coord_mul_left_one (Γ : CoordSystem L)
    (a : L) (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    coord_mul Γ Γ.I a = a := by
  unfold coord_mul
  -- (I⊔C) ⊓ (U⊔V) = E_I definitionally. Fold it.
  change ((Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = a
  -- σ ⊔ E_I = a ⊔ E_I by the modular law.
  have haEI_le_π : a ⊔ Γ.E_I ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (ha_on.trans le_sup_left)
      (Γ.hE_I_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  have hED : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ⊔ Γ.E_I = a ⊔ Γ.E_I :=
    calc (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ⊔ Γ.E_I
        = Γ.E_I ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) := sup_comm _ _
      _ = (Γ.E_I ⊔ (Γ.O ⊔ Γ.C)) ⊓ (a ⊔ Γ.E_I) :=
            (sup_inf_assoc_of_le _ le_sup_right).symm
      _ = (Γ.O ⊔ Γ.U ⊔ Γ.V) ⊓ (a ⊔ Γ.E_I) := by rw [EI_sup_OC_eq_π]
      _ = a ⊔ Γ.E_I := inf_eq_right.mpr haEI_le_π
  rw [hED]
  -- (a ⊔ E_I) ⊓ l = a: a ≤ l, E_I ≰ l, standard line_height_two.
  have ha_le : a ≤ (a ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left ha_on
  have haEI : a ≠ Γ.E_I := fun h => ha_ne_U
    (Γ.atom_on_both_eq_U ha ha_on (h ▸ Γ.hE_I_on_m))
  have h_lt : (a ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro h
    have hl_le : Γ.O ⊔ Γ.U ≤ a ⊔ Γ.E_I := inf_eq_right.mp h
    have h_eq := ((atom_covBy_join ha Γ.hE_I_atom haEI).eq_or_eq
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le hl_le).resolve_left
      (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)
    exact Γ.hE_I_not_l (le_sup_right.trans (le_of_eq h_eq.symm))
  exact ((line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le ha.bot_lt ha_le) h_lt
    |>.le_iff.mp ha_le).resolve_left ha.1).symm

/-- I ⊔ E_I = I ⊔ C: E_I ≤ I⊔C (by definition), so both lines
    through I contain E_I, and CovBy forces equality. -/
private theorem I_sup_EI_eq_IC : Γ.I ⊔ Γ.E_I = Γ.I ⊔ Γ.C := by
  have hIEI_le : Γ.I ⊔ Γ.E_I ≤ Γ.I ⊔ Γ.C := sup_le le_sup_left Γ.hE_I_le_IC
  have hI_ne_EI : Γ.I ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ Γ.hI_on)
  have hIC : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  exact ((atom_covBy_join Γ.hI Γ.hC hIC).eq_or_eq
    (atom_covBy_join Γ.hI Γ.hE_I_atom hI_ne_EI).lt.le hIEI_le).resolve_left
    (ne_of_gt (atom_covBy_join Γ.hI Γ.hE_I_atom hI_ne_EI).lt)

/-- (O⊔C) ⊓ (I⊔C) = C: two distinct lines meeting at their common point. -/
private theorem OC_inf_IC_eq_C : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ Γ.C) = Γ.C := by
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hIC : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hI_not_OC : ¬ Γ.I ≤ Γ.O ⊔ Γ.C := by
    intro h
    have hI_le : Γ.I ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) := le_inf Γ.hI_on h
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _,
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)] at hI_le
    exact Γ.hOI ((Γ.hO.le_iff.mp hI_le).resolve_left Γ.hI.1).symm
  rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _,
      show Γ.I ⊔ Γ.C = Γ.C ⊔ Γ.I from sup_comm _ _]
  exact modular_intersection Γ.hC Γ.hO Γ.hI hOC.symm hIC.symm Γ.hOI
    (show ¬ Γ.I ≤ Γ.C ⊔ Γ.O from sup_comm Γ.O Γ.C ▸ hI_not_OC)

/-- I is a right multiplicative identity: a · I = a.

    With b = I, the first perspectivity gives (O⊔C) ⊓ (I⊔E_I) = C
    (since I⊔E_I = I⊔C, and (O⊔C)⊓(I⊔C) = C). Then C ⊔ d_a = a ⊔ C
    by CovBy, and (a⊔C) ⊓ l = a. Same pattern as coord_add_right_zero. -/
theorem coord_mul_right_one (Γ : CoordSystem L)
    (a : L) (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) :
    coord_mul Γ a Γ.I = a := by
  unfold coord_mul
  rw [I_sup_EI_eq_IC, OC_inf_IC_eq_C]
  -- Goal: (C ⊔ (a⊔C) ⊓ m) ⊓ l = a.
  -- d_a ⊔ C = a ⊔ C by CovBy (same as coord_add_right_zero).
  have hAC : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have ha'C_le : Γ.C ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ a ⊔ Γ.C :=
    sup_le le_sup_right inf_le_left
  have ha_lt_aC : a < a ⊔ Γ.C := by
    apply lt_of_le_of_ne le_sup_left; intro h
    exact Γ.hC_not_l ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hC.1 ▸ ha_on)
  have ha'_ne_bot : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≠ ⊥ := by
    have h_meet := lines_meet_if_coplanar Γ.m_covBy_π
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane)
      (fun h => Γ.hC_not_m (le_trans le_sup_right h))
      ha ha_lt_aC
    rwa [@inf_comm L _] at h_meet
  have hC_lt : Γ.C < Γ.C ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
    apply lt_of_le_of_ne le_sup_left; intro h
    have ha'_le_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.C := le_sup_right.trans h.symm.le
    have hCm : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ := by
      rcases Γ.hC.le_iff.mp inf_le_left with h | h
      · exact h
      · exact absurd (h ▸ inf_le_right) Γ.hC_not_m
    have : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ ⊥ := hCm ▸ le_inf ha'_le_C inf_le_right
    exact ha'_ne_bot (le_antisymm this bot_le)
  have h_cov_Ca : Γ.C ⋖ a ⊔ Γ.C := by
    have := atom_covBy_join Γ.hC ha hAC.symm; rwa [sup_comm] at this
  have ha'C_eq : Γ.C ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = a ⊔ Γ.C :=
    (h_cov_Ca.eq_or_eq hC_lt.le ha'C_le).resolve_left (ne_of_gt hC_lt)
  rw [ha'C_eq]
  -- (a ⊔ C) ⊓ l = a.
  have ha_le : a ≤ (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left ha_on
  have h_lt : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro h
    have hl_le := inf_eq_right.mp h
    have h_eq := ((atom_covBy_join ha Γ.hC hAC).eq_or_eq
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le hl_le).resolve_left
      (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)
    exact Γ.hC_not_l (le_sup_right.trans (le_of_eq h_eq.symm))
  exact ((line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le ha.bot_lt ha_le) h_lt
    |>.le_iff.mp ha_le).resolve_left ha.1).symm

end Foam.FTPGExplore
