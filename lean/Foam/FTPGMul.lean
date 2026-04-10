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

end Foam.FTPGExplore
