/-
# Commutativity of coordinate addition

Proves coord_add_comm: a + b = b + a for von Staudt addition.

Two Desargues applications (coord_first_desargues, coord_second_desargues)
establish that the addition diagram commutes. Split from FTPGCoord.lean.
-/

import Foam.FTPGCoord

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

-- § Helpers for coord_add commutativity

variable (Γ : CoordSystem L)

/-- Two lines through C from distinct points on l meet at C. -/
theorem CoordSystem.lines_through_C_meet {a b : L}
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) :
    (a ⊔ Γ.C) ⊓ (b ⊔ Γ.C) = Γ.C := by
  rw [sup_comm a Γ.C, sup_comm b Γ.C]
  apply modular_intersection Γ.hC ha hb
    (fun h => Γ.hC_not_l (h ▸ ha_on))
    (fun h => Γ.hC_not_l (h ▸ hb_on)) hab
  intro hle
  have hb_le_a : b ≤ a := by
    have := le_inf hb_on hle
    rw [inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at this
    exact this
  exact hab ((ha.le_iff.mp hb_le_a).resolve_left hb.1).symm

/-- Two lines through E from distinct points on l meet at E. -/
theorem CoordSystem.lines_through_E_meet {a b : L}
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) :
    (a ⊔ Γ.E) ⊓ (b ⊔ Γ.E) = Γ.E := by
  rw [sup_comm a Γ.E, sup_comm b Γ.E]
  apply modular_intersection Γ.hE_atom ha hb
    (fun h => CoordSystem.hE_not_l (h ▸ ha_on))
    (fun h => CoordSystem.hE_not_l (h ▸ hb_on)) hab
  intro hle
  have hb_le_a : b ≤ a := by
    have := le_inf hb_on hle
    rw [inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l ha_on] at this
    exact this
  exact hab ((ha.le_iff.mp hb_le_a).resolve_left hb.1).symm

/-- O ⊔ C is covered by the plane π = O ⊔ U ⊔ V. -/
theorem CoordSystem.OC_covBy_π : Γ.O ⊔ Γ.C ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
  -- U ⊓ (O ⊔ C) = ⊥ (U not on line O ⊔ C, since that would give C on l)
  have hU_disj : Γ.U ⊓ (Γ.O ⊔ Γ.C) = ⊥ := by
    rcases Γ.hU.le_iff.mp inf_le_left with h | h
    · exact h
    · exfalso
      have hU_le := h ▸ inf_le_right  -- U ≤ O ⊔ C
      have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le (sup_le le_sup_left hU_le)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
  -- O ⊔ C ⋖ U ⊔ (O ⊔ C)
  have h := covBy_sup_of_inf_covBy_left (hU_disj ▸ Γ.hU.bot_covBy)
  -- Rewrite: U ⊔ (O ⊔ C) = O ⊔ U ⊔ C
  have h_assoc : Γ.U ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.C := by
    rw [← sup_assoc, sup_comm Γ.U Γ.O]
  rw [h_assoc] at h
  -- O ⊔ U ⊔ C = O ⊔ U ⊔ V (both = π)
  -- (O ⊔ U) ⊔ V = π by def. (O ⊔ U) ⋖ (O ⊔ U) ⊔ V (V off l).
  -- (O ⊔ U) < (O ⊔ U) ⊔ C ≤ (O ⊔ U) ⊔ V by CovBy.
  have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
    (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
  have h_l_cov : Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
  have h_lt : Γ.O ⊔ Γ.U < Γ.O ⊔ Γ.U ⊔ Γ.C := lt_of_le_of_ne le_sup_left
    (fun heq => Γ.hC_not_l (heq ▸ le_sup_right))
  have h_le : Γ.O ⊔ Γ.U ⊔ Γ.C ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le le_sup_left Γ.hC_plane
  rw [(h_l_cov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)] at h
  exact h


/-- **First Desargues for addition.** The point
    (a'⊔D_a) ⊓ (b'⊔D_b) lies on the line O⊔C.
    Proved by applying desargues_planar to triangles
    (a, a', D_a) and (b, b', D_b) perspective from U. -/
theorem coord_first_desargues (Γ : CoordSystem L) {a b : L}
    (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : a ≠ b)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓
    ((b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ≤ Γ.O ⊔ Γ.C := by
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set a' := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set b' := (b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set D_a := (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  set D_b := (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  -- All hypotheses for desargues_planar, proved individually
  have ha'_atom : IsAtom a' := by
    exact perspect_atom Γ.hC ha (fun h => Γ.hC_not_l (h ▸ ha_on)) Γ.hU Γ.hV
      (fun h => Γ.hV_off (h ▸ le_sup_right)) Γ.hC_not_m
      (sup_le (ha_on.trans (le_sup_left.trans (le_of_eq Γ.m_sup_C_eq_π.symm))) le_sup_right)
  have hb'_atom : IsAtom b' := by
    exact perspect_atom Γ.hC hb (fun h => Γ.hC_not_l (h ▸ hb_on)) Γ.hU Γ.hV
      (fun h => Γ.hV_off (h ▸ le_sup_right)) Γ.hC_not_m
      (sup_le (hb_on.trans (le_sup_left.trans (le_of_eq Γ.m_sup_C_eq_π.symm))) le_sup_right)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hE_not_UC : ¬ Γ.E ≤ Γ.U ⊔ Γ.C := by
    have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
      apply modular_intersection Γ.hU Γ.hC Γ.hV hUC
        (fun h => Γ.hV_off (h ▸ le_sup_right))
        (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      intro hle
      exact Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt.le
        (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt)
        ▸ le_sup_right)
    intro h
    exact CoordSystem.hEU (Γ.hU.le_iff.mp
      (hUC_inf_m ▸ le_inf h CoordSystem.hE_on_m) |>.resolve_left Γ.hE_atom.1)
  have ha_ne_E : a ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ ha_on)
  have hb_ne_E : b ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hb_on)
  have hUCE_eq_π : (Γ.U ⊔ Γ.C) ⊔ Γ.E = π := by
    have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
      have h_le : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right CoordSystem.hE_le_OC
      have h_lt : Γ.C < Γ.C ⊔ Γ.E := by
        apply lt_of_le_of_ne le_sup_left; intro h
        exact hCE ((Γ.hC.le_iff.mp (h ▸ le_sup_right : Γ.E ≤ Γ.C)).resolve_left
          Γ.hE_atom.1).symm
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact (atom_covBy_join Γ.hC Γ.hO hOC.symm |>.eq_or_eq h_lt.le
        (sup_comm Γ.C Γ.O ▸ h_le)).resolve_left (ne_of_gt h_lt)
    rw [show (Γ.U ⊔ Γ.C) ⊔ Γ.E = Γ.U ⊔ (Γ.C ⊔ Γ.E) from sup_assoc _ _ _, hCE_eq,
        show Γ.U ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.C from by rw [← sup_assoc, sup_comm Γ.U Γ.O]]
    have h_lt_OC : Γ.O ⊔ Γ.C < Γ.O ⊔ Γ.U ⊔ Γ.C := by
      apply lt_of_le_of_ne (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      intro h
      have hOU_le := h.symm ▸ (le_sup_left : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.U ⊔ Γ.C)
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le hOU_le).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt_OC.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt_OC)
  have hDa_atom : IsAtom D_a :=
    perspect_atom Γ.hE_atom ha ha_ne_E Γ.hU Γ.hC hUC hE_not_UC
      (sup_le (ha_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  have hDb_atom : IsAtom D_b :=
    perspect_atom Γ.hE_atom hb hb_ne_E Γ.hU Γ.hC hUC hE_not_UC
      (sup_le (hb_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  -- All 30+ hypotheses
  have hU_le_π : Γ.U ≤ π := le_sup_right.trans le_sup_left
  have hm_le_π : Γ.U ⊔ Γ.V ≤ π := sup_le hU_le_π le_sup_right
  have h_ho_le : Γ.U ≤ π := hU_le_π
  have h_ha1_le : a ≤ π := ha_on.trans le_sup_left
  have h_ha2_le : a' ≤ π := (inf_le_right : a' ≤ Γ.U ⊔ Γ.V).trans hm_le_π
  have h_ha3_le : D_a ≤ π := (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C).trans (sup_le hU_le_π Γ.hC_plane)
  have h_hb1_le : b ≤ π := hb_on.trans le_sup_left
  have h_hb2_le : b' ≤ π := (inf_le_right : b' ≤ Γ.U ⊔ Γ.V).trans hm_le_π
  have h_hb3_le : D_b ≤ π := (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C).trans (sup_le hU_le_π Γ.hC_plane)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)
  have hl_inf_UC : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U := by
    rw [sup_comm Γ.O Γ.U]
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm
      (fun h => Γ.hC_not_l (h ▸ le_sup_right))
      (fun h => Γ.hC_not_l (h ▸ le_sup_left))
      (fun h => Γ.hC_not_l (by rwa [sup_comm] at h))
  have ha_not_UC : ¬ a ≤ Γ.U ⊔ Γ.C := by
    intro h; exact ha_ne_U (Γ.hU.le_iff.mp (hl_inf_UC ▸ le_inf ha_on h) |>.resolve_left ha.1)
  -- Perspective: b_i ≤ U ⊔ a_i
  -- U ⊔ a = O ⊔ U (covering)
  have hUa_eq : Γ.U ⊔ a = Γ.O ⊔ Γ.U := by
    have h_lt : Γ.U < Γ.U ⊔ a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left ha.1))
    have : Γ.U ⊔ a ≤ Γ.U ⊔ Γ.O := sup_le le_sup_left (ha_on.trans (by rw [sup_comm]))
    exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le this).resolve_left
      (ne_of_gt h_lt) |>.trans (sup_comm _ _)
  have hb1_on : b ≤ Γ.U ⊔ a := hUa_eq ▸ hb_on
  have hb2_on : b' ≤ Γ.U ⊔ a' := by
    -- U ⊔ a' = U ⊔ V (covering), b' ≤ U ⊔ V
    have ha'_ne_U : a' ≠ Γ.U := by
      intro h
      have : Γ.U ≤ a ⊔ Γ.C := h ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
      have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) this
      rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
      exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
    have h_lt : Γ.U < Γ.U ⊔ a' := lt_of_le_of_ne le_sup_left
      (fun h => ha'_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left ha'_atom.1))
    have hUa'_eq : Γ.U ⊔ a' = Γ.U ⊔ Γ.V :=
      ((atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).eq_or_eq h_lt.le
        (sup_le le_sup_left inf_le_right)).resolve_left (ne_of_gt h_lt)
    exact hUa'_eq ▸ inf_le_right
  have hb3_on : D_b ≤ Γ.U ⊔ D_a := by
    -- U ⊔ D_a = U ⊔ C (covering), D_b ≤ U ⊔ C
    have hDa_ne_U : D_a ≠ Γ.U := by
      intro h
      have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := h ▸ (inf_le_left : D_a ≤ a ⊔ Γ.E)
      have h_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
        ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq
          (atom_covBy_join ha Γ.hU ha_ne_U).lt.le (sup_le le_sup_left hU_le_aE)).resolve_left
          (ne_of_gt (atom_covBy_join ha Γ.hU ha_ne_U).lt)
      exact CoordSystem.hE_not_l (le_of_le_of_eq le_sup_right h_eq.symm |>.trans
        (le_of_eq (show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _)) |>.trans (le_of_eq hUa_eq))
    have h_lt : Γ.U < Γ.U ⊔ D_a := lt_of_le_of_ne le_sup_left
      (fun h => hDa_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left hDa_atom.1))
    have hUDa_eq : Γ.U ⊔ D_a = Γ.U ⊔ Γ.C :=
      ((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq h_lt.le
        (sup_le le_sup_left inf_le_right)).resolve_left (ne_of_gt h_lt)
    exact hUDa_eq ▸ inf_le_right
  -- Vertex distinctness
  have h12a : a ≠ a' := fun h => ha_ne_U
    (Γ.atom_on_both_eq_U ha ha_on (h ▸ (inf_le_right : a' ≤ Γ.U ⊔ Γ.V)))
  have h13a : a ≠ D_a := fun h_eq => ha_ne_U (Γ.hU.le_iff.mp
    (hl_inf_UC ▸ le_inf ha_on (h_eq ▸ (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C)))
    |>.resolve_left ha.1)
  have h23a : a' ≠ D_a := by
    intro h
    have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
      apply modular_intersection Γ.hU Γ.hC Γ.hV hUC
        (fun h => Γ.hV_off (h ▸ le_sup_right))
        (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      intro hle
      exact Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt.le
        (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt)
        ▸ le_sup_right)
    have h1 : a' ≤ (Γ.U ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.C) := le_inf inf_le_right (h ▸ inf_le_right)
    rw [inf_comm, hUC_inf_m] at h1
    have ha'_ne_U : a' ≠ Γ.U := by
      intro heq
      have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := (le_of_eq heq.symm).trans inf_le_left
      have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hU_le_aC
      rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
      exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
    exact ha'_ne_U ((Γ.hU.le_iff.mp h1).resolve_left ha'_atom.1)
  have h12b : b ≠ b' := by
    intro heq
    exact hb_ne_U (Γ.atom_on_both_eq_U hb hb_on
      ((le_of_eq heq).trans inf_le_right))
  have h13b : b ≠ D_b := fun h_eq => hb_ne_U (Γ.hU.le_iff.mp
    (hl_inf_UC ▸ le_inf hb_on (h_eq ▸ (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C)))
    |>.resolve_left hb.1)
  have h23b : b' ≠ D_b := by
    intro h
    have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
      apply modular_intersection Γ.hU Γ.hC Γ.hV hUC
        (fun h => Γ.hV_off (h ▸ le_sup_right))
        (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      intro hle
      exact Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt.le
        (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt)
        ▸ le_sup_right)
    have h1 : b' ≤ (Γ.U ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.C) := le_inf inf_le_right (h ▸ inf_le_right)
    rw [inf_comm, hUC_inf_m] at h1
    have hb'_ne_U : b' ≠ Γ.U := by
      intro h2
      have hU_le_bC : Γ.U ≤ b ⊔ Γ.C := (le_of_eq h2.symm).trans inf_le_left
      have h3 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hU_le_bC
      rw [show b ⊔ Γ.C = Γ.C ⊔ b from sup_comm _ _,
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on] at h3
      exact hb_ne_U ((hb.le_iff.mp h3).resolve_left Γ.hU.1).symm
    exact hb'_ne_U ((Γ.hU.le_iff.mp h1).resolve_left hb'_atom.1)
  -- Join equalities (needed for sides and triangle planes)
  have haa' : a ⊔ a' = a ⊔ Γ.C := by
    have h_lt : a < a ⊔ a' := lt_of_le_of_ne le_sup_left
      (fun h => h12a ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left ha'_atom.1).symm)
    exact ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have hbb' : b ⊔ b' = b ⊔ Γ.C := by
    have h_lt : b < b ⊔ b' := lt_of_le_of_ne le_sup_left
      (fun h => h12b ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left hb'_atom.1).symm)
    exact ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have haDa : a ⊔ D_a = a ⊔ Γ.E := by
    have h_lt : a < a ⊔ D_a := lt_of_le_of_ne le_sup_left
      (fun h => h13a ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left hDa_atom.1).symm)
    exact ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have hbDb : b ⊔ D_b = b ⊔ Γ.E := by
    have h_lt : b < b ⊔ D_b := lt_of_le_of_ne le_sup_left
      (fun h => h13b ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left hDb_atom.1).symm)
    exact ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  -- Side distinctness
  have hs12 : a ⊔ a' ≠ b ⊔ b' := by
    rw [haa', hbb']; intro h
    have h2 := le_inf ha_on (le_of_le_of_eq le_sup_left h)
    rw [show b ⊔ Γ.C = Γ.C ⊔ b from sup_comm _ _,
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on] at h2
    exact hab ((hb.le_iff.mp h2).resolve_left ha.1)
  have hs13 : a ⊔ D_a ≠ b ⊔ D_b := by
    rw [haDa, hbDb]; intro h
    have h2 := le_inf ha_on (le_of_le_of_eq le_sup_left h)
    rw [show b ⊔ Γ.E = Γ.E ⊔ b from sup_comm _ _,
        inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l hb_on] at h2
    exact hab ((hb.le_iff.mp h2).resolve_left ha.1)
  have hs23 : a' ⊔ D_a ≠ b' ⊔ D_b := by
    -- Auxiliary: (U⊔C) ⊓ (U⊔V) = U
    have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
    have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
      apply modular_intersection Γ.hU Γ.hC Γ.hV hUC hUV
        (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      intro hle
      exact Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV hUV).lt.le
        (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV hUV).lt)
        ▸ le_sup_right)
    -- Auxiliary: D_a ≠ U
    have hDa_ne_U : D_a ≠ Γ.U := by
      intro h
      have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := h ▸ (inf_le_left : D_a ≤ a ⊔ Γ.E)
      have h_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
        ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq
          (atom_covBy_join ha Γ.hU ha_ne_U).lt.le (sup_le le_sup_left hU_le_aE)).resolve_left
          (ne_of_gt (atom_covBy_join ha Γ.hU ha_ne_U).lt)
      exact CoordSystem.hE_not_l (le_of_le_of_eq le_sup_right h_eq.symm |>.trans
        (le_of_eq (show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _)) |>.trans (le_of_eq hUa_eq))
    -- Auxiliary: D_a not on m
    have hDa_not_m : ¬ D_a ≤ Γ.U ⊔ Γ.V := by
      intro hle
      have h1 : D_a ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := le_inf inf_le_right hle
      rw [hUC_inf_m] at h1
      exact hDa_ne_U ((Γ.hU.le_iff.mp h1).resolve_left hDa_atom.1)
    -- Main proof by contradiction
    intro heq
    -- Case split: a' = b' or a' ≠ b'
    by_cases hab' : a' = b'
    · -- Case a' = b': a' ≤ (C⊔a) ⊓ (C⊔b) = C, contradicting C not on m
      exfalso
      have ha'_le_aC : a' ≤ Γ.C ⊔ a := sup_comm a Γ.C ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
      have ha'_le_bC : a' ≤ Γ.C ⊔ b :=
        sup_comm b Γ.C ▸ (hab' ▸ (inf_le_left : b' ≤ b ⊔ Γ.C))
      have hb_not_Ca : ¬ b ≤ Γ.C ⊔ a := by
        intro hle
        -- b ≤ C⊔a and a ≤ C⊔a, so a⊔b ≤ C⊔a.
        -- a ⋖ C⊔a (covering of distinct atoms C, a with sup_comm).
        -- a ≤ a⊔b ≤ C⊔a and a < a⊔b (since a ≠ b), so a⊔b = C⊔a by covering.
        -- Then C ≤ a⊔b ≤ l, contradicting hC_not_l.
        have hab_le : a ⊔ b ≤ Γ.C ⊔ a := sup_le le_sup_right hle
        have h_cov_aCa : a ⋖ Γ.C ⊔ a := sup_comm Γ.C a ▸
          atom_covBy_join ha Γ.hC ha_ne_C
        have h_lt_ab : a < a ⊔ b := lt_of_le_of_ne le_sup_left
          (fun h => hab ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left hb.1).symm)
        have h_eq : a ⊔ b = Γ.C ⊔ a :=
          (h_cov_aCa.eq_or_eq h_lt_ab.le hab_le).resolve_left (ne_of_gt h_lt_ab)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_left h_eq.symm |>.trans
          (sup_le ha_on hb_on))
      have hCab : (Γ.C ⊔ a) ⊓ (Γ.C ⊔ b) = Γ.C :=
        modular_intersection Γ.hC ha hb (fun h => ha_ne_C h.symm)
          (fun h => hb_ne_C h.symm) hab hb_not_Ca
      have ha'_le_C : a' ≤ Γ.C := le_of_le_of_eq (le_inf ha'_le_aC ha'_le_bC) hCab
      have ha'_eq_C : a' = Γ.C := (Γ.hC.le_iff.mp ha'_le_C).resolve_left ha'_atom.1
      exact Γ.hC_not_m (ha'_eq_C ▸ inf_le_right)
    · -- Case a' ≠ b': a'⊔b' = U⊔V, so m ≤ a'⊔D_a, forcing D_a on m — contradiction
      exfalso
      have h_cov_UV : Γ.U ⋖ Γ.U ⊔ Γ.V := atom_covBy_join Γ.hU Γ.hV hUV
      have ha'b'_le : a' ⊔ b' ≤ Γ.U ⊔ Γ.V := sup_le inf_le_right inf_le_right
      -- a' < a'⊔b' (since a' ≠ b', both atoms)
      have h_a'_lt_a'b' : a' < a' ⊔ b' := lt_of_le_of_ne le_sup_left
        (fun h => hab' ((ha'_atom.le_iff.mp
          (le_of_le_of_eq le_sup_right h.symm)).resolve_left hb'_atom.1).symm)
      -- a' < U⊔V
      have h_lt_m : a' < Γ.U ⊔ Γ.V := lt_of_lt_of_le h_a'_lt_a'b' ha'b'_le
      -- U ≤ a'⊔b' (by modularity: if not, then b' ≤ a')
      have hU_le_a'b' : Γ.U ≤ a' ⊔ b' := by
        by_contra hU_not
        have hU_inf : Γ.U ⊓ (a' ⊔ b') = ⊥ :=
          (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun h => hU_not (h ▸ inf_le_right))
        -- a' ≠ U (otherwise U ⊓ (U⊔b') = U ≠ ⊥)
        have ha'_ne_U : a' ≠ Γ.U := by
          intro h; rw [h] at hU_inf
          exact Γ.hU.1 (le_bot_iff.mp (hU_inf ▸ le_inf le_rfl le_sup_left))
        -- U⊔a' = U⊔V (covering)
        have ha'U_eq : Γ.U ⊔ a' = Γ.U ⊔ Γ.V := by
          have h_lt : Γ.U < Γ.U ⊔ a' := lt_of_le_of_ne le_sup_left
            (fun h => ha'_ne_U ((Γ.hU.le_iff.mp
              (le_of_le_of_eq le_sup_right h.symm)).resolve_left ha'_atom.1))
          exact (h_cov_UV.eq_or_eq h_lt.le
            (sup_le le_sup_left inf_le_right)).resolve_left (ne_of_gt h_lt)
        -- Modularity: (a'⊔U) ⊓ (a'⊔b') = a' ⊔ (U ⊓ (a'⊔b')) = a' ⊔ ⊥ = a'
        have hmod : (Γ.U ⊔ a') ⊓ (a' ⊔ b') = a' := by
          have h1 := sup_inf_assoc_of_le Γ.U (le_sup_left : a' ≤ a' ⊔ b')
          rw [hU_inf, sup_bot_eq, sup_comm a' Γ.U] at h1; exact h1
        -- So (U⊔V) ⊓ (a'⊔b') = a', and b' ≤ both, so b' ≤ a'
        rw [ha'U_eq] at hmod
        have hb'_le_a' : b' ≤ a' :=
          le_of_le_of_eq (le_inf inf_le_right (le_sup_right : b' ≤ a' ⊔ b')) hmod
        exact hab' ((ha'_atom.le_iff.mp hb'_le_a').resolve_left hb'_atom.1).symm
      -- a'⊔b' = U⊔V (by covering U⋖U⊔V, since U < a'⊔b')
      have hU_lt_a'b' : Γ.U < a' ⊔ b' :=
        lt_of_le_of_ne hU_le_a'b' (fun h => by
          have ha'_le_U : a' ≤ Γ.U := le_of_le_of_eq le_sup_left h.symm
          have hb'_le_U : b' ≤ Γ.U := le_of_le_of_eq le_sup_right h.symm
          exact hab' ((Γ.hU.le_iff.mp ha'_le_U).resolve_left ha'_atom.1 |>.trans
            ((Γ.hU.le_iff.mp hb'_le_U).resolve_left hb'_atom.1).symm))
      have hm_eq : a' ⊔ b' = Γ.U ⊔ Γ.V :=
        (h_cov_UV.eq_or_eq hU_lt_a'b'.le ha'b'_le).resolve_left (ne_of_gt hU_lt_a'b')
      -- b' ≤ a'⊔D_a (from heq), so m = a'⊔b' ≤ a'⊔D_a
      have hb'_le : b' ≤ a' ⊔ D_a := le_of_le_of_eq le_sup_left heq.symm
      have ha'b'_le_a'Da : a' ⊔ b' ≤ a' ⊔ D_a := sup_le le_sup_left hb'_le
      have hm_le : Γ.U ⊔ Γ.V ≤ a' ⊔ D_a := hm_eq ▸ ha'b'_le_a'Da
      -- a' ⋖ a'⊔D_a, and a' < m ≤ a'⊔D_a, so a'⊔D_a = m (covering)
      have h_cov : a' ⋖ a' ⊔ D_a := atom_covBy_join ha'_atom hDa_atom h23a
      have h_eq_m : a' ⊔ D_a = Γ.U ⊔ Γ.V :=
        ((h_cov.eq_or_eq h_lt_m.le hm_le).resolve_left (ne_of_gt h_lt_m)).symm
      -- D_a ≤ m, contradiction
      exact hDa_not_m (le_of_le_of_eq le_sup_right h_eq_m)
  -- D_a ≠ C (helper for triangle planes)
  have hDa_ne_C : D_a ≠ Γ.C := by
    intro h
    have hC_le_aE : Γ.C ≤ a ⊔ Γ.E := (le_of_eq h.symm).trans inf_le_left
    have h_aCE : a ⊔ Γ.C ≤ a ⊔ Γ.E := sup_le le_sup_left hC_le_aE
    have h_aC_lt : a < a ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_C ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hC.1).symm)
    have h_eq : a ⊔ Γ.C = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq h_aC_lt.le h_aCE).resolve_left
        (ne_of_gt h_aC_lt)
    have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := le_of_le_of_eq le_sup_right h_eq.symm
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
    have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
        hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
    have hCE' : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
    exact hCE' ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_aC CoordSystem.hE_le_OC) h_inf_C)).resolve_left
      Γ.hE_atom.1).symm
  have hCDa_eq : Γ.C ⊔ D_a = Γ.U ⊔ Γ.C := by
    have h_lt : Γ.C < Γ.C ⊔ D_a := by
      apply lt_of_le_of_ne le_sup_left
      intro heq
      have hDa_le_C : D_a ≤ Γ.C := le_of_le_of_eq le_sup_right heq.symm
      exact hDa_ne_C ((Γ.hC.le_iff.mp hDa_le_C).resolve_left hDa_atom.1)
    rw [sup_comm Γ.U Γ.C]
    exact ((atom_covBy_join Γ.hC Γ.hU hUC.symm).eq_or_eq h_lt.le
      (sup_le le_sup_left ((inf_le_right).trans (le_of_eq (sup_comm Γ.U Γ.C))))).resolve_left (ne_of_gt h_lt)
  have hDa_not_aC : ¬ D_a ≤ a ⊔ Γ.C := by
    intro hle
    have h_le : D_a ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.U) :=
      le_inf ((sup_comm a Γ.C).symm ▸ hle) ((sup_comm Γ.U Γ.C).symm ▸ inf_le_right)
    rw [modular_intersection Γ.hC ha Γ.hU (fun h => ha_ne_C h.symm) hUC.symm
      ha_ne_U (by
        intro hle; rw [sup_comm] at hle
        have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hle
        rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
            inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
        exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm)] at h_le
    exact hDa_ne_C ((Γ.hC.le_iff.mp h_le).resolve_left hDa_atom.1)
  -- Triangle planes
  have hπA : a ⊔ a' ⊔ D_a = π := by
    rw [haa', sup_assoc, hCDa_eq, show a ⊔ (Γ.U ⊔ Γ.C) = (a ⊔ Γ.U) ⊔ Γ.C from
      (sup_assoc _ _ _).symm, show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _, hUa_eq]
    have h_OC_le : Γ.O ⊔ Γ.C ≤ (Γ.O ⊔ Γ.U) ⊔ Γ.C :=
      sup_le (le_sup_left.trans le_sup_left) le_sup_right
    have h_lt : Γ.O ⊔ Γ.C < (Γ.O ⊔ Γ.U) ⊔ Γ.C := by
      apply lt_of_le_of_ne h_OC_le
      intro heq
      have : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.C := le_of_le_of_eq le_sup_left heq.symm
      have h_eq := (((atom_covBy_join Γ.hO Γ.hC (fun h => Γ.hC_not_l (h ▸ le_sup_left))).eq_or_eq
          (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le this).resolve_left
          (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt))
      -- h_eq : Γ.O ⊔ Γ.U = Γ.O ⊔ Γ.C, so C ≤ O⊔C = O⊔U = l
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right h_eq.symm)
    exact (((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt))
  have hπB : b ⊔ b' ⊔ D_b = π := by
    rw [hbb']
    have hDb_ne_C : D_b ≠ Γ.C := by
      intro h
      have hC_le_bE : Γ.C ≤ b ⊔ Γ.E := (le_of_eq h.symm).trans inf_le_left
      have h_bC_lt : b < b ⊔ Γ.C := lt_of_le_of_ne le_sup_left
        (fun h => hb_ne_C ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hC.1).symm)
      have h_eq : b ⊔ Γ.C = b ⊔ Γ.E :=
        ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq h_bC_lt.le
          (sup_le le_sup_left hC_le_bE)).resolve_left (ne_of_gt h_bC_lt)
      have hE_le_bC : Γ.E ≤ b ⊔ Γ.C := le_of_le_of_eq le_sup_right h_eq.symm
      have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
      have hO_not_bC : ¬ Γ.O ≤ b ⊔ Γ.C := by
        intro hle
        have heq : b ⊔ Γ.O = b ⊔ Γ.C :=
          ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq (atom_covBy_join hb Γ.hO hb_ne_O).lt.le
            (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join hb Γ.hO hb_ne_O).lt)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le hb_on le_sup_left))
      have h_inf_C : (b ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm b Γ.C, sup_comm Γ.O Γ.C]
        exact modular_intersection Γ.hC hb Γ.hO (fun h => hb_ne_C h.symm)
          hOC.symm hb_ne_O (by rwa [sup_comm] at hO_not_bC)
      have hCE' : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
      exact hCE' ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_bC CoordSystem.hE_le_OC)
          h_inf_C)).resolve_left Γ.hE_atom.1).symm
    have hCDb_eq : Γ.C ⊔ D_b = Γ.U ⊔ Γ.C := by
      have h_lt : Γ.C < Γ.C ⊔ D_b := by
        apply lt_of_le_of_ne le_sup_left
        intro heq
        exact hDb_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq le_sup_right heq.symm)).resolve_left
          hDb_atom.1)
      rw [sup_comm Γ.U Γ.C]
      exact ((atom_covBy_join Γ.hC Γ.hU hUC.symm).eq_or_eq h_lt.le
        (sup_le le_sup_left ((inf_le_right).trans (le_of_eq (sup_comm Γ.U Γ.C))))).resolve_left
        (ne_of_gt h_lt)
    rw [sup_assoc, hCDb_eq, show b ⊔ (Γ.U ⊔ Γ.C) = (b ⊔ Γ.U) ⊔ Γ.C from
      (sup_assoc _ _ _).symm, show b ⊔ Γ.U = Γ.U ⊔ b from sup_comm _ _]
    have hUb_eq : Γ.U ⊔ b = Γ.O ⊔ Γ.U := by
      have h_lt : Γ.U < Γ.U ⊔ b := lt_of_le_of_ne le_sup_left
        (fun h => hb_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left hb.1))
      exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le
        (sup_le le_sup_left (hb_on.trans (by rw [sup_comm])))).resolve_left
        (ne_of_gt h_lt) |>.trans (sup_comm _ _)
    rw [hUb_eq]
    have h_OC_le : Γ.O ⊔ Γ.C ≤ (Γ.O ⊔ Γ.U) ⊔ Γ.C :=
      sup_le (le_sup_left.trans le_sup_left) le_sup_right
    have h_lt : Γ.O ⊔ Γ.C < (Γ.O ⊔ Γ.U) ⊔ Γ.C := by
      apply lt_of_le_of_ne h_OC_le; intro heq
      have : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.C := le_of_le_of_eq le_sup_left heq.symm
      have h_eq := (((atom_covBy_join Γ.hO Γ.hC (fun h => Γ.hC_not_l (h ▸ le_sup_left))).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le this).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt))
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right h_eq.symm)
    exact (((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt))
  -- U ≠ vertices
  have hoa1 : Γ.U ≠ a := ha_ne_U.symm
  have hoa2 : Γ.U ≠ a' := by
    intro h
    have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := (le_of_eq h).trans inf_le_left
    have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hU_le_aC
    rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
    exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
  have hoa3 : Γ.U ≠ D_a := by
    intro h
    have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := (le_of_eq h).trans inf_le_left
    have h_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq
        (atom_covBy_join ha Γ.hU ha_ne_U).lt.le (sup_le le_sup_left hU_le_aE)).resolve_left
        (ne_of_gt (atom_covBy_join ha Γ.hU ha_ne_U).lt)
    exact CoordSystem.hE_not_l (calc Γ.E ≤ a ⊔ Γ.E := le_sup_right
      _ = a ⊔ Γ.U := h_eq.symm
      _ = Γ.U ⊔ a := sup_comm _ _
      _ = Γ.O ⊔ Γ.U := hUa_eq)
  have hob1 : Γ.U ≠ b := hb_ne_U.symm
  have hob2 : Γ.U ≠ b' := by
    intro h
    have hU_le_bC : Γ.U ≤ b ⊔ Γ.C := (le_of_eq h).trans inf_le_left
    have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hU_le_bC
    rw [show b ⊔ Γ.C = Γ.C ⊔ b from sup_comm _ _,
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on] at h2
    exact hb_ne_U ((hb.le_iff.mp h2).resolve_left Γ.hU.1).symm
  have hob3 : Γ.U ≠ D_b := by
    intro h
    have hU_le_bE : Γ.U ≤ b ⊔ Γ.E := (le_of_eq h).trans inf_le_left
    have hUb_eq : Γ.U ⊔ b = Γ.O ⊔ Γ.U := by
      have h_lt : Γ.U < Γ.U ⊔ b := lt_of_le_of_ne le_sup_left
        (fun h => hb_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left hb.1))
      exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le
        (sup_le le_sup_left (hb_on.trans (by rw [sup_comm])))).resolve_left
        (ne_of_gt h_lt) |>.trans (sup_comm _ _)
    have h_eq : b ⊔ Γ.U = b ⊔ Γ.E :=
      ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq
        (atom_covBy_join hb Γ.hU hb_ne_U).lt.le (sup_le le_sup_left hU_le_bE)).resolve_left
        (ne_of_gt (atom_covBy_join hb Γ.hU hb_ne_U).lt)
    exact CoordSystem.hE_not_l (calc Γ.E ≤ b ⊔ Γ.E := le_sup_right
      _ = b ⊔ Γ.U := h_eq.symm
      _ = Γ.U ⊔ b := sup_comm _ _
      _ = Γ.O ⊔ Γ.U := hUb_eq)
  -- Corresponding vertices distinct
  have hab12 : a ≠ b := hab
  have hab22 : a' ≠ b' := by
    intro h
    have h_le_C : a' ≤ (a ⊔ Γ.C) ⊓ (b ⊔ Γ.C) :=
      le_inf inf_le_left ((le_of_eq h).trans inf_le_left)
    rw [CoordSystem.lines_through_C_meet Γ ha hb hab ha_on hb_on] at h_le_C
    exact Γ.hC_not_m (((Γ.hC.le_iff.mp h_le_C).resolve_left ha'_atom.1).symm ▸ inf_le_right)
  have hab32 : D_a ≠ D_b := by
    intro h
    have h_le_E : D_a ≤ (a ⊔ Γ.E) ⊓ (b ⊔ Γ.E) :=
      le_inf inf_le_left ((le_of_eq h).trans inf_le_left)
    rw [CoordSystem.lines_through_E_meet Γ ha hb hab ha_on hb_on] at h_le_E
    exact hE_not_UC (((Γ.hE_atom.le_iff.mp h_le_E).resolve_left hDa_atom.1).symm ▸ inf_le_right)
  -- Sides covered by π
  have hcov12 : a ⊔ a' ⋖ π := by
    rw [haa']
    have hDa_inf : D_a ⊓ (a ⊔ Γ.C) = ⊥ :=
      (hDa_atom.le_iff.mp inf_le_left).resolve_right
        (fun h => hDa_not_aC ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (hDa_inf ▸ hDa_atom.bot_covBy)
    rwa [show D_a ⊔ (a ⊔ Γ.C) = a ⊔ Γ.C ⊔ D_a from sup_comm _ _,
         show a ⊔ Γ.C ⊔ D_a = a ⊔ a' ⊔ D_a from by rw [← haa'], hπA] at h_cov
  have hcov13 : a ⊔ D_a ⋖ π := by
    rw [haDa]
    have ha_not_m : ¬ a ≤ Γ.U ⊔ Γ.V :=
      fun hle => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on hle)
    have ha'_not_aE : ¬ a' ≤ a ⊔ Γ.E := by
      intro h
      have ha_inf_m : a ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
        (ha.le_iff.mp inf_le_left).resolve_right (fun h => ha_not_m ((le_of_eq h.symm).trans inf_le_right))
      have h_mod : (Γ.E ⊔ a) ⊓ (Γ.U ⊔ Γ.V) = Γ.E ⊔ a ⊓ (Γ.U ⊔ Γ.V) :=
        sup_inf_assoc_of_le a CoordSystem.hE_on_m
      rw [ha_inf_m, sup_bot_eq] at h_mod
      have ha'_le_E : a' ≤ Γ.E := by
        have := le_inf h (inf_le_right : a' ≤ Γ.U ⊔ Γ.V)
        rwa [show (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.V) = (Γ.E ⊔ a) ⊓ (Γ.U ⊔ Γ.V) from by
          rw [sup_comm a Γ.E], h_mod] at this
      have hE_on_aC : Γ.E ≤ a ⊔ Γ.C := by
        have ha'_eq_E := (Γ.hE_atom.le_iff.mp ha'_le_E).resolve_left ha'_atom.1
        exact (le_of_eq ha'_eq_E.symm).trans inf_le_left
      have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
        intro hle
        have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
          ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
            (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
      have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
        have hOC' : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
        exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
          hOC'.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
      have hCE' : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
      exact hCE' ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_on_aC CoordSystem.hE_le_OC)
          h_inf_C)).resolve_left Γ.hE_atom.1).symm
    have ha'_inf : a' ⊓ (a ⊔ Γ.E) = ⊥ :=
      (ha'_atom.le_iff.mp inf_le_left).resolve_right
        (fun h => ha'_not_aE ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (ha'_inf ▸ ha'_atom.bot_covBy)
    rwa [show a' ⊔ (a ⊔ Γ.E) = a ⊔ Γ.E ⊔ a' from sup_comm _ _,
         show a ⊔ Γ.E ⊔ a' = a ⊔ a' ⊔ D_a from by
           rw [← haDa, sup_comm (a ⊔ D_a) a', ← sup_assoc, sup_comm a' a],
         hπA] at h_cov
  have hcov23 : a' ⊔ D_a ⋖ π := by
    have ha_not_a'Da : ¬ a ≤ a' ⊔ D_a := by
      intro h
      have h_le : a ⊔ a' ≤ a' ⊔ D_a := sup_le h le_sup_left
      have h_le' : a' ⊔ a ≤ a' ⊔ D_a := sup_comm a a' ▸ h_le
      rcases (atom_covBy_join ha'_atom hDa_atom h23a).eq_or_eq
        (atom_covBy_join ha'_atom ha h12a.symm).lt.le h_le' with h_abs | h_abs
      · -- h_abs : a' ⊔ a = a', so a ≤ a'
        have ha_le_a' : a ≤ a' := le_of_le_of_eq (le_sup_right : a ≤ a' ⊔ a) h_abs
        exact h12a ((ha'_atom.le_iff.mp ha_le_a').resolve_left ha.1)
      · -- h_abs : a' ⊔ a = a' ⊔ D_a, so D_a ≤ a' ⊔ a = a ⊔ a' = a ⊔ C
        have : D_a ≤ a ⊔ Γ.C := by
          calc D_a ≤ a' ⊔ D_a := le_sup_right
            _ = a' ⊔ a := h_abs.symm
            _ = a ⊔ a' := sup_comm _ _
            _ = a ⊔ Γ.C := haa'
        exact hDa_not_aC this
    have ha_inf : a ⊓ (a' ⊔ D_a) = ⊥ :=
      (ha.le_iff.mp inf_le_left).resolve_right
        (fun h => ha_not_a'Da ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (ha_inf ▸ ha.bot_covBy)
    rwa [show a ⊔ (a' ⊔ D_a) = a ⊔ a' ⊔ D_a from (sup_assoc _ _ _).symm, hπA] at h_cov
  -- Apply desargues_planar
  obtain ⟨axis, h_axis_le, h_axis_ne, h₁, h₂, h₃⟩ := desargues_planar
    Γ.hU ha ha'_atom hDa_atom hb hb'_atom hDb_atom
    h_ho_le h_ha1_le h_ha2_le h_ha3_le h_hb1_le h_hb2_le h_hb3_le
    hb1_on hb2_on hb3_on
    h12a h13a h23a
    h12b h13b h23b
    hs12 hs13 hs23
    hπA hπB
    hoa1 hoa2 hoa3 hob1 hob2 hob3
    hab12 hab22 hab32
    R hR hR_not h_irred
    hcov12 hcov13 hcov23
  -- First two side-intersections are C and E
  rw [haa', hbb', CoordSystem.lines_through_C_meet Γ ha hb hab ha_on hb_on] at h₁
  rw [haDa, hbDb, CoordSystem.lines_through_E_meet Γ ha hb hab ha_on hb_on] at h₂
  -- collinear_of_common_bound
  have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
    have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have h_le : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right CoordSystem.hE_le_OC
    have h_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hCE ((Γ.hC.le_iff.mp (h ▸ le_sup_right : Γ.E ≤ Γ.C)).resolve_left
        Γ.hE_atom.1).symm)
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
    exact (atom_covBy_join Γ.hC Γ.hO hOC.symm |>.eq_or_eq h_lt.le
      (sup_comm Γ.C Γ.O ▸ h_le)).resolve_left (ne_of_gt h_lt)
  have hCE_covBy : Γ.C ⊔ Γ.E ⋖ π := by rw [hCE_eq]; exact CoordSystem.OC_covBy_π Γ
  exact (collinear_of_common_bound (s₁ := Γ.C) (s₂ := Γ.E) hCE_covBy h_axis_le h_axis_ne h₁ h₂ h₃).trans
    (le_of_eq hCE_eq)

/-- **Second Desargues for addition.** Given P₁ ≤ O⊔C (from the first),
    the point W = (a'⊔D_b) ⊓ (b'⊔D_a) lies on l = O⊔U.
    Proved by applying desargues_planar to triangles
    (C, a', D_b) and (E, D_a, b') perspective from P₁. -/
theorem coord_second_desargues (Γ : CoordSystem L) {a b : L}
    (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : a ≠ b)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q)
    (hP₁ : ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓
            ((b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ≤ Γ.O ⊔ Γ.C) :
    ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓
    ((b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ≤ Γ.O ⊔ Γ.U := by
  /- Proof plan: apply desargues_planar to
     Center: P₁ = (a'⊔D_a) ⊓ (b'⊔D_b)
     Triangle A: (C, a', D_b)  Triangle B: (E, D_a, b')
     Side intersections: (C⊔a')⊓(E⊔D_a)=a, (C⊔D_b)⊓(E⊔b')=U, (a'⊔D_b)⊓(D_a⊔b')=W
     Then a ⊔ U = O⊔U = l, and collinear_of_common_bound gives W ≤ l. -/
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set a' := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set b' := (b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set D_a := (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  set D_b := (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  set P₁ := (a' ⊔ D_a) ⊓ (b' ⊔ D_b)
  -- ── basic distinctness ──
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
  have ha_ne_E : a ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ ha_on)
  have hb_ne_E : b ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hb_on)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)
  -- ── key modular intersections ──
  have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U :=
    modular_intersection Γ.hU Γ.hC Γ.hV hUC hUV
      (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      (fun hle => Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV hUV).lt.le (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV hUV).lt) ▸ le_sup_right))
  have hE_not_UC : ¬ Γ.E ≤ Γ.U ⊔ Γ.C := fun h =>
    CoordSystem.hEU (Γ.hU.le_iff.mp (hUC_inf_m ▸ le_inf h CoordSystem.hE_on_m)
      |>.resolve_left Γ.hE_atom.1)
  have hl_inf_UC : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U := by
    rw [sup_comm Γ.O Γ.U]
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm
      (fun h => Γ.hC_not_l (h ▸ le_sup_right))
      (fun h => Γ.hC_not_l (h ▸ le_sup_left))
      (fun h => Γ.hC_not_l (by rwa [sup_comm] at h))
  -- ── coplanarity ──
  have hUCE_eq_π : (Γ.U ⊔ Γ.C) ⊔ Γ.E = π := by
    have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
      have h_le : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right CoordSystem.hE_le_OC
      have h_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
        (fun h => hCE ((Γ.hC.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hE_atom.1).symm)
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact (atom_covBy_join Γ.hC Γ.hO hOC.symm |>.eq_or_eq h_lt.le
        (sup_comm Γ.C Γ.O ▸ h_le)).resolve_left (ne_of_gt h_lt)
    rw [show (Γ.U ⊔ Γ.C) ⊔ Γ.E = Γ.U ⊔ (Γ.C ⊔ Γ.E) from sup_assoc _ _ _, hCE_eq,
        show Γ.U ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.C from by rw [← sup_assoc, sup_comm Γ.U Γ.O]]
    have h_lt : Γ.O ⊔ Γ.C < Γ.O ⊔ Γ.U ⊔ Γ.C := by
      apply lt_of_le_of_ne (sup_le (le_sup_left.trans le_sup_left) le_sup_right); intro h
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le
        (h.symm ▸ le_sup_left)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt)
  -- ── atom properties ──
  have ha'_atom : IsAtom a' := perspect_atom Γ.hC ha
    (fun h => Γ.hC_not_l (h ▸ ha_on)) Γ.hU Γ.hV hUV Γ.hC_not_m
    (sup_le (ha_on.trans (le_sup_left.trans (le_of_eq Γ.m_sup_C_eq_π.symm))) le_sup_right)
  have hb'_atom : IsAtom b' := perspect_atom Γ.hC hb
    (fun h => Γ.hC_not_l (h ▸ hb_on)) Γ.hU Γ.hV hUV Γ.hC_not_m
    (sup_le (hb_on.trans (le_sup_left.trans (le_of_eq Γ.m_sup_C_eq_π.symm))) le_sup_right)
  have hDa_atom : IsAtom D_a := perspect_atom Γ.hE_atom ha ha_ne_E Γ.hU Γ.hC hUC hE_not_UC
    (sup_le (ha_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  have hDb_atom : IsAtom D_b := perspect_atom Γ.hE_atom hb hb_ne_E Γ.hU Γ.hC hUC hE_not_UC
    (sup_le (hb_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  -- ── more distinctness ──
  have hDa_ne_U : D_a ≠ Γ.U := by
    intro h
    have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := h ▸ (inf_le_left : D_a ≤ a ⊔ Γ.E)
    have h_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq
        (atom_covBy_join ha Γ.hU ha_ne_U).lt.le (sup_le le_sup_left hU_le_aE)).resolve_left
        (ne_of_gt (atom_covBy_join ha Γ.hU ha_ne_U).lt)
    have hUa_eq' : Γ.U ⊔ a = Γ.O ⊔ Γ.U := by
      have h_lt : Γ.U < Γ.U ⊔ a := lt_of_le_of_ne le_sup_left
        (fun h => ha_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left ha.1))
      exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le
        (sup_le le_sup_left (ha_on.trans (sup_comm Γ.O Γ.U).le))).resolve_left
        (ne_of_gt h_lt) |>.trans (sup_comm _ _)
    exact CoordSystem.hE_not_l (le_of_le_of_eq le_sup_right h_eq.symm |>.trans
      (le_of_eq (show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _)) |>.trans (le_of_eq hUa_eq'))
  have hDb_ne_U : D_b ≠ Γ.U := by
    intro h
    have hU_le_bE : Γ.U ≤ b ⊔ Γ.E := h ▸ (inf_le_left : D_b ≤ b ⊔ Γ.E)
    have hUb_eq : Γ.U ⊔ b = Γ.O ⊔ Γ.U := by
      have h_lt : Γ.U < Γ.U ⊔ b := lt_of_le_of_ne le_sup_left
        (fun h => hb_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left hb.1))
      exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le
        (sup_le le_sup_left (hb_on.trans (by rw [sup_comm])))).resolve_left
        (ne_of_gt h_lt) |>.trans (sup_comm _ _)
    have h_eq : b ⊔ Γ.U = b ⊔ Γ.E :=
      ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq
        (atom_covBy_join hb Γ.hU hb_ne_U).lt.le (sup_le le_sup_left hU_le_bE)).resolve_left
        (ne_of_gt (atom_covBy_join hb Γ.hU hb_ne_U).lt)
    exact CoordSystem.hE_not_l (calc Γ.E ≤ b ⊔ Γ.E := le_sup_right
      _ = b ⊔ Γ.U := h_eq.symm
      _ = Γ.U ⊔ b := sup_comm _ _
      _ = Γ.O ⊔ Γ.U := hUb_eq)
  have hDa_ne_C : D_a ≠ Γ.C := by
    intro h
    have hC_le_aE : Γ.C ≤ a ⊔ Γ.E := (le_of_eq h.symm).trans inf_le_left
    have h_aCE : a ⊔ Γ.C ≤ a ⊔ Γ.E := sup_le le_sup_left hC_le_aE
    have h_aC_lt : a < a ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_C ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hC.1).symm)
    have h_eq : a ⊔ Γ.C = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq h_aC_lt.le h_aCE).resolve_left
        (ne_of_gt h_aC_lt)
    have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := le_of_le_of_eq le_sup_right h_eq.symm
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
    have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
        hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
    exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_aC CoordSystem.hE_le_OC) h_inf_C)).resolve_left
      Γ.hE_atom.1).symm
  have hDb_ne_C : D_b ≠ Γ.C := by
    intro h
    have hC_le_bE : Γ.C ≤ b ⊔ Γ.E := (le_of_eq h.symm).trans inf_le_left
    have h_bC_lt : b < b ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h => hb_ne_C ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hC.1).symm)
    have h_eq : b ⊔ Γ.C = b ⊔ Γ.E :=
      ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq h_bC_lt.le
        (sup_le le_sup_left hC_le_bE)).resolve_left (ne_of_gt h_bC_lt)
    have hE_le_bC : Γ.E ≤ b ⊔ Γ.C := le_of_le_of_eq le_sup_right h_eq.symm
    have hO_not_bC : ¬ Γ.O ≤ b ⊔ Γ.C := by
      intro hle
      have heq : b ⊔ Γ.O = b ⊔ Γ.C :=
        ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq (atom_covBy_join hb Γ.hO hb_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join hb Γ.hO hb_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le hb_on le_sup_left))
    have h_inf_C : (b ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm b Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC hb Γ.hO (fun h => hb_ne_C h.symm)
        hOC.symm hb_ne_O (by rwa [sup_comm] at hO_not_bC)
    exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_bC CoordSystem.hE_le_OC)
        h_inf_C)).resolve_left Γ.hE_atom.1).symm
  have hDa_ne_E : D_a ≠ Γ.E := fun h => hE_not_UC (h ▸ inf_le_right)
  have hDb_ne_E : D_b ≠ Γ.E := fun h => hE_not_UC (h ▸ inf_le_right)
  have ha'_ne_U : a' ≠ Γ.U := by
    intro h; have : Γ.U ≤ a ⊔ Γ.C := h ▸ inf_le_left
    exact ha_ne_U ((ha.le_iff.mp (le_of_le_of_eq (le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) this)
      (show (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) = a from by
        rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _]; exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on))).resolve_left Γ.hU.1).symm
  have hb'_ne_U : b' ≠ Γ.U := by
    intro h; have : Γ.U ≤ b ⊔ Γ.C := h ▸ inf_le_left
    exact hb_ne_U ((hb.le_iff.mp (le_of_le_of_eq (le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) this)
      (show (Γ.O ⊔ Γ.U) ⊓ (b ⊔ Γ.C) = b from by
        rw [show b ⊔ Γ.C = Γ.C ⊔ b from sup_comm _ _]; exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on))).resolve_left Γ.hU.1).symm
  have ha'_ne_C : a' ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ inf_le_right)
  have hb'_ne_C : b' ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ inf_le_right)
  have ha'_ne_E : a' ≠ Γ.E := by
    intro heq
    have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := heq ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      have h_eq : a ⊔ Γ.O = a ⊔ Γ.C :=
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right h_eq.symm |>.trans (sup_le ha_on le_sup_left))
    have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
        hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
    exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_aC CoordSystem.hE_le_OC)
        h_inf_C)).resolve_left Γ.hE_atom.1).symm
  have hb'_ne_E : b' ≠ Γ.E := by
    intro heq
    have hE_le_bC : Γ.E ≤ b ⊔ Γ.C := heq ▸ (inf_le_left : b' ≤ b ⊔ Γ.C)
    have hO_not_bC : ¬ Γ.O ≤ b ⊔ Γ.C := by
      intro hle
      have h_eq : b ⊔ Γ.O = b ⊔ Γ.C :=
        ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq (atom_covBy_join hb Γ.hO hb_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join hb Γ.hO hb_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right h_eq.symm |>.trans (sup_le hb_on le_sup_left))
    have h_inf_C : (b ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm b Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC hb Γ.hO (fun h => hb_ne_C h.symm)
        hOC.symm hb_ne_O (by rwa [sup_comm] at hO_not_bC)
    exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_bC CoordSystem.hE_le_OC)
        h_inf_C)).resolve_left Γ.hE_atom.1).symm
  have ha'Da_ne : a' ≠ D_a := by
    intro h; exact ha'_ne_U ((Γ.hU.le_iff.mp
      (hUC_inf_m ▸ (le_inf (h ▸ inf_le_right) inf_le_right : a' ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)))).resolve_left ha'_atom.1)
  have hb'Db_ne : b' ≠ D_b := by
    intro h; exact hb'_ne_U ((Γ.hU.le_iff.mp
      (hUC_inf_m ▸ (le_inf (h ▸ inf_le_right) inf_le_right : b' ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)))).resolve_left hb'_atom.1)
  have ha'Db_ne : a' ≠ D_b := by
    intro h; exact ha'_ne_U ((Γ.hU.le_iff.mp
      (hUC_inf_m ▸ (le_inf (h ▸ inf_le_right) inf_le_right : a' ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)))).resolve_left ha'_atom.1)
  have hDa_ne_b' : D_a ≠ b' := by
    intro h; exact hDa_ne_U ((Γ.hU.le_iff.mp
      (hUC_inf_m ▸ (le_inf inf_le_right (h ▸ inf_le_right) : D_a ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)))).resolve_left hDa_atom.1)
  -- ── join equalities (sorry for hard ones) ──
  have hCa'_eq : Γ.C ⊔ a' = a ⊔ Γ.C := by
    have h_lt : Γ.C < Γ.C ⊔ a' := by
      apply lt_of_le_of_ne le_sup_left; intro h
      exact ha'_ne_C (Γ.hC.le_iff.mp (le_of_le_of_eq le_sup_right h.symm) |>.resolve_left ha'_atom.1)
    have h_le : Γ.C ⊔ a' ≤ Γ.C ⊔ a :=
      sup_le le_sup_left ((inf_le_left : a' ≤ a ⊔ Γ.C).trans (sup_comm a Γ.C).le)
    rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _]
    exact ((atom_covBy_join Γ.hC ha (fun h => ha_ne_C h.symm)).eq_or_eq h_lt.le h_le).resolve_left
      (ne_of_gt h_lt)
  have hEDa_eq : Γ.E ⊔ D_a = a ⊔ Γ.E := by
    have h_lt : Γ.E < Γ.E ⊔ D_a := by
      apply lt_of_le_of_ne le_sup_left; intro h
      exact hDa_ne_E (Γ.hE_atom.le_iff.mp (le_of_le_of_eq le_sup_right h.symm) |>.resolve_left hDa_atom.1)
    have h_le : Γ.E ⊔ D_a ≤ Γ.E ⊔ a :=
      sup_le le_sup_left ((inf_le_left : D_a ≤ a ⊔ Γ.E).trans (sup_comm a Γ.E).le)
    rw [show a ⊔ Γ.E = Γ.E ⊔ a from sup_comm _ _]
    exact ((atom_covBy_join Γ.hE_atom ha (fun h => ha_ne_E h.symm)).eq_or_eq h_lt.le h_le).resolve_left
      (ne_of_gt h_lt)
  have hCDb_eq : Γ.C ⊔ D_b = Γ.U ⊔ Γ.C := by
    have h_lt : Γ.C < Γ.C ⊔ D_b := lt_of_le_of_ne le_sup_left
      (fun h => hDb_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq le_sup_right h.symm)).resolve_left hDb_atom.1))
    rw [sup_comm Γ.U Γ.C]
    exact ((atom_covBy_join Γ.hC Γ.hU hUC.symm).eq_or_eq h_lt.le
      (sup_le le_sup_left ((inf_le_right).trans (sup_comm Γ.U Γ.C).le))).resolve_left (ne_of_gt h_lt)
  have hEb'_eq : Γ.E ⊔ b' = Γ.U ⊔ Γ.V := by
    have hb'_cov : b' ⋖ Γ.U ⊔ Γ.V :=
      line_covers_its_atoms Γ.hU Γ.hV hUV hb'_atom inf_le_right
    have h_lt : b' < Γ.E ⊔ b' := by
      apply lt_of_le_of_ne le_sup_right; intro h
      have hE_le : Γ.E ≤ b' := by
        calc Γ.E ≤ Γ.E ⊔ b' := le_sup_left
          _ = b' := h.symm
      exact hb'_ne_E ((hb'_atom.le_iff.mp hE_le).resolve_left Γ.hE_atom.1).symm
    exact (hb'_cov.eq_or_eq h_lt.le (sup_le CoordSystem.hE_on_m inf_le_right)).resolve_left (ne_of_gt h_lt)
  have hUa_eq : Γ.U ⊔ a = Γ.O ⊔ Γ.U := by
    have h_lt : Γ.U < Γ.U ⊔ a := by
      apply lt_of_le_of_ne le_sup_left; intro h
      have ha_le : a ≤ Γ.U := by
        calc a ≤ Γ.U ⊔ a := le_sup_right
          _ = Γ.U := h.symm
      exact ha_ne_U ((Γ.hU.le_iff.mp ha_le).resolve_left ha.1)
    exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le
      (sup_le le_sup_left (ha_on.trans (sup_comm Γ.O Γ.U).le))).resolve_left
      (ne_of_gt h_lt) |>.trans (sup_comm _ _)
  -- ── a'⊔D_a ≠ b'⊔D_b ──
  have hDa_not_m : ¬ D_a ≤ Γ.U ⊔ Γ.V := by
    intro hle
    have h1 : D_a ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := le_inf inf_le_right hle
    rw [hUC_inf_m] at h1
    exact hDa_ne_U ((Γ.hU.le_iff.mp h1).resolve_left hDa_atom.1)
  have hDb_not_m : ¬ D_b ≤ Γ.U ⊔ Γ.V := by
    intro hle
    have h1 : D_b ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := le_inf inf_le_right hle
    rw [hUC_inf_m] at h1
    exact hDb_ne_U ((Γ.hU.le_iff.mp h1).resolve_left hDb_atom.1)
  have ha'Da_ne_b'Db : a' ⊔ D_a ≠ b' ⊔ D_b := by
    intro heq
    by_cases hab' : a' = b'
    · exfalso
      have ha'_le_aC : a' ≤ Γ.C ⊔ a := sup_comm a Γ.C ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
      have ha'_le_bC : a' ≤ Γ.C ⊔ b :=
        sup_comm b Γ.C ▸ (hab' ▸ (inf_le_left : b' ≤ b ⊔ Γ.C))
      have hb_not_Ca : ¬ b ≤ Γ.C ⊔ a := by
        intro hle
        have hab_le : a ⊔ b ≤ Γ.C ⊔ a := sup_le le_sup_right hle
        have h_cov_aCa : a ⋖ Γ.C ⊔ a := sup_comm Γ.C a ▸
          atom_covBy_join ha Γ.hC ha_ne_C
        have h_lt_ab : a < a ⊔ b := lt_of_le_of_ne le_sup_left
          (fun h => hab ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left hb.1).symm)
        have h_eq : a ⊔ b = Γ.C ⊔ a :=
          (h_cov_aCa.eq_or_eq h_lt_ab.le hab_le).resolve_left (ne_of_gt h_lt_ab)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_left h_eq.symm |>.trans (sup_le ha_on hb_on))
      have hCab : (Γ.C ⊔ a) ⊓ (Γ.C ⊔ b) = Γ.C :=
        modular_intersection Γ.hC ha hb (fun h => ha_ne_C h.symm)
          (fun h => hb_ne_C h.symm) hab hb_not_Ca
      have ha'_le_C : a' ≤ Γ.C := le_of_le_of_eq (le_inf ha'_le_aC ha'_le_bC) hCab
      have ha'_eq_C : a' = Γ.C := (Γ.hC.le_iff.mp ha'_le_C).resolve_left ha'_atom.1
      exact Γ.hC_not_m (ha'_eq_C ▸ inf_le_right)
    · exfalso
      have h_cov_UV : Γ.U ⋖ Γ.U ⊔ Γ.V := atom_covBy_join Γ.hU Γ.hV hUV
      have ha'b'_le : a' ⊔ b' ≤ Γ.U ⊔ Γ.V := sup_le inf_le_right inf_le_right
      have h_a'_lt_a'b' : a' < a' ⊔ b' := lt_of_le_of_ne le_sup_left
        (fun h => hab' ((ha'_atom.le_iff.mp
          (le_of_le_of_eq le_sup_right h.symm)).resolve_left hb'_atom.1).symm)
      have h_lt_m : a' < Γ.U ⊔ Γ.V := lt_of_lt_of_le h_a'_lt_a'b' ha'b'_le
      have hU_le_a'b' : Γ.U ≤ a' ⊔ b' := by
        by_contra hU_not
        have hU_inf : Γ.U ⊓ (a' ⊔ b') = ⊥ :=
          (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun h => hU_not (h ▸ inf_le_right))
        have ha'U_eq : Γ.U ⊔ a' = Γ.U ⊔ Γ.V := by
          have h_lt : Γ.U < Γ.U ⊔ a' := lt_of_le_of_ne le_sup_left
            (fun h => ha'_ne_U ((Γ.hU.le_iff.mp
              (le_of_le_of_eq le_sup_right h.symm)).resolve_left ha'_atom.1))
          exact (h_cov_UV.eq_or_eq h_lt.le
            (sup_le le_sup_left inf_le_right)).resolve_left (ne_of_gt h_lt)
        have hmod : (Γ.U ⊔ a') ⊓ (a' ⊔ b') = a' := by
          have h1 := sup_inf_assoc_of_le Γ.U (le_sup_left : a' ≤ a' ⊔ b')
          rw [hU_inf, sup_bot_eq, sup_comm a' Γ.U] at h1; exact h1
        rw [ha'U_eq] at hmod
        have hb'_le_a' : b' ≤ a' :=
          le_of_le_of_eq (le_inf inf_le_right (le_sup_right : b' ≤ a' ⊔ b')) hmod
        exact hab' ((ha'_atom.le_iff.mp hb'_le_a').resolve_left hb'_atom.1).symm
      have hU_lt_a'b' : Γ.U < a' ⊔ b' :=
        lt_of_le_of_ne hU_le_a'b' (fun h => by
          have ha'_le_U : a' ≤ Γ.U := le_of_le_of_eq le_sup_left h.symm
          have hb'_le_U : b' ≤ Γ.U := le_of_le_of_eq le_sup_right h.symm
          exact hab' ((Γ.hU.le_iff.mp ha'_le_U).resolve_left ha'_atom.1 |>.trans
            ((Γ.hU.le_iff.mp hb'_le_U).resolve_left hb'_atom.1).symm))
      have hm_eq : a' ⊔ b' = Γ.U ⊔ Γ.V :=
        (h_cov_UV.eq_or_eq hU_lt_a'b'.le ha'b'_le).resolve_left (ne_of_gt hU_lt_a'b')
      have hb'_le : b' ≤ a' ⊔ D_a := le_of_le_of_eq le_sup_left heq.symm
      have ha'b'_le_a'Da : a' ⊔ b' ≤ a' ⊔ D_a := sup_le le_sup_left hb'_le
      have hm_le : Γ.U ⊔ Γ.V ≤ a' ⊔ D_a := hm_eq ▸ ha'b'_le_a'Da
      have h_cov : a' ⋖ a' ⊔ D_a := atom_covBy_join ha'_atom hDa_atom ha'Da_ne
      have h_eq_m : a' ⊔ D_a = Γ.U ⊔ Γ.V :=
        ((h_cov.eq_or_eq h_lt_m.le hm_le).resolve_left (ne_of_gt h_lt_m)).symm
      exact hDa_not_m (le_of_le_of_eq le_sup_right h_eq_m)
  -- ── P₁ is an atom ──
  have hDa_not_aC_early : ¬ D_a ≤ a ⊔ Γ.C := by
    intro hle
    have h_le : D_a ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.U) :=
      le_inf ((sup_comm a Γ.C).symm ▸ hle) ((sup_comm Γ.U Γ.C).symm ▸ inf_le_right)
    have hU_not_aC : ¬ Γ.U ≤ a ⊔ Γ.C := by
      intro hle2
      have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hle2
      rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
      exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
    rw [modular_intersection Γ.hC ha Γ.hU (fun h => ha_ne_C h.symm) hUC.symm
      ha_ne_U (by rwa [sup_comm] at hU_not_aC)] at h_le
    exact hDa_ne_C ((Γ.hC.le_iff.mp h_le).resolve_left hDa_atom.1)
  -- a not on a'⊔D_a (for covering)
  have ha_not_a'Da : ¬ a ≤ a' ⊔ D_a := by
    intro h
    have h_le : a ⊔ a' ≤ a' ⊔ D_a := sup_le h le_sup_left
    have h_le' : a' ⊔ a ≤ a' ⊔ D_a := sup_comm a a' ▸ h_le
    -- a' ⋖ a'⊔D_a, a' < a'⊔a ≤ a'⊔D_a.
    -- a ≠ a' (if a = a', then a ≤ U⊔V, forcing a = U, contradiction)
    have h12a : a ≠ a' := by
      intro heq; exact ha_ne_U (Γ.atom_on_both_eq_U ha ha_on (heq ▸ inf_le_right))
    rcases (atom_covBy_join ha'_atom hDa_atom ha'Da_ne).eq_or_eq
      (atom_covBy_join ha'_atom ha h12a.symm).lt.le h_le' with h_abs | h_abs
    · exact h12a ((ha'_atom.le_iff.mp (le_of_le_of_eq (le_sup_right : a ≤ a' ⊔ a) h_abs)).resolve_left ha.1)
    · -- a'⊔a = a'⊔D_a, so D_a ≤ a⊔C
      have hDa_le : D_a ≤ a ⊔ Γ.C := calc
        D_a ≤ a' ⊔ D_a := le_sup_right
        _ = a' ⊔ a := h_abs.symm
        _ ≤ a ⊔ Γ.C := sup_le (inf_le_left : a' ≤ a ⊔ Γ.C) le_sup_left
      exact hDa_not_aC_early hDa_le
  have ha_inf_a'Da : a ⊓ (a' ⊔ D_a) = ⊥ :=
    (ha.le_iff.mp inf_le_left).resolve_right
      (fun h => ha_not_a'Da ((le_of_eq h.symm).trans inf_le_right))
  have hCDa_eq : Γ.C ⊔ D_a = Γ.U ⊔ Γ.C := by
    have h_lt : Γ.C < Γ.C ⊔ D_a := by
      apply lt_of_le_of_ne le_sup_left
      intro heq; exact hDa_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq le_sup_right heq.symm)).resolve_left hDa_atom.1)
    rw [sup_comm Γ.U Γ.C]
    exact ((atom_covBy_join Γ.hC Γ.hU hUC.symm).eq_or_eq h_lt.le
      (sup_le le_sup_left ((inf_le_right).trans (le_of_eq (sup_comm Γ.U Γ.C))))).resolve_left (ne_of_gt h_lt)
  have haa'_eq : a ⊔ a' = a ⊔ Γ.C := by
    have h12a : a ≠ a' := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on (h ▸ inf_le_right))
    have h_lt : a < a ⊔ a' := lt_of_le_of_ne le_sup_left
      (fun h => h12a ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left ha'_atom.1).symm)
    exact ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have hπA_orig : a ⊔ a' ⊔ D_a = π := by
    rw [haa'_eq, sup_assoc, hCDa_eq, show a ⊔ (Γ.U ⊔ Γ.C) = (a ⊔ Γ.U) ⊔ Γ.C from
      (sup_assoc _ _ _).symm, show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _, hUa_eq]
    have h_lt : Γ.O ⊔ Γ.C < (Γ.O ⊔ Γ.U) ⊔ Γ.C := by
      apply lt_of_le_of_ne (sup_le (le_sup_left.trans le_sup_left) le_sup_right); intro h
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le (h.symm ▸ le_sup_left)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt)
  have ha'Da_covBy_π : a' ⊔ D_a ⋖ π := by
    have h_cov := covBy_sup_of_inf_covBy_left (ha_inf_a'Da ▸ ha.bot_covBy)
    rwa [show a ⊔ (a' ⊔ D_a) = a ⊔ a' ⊔ D_a from (sup_assoc _ _ _).symm,
         hπA_orig] at h_cov
  have hU_le_π' : Γ.U ≤ π := le_sup_right.trans le_sup_left
  have ha'Da_le_π : a' ⊔ D_a ≤ π := sup_le
    (inf_le_right.trans (sup_le hU_le_π' le_sup_right))
    (inf_le_right.trans (sup_le hU_le_π' Γ.hC_plane))
  have hb'Db_le_π : b' ⊔ D_b ≤ π := sup_le
    (inf_le_right.trans (sup_le hU_le_π' le_sup_right))
    (inf_le_right.trans (sup_le hU_le_π' Γ.hC_plane))
  have hb'Db_not_le_a'Da : ¬ b' ⊔ D_b ≤ a' ⊔ D_a := by
    intro h
    rcases lt_or_eq_of_le h with h_lt | h_eq
    · -- b'⊔D_b is an atom of a'⊔D_a. But b' < b'⊔D_b, contradiction.
      have hbd_atom := line_height_two ha'_atom hDa_atom ha'Da_ne
        (atom_covBy_join hb'_atom hDb_atom hb'Db_ne).lt.bot_lt h_lt
      have hb'_eq : b' = b' ⊔ D_b := (hbd_atom.le_iff.mp le_sup_left).resolve_left hb'_atom.1
      have hDb_le_b' : D_b ≤ b' := le_of_le_of_eq le_sup_right hb'_eq.symm
      exact hb'Db_ne ((hb'_atom.le_iff.mp hDb_le_b').resolve_left hDb_atom.1).symm
    · exact ha'Da_ne_b'Db h_eq.symm
  have hP₁_pos : ⊥ < P₁ := by
    rw [bot_lt_iff_ne_bot]; intro hP₁_bot
    exact lines_meet_if_coplanar ha'Da_covBy_π hb'Db_le_π hb'Db_not_le_a'Da
      hb'_atom (atom_covBy_join hb'_atom hDb_atom hb'Db_ne).lt hP₁_bot
  have hP₁_lt : P₁ < a' ⊔ D_a := by
    apply lt_of_le_of_ne inf_le_left; intro h
    have h2 : a' ⊔ D_a ≤ b' ⊔ D_b := h ▸ inf_le_right
    rcases lt_or_eq_of_le h2 with h_lt | h_eq
    · have had_atom := line_height_two hb'_atom hDb_atom hb'Db_ne
        (atom_covBy_join ha'_atom hDa_atom ha'Da_ne).lt.bot_lt h_lt
      have ha'_eq : a' = a' ⊔ D_a := (had_atom.le_iff.mp le_sup_left).resolve_left ha'_atom.1
      have hDa_le_a' : D_a ≤ a' := le_of_le_of_eq le_sup_right ha'_eq.symm
      exact ha'Da_ne ((ha'_atom.le_iff.mp hDa_le_a').resolve_left hDa_atom.1).symm
    · exact ha'Da_ne_b'Db h_eq
  have hP₁_atom : IsAtom P₁ := line_height_two ha'_atom hDa_atom ha'Da_ne hP₁_pos hP₁_lt
  -- ── perspective conditions ──
  have hE_on : Γ.E ≤ P₁ ⊔ Γ.C := by
    -- P₁⊔C = O⊔C (since P₁ ≤ O⊔C, P₁ ≠ C, covering). E ≤ O⊔C.
    have hP₁_ne_C : P₁ ≠ Γ.C := by
      intro h
      -- P₁ = C, so C ≤ a'⊔D_a. Then C⊔D_a ≤ a'⊔D_a.
      -- hCDa_eq: C⊔D_a = U⊔C. So U⊔C ≤ a'⊔D_a (both lines, must be equal).
      -- Then U ≤ a'⊔D_a. a' ≤ (U⊔V)⊓(U⊔C) = U. Contradiction.
      have hC_le : Γ.C ≤ a' ⊔ D_a := h ▸ inf_le_left
      have hUC_le : Γ.U ⊔ Γ.C ≤ a' ⊔ D_a := by
        calc Γ.U ⊔ Γ.C = Γ.C ⊔ D_a := hCDa_eq.symm
          _ ≤ a' ⊔ D_a := sup_le hC_le le_sup_right
      rcases lt_or_eq_of_le hUC_le with h_lt | h_eq
      · have hUC_atom := line_height_two ha'_atom hDa_atom ha'Da_ne
            (atom_covBy_join Γ.hU Γ.hC hUC).lt.bot_lt h_lt
        -- U⊔C is an atom but U ≤ U⊔C and U ≠ ⊥ gives U = U⊔C, so C ≤ U, C = U. Contradiction.
        have hU_eq_UC : Γ.U = Γ.U ⊔ Γ.C := (hUC_atom.le_iff.mp le_sup_left).resolve_left Γ.hU.1
        have hC_le_U : Γ.C ≤ Γ.U := le_of_le_of_eq le_sup_right hU_eq_UC.symm
        exact hUC ((Γ.hU.le_iff.mp hC_le_U).resolve_left Γ.hC.1).symm
      · exact ha'_ne_U ((Γ.hU.le_iff.mp (le_of_le_of_eq
          (le_inf (inf_le_right : a' ≤ Γ.U ⊔ Γ.V) (le_of_le_of_eq le_sup_left h_eq.symm : a' ≤ Γ.U ⊔ Γ.C))
          (by rw [inf_comm]; exact hUC_inf_m))).resolve_left ha'_atom.1)
    have h_lt : Γ.C < P₁ ⊔ Γ.C := by
      apply lt_of_le_of_ne le_sup_right; intro h
      exact hP₁_ne_C (Γ.hC.le_iff.mp (le_of_le_of_eq le_sup_left h.symm) |>.resolve_left hP₁_atom.1)
    have h_le : P₁ ⊔ Γ.C ≤ Γ.O ⊔ Γ.C := sup_le hP₁ le_sup_right
    have hP₁C_eq : P₁ ⊔ Γ.C = Γ.O ⊔ Γ.C := by
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact ((atom_covBy_join Γ.hC Γ.hO hOC.symm).eq_or_eq h_lt.le
        (sup_comm Γ.C Γ.O ▸ h_le)).resolve_left (ne_of_gt h_lt)
    exact hP₁C_eq ▸ CoordSystem.hE_le_OC
  have hDa_on : D_a ≤ P₁ ⊔ a' := by
    -- P₁⊔a' = a'⊔D_a (P₁ ≤ a'⊔D_a, covering). So D_a ≤ P₁⊔a'.
    have hP₁_ne_a' : P₁ ≠ a' := by
      intro h
      -- a' ≤ O⊔C (from hP₁) and a' ≤ a⊔C (from inf_le_left). Their meet is C. So a' ≤ C.
      have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
        intro hle
        have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
          ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
            (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
      have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
        exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
          hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
      have ha'_le_OC : a' ≤ Γ.O ⊔ Γ.C := h ▸ hP₁
      exact ha'_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf inf_le_left ha'_le_OC) h_inf_C)).resolve_left ha'_atom.1)
    have h_lt : a' < P₁ ⊔ a' := by
      apply lt_of_le_of_ne le_sup_right; intro h
      exact hP₁_ne_a' (ha'_atom.le_iff.mp (le_of_le_of_eq le_sup_left h.symm) |>.resolve_left hP₁_atom.1)
    have h_le : P₁ ⊔ a' ≤ a' ⊔ D_a := sup_le inf_le_left le_sup_left
    have h_eq : P₁ ⊔ a' = a' ⊔ D_a :=
      ((atom_covBy_join ha'_atom hDa_atom ha'Da_ne).eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
    exact h_eq ▸ le_sup_right
  have hb'_on : b' ≤ P₁ ⊔ D_b := by
    -- P₁⊔D_b = b'⊔D_b (P₁ ≤ b'⊔D_b, covering). So b' ≤ P₁⊔D_b.
    have hP₁_ne_Db : P₁ ≠ D_b := by
      intro h
      -- D_b ≤ O⊔C and D_b ≤ U⊔C. (C⊔U)⊓(C⊔O) = C. So D_b ≤ C. Contradiction.
      have hUC_inf_OC_local : (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm Γ.U Γ.C, sup_comm Γ.O Γ.C]
        exact modular_intersection Γ.hC Γ.hU Γ.hO hUC.symm hOC.symm Γ.hOU.symm
          (by rw [sup_comm]; exact CoordSystem.hO_not_UC)
      have hDb_le_OC : D_b ≤ Γ.O ⊔ Γ.C := h ▸ hP₁
      exact hDb_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq
        (le_inf inf_le_right hDb_le_OC) hUC_inf_OC_local)).resolve_left hDb_atom.1)
    have h_lt : D_b < P₁ ⊔ D_b := by
      apply lt_of_le_of_ne le_sup_right; intro h
      exact hP₁_ne_Db (hDb_atom.le_iff.mp (le_of_le_of_eq le_sup_left h.symm) |>.resolve_left hP₁_atom.1)
    have h_le : P₁ ⊔ D_b ≤ D_b ⊔ b' := sup_le ((inf_le_right).trans (sup_comm b' D_b).le) le_sup_left
    have h_cov : D_b ⋖ D_b ⊔ b' := atom_covBy_join hDb_atom hb'_atom hb'Db_ne.symm
    have h_eq : P₁ ⊔ D_b = D_b ⊔ b' :=
      (h_cov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
    calc b' ≤ D_b ⊔ b' := le_sup_right
      _ = P₁ ⊔ D_b := h_eq.symm
  -- ── all in π ──
  have hU_le_π : Γ.U ≤ π := le_sup_right.trans le_sup_left
  have hm_le_π : Γ.U ⊔ Γ.V ≤ π := sup_le hU_le_π le_sup_right
  have hP₁_le_π : P₁ ≤ π := hP₁.trans (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane)
  have hC_le_π : Γ.C ≤ π := Γ.hC_plane
  have ha'_le_π : a' ≤ π := inf_le_right.trans hm_le_π
  have hDa_le_π : D_a ≤ π := inf_le_right.trans (sup_le hU_le_π hC_le_π)
  have hDb_le_π : D_b ≤ π := inf_le_right.trans (sup_le hU_le_π hC_le_π)
  have hE_le_π : Γ.E ≤ π := CoordSystem.hE_on_m.trans hm_le_π
  have hb'_le_π : b' ≤ π := inf_le_right.trans hm_le_π
  -- ── helpers for distinctness ──
  have hO_not_UC : ¬ Γ.O ≤ Γ.U ⊔ Γ.C := by
    intro hle
    have h_le : Γ.O ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) := le_inf le_sup_left hle
    rw [hl_inf_UC] at h_le
    exact Γ.hOU ((Γ.hU.le_iff.mp h_le).resolve_left Γ.hO.1)
  have hUC_inf_OC : (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
    rw [sup_comm Γ.U Γ.C, sup_comm Γ.O Γ.C]
    exact modular_intersection Γ.hC Γ.hU Γ.hO hUC.symm hOC.symm Γ.hOU.symm
      (by rwa [sup_comm] at hO_not_UC)
  have hDa_not_OC : ¬ D_a ≤ Γ.O ⊔ Γ.C := by
    intro hle; exact hDa_ne_C ((Γ.hC.le_iff.mp
      (hUC_inf_OC ▸ le_inf inf_le_right hle)).resolve_left hDa_atom.1)
  have hDb_not_OC : ¬ D_b ≤ Γ.O ⊔ Γ.C := by
    intro hle; exact hDb_ne_C ((Γ.hC.le_iff.mp
      (hUC_inf_OC ▸ le_inf inf_le_right hle)).resolve_left hDb_atom.1)
  have ha'_not_OC : ¬ a' ≤ Γ.O ⊔ Γ.C := by
    intro hle
    have h := le_inf (inf_le_right : a' ≤ Γ.U ⊔ Γ.V) hle
    -- a' ≤ (U⊔V) ⊓ (O⊔C). Need: (U⊔V)⊓(O⊔C) = ?
    -- O⊔C ≤ π. U⊔V ≤ π. Their meet in π: O is not on U⊔V (otherwise O on m, but O⊔U = l ≠ m).
    -- Actually: if a' ≤ O⊔C and a' = (a���C) ⊓ (U⊔V), then a' ≤ (a⊔C) ⊓ (O⊔C).
    -- (a⊔C) ⊓ (O⊔C) = C (if O not on a⊔C, modular_intersection with C, a, O).
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle2
      have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
          (sup_le le_sup_left hle2)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
    have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
        hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
    exact ha'_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf inf_le_left hle) h_inf_C)).resolve_left ha'_atom.1)
  have hb'_not_OC : ¬ b' ≤ Γ.O ⊔ Γ.C := by
    intro hle
    have hO_not_bC : ¬ Γ.O ≤ b ⊔ Γ.C := by
      intro hle2
      have heq : b ⊔ Γ.O = b ⊔ Γ.C :=
        ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq (atom_covBy_join hb Γ.hO hb_ne_O).lt.le
          (sup_le le_sup_left hle2)).resolve_left (ne_of_gt (atom_covBy_join hb Γ.hO hb_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le hb_on le_sup_left))
    have h_inf_C : (b ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm b Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC hb Γ.hO (fun h => hb_ne_C h.symm)
        hOC.symm hb_ne_O (by rwa [sup_comm] at hO_not_bC)
    exact hb'_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf inf_le_left hle) h_inf_C)).resolve_left hb'_atom.1)
  have hDa_not_aC : ¬ D_a ≤ a ⊔ Γ.C := by
    intro hle
    have h_le : D_a ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.U) :=
      le_inf ((sup_comm a Γ.C).symm ▸ hle) ((sup_comm Γ.U Γ.C).symm ▸ inf_le_right)
    have hU_not_aC : ¬ Γ.U ≤ a ⊔ Γ.C := by
      intro hle2
      have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hle2
      rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
      exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
    rw [modular_intersection Γ.hC ha Γ.hU (fun h => ha_ne_C h.symm) hUC.symm
      ha_ne_U (by rwa [sup_comm] at hU_not_aC)] at h_le
    exact hDa_ne_C ((Γ.hC.le_iff.mp h_le).resolve_left hDa_atom.1)
  -- ── vertex/side distinctness ──
  have hs12 : Γ.C ⊔ a' ≠ Γ.E ⊔ D_a := by
    rw [hCa'_eq, hEDa_eq]; intro h
    -- a⊔C = a⊔E: so C ≤ a⊔E and E ≤ a⊔C. (a⊔C) ⊓ (O⊔C) = C. E ≤ a⊔C and E ≤ O⊔C. So E ≤ C. But E ≠ C.
    have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := le_of_le_of_eq le_sup_right h.symm
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
    have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
        hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
    exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_aC CoordSystem.hE_le_OC) h_inf_C)).resolve_left
      Γ.hE_atom.1).symm
  have hs13 : Γ.C ⊔ D_b ≠ Γ.E ⊔ b' := by
    rw [hCDb_eq, hEb'_eq]; exact fun h => Γ.hC_not_m (h ▸ (le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C))
  have hab' : a' ≠ b' := by
    intro h
    have h_le_C : a' ≤ (a ⊔ Γ.C) ⊓ (b ⊔ Γ.C) :=
      le_inf inf_le_left ((le_of_eq h).trans inf_le_left)
    rw [CoordSystem.lines_through_C_meet Γ ha hb hab ha_on hb_on] at h_le_C
    exact Γ.hC_not_m (((Γ.hC.le_iff.mp h_le_C).resolve_left ha'_atom.1).symm ▸ inf_le_right)
  have hs23 : a' ⊔ D_b ≠ D_a ⊔ b' := by
    intro heq
    -- a' and b' are both ≤ a'⊔D_b (a' trivially, b' from heq)
    have hb'_le : b' ≤ a' ⊔ D_b := le_of_le_of_eq le_sup_right heq.symm
    -- a'⊔b' ≤ a'⊔D_b
    have ha'b'_le : a' ⊔ b' ≤ a' ⊔ D_b := sup_le le_sup_left hb'_le
    -- a'⊔b' is a line (a' ≠ b'), a'⊔D_b is a line. Rank argument:
    rcases lt_or_eq_of_le ha'b'_le with h_lt | h_eq
    · -- a'⊔b' < a'⊔D_b: a'⊔b' is an atom. But a' < a'⊔b'. Contradiction.
      have h_atom := line_height_two ha'_atom hDb_atom ha'Db_ne
        (atom_covBy_join ha'_atom hb'_atom hab').lt.bot_lt h_lt
      have ha'_eq : a' = a' ⊔ b' := (h_atom.le_iff.mp le_sup_left).resolve_left ha'_atom.1
      have hb'_le_a' : b' ≤ a' := le_of_le_of_eq le_sup_right ha'_eq.symm
      exact hab' ((ha'_atom.le_iff.mp hb'_le_a').resolve_left hb'_atom.1).symm
    · -- a'⊔b' = a'⊔D_b: then D_b ≤ a'⊔b' ≤ U⊔V. Contradiction.
      have hDb_le_m : D_b ≤ Γ.U ⊔ Γ.V :=
        le_of_le_of_eq le_sup_right h_eq.symm |>.trans (sup_le inf_le_right inf_le_right)
      exact hDb_not_m hDb_le_m
  have hP₁_ne_C : P₁ ≠ Γ.C := by
    intro h
    have hC_le : Γ.C ≤ a' ⊔ D_a := h ▸ inf_le_left
    have hUC_le : Γ.U ⊔ Γ.C ≤ a' ⊔ D_a := by
      calc Γ.U ⊔ Γ.C = Γ.C ⊔ D_a := hCDa_eq.symm
        _ ≤ a' ⊔ D_a := sup_le hC_le le_sup_right
    rcases lt_or_eq_of_le hUC_le with h_lt | h_eq
    · have hUC_atom := line_height_two ha'_atom hDa_atom ha'Da_ne
        (atom_covBy_join Γ.hU Γ.hC hUC).lt.bot_lt h_lt
      have hU_eq_UC : Γ.U = Γ.U ⊔ Γ.C := (hUC_atom.le_iff.mp le_sup_left).resolve_left Γ.hU.1
      have hC_le_U : Γ.C ≤ Γ.U := le_of_le_of_eq le_sup_right hU_eq_UC.symm
      exact hUC ((Γ.hU.le_iff.mp hC_le_U).resolve_left Γ.hC.1).symm
    · exact ha'_ne_U ((Γ.hU.le_iff.mp (le_of_le_of_eq
        (le_inf (inf_le_right : a' ≤ Γ.U ⊔ Γ.V) (le_of_le_of_eq le_sup_left h_eq.symm : a' ≤ Γ.U ⊔ Γ.C))
        (by rw [inf_comm]; exact hUC_inf_m))).resolve_left ha'_atom.1)
  have hP₁_ne_a' : P₁ ≠ a' := fun h => ha'_not_OC (h ▸ hP₁)
  have hP₁_ne_Db : P₁ ≠ D_b := fun h => hDb_not_OC (h ▸ hP₁)
  have hP₁_ne_E : P₁ ≠ Γ.E := by
    intro h
    -- E ≤ a'⊔D_a. Then E⊔D_a ≤ a'⊔D_a. hEDa_eq: E⊔D_a = a⊔E. So a⊔E ≤ a'⊔D_a.
    -- Both rank 2. So a⊔E = a'⊔D_a. Then a ≤ a'⊔D_a. But ha_not_a'Da. Contradiction.
    have hE_le : Γ.E ≤ a' ⊔ D_a := h ▸ inf_le_left
    have haE_le : a ⊔ Γ.E ≤ a' ⊔ D_a := by
      calc a ⊔ Γ.E = Γ.E ⊔ D_a := hEDa_eq.symm
        _ ≤ a' ⊔ D_a := sup_le hE_le le_sup_right
    exact ha_not_a'Da (le_trans le_sup_left haE_le)
  have hP₁_ne_Da : P₁ ≠ D_a := fun h => hDa_not_OC (h ▸ hP₁)
  have hP₁_ne_b' : P₁ ≠ b' := fun h => hb'_not_OC (h ▸ hP₁)
  have hDb_ne_b' : D_b ≠ b' := by
    intro h; exact hDb_ne_U ((Γ.hU.le_iff.mp
      (hUC_inf_m ▸ (le_inf inf_le_right (h ▸ inf_le_right) : D_b ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)))).resolve_left hDb_atom.1)
  -- ── triangle planes = π ──
  have hπA : Γ.C ⊔ a' ⊔ D_b = π := by
    rw [hCa'_eq, sup_assoc, hCDb_eq,
        show a ⊔ (Γ.U ⊔ Γ.C) = (a ⊔ Γ.U) ⊔ Γ.C from (sup_assoc _ _ _).symm,
        show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _, hUa_eq]
    have h_lt : Γ.O ⊔ Γ.C < (Γ.O ⊔ Γ.U) ⊔ Γ.C := by
      apply lt_of_le_of_ne (sup_le (le_sup_left.trans le_sup_left) le_sup_right); intro h
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le (h.symm ▸ le_sup_left)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt)
  have hπB : Γ.E ⊔ D_a ⊔ b' = π := by
    rw [hEDa_eq, sup_assoc, hEb'_eq]
    -- a ⊔ (U ⊔ V) = π since (U⊔a)⊔V = (O⊔U)⊔V = π
    rw [show a ⊔ (Γ.U ⊔ Γ.V) = (a ⊔ Γ.U) ⊔ Γ.V from (sup_assoc _ _ _).symm,
        show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _, hUa_eq]
  -- ── sides covered by π ──
  have hcov12 : Γ.C ⊔ a' ⋖ π := by
    -- D_b not on a⊔C = C⊔a' (hCa'_eq)
    have hDb_not_aC : ¬ D_b ≤ a ⊔ Γ.C := by
      intro hle
      have h_le : D_b ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.U) :=
        le_inf ((sup_comm a Γ.C).symm ▸ hle) ((sup_comm Γ.U Γ.C).symm ▸ inf_le_right)
      have hU_not_aC : ¬ Γ.U ≤ a ⊔ Γ.C := by
        intro hle2
        have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hle2
        rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
            inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
        exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
      rw [modular_intersection Γ.hC ha Γ.hU (fun h => ha_ne_C h.symm) hUC.symm
        ha_ne_U (by rwa [sup_comm] at hU_not_aC)] at h_le
      exact hDb_ne_C ((Γ.hC.le_iff.mp h_le).resolve_left hDb_atom.1)
    rw [hCa'_eq]
    have hDb_inf : D_b ⊓ (a ⊔ Γ.C) = ⊥ :=
      (hDb_atom.le_iff.mp inf_le_left).resolve_right
        (fun h => hDb_not_aC ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (hDb_inf ▸ hDb_atom.bot_covBy)
    rwa [show D_b ⊔ (a ⊔ Γ.C) = Γ.C ⊔ a' ⊔ D_b from by
           rw [sup_comm D_b, ← hCa'_eq, sup_comm (Γ.C ⊔ a')],
         hπA] at h_cov
  have hcov13 : Γ.C ⊔ D_b ⋖ π := by
    rw [hCDb_eq]
    have hE_inf : Γ.E ⊓ (Γ.U ⊔ Γ.C) = ⊥ :=
      (Γ.hE_atom.le_iff.mp inf_le_left).resolve_right
        (fun h => hE_not_UC ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (hE_inf ▸ Γ.hE_atom.bot_covBy)
    rwa [show Γ.E ⊔ (Γ.U ⊔ Γ.C) = (Γ.U ⊔ Γ.C) ⊔ Γ.E from sup_comm _ _,
         hUCE_eq_π] at h_cov
  have hcov23 : a' ⊔ D_b ⋖ π := by
    have hC_not_a'Db : ¬ Γ.C ≤ a' ⊔ D_b := by
      intro hle
      have hUC_le : Γ.U ⊔ Γ.C ≤ a' ⊔ D_b := by
        calc Γ.U ⊔ Γ.C = Γ.C ⊔ D_b := hCDb_eq.symm
          _ ≤ a' ⊔ D_b := sup_le hle le_sup_right
      rcases lt_or_eq_of_le hUC_le with h_lt | h_eq
      · have hUC_atom := line_height_two ha'_atom hDb_atom ha'Db_ne
          (atom_covBy_join Γ.hU Γ.hC hUC).lt.bot_lt h_lt
        have hU_eq_UC : Γ.U = Γ.U ⊔ Γ.C := (hUC_atom.le_iff.mp le_sup_left).resolve_left Γ.hU.1
        have hC_le_U : Γ.C ≤ Γ.U := le_of_le_of_eq le_sup_right hU_eq_UC.symm
        exact hUC ((Γ.hU.le_iff.mp hC_le_U).resolve_left Γ.hC.1).symm
      · exact ha'_ne_U ((Γ.hU.le_iff.mp (le_of_le_of_eq
          (le_inf (inf_le_right : a' ≤ Γ.U ⊔ Γ.V) (le_of_le_of_eq le_sup_left h_eq.symm))
          (by rw [inf_comm]; exact hUC_inf_m))).resolve_left ha'_atom.1)
    have hC_inf : Γ.C ⊓ (a' ⊔ D_b) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right
        (fun h => hC_not_a'Db ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (hC_inf ▸ Γ.hC.bot_covBy)
    rwa [show Γ.C ⊔ (a' ⊔ D_b) = Γ.C ⊔ a' ⊔ D_b from (sup_assoc _ _ _).symm,
         hπA] at h_cov
  -- ── apply desargues_planar ──
  obtain ⟨axis, h_axis_le, h_axis_ne, h₁, h₂, h₃⟩ := desargues_planar
    hP₁_atom Γ.hC ha'_atom hDb_atom Γ.hE_atom hDa_atom hb'_atom
    hP₁_le_π hC_le_π ha'_le_π hDb_le_π hE_le_π hDa_le_π hb'_le_π
    hE_on hDa_on hb'_on
    ha'_ne_C.symm hDb_ne_C.symm ha'Db_ne
    hDa_ne_E.symm hb'_ne_E.symm hDa_ne_b'
    hs12 hs13 hs23
    hπA hπB
    hP₁_ne_C hP₁_ne_a' hP₁_ne_Db
    hP₁_ne_E hP₁_ne_Da hP₁_ne_b'
    hCE ha'Da_ne hDb_ne_b'
    R hR hR_not h_irred
    hcov12 hcov13 hcov23
  -- ── compute side intersections and conclude ──
  -- Side 1: (C⊔a') ⊓ (E⊔D_a) = a  (after rw with hCa'_eq, hEDa_eq, modular_intersection)
  -- Side 2: (C⊔D_b) ⊓ (E⊔b') = U  (after rw with hCDb_eq, hEb'_eq, hUC_inf_m)
  -- Side 3: (a'⊔D_b) ⊓ (D_a⊔b') = W  (target)
  -- Then a ⊔ U = O⊔U = l, and W ≤ l by collinear_of_common_bound.
  -- Side 1: (C⊔a')⊓(E⊔D_a) rewrites to (a⊔C)⊓(a⊔E) = a via hCa'_eq, hEDa_eq, modular_intersection.
  have h₁' : a ≤ axis := by
    have hE_not_aC : ¬ Γ.E ≤ a ⊔ Γ.C := by
      intro hle
      have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
        intro hle2
        have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
          ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
            (sup_le le_sup_left hle2)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
      have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
        exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
          hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
      exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hle CoordSystem.hE_le_OC) h_inf_C)).resolve_left
        Γ.hE_atom.1).symm
    have : (a ⊔ Γ.C) ⊓ (a ⊔ Γ.E) = a := modular_intersection ha Γ.hC Γ.hE_atom ha_ne_C ha_ne_E hCE hE_not_aC
    calc a = (a ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := this.symm
      _ = (Γ.C ⊔ a') ⊓ (Γ.E ⊔ D_a) := by rw [hCa'_eq, hEDa_eq]
      _ ≤ axis := h₁
  -- Side 2: (C⊔D_b)⊓(E⊔b') = (U⊔C)⊓(U⊔V) = U
  have h₂' : Γ.U ≤ axis := by
    calc Γ.U = (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := hUC_inf_m.symm
      _ = (Γ.C ⊔ D_b) ⊓ (Γ.E ⊔ b') := by rw [hCDb_eq, hEb'_eq]
      _ ≤ axis := h₂
  -- Side 3: h₃ says (a'⊔D_b)⊓(D_a⊔b') ≤ axis. Goal: (a'⊔D_b)⊓(b'⊔D_a) ≤ O⊔U.
  have h₃' : (a' ⊔ D_b) ⊓ (b' ⊔ D_a) ≤ axis := by
    rw [show b' ⊔ D_a = D_a ⊔ b' from sup_comm _ _]; exact h₃
  -- Conclude: a ⊔ U = O⊔U (from hUa_eq), and collinear_of_common_bound gives W ≤ a⊔U.
  have hau_covBy : a ⊔ Γ.U ⋖ π := by
    rw [sup_comm a Γ.U, hUa_eq]
    have h_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    exact show Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V from by
      have h_cov := covBy_sup_of_inf_covBy_left (h_disj ▸ Γ.hV.bot_covBy)
      rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from sup_comm _ _] at h_cov
  exact (collinear_of_common_bound (s₁ := a) (s₂ := Γ.U) hau_covBy h_axis_le h_axis_ne h₁' h₂' h₃').trans
    (show a ⊔ Γ.U = Γ.O ⊔ Γ.U from by rw [sup_comm a Γ.U]; exact hUa_eq).le


/-- **Commutativity of von Staudt addition.**

    The proof chains two applications of Desargues' theorem:

    1. Triangles (a, a', D_a) and (b, b', D_b), perspective from U.
       Side intersections are C and E (computed by lines_through_C/E_meet).
       Desargues + collinearity → P₁ = (a'⊔D_a) ⊓ (b'⊔D_b) ∈ O⊔C.

    2. Triangles (C, a', D_b) and (E, D_a, b'), perspective from P₁.
       Side intersections are a and U.
       Desargues + collinearity → W = (a'⊔D_b) ⊓ (b'⊔D_a) ∈ a⊔U = l.

    W is an atom on both addition lines and on l, so W = a+b = b+a. -/
theorem coord_add_comm (Γ : CoordSystem L)
    (a b : L) (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : a ≠ b)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ a b = coord_add Γ b a := by
  -- Name the key objects
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set a' := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set b' := (b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set D_a := (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  set D_b := (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  set W := (a' ⊔ D_b) ⊓ (b' ⊔ D_a)
  -- Atom properties
  have h_in_π : ∀ x, x ≤ Γ.O ⊔ Γ.U → x ≤ (Γ.U ⊔ Γ.V) ⊔ Γ.C :=
    fun x hx => hx.trans (le_sup_left.trans (le_of_eq Γ.m_sup_C_eq_π.symm))
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have ha'_atom : IsAtom a' :=
    perspect_atom Γ.hC ha (fun h => Γ.hC_not_l (h ▸ ha_on)) Γ.hU Γ.hV hUV Γ.hC_not_m
      (sup_le (h_in_π a ha_on) le_sup_right)
  have hb'_atom : IsAtom b' :=
    perspect_atom Γ.hC hb (fun h => Γ.hC_not_l (h ▸ hb_on)) Γ.hU Γ.hV hUV Γ.hC_not_m
      (sup_le (h_in_π b hb_on) le_sup_right)
  have ha_ne_E : a ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ ha_on)
  have hb_ne_E : b ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hb_on)
  -- (U⊔C)⊓m = U (needed for return center facts)
  have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
    have hCV : Γ.C ≠ Γ.V := fun h => Γ.hC_not_m (h ▸ le_sup_right)
    have hV_not_UC : ¬ Γ.V ≤ Γ.U ⊔ Γ.C := by
      intro hle
      exact Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC
        (fun h => Γ.hC_not_l (h ▸ le_sup_right))).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV hUV).lt.le (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV hUV).lt) ▸ le_sup_right)
    exact modular_intersection Γ.hU Γ.hC Γ.hV
      (fun h => Γ.hC_not_l (h ▸ le_sup_right)) hUV hCV hV_not_UC
  -- E is not on U⊔C
  have hE_not_UC : ¬ Γ.E ≤ Γ.U ⊔ Γ.C := by
    intro h
    exact CoordSystem.hEU (Γ.hU.le_iff.mp
      (hUC_inf_m ▸ le_inf h CoordSystem.hE_on_m) |>.resolve_left Γ.hE_atom.1)
  -- l ⊓ (U⊔C) = U
  have hl_inf_UC : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U := by
    rw [sup_comm Γ.O Γ.U]
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm
      (fun h => Γ.hC_not_l (h ▸ le_sup_right))
      (fun h => Γ.hC_not_l (h ▸ le_sup_left))
      (fun h => Γ.hC_not_l (by rwa [sup_comm] at h))
  -- Return centers are atoms (perspect_atom with center E, target U⊔C)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  -- Coplanarity: (U⊔C)⊔E = π (since C⊔E = O⊔C, so U⊔C⊔E = U⊔O⊔C = π)
  have hUCE_eq_π : (Γ.U ⊔ Γ.C) ⊔ Γ.E = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    -- C ⊔ E = O ⊔ C (E ≤ O⊔C, C ≤ O⊔C, covering gives C⊔E = O⊔C)
    have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
    have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
      have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
      have h_le : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right CoordSystem.hE_le_OC
      have h_lt : Γ.C < Γ.C ⊔ Γ.E := by
        apply lt_of_le_of_ne le_sup_left; intro h
        exact hCE ((Γ.hC.le_iff.mp (h ▸ le_sup_right : Γ.E ≤ Γ.C)).resolve_left
          Γ.hE_atom.1).symm
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact (atom_covBy_join Γ.hC Γ.hO hOC.symm |>.eq_or_eq h_lt.le
        (sup_comm Γ.C Γ.O ▸ h_le)).resolve_left (ne_of_gt h_lt)
    -- (U⊔C)⊔E = U⊔(C⊔E) = U⊔(O⊔C) = O⊔U⊔C
    rw [show (Γ.U ⊔ Γ.C) ⊔ Γ.E = Γ.U ⊔ (Γ.C ⊔ Γ.E) from sup_assoc _ _ _, hCE_eq,
        show Γ.U ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.C from by rw [← sup_assoc, sup_comm Γ.U Γ.O]]
    -- O⊔U⊔C = O⊔U⊔V (= π): O⊔C ⋖ π and O⊔C < O⊔U⊔C ≤ π gives O⊔U⊔C = π
    have h_lt_OC : Γ.O ⊔ Γ.C < Γ.O ⊔ Γ.U ⊔ Γ.C := by
      apply lt_of_le_of_ne (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      intro h
      -- O⊔C = O⊔U⊔C → O⊔U ≤ O⊔C → U ≤ O⊔C → O⊔U = O⊔C → C ≤ l
      have hOU_le := h.symm ▸ (le_sup_left : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.U ⊔ Γ.C)
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC
        (fun h => Γ.hC_not_l (h ▸ le_sup_left))).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le hOU_le).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt_OC.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt_OC)
  have hDa_atom : IsAtom D_a :=
    perspect_atom Γ.hE_atom ha ha_ne_E Γ.hU Γ.hC hUC hE_not_UC
      (sup_le (ha_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  have hDb_atom : IsAtom D_b :=
    perspect_atom Γ.hE_atom hb hb_ne_E Γ.hU Γ.hC hUC hE_not_UC
      (sup_le (hb_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  -- Distinctness facts
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)
  have ha'_ne_a : a' ≠ a := fun h => ha_ne_U
    (Γ.atom_on_both_eq_U ha ha_on (h ▸ (inf_le_right : a' ≤ Γ.U ⊔ Γ.V)))
  have hb'_ne_b : b' ≠ b := fun h => hb_ne_U
    (Γ.atom_on_both_eq_U hb hb_on (h ▸ (inf_le_right : b' ≤ Γ.U ⊔ Γ.V)))
  -- === The Desargues chain ===
  -- Join equalities: a ⊔ a' = a ⊔ C (covering argument)
  have haa' : a ⊔ a' = a ⊔ Γ.C := by
    have h_lt : a < a ⊔ a' := lt_of_le_of_ne le_sup_left
      (fun h => ha'_ne_a ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left ha'_atom.1))
    exact ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have hbb' : b ⊔ b' = b ⊔ Γ.C := by
    have h_lt : b < b ⊔ b' := lt_of_le_of_ne le_sup_left
      (fun h => hb'_ne_b ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left hb'_atom.1))
    exact ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  -- Side intersection 1: (a⊔a') ⊓ (b⊔b') = C
  have hS₁ : (a ⊔ a') ⊓ (b ⊔ b') = Γ.C := by
    rw [haa', hbb']; exact CoordSystem.lines_through_C_meet Γ ha hb hab ha_on hb_on
  -- Join equalities for return centers: a ⊔ D_a = a ⊔ E
  -- D_a ≠ a: if D_a = a, then a ≤ U⊔C, so a ≤ l⊓(U⊔C) = U, a = U.
  have hDa_ne_a : D_a ≠ a := fun h_eq => ha_ne_U (Γ.hU.le_iff.mp
    (hl_inf_UC ▸ le_inf ha_on (h_eq ▸ (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C)))
    |>.resolve_left ha.1)
  have hDb_ne_b : D_b ≠ b := fun h_eq => hb_ne_U (Γ.hU.le_iff.mp
    (hl_inf_UC ▸ le_inf hb_on (h_eq ▸ (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C)))
    |>.resolve_left hb.1)
  have haDa : a ⊔ D_a = a ⊔ Γ.E := by
    have h_lt : a < a ⊔ D_a := lt_of_le_of_ne le_sup_left
      (fun h => hDa_ne_a ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left hDa_atom.1))
    exact ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have hbDb : b ⊔ D_b = b ⊔ Γ.E := by
    have h_lt : b < b ⊔ D_b := lt_of_le_of_ne le_sup_left
      (fun h => hDb_ne_b ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left hDb_atom.1))
    exact ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  -- Side intersection 2: (a⊔D_a) ⊓ (b⊔D_b) = E
  have hS₂ : (a ⊔ D_a) ⊓ (b ⊔ D_b) = Γ.E := by
    rw [haDa, hbDb]; exact CoordSystem.lines_through_E_meet Γ ha hb hab ha_on hb_on
  -- First Desargues: P₁ = (a'⊔D_a) ⊓ (b'⊔D_b) ≤ O⊔C
  have hP₁_le : (a' ⊔ D_a) ⊓ (b' ⊔ D_b) ≤ Γ.O ⊔ Γ.C :=
    coord_first_desargues Γ ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U hab R hR hR_not h_irred
  -- Second Desargues: W ≤ l (the core result)
  have hW_on_l : W ≤ Γ.O ⊔ Γ.U :=
    coord_second_desargues Γ ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U hab R hR hR_not h_irred hP₁_le
  -- Remaining atom facts
  -- a' not on l (a' on m, a' ≤ l → a' ≤ l⊓m = U → a' = U → contradiction)
  -- Helper facts (all provable, some need covering/modular arguments)
  have ha'_not_l : ¬ a' ≤ Γ.O ⊔ Γ.U := by
    intro h
    have ha'_le_U : a' ≤ Γ.U := by
      have := le_inf h (inf_le_right : a' ≤ Γ.U ⊔ Γ.V)
      rwa [Γ.l_inf_m_eq_U] at this
    have ha'_eq_U := (Γ.hU.le_iff.mp ha'_le_U).resolve_left ha'_atom.1
    have hU_le_a : Γ.U ≤ a := by
      have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := ha'_eq_U ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ a) = a :=
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ a) :=
        le_inf le_sup_right (hU_le_aC.trans (sup_comm a Γ.C).le)
        _ = a := this
    exact ha_ne_U ((ha.le_iff.mp hU_le_a).resolve_left Γ.hU.1).symm
  have hb'_not_l : ¬ b' ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hb'_le_U : b' ≤ Γ.U := by
      have := le_inf h (inf_le_right : b' ≤ Γ.U ⊔ Γ.V)
      rwa [Γ.l_inf_m_eq_U] at this
    have hb'_eq_U := (Γ.hU.le_iff.mp hb'_le_U).resolve_left hb'_atom.1
    have hU_le_b : Γ.U ≤ b := by
      have hU_le_bC : Γ.U ≤ b ⊔ Γ.C := hb'_eq_U ▸ (inf_le_left : b' ≤ b ⊔ Γ.C)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ b) = b :=
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ b) :=
        le_inf le_sup_right (hU_le_bC.trans (sup_comm b Γ.C).le)
        _ = b := this
    exact hb_ne_U ((hb.le_iff.mp hU_le_b).resolve_left Γ.hU.1).symm
  have hDb_not_l : ¬ D_b ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hDb_le_U : D_b ≤ Γ.U := by
      have := le_inf h (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C)
      rwa [hl_inf_UC] at this
    have hDb_eq_U := (Γ.hU.le_iff.mp hDb_le_U).resolve_left hDb_atom.1
    have hU_le_b : Γ.U ≤ b := by
      have hU_le_bE : Γ.U ≤ b ⊔ Γ.E := hDb_eq_U ▸ (inf_le_left : D_b ≤ b ⊔ Γ.E)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ b) = b :=
        inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l hb_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ b) :=
        le_inf le_sup_right (hU_le_bE.trans (sup_comm b Γ.E).le)
        _ = b := this
    exact hb_ne_U ((hb.le_iff.mp hU_le_b).resolve_left Γ.hU.1).symm
  have hDa_not_l : ¬ D_a ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hDa_le_U : D_a ≤ Γ.U := by
      have := le_inf h (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C)
      rwa [hl_inf_UC] at this
    have hDa_eq_U := (Γ.hU.le_iff.mp hDa_le_U).resolve_left hDa_atom.1
    have hU_le_a : Γ.U ≤ a := by
      have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := hDa_eq_U ▸ (inf_le_left : D_a ≤ a ⊔ Γ.E)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ a) = a :=
        inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l ha_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ a) :=
        le_inf le_sup_right (hU_le_aE.trans (sup_comm a Γ.E).le)
        _ = a := this
    exact ha_ne_U ((ha.le_iff.mp hU_le_a).resolve_left Γ.hU.1).symm
  have ha'Db : a' ≠ D_b := by
    intro h_eq
    have ha'_le_UC : a' ≤ Γ.U ⊔ Γ.C := h_eq ▸ (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C)
    have ha'_le_U : a' ≤ Γ.U := by
      have := le_inf ha'_le_UC (inf_le_right : a' ≤ Γ.U ⊔ Γ.V)
      rwa [hUC_inf_m] at this
    have ha'_eq_U := (Γ.hU.le_iff.mp ha'_le_U).resolve_left ha'_atom.1
    have hU_le_a : Γ.U ≤ a := by
      have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := ha'_eq_U ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ a) = a :=
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ a) :=
        le_inf le_sup_right (hU_le_aC.trans (sup_comm a Γ.C).le)
        _ = a := this
    exact ha_ne_U ((ha.le_iff.mp hU_le_a).resolve_left Γ.hU.1).symm
  have hb'Da : b' ≠ D_a := by
    intro h_eq
    have hb'_le_UC : b' ≤ Γ.U ⊔ Γ.C := h_eq ▸ (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C)
    have hb'_le_U : b' ≤ Γ.U := by
      have := le_inf hb'_le_UC (inf_le_right : b' ≤ Γ.U ⊔ Γ.V)
      rwa [hUC_inf_m] at this
    have hb'_eq_U := (Γ.hU.le_iff.mp hb'_le_U).resolve_left hb'_atom.1
    have hU_le_b : Γ.U ≤ b := by
      have hU_le_bC : Γ.U ≤ b ⊔ Γ.C := hb'_eq_U ▸ (inf_le_left : b' ≤ b ⊔ Γ.C)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ b) = b :=
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ b) :=
        le_inf le_sup_right (hU_le_bC.trans (sup_comm b Γ.C).le)
        _ = b := this
    exact hb_ne_U ((hb.le_iff.mp hU_le_b).resolve_left Γ.hU.1).symm
  -- coord_add values and W are atoms
  -- l ⋖ π (needed for coplanarity arguments)
  have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
    (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
  have hl_covBy_π : Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
  -- Helper: (O⊔U) ⊔ x = π when x is an atom in π but not on l
  have l_sup_eq_π : ∀ x : L, IsAtom x → x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V → ¬ x ≤ Γ.O ⊔ Γ.U →
      (Γ.O ⊔ Γ.U) ⊔ x = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    intro x hx hx_le hx_not
    have h_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ x :=
      lt_of_le_of_ne le_sup_left (fun h => hx_not (h ▸ le_sup_right))
    exact (hl_covBy_π.eq_or_eq h_lt.le (sup_le le_sup_left hx_le)).resolve_left
      (ne_of_gt h_lt)
  -- Atoms ≤ π
  have hDb_le_π : D_b ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C).trans
      (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
  have hDa_le_π : D_a ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C).trans
      (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
  have ha'_le_π : a' ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    (inf_le_right : a' ≤ Γ.U ⊔ Γ.V).trans
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hb'_le_π : b' ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    (inf_le_right : b' ≤ Γ.U ⊔ Γ.V).trans
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  -- hab_atom: perspect_atom with center D_b, point a', target line O⊔U
  have hab_atom : IsAtom (coord_add Γ a b) := by
    show IsAtom ((a' ⊔ D_b) ⊓ (Γ.O ⊔ Γ.U))
    exact perspect_atom hDb_atom ha'_atom ha'Db Γ.hO Γ.hU Γ.hOU hDb_not_l
      (by rw [l_sup_eq_π D_b hDb_atom hDb_le_π hDb_not_l]; exact sup_le ha'_le_π hDb_le_π)
  -- hba_atom: perspect_atom with center D_a, point b', target line O⊔U
  have hba_atom : IsAtom (coord_add Γ b a) := by
    show IsAtom ((b' ⊔ D_a) ⊓ (Γ.O ⊔ Γ.U))
    exact perspect_atom hDa_atom hb'_atom hb'Da Γ.hO Γ.hU Γ.hOU hDa_not_l
      (by rw [l_sup_eq_π D_a hDa_atom hDa_le_π hDa_not_l]; exact sup_le hb'_le_π hDa_le_π)
  -- hW_atom: W is the meet of two lines in π, use line_height_two on l = O⊔U
  have hW_atom : IsAtom W := by
    -- Strategy: W ≤ l (from hW_on_l), show ⊥ < W and W < l, apply line_height_two
    have ha'Db_le_π : a' ⊔ D_b ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := sup_le ha'_le_π hDb_le_π
    have hb'Da_le_π : b' ⊔ D_a ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := sup_le hb'_le_π hDa_le_π
    -- l ⊔ (a'⊔D_b) = π
    have hl_sup_a'Db : (Γ.O ⊔ Γ.U) ⊔ (a' ⊔ D_b) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      have h_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ (a' ⊔ D_b) :=
        lt_of_le_of_ne le_sup_left
          (fun h => hDb_not_l (h ▸ (le_sup_right.trans le_sup_right)))
      exact (hl_covBy_π.eq_or_eq h_lt.le (sup_le le_sup_left ha'Db_le_π)).resolve_left
        (ne_of_gt h_lt)
    -- Lower mod: l ⊓ (a'⊔D_b) ⋖ a'⊔D_b, i.e., coord_add ⋖ a'⊔D_b
    have h_inf_covBy : (Γ.O ⊔ Γ.U) ⊓ (a' ⊔ D_b) ⋖ a' ⊔ D_b :=
      IsLowerModularLattice.inf_covBy_of_covBy_sup (hl_sup_a'Db ▸ hl_covBy_π)
    -- a'⊔D_b < π (if equal, coord_add = l, but l is not an atom)
    have ha'Db_lt_π : a' ⊔ D_b < Γ.O ⊔ Γ.U ⊔ Γ.V := by
      apply lt_of_le_of_ne ha'Db_le_π; intro h_eq
      have h_coord_eq : coord_add Γ a b = Γ.O ⊔ Γ.U :=
        le_antisymm (inf_le_right) (le_inf (h_eq ▸ le_sup_left) le_rfl)
      rw [h_coord_eq] at hab_atom
      -- hab_atom : IsAtom (O⊔U). O ≤ O⊔U → O = ⊥ ∨ O = O⊔U → O = O⊔U → U ≤ O → U = O
      have h1 : Γ.O = Γ.O ⊔ Γ.U :=
        (hab_atom.le_iff.mp le_sup_left).resolve_left Γ.hO.1
      have h2 : Γ.U = Γ.O ⊔ Γ.U :=
        (hab_atom.le_iff.mp le_sup_right).resolve_left Γ.hU.1
      exact Γ.hOU (h1.trans h2.symm)
    -- a'⊔D_b ⋖ π
    have ha'Db_covBy_π : a' ⊔ D_b ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
      refine ⟨ha'Db_lt_π, fun z hz_lt hz_lt2 => ?_⟩
      have hl_sup_z : (Γ.O ⊔ Γ.U) ⊔ z = Γ.O ⊔ Γ.U ⊔ Γ.V :=
        le_antisymm (sup_le le_sup_left hz_lt2.le)
          (hl_sup_a'Db ▸ sup_le_sup_left hz_lt.le _)
      have h_inf_z_covBy : (Γ.O ⊔ Γ.U) ⊓ z ⋖ z :=
        IsLowerModularLattice.inf_covBy_of_covBy_sup (hl_sup_z ▸ hl_covBy_π)
      have hab_le_inf_z : coord_add Γ a b ≤ (Γ.O ⊔ Γ.U) ⊓ z :=
        le_inf (show coord_add Γ a b ≤ Γ.O ⊔ Γ.U from inf_le_right)
          ((show coord_add Γ a b ≤ a' ⊔ D_b from inf_le_left).trans hz_lt.le)
      by_cases h_lz_lt : (Γ.O ⊔ Γ.U) ⊓ z < Γ.O ⊔ Γ.U
      · -- l⊓z < l: l⊓z is atom = coord_add, so coord_add ⋖ z
        have h_lz_atom := line_height_two Γ.hO Γ.hU Γ.hOU
          (lt_of_lt_of_le hab_atom.bot_lt hab_le_inf_z) h_lz_lt
        have h_lz_eq : (Γ.O ⊔ Γ.U) ⊓ z = coord_add Γ a b :=
          ((h_lz_atom.le_iff.mp hab_le_inf_z).resolve_left hab_atom.1).symm
        rw [h_lz_eq] at h_inf_z_covBy
        -- a'⊔D_b between coord_add and z: coord_add ≤ a'⊔D_b ≤ z, with coord_add ⋖ z
        rcases h_inf_z_covBy.eq_or_eq
          (show coord_add Γ a b ≤ a' ⊔ D_b from inf_le_left) hz_lt.le with h | h
        · -- a'⊔D_b = coord_add: then a' ≤ coord_add ≤ l, contradicting ha'_not_l
          exact ha'_not_l (h ▸ le_sup_left |>.trans (inf_le_right : coord_add Γ a b ≤ Γ.O ⊔ Γ.U))
        · -- a'⊔D_b = z: contradicts hz_lt
          exact absurd h hz_lt.ne
      · -- l⊓z = l (since l⊓z ≤ l and ¬(l⊓z < l)), so l ≤ z
        have h_inf_eq : (Γ.O ⊔ Γ.U) ⊓ z = Γ.O ⊔ Γ.U :=
          eq_of_le_of_not_lt inf_le_left h_lz_lt
        have h_l_le_z : Γ.O ⊔ Γ.U ≤ z := h_inf_eq ▸ inf_le_right
        exact absurd (le_antisymm hz_lt2.le (hl_sup_a'Db ▸
          sup_le h_l_le_z hz_lt.le)) hz_lt2.ne
    -- ⊥ < W: if W = ⊥, the two lines are disjoint in π, impossible
    have hW_pos : ⊥ < W := by
      rw [bot_lt_iff_ne_bot]; intro hW_bot
      change (a' ⊔ D_b) ⊓ (b' ⊔ D_a) = ⊥ at hW_bot
      by_cases h_le : b' ⊔ D_a ≤ a' ⊔ D_b
      · -- b'⊔D_a ≤ a'⊔D_b: then inf = b'⊔D_a, so b'⊔D_a = ⊥, contradicting b' atom
        exact absurd (le_bot_iff.mp (le_sup_left.trans
          ((inf_eq_right.mpr h_le).symm.trans hW_bot).le)) hb'_atom.1
      · -- b'⊔D_a ≰ a'⊔D_b: by covBy_inf_disjoint_atom, ⊥ ⋖ b'⊔D_a
        -- but b' < b'⊔D_a (from atom_covBy_join), contradicting nothing between ⊥ and b'⊔D_a
        exact absurd (atom_covBy_join hb'_atom hDa_atom hb'Da).lt
          ((covBy_inf_disjoint_atom ha'Db_covBy_π hb'Da_le_π h_le hW_bot).2
            hb'_atom.bot_lt)
    -- W < l: if W = l then l ≤ b'⊔D_a, and line_eq_of_atom_le forces b' on l
    have hW_lt : W < Γ.O ⊔ Γ.U := by
      apply lt_of_le_of_ne hW_on_l; intro h_eq
      have hl_le : Γ.O ⊔ Γ.U ≤ b' ⊔ D_a := h_eq ▸ (inf_le_right : W ≤ b' ⊔ D_a)
      -- O ≠ b' (O not on m, b' on m) and O ≠ D_a (if so, O ≤ U⊔C, O ≤ l⊓(U⊔C) = U)
      have hOb' : Γ.O ≠ b' := fun h => Γ.hO_not_m (h ▸ (inf_le_right : b' ≤ Γ.U ⊔ Γ.V))
      have hODa : Γ.O ≠ D_a := fun h => Γ.hOU ((Γ.hU.le_iff.mp
        (show Γ.O ≤ Γ.U from hl_inf_UC ▸
          le_inf (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
                (h ▸ (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C)))
        ).resolve_left Γ.hO.1)
      -- O ≤ b'⊔D_a, so b'⊔D_a = b'⊔O (line_eq_of_atom_le)
      have h1 := line_eq_of_atom_le hb'_atom hDa_atom Γ.hO hb'Da hOb'.symm hODa.symm
        (le_sup_left.trans hl_le)
      -- U ≠ b' (b' not on l, U on l) and U ≠ D_a (handled by hDa_not_l: if U = D_a ...)
      have hUb' : Γ.U ≠ b' := fun h => hb'_not_l (h ▸ le_sup_right)
      have hUDa : Γ.U ≠ D_a := fun h => hDa_not_l (h ▸ le_sup_right)
      -- U ≤ b'⊔D_a = b'⊔O, so b'⊔O = b'⊔U (line_eq_of_atom_le)
      have h2 := line_eq_of_atom_le hb'_atom Γ.hO Γ.hU hOb'.symm hUb'.symm Γ.hOU
        (h1 ▸ le_sup_right.trans hl_le)
      -- U ⋖ U⊔b', O⊔U ≤ U⊔b' = b'⊔U. From covering: O⊔U = U or O⊔U = U⊔b'.
      -- O⊔U ≤ b'⊔D_a = b'⊔O = b'⊔U
      have hOU_le_bU : Γ.O ⊔ Γ.U ≤ b' ⊔ Γ.U :=
        hl_le.trans (h1.le.trans h2.le)
      -- From U ⋖ U⊔b' = b'⊔U and O⊔U ≤ b'⊔U: eq_or_eq gives O⊔U = U or O⊔U = U⊔b'
      have hUb'_cov := atom_covBy_join Γ.hU hb'_atom hUb'
      have hOU_le' : Γ.O ⊔ Γ.U ≤ Γ.U ⊔ b' := by rwa [sup_comm b' Γ.U] at hOU_le_bU
      rcases hUb'_cov.eq_or_eq
        (show Γ.U ≤ Γ.O ⊔ Γ.U from le_sup_right) hOU_le' with h3 | h3
      · -- O⊔U = U → O ≤ U → O = U, contradiction
        have hO_le_U : Γ.O ≤ Γ.U := h3 ▸ le_sup_left
        exact Γ.hOU ((Γ.hU.le_iff.mp hO_le_U).resolve_left Γ.hO.1)
      · -- O⊔U = U⊔b' → b' ≤ O⊔U, contradicting hb'_not_l
        exact hb'_not_l (h3.symm ▸ le_sup_right)
    exact line_height_two Γ.hO Γ.hU Γ.hOU hW_pos hW_lt
  -- Combination: W on both addition lines and on l → W = a+b = b+a
  have hW_le_ab : W ≤ coord_add Γ a b :=
    le_inf (inf_le_left : W ≤ a' ⊔ D_b) hW_on_l
  have hW_le_ba : W ≤ coord_add Γ b a :=
    le_inf (inf_le_right : W ≤ b' ⊔ D_a) hW_on_l
  exact ((hab_atom.le_iff.mp hW_le_ab).resolve_left hW_atom.1).symm.trans
    ((hba_atom.le_iff.mp hW_le_ba).resolve_left hW_atom.1)

-- coord_add_assoc: The diagram-chasing approach to associativity (originally here,
-- ~900 lines) is superseded by the Hartshorne translation approach in
-- FTPGAssoc.lean (via FTPGParallelogram → FTPGWellDefined → FTPGCrossParallelism).
-- The theorem statement and proof now live there, built on the translation
-- group structure rather than direct parallelism chasing.

end Foam.FTPGExplore
