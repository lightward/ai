/-
# Left distributivity (Part VII-D)
a · (b + c) = a·b + a·c

## Architecture

Single forward `desargues_planar` call, center σ_b on k = O⊔C.

### Setup
  s  = b + c           (von Staudt addition on l)
  σ_x = k ⊓ (x⊔E_I)    (perspectivity l → k, center E_I)
  d_a = (a⊔C) ⊓ m      (multiplication center on m)
  a·x = (σ_x ⊔ d_a) ⊓ l

### Forward Desargues (`desargues_planar`)
  Triangles T1 = (C, ab, U), T2 = (E, d_a, W') in π, center σ_b.
  W' = (σ_b⊔U) ⊓ (ac⊔E).
  Central perspectivity is free by coord definitions.
  Output: axis through (ab⊔C)⊓m, (ac⊔E)⊓q, and (ab⊔U)⊓(d_a⊔W') on l.

### Concurrence (prerequisite)
  W' ≤ σ_s ⊔ d_a.
  With this, d_a⊔W' = σ_s⊔d_a (atoms on covering line), so
  (d_a⊔W') ⊓ l = (σ_s⊔d_a) ⊓ l = a·s.

### Combination
  Axis collinearity + concurrence ⇒ a·s = ((ab⊔C)⊓m ⊔ (ac⊔E)⊓q) ⊓ l = ab + ac.

## Multiplication order

`dilation_ext Γ c` is a collineation for right multiplication x ↦ x·c.
Left multiplication x ↦ a·x is NOT a single collineation in the non-
commutative case. This is why left distrib requires the two-piece
(Desargues + concurrence) proof rather than a direct collineation argument.

## Status (session 118, 2026-04-24)

The forward Desargues piece (`_scratch_forward_planar_call`) and the
axis-to-left-distrib bridge (`_scratch_left_distrib_via_axis`) are both
fully discharged. The remaining work is a standalone proof of the
concurrence lemma `concurrence : W' ≤ σ_s ⊔ d_a`, which is currently
stated below with `sorry`. Session 114's architectural finding rules
out the `desargues_converse_nonplanar` lift+recurse route (structurally
non-terminating at Level 2 h_ax₂₃); session 118 preserves the gap
cleanly so that a different approach (e.g. exploiting the fact that the
natural axis of (σ_b, ac, σ_s) vs (U, E, d_a) lies on m) can be tried
in isolation.
-/
import Foam.FTPGNeg

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]


/-- σ_b = C iff b = I. Given atom b on l with b ≠ O, b ≠ U, the projection
    σ_b = (O⊔C)⊓(b⊔E_I) equals C exactly when b is the identity coordinate.

    Forward direction proven here; used to turn `hσb_ne_C` into `hb_ne_I`
    (a native coord hypothesis) at the `_scratch_forward_planar_call` site.
    Geometric content: C ≤ b⊔E_I forces b⊔E_I = I⊔C (both lines through C
    and E_I), so b ≤ (I⊔C)⊓l = I. -/
private theorem sigma_b_eq_C_imp_b_eq_I (Γ : CoordSystem L) {b : L}
    (hb : IsAtom b) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (h_eq : (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) = Γ.C) :
    b = Γ.I := by
  -- Basic distinctness
  have hC_ne_EI : Γ.C ≠ Γ.E_I := fun h => Γ.hC_not_m (h ▸ Γ.hE_I_on_m)
  have hI_ne_C : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h.symm ▸ Γ.hI_on)
  have hI_ne_EI : Γ.I ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ Γ.hI_on)
  have hb_ne_EI : b ≠ Γ.E_I :=
    fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h ▸ Γ.hE_I_on_m))
  have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)
  -- Step 1: C ≤ b ⊔ E_I (since σ_b = C, σ_b ≤ b⊔E_I).
  have hC_le_bEI : Γ.C ≤ b ⊔ Γ.E_I :=
    h_eq ▸ (inf_le_right : (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ≤ b ⊔ Γ.E_I)
  -- Step 2: C ⊔ I = C ⊔ E_I (line through C, I, E_I; E_I on I⊔C by hE_I_le_IC).
  have hCI_eq_CEI : Γ.C ⊔ Γ.I = Γ.C ⊔ Γ.E_I :=
    line_eq_of_atom_le Γ.hC Γ.hI Γ.hE_I_atom hI_ne_C.symm hC_ne_EI hI_ne_EI
      (by rw [sup_comm]; exact Γ.hE_I_le_IC)
  -- Step 3: E_I ⊔ b = E_I ⊔ C (line through b, E_I, C; C on b⊔E_I from Step 1).
  have hEIb_eq_EIC : Γ.E_I ⊔ b = Γ.E_I ⊔ Γ.C :=
    line_eq_of_atom_le Γ.hE_I_atom hb Γ.hC hb_ne_EI.symm hC_ne_EI.symm hb_ne_C
      (by rw [sup_comm]; exact hC_le_bEI)
  -- Step 4: b ⊔ E_I = I ⊔ C via the two line identities above.
  have hbEI_eq_IC : b ⊔ Γ.E_I = Γ.I ⊔ Γ.C := by
    calc b ⊔ Γ.E_I = Γ.E_I ⊔ b := sup_comm _ _
      _ = Γ.E_I ⊔ Γ.C := hEIb_eq_EIC
      _ = Γ.C ⊔ Γ.E_I := sup_comm _ _
      _ = Γ.C ⊔ Γ.I := hCI_eq_CEI.symm
      _ = Γ.I ⊔ Γ.C := sup_comm _ _
  -- Step 5: b = (b⊔E_I) ⊓ l = (I⊔C) ⊓ l = I.
  have hEI_inf_l : Γ.E_I ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
    (Γ.hE_I_atom.le_iff.mp inf_le_left).resolve_right
      (fun h => Γ.hE_I_not_l (h ▸ inf_le_right))
  have hbEI_inf_l : (b ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = b := by
    have h1 := sup_inf_assoc_of_le Γ.E_I hb_on
    rw [h1, hEI_inf_l]; simp
  have hC_inf_l : Γ.C ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
    (Γ.hC.le_iff.mp inf_le_left).resolve_right
      (fun h => Γ.hC_not_l (h ▸ inf_le_right))
  have hIC_inf_l : (Γ.I ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.I := by
    have h1 := sup_inf_assoc_of_le Γ.C Γ.hI_on
    rw [h1, hC_inf_l]; simp
  -- Combine: b = (b⊔E_I)⊓l = (I⊔C)⊓l = I.
  have : b = Γ.I := by
    rw [← hbEI_inf_l, hbEI_eq_IC, hIC_inf_l]
  exact this

/-- Scratch (session 114, closed session 117): structural viability test for
    the direct `desargues_planar` route. All triage hypotheses discharge from
    the shared prologue; `hσb_ne_C` is now derived internally from `hb_ne_I`
    via `sigma_b_eq_C_imp_b_eq_I`. See the docs block above for the finding,
    context, and next steps.
-/
private theorem _scratch_forward_planar_call
    (Γ : CoordSystem L) (a b c : L)
    (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hab_ne_O : coord_mul Γ a b ≠ Γ.O) (hab_ne_U : coord_mul Γ a b ≠ Γ.U)
    (hac_ne_O : coord_mul Γ a c ≠ Γ.O) (hac_ne_U : coord_mul Γ a c ≠ Γ.U)
    -- σ_b ≠ C iff b ≠ I (by `sigma_b_eq_C_imp_b_eq_I`); real usage must
    -- case-split on b = I, since a·I = a makes the forward Desargues degenerate.
    (hb_ne_I : b ≠ Γ.I)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    -- Axis collinearity for T1=(C,ab,U), T2=(E,d_a,W') in π, center σ_b
    ∃ (axis : L), axis ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ∧ axis ≠ Γ.O ⊔ Γ.U ⊔ Γ.V ∧
      (Γ.C ⊔ coord_mul Γ a b) ⊓ (Γ.E ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤ axis ∧
      (Γ.C ⊔ Γ.U) ⊓ (Γ.E ⊔ ((Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ⊔ Γ.U) ⊓
        (coord_mul Γ a c ⊔ Γ.E)) ≤ axis ∧
      (coord_mul Γ a b ⊔ Γ.U) ⊓
        ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ ((Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ⊔ Γ.U) ⊓
          (coord_mul Γ a c ⊔ Γ.E)) ≤ axis := by
  set σ_b := (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) with hσb_def
  set ab := coord_mul Γ a b with hab_def
  set ac := coord_mul Γ a c with hac_def
  set d_a := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) with hda_def
  set W' := (σ_b ⊔ Γ.U) ⊓ (ac ⊔ Γ.E) with hW'_def
  -- Derive σ_b ≠ C from b ≠ I via the standalone lemma.
  have hσb_ne_C : σ_b ≠ Γ.C :=
    fun h => hb_ne_I (sigma_b_eq_C_imp_b_eq_I Γ hb hb_on hb_ne_U h)
  -- Common facts used in multiple sorry discharges
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hm_π : Γ.U ⊔ Γ.V ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hk_π : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane
  have hab_atom : IsAtom ab :=
    coord_mul_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
  have hac_atom : IsAtom ac :=
    coord_mul_atom Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U
  have hab_l : ab ≤ Γ.O ⊔ Γ.U := by
    show coord_mul Γ a b ≤ Γ.O ⊔ Γ.U; unfold coord_mul; exact inf_le_right
  have hac_l : ac ≤ Γ.O ⊔ Γ.U := by
    show coord_mul Γ a c ≤ Γ.O ⊔ Γ.U; unfold coord_mul; exact inf_le_right
  have hσb_k : σ_b ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hkl_eq_O : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.O := by
    rw [inf_comm]; exact modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU
      (fun h => Γ.hC_not_l (h ▸ le_sup_left))
      (fun h => Γ.hC_not_l (h.symm.le.trans le_sup_right))
      Γ.hC_not_l
  have hσb_atom : IsAtom σ_b := by
    rw [show σ_b = (b ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) from inf_comm _ _]
    have hb_ne_EI : b ≠ Γ.E_I :=
      fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h ▸ Γ.hE_I_on_m))
    have hEI_sup_OC : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      have h_lt : Γ.O ⊔ Γ.C < Γ.E_I ⊔ (Γ.O ⊔ Γ.C) :=
        lt_of_le_of_ne le_sup_right (fun h => Γ.hE_I_not_OC (h ▸ le_sup_left))
      exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
        (sup_le (Γ.hE_I_on_m.trans hm_π) hk_π)).resolve_left (ne_of_gt h_lt)
    exact perspect_atom Γ.hE_I_atom hb hb_ne_EI Γ.hO Γ.hC hOC Γ.hE_I_not_OC
      (sup_comm (Γ.O ⊔ Γ.C) Γ.E_I ▸ hEI_sup_OC ▸
        sup_le (hb_on.trans le_sup_left) (Γ.hE_I_on_m.trans hm_π))
  have hE_m : Γ.E ≤ Γ.U ⊔ Γ.V := Γ.hE_on_m
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hda_m : d_a ≤ Γ.U ⊔ Γ.V := inf_le_right
  have hda_atom : IsAtom d_a := by
    have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
    exact perspect_atom Γ.hC ha ha_ne_C Γ.hU Γ.hV hUV Γ.hC_not_m
      (sup_le (ha_on.trans (le_sup_left.trans Γ.m_sup_C_eq_π.symm.le)) le_sup_right)
  have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
    (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
  have hl_covBy_π : Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
  have hlC_eq_π : (Γ.O ⊔ Γ.U) ⊔ Γ.C = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ Γ.C :=
      lt_of_le_of_ne le_sup_left
        (fun h => Γ.hC_not_l (h ▸ le_sup_right))
    exact (hl_covBy_π.eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt)
  have habU_eq_l : ab ⊔ Γ.U = Γ.O ⊔ Γ.U := by
    have h1 : Γ.U ⊔ Γ.O = Γ.U ⊔ ab :=
      line_eq_of_atom_le Γ.hU Γ.hO hab_atom Γ.hOU.symm hab_ne_U.symm
        hab_ne_O.symm (le_of_le_of_eq hab_l (sup_comm _ _))
    rw [sup_comm ab Γ.U, ← h1, sup_comm Γ.U Γ.O]
  have hda_not_l : ¬ d_a ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hda_le_U : d_a ≤ Γ.U := by
      have hda_le_inf : d_a ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) := le_inf h hda_m
      rw [Γ.l_inf_m_eq_U] at hda_le_inf
      exact hda_le_inf
    have hda_eq_U : d_a = Γ.U :=
      (Γ.hU.le_iff.mp hda_le_U).resolve_left hda_atom.1
    have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := hda_eq_U ▸ inf_le_left
    have hCU : Γ.C ≠ Γ.U :=
      fun h' => Γ.hC_not_l (h'.symm ▸ (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U))
    have haC_eq_aU : a ⊔ Γ.C = a ⊔ Γ.U :=
      line_eq_of_atom_le ha Γ.hC Γ.hU ha_ne_C ha_ne_U hCU hU_le_aC
    exact Γ.hC_not_l ((le_sup_right : Γ.C ≤ a ⊔ Γ.C).trans
      (haC_eq_aU ▸ sup_le ha_on le_sup_right : a ⊔ Γ.C ≤ Γ.O ⊔ Γ.U))
  have hσb_not_m : ¬ σ_b ≤ Γ.U ⊔ Γ.V := by
    intro h
    have hE_eq : (Γ.U ⊔ Γ.V) ⊓ (Γ.O ⊔ Γ.C) = Γ.E := by
      rw [inf_comm]; rfl
    have hσb_le_E : σ_b ≤ Γ.E := hE_eq ▸ le_inf h hσb_k
    have hb_inf_m : b ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (hb.le_iff.mp inf_le_left).resolve_right
        (fun h' => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h' ▸ inf_le_right)))
    have hbEI_inf_m : (b ⊔ Γ.E_I) ⊓ (Γ.U ⊔ Γ.V) = Γ.E_I := by
      rw [sup_comm b Γ.E_I]
      have h1 := sup_inf_assoc_of_le b Γ.hE_I_on_m
      rw [h1, hb_inf_m]; simp
    have hσb_le_bEI : σ_b ≤ b ⊔ Γ.E_I := inf_le_right
    have hσb_le_EI : σ_b ≤ Γ.E_I := by
      have : σ_b ≤ (b ⊔ Γ.E_I) ⊓ (Γ.U ⊔ Γ.V) :=
        le_inf hσb_le_bEI (hσb_le_E.trans hE_m)
      rw [hbEI_inf_m] at this; exact this
    exact Γ.hE_I_not_OC ((Γ.hE_I_atom.le_iff.mp hσb_le_EI).resolve_left
      hσb_atom.1 ▸ hσb_k)
  -- Π-membership helpers
  have hE_le_OC : Γ.E ≤ Γ.O ⊔ Γ.C := CoordSystem.hE_le_OC
  have hE_π : Γ.E ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hE_m.trans hm_π
  have hU_π : Γ.U ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := le_sup_right.trans le_sup_left
  have hab_π : ab ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hab_l.trans le_sup_left
  have hac_π : ac ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hac_l.trans le_sup_left
  have hσb_π : σ_b ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hσb_k.trans hk_π
  -- σ_b distinctnesses (σ_b ≠ O, σ_b ≠ U)
  have hσb_ne_O : σ_b ≠ Γ.O := by
    intro h_eq
    have hEI_inf_l : Γ.E_I ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
      (Γ.hE_I_atom.le_iff.mp inf_le_left).resolve_right
        (fun h' => Γ.hE_I_not_l (h' ▸ inf_le_right))
    have hbEI_inf_l : (b ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = b := by
      have h1 := sup_inf_assoc_of_le Γ.E_I hb_on
      rw [hEI_inf_l] at h1; simp at h1; exact h1
    have hO_le_b : Γ.O ≤ b :=
      hbEI_inf_l ▸ le_inf (h_eq ▸ (inf_le_right : σ_b ≤ b ⊔ Γ.E_I))
        (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
    exact hb_ne_O ((hb.le_iff.mp hO_le_b).resolve_left Γ.hO.1).symm
  have hσb_ne_U : σ_b ≠ Γ.U :=
    fun h => hσb_not_m (h ▸ (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V))
  -- ac-side helpers
  have hac_ne_E : ac ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hac_l)
  have hac_not_m : ¬ ac ≤ Γ.U ⊔ Γ.V :=
    fun h => hac_ne_U (Γ.atom_on_both_eq_U hac_atom hac_l h)
  have hac_sup_U_eq_l : ac ⊔ Γ.U = Γ.O ⊔ Γ.U :=
    ((line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hac_atom hac_l).eq_or_eq
      (atom_covBy_join hac_atom Γ.hU hac_ne_U).lt.le
      (sup_le hac_l le_sup_right)).resolve_left
      (ne_of_gt (atom_covBy_join hac_atom Γ.hU hac_ne_U).lt)
  have hU_disj_acE : Γ.U ⊓ (ac ⊔ Γ.E) = ⊥ := by
    rcases Γ.hU.le_iff.mp inf_le_left with h | h
    · exact h
    · exfalso
      have hl_le : Γ.O ⊔ Γ.U ≤ ac ⊔ Γ.E :=
        hac_sup_U_eq_l ▸ sup_le le_sup_left (h ▸ inf_le_right)
      have hl_eq : Γ.O ⊔ Γ.U = ac ⊔ Γ.E :=
        ((atom_covBy_join hac_atom Γ.hE_atom hac_ne_E).eq_or_eq hac_l hl_le
          ).resolve_left (fun h' => hac_ne_U ((hac_atom.le_iff.mp
            (h' ▸ (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U))).resolve_left Γ.hU.1).symm)
      exact CoordSystem.hE_not_l (hl_eq ▸ (le_sup_right : Γ.E ≤ ac ⊔ Γ.E))
  have hU_not_acE : ¬ Γ.U ≤ ac ⊔ Γ.E := fun h =>
    Γ.hU.1 (le_antisymm (hU_disj_acE ▸ le_inf le_rfl h) bot_le)
  have hl_sup_E : (Γ.O ⊔ Γ.U) ⊔ Γ.E = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ Γ.E :=
      lt_of_le_of_ne le_sup_left (fun h => CoordSystem.hE_not_l
        (h.symm ▸ (le_sup_right : Γ.E ≤ (Γ.O ⊔ Γ.U) ⊔ Γ.E)))
    exact (hl_covBy_π.eq_or_eq h_lt.le (sup_le le_sup_left hE_π)).resolve_left
      (ne_of_gt h_lt)
  have hacE_sup_U_eq_π : ac ⊔ Γ.E ⊔ Γ.U = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    calc ac ⊔ Γ.E ⊔ Γ.U = (ac ⊔ Γ.U) ⊔ Γ.E := by
          simp only [sup_assoc, sup_comm]
      _ = (Γ.O ⊔ Γ.U) ⊔ Γ.E := by rw [hac_sup_U_eq_l]
      _ = Γ.O ⊔ Γ.U ⊔ Γ.V := hl_sup_E
  have hacE_covBy_π : ac ⊔ Γ.E ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h : ac ⊔ Γ.E ⋖ Γ.U ⊔ (ac ⊔ Γ.E) :=
      covBy_sup_of_inf_covBy_left (hU_disj_acE ▸ Γ.hU.bot_covBy)
    rwa [sup_comm Γ.U (ac ⊔ Γ.E), hacE_sup_U_eq_π] at h
  -- σ_b ⊔ U helpers
  have hσbU_π : σ_b ⊔ Γ.U ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := sup_le hσb_π hU_π
  have hσb_inf_m : σ_b ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
    (hσb_atom.le_iff.mp inf_le_left).resolve_right
      (fun h => hσb_not_m (h ▸ inf_le_right))
  have hσbU_inf_m : (σ_b ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
    rw [sup_comm]
    have h1 := sup_inf_assoc_of_le σ_b (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)
    rw [hσb_inf_m] at h1; simp at h1; exact h1
  -- W' atomicity and related
  have hW'_atom : IsAtom W' :=
    perspect_atom Γ.hU hσb_atom hσb_ne_U hac_atom Γ.hE_atom hac_ne_E
      hU_not_acE (by
        show σ_b ⊔ Γ.U ≤ (ac ⊔ Γ.E) ⊔ Γ.U
        rw [show (ac ⊔ Γ.E) ⊔ Γ.U = Γ.O ⊔ Γ.U ⊔ Γ.V from hacE_sup_U_eq_π]
        exact hσbU_π)
  have hW'_le_acE : W' ≤ ac ⊔ Γ.E := inf_le_right
  have hW'_le_σbU : W' ≤ σ_b ⊔ Γ.U := inf_le_left
  have hW'_π : W' ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hW'_le_acE.trans (sup_le hac_π hE_π)
  have hacE_inf_m : (ac ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.V) = Γ.E := by
    rw [sup_comm]
    have h1 := sup_inf_assoc_of_le ac hE_m
    rw [(hac_atom.le_iff.mp inf_le_left).resolve_right
      (fun h' => hac_not_m (h' ▸ inf_le_right))] at h1; simp at h1; exact h1
  have hW'_ne_E : W' ≠ Γ.E := fun h =>
    CoordSystem.hEU ((Γ.hU.le_iff.mp
      (hσbU_inf_m ▸ le_inf (h ▸ hW'_le_σbU) hE_m)).resolve_left Γ.hE_atom.1)
  have hW'_not_m : ¬ W' ≤ Γ.U ⊔ Γ.V := fun h =>
    hW'_ne_E ((Γ.hE_atom.le_iff.mp (hacE_inf_m ▸ le_inf hW'_le_acE h)).resolve_left
      hW'_atom.1)
  have hW'_ne_U : W' ≠ Γ.U :=
    fun h => hW'_not_m (h ▸ (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V))
  have hda_ne_E : d_a ≠ Γ.E := by
    intro h
    have ha_inf_k : a ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
      (ha.le_iff.mp inf_le_left).resolve_right
        (fun h' => ha_ne_O ((Γ.hO.le_iff.mp
          (hkl_eq_O ▸ le_inf (h' ▸ inf_le_right) ha_on)).resolve_left ha.1))
    have haC_inf_k : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm, inf_comm]
      have h1 := sup_inf_assoc_of_le a (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)
      rw [ha_inf_k] at h1; simp at h1; rw [inf_comm] at h1; exact h1
    exact Γ.hC_not_m ((Γ.hC.le_iff.mp
      (haC_inf_k ▸ le_inf (h ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)) hE_le_OC)
      ).resolve_left Γ.hE_atom.1 ▸ hE_m)
  have hW'_ne_da : W' ≠ d_a := fun h =>
    hda_ne_E ((Γ.hE_atom.le_iff.mp
      (hacE_inf_m ▸ le_inf (h ▸ hW'_le_acE) hda_m)).resolve_left hda_atom.1)
  -- σ_b ≠ W' (W' would land σ_b on m — contradicts hσb_not_m)
  have hσb_ne_W' : σ_b ≠ W' := by
    intro h
    have hσb_le_acE : σ_b ≤ ac ⊔ Γ.E := h ▸ hW'_le_acE
    have hac_inf_k : ac ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
      (hac_atom.le_iff.mp inf_le_left).resolve_right
        (fun h' => hac_ne_O ((Γ.hO.le_iff.mp
          (hkl_eq_O ▸ le_inf (h' ▸ inf_le_right) hac_l)).resolve_left hac_atom.1))
    have hacE_inf_k : (ac ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.C) = Γ.E := by
      rw [sup_comm]
      have h1 := sup_inf_assoc_of_le ac hE_le_OC
      rw [h1, hac_inf_k]; simp
    have hσb_le_E : σ_b ≤ Γ.E :=
      hacE_inf_k ▸ le_inf hσb_le_acE hσb_k
    exact hσb_not_m ((Γ.hE_atom.le_iff.mp hσb_le_E).resolve_left hσb_atom.1 ▸ hE_m)
  exact desargues_planar
    (o := σ_b) (a₁ := Γ.C) (a₂ := ab) (a₃ := Γ.U)
    (b₁ := Γ.E) (b₂ := d_a) (b₃ := W')
    (π := Γ.O ⊔ Γ.U ⊔ Γ.V)
    -- Atomicity
    (ho := hσb_atom)
    (ha₁ := Γ.hC)
    (ha₂ := hab_atom)
    (ha₃ := Γ.hU)
    (hb₁ := Γ.hE_atom)
    (hb₂ := by
      have hAC : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
      have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
      exact perspect_atom Γ.hC ha hAC Γ.hU Γ.hV hUV Γ.hC_not_m
        (sup_le (ha_on.trans (le_sup_left.trans Γ.m_sup_C_eq_π.symm.le)) le_sup_right))
    (hb₃ := hW'_atom)
    -- In-plane
    (ho_le := inf_le_left.trans (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane))
    (ha₁_le := Γ.hC_plane)
    (ha₂_le := by
      show coord_mul Γ a b ≤ Γ.O ⊔ Γ.U ⊔ Γ.V
      unfold coord_mul
      exact inf_le_right.trans le_sup_left)
    (ha₃_le := le_sup_right.trans le_sup_left)
    (hb₁_le := Γ.hE_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
    (hb₂_le := inf_le_right.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
    (hb₃_le := inf_le_left.trans (sup_le
      (inf_le_left.trans (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane))
      (le_sup_right.trans le_sup_left)))
    -- KEY: Central perspectivity from σ_b (the three load-bearing conditions)
    (hb₁_on := by
      -- E ≤ σ_b ⊔ C: σ_b, C, E all ≤ k=O⊔C with σ_b ≠ C and C ⋖ k.
      have hC_covBy_k : Γ.C ⋖ Γ.O ⊔ Γ.C := by
        have h := atom_covBy_join Γ.hC Γ.hO hOC.symm
        rwa [sup_comm] at h
      have h_le : σ_b ⊔ Γ.C ≤ Γ.O ⊔ Γ.C := sup_le hσb_k le_sup_right
      rcases hC_covBy_k.eq_or_eq (le_sup_right : Γ.C ≤ σ_b ⊔ Γ.C) h_le with h_eq_C | h_eq_k
      · exfalso
        exact hσb_ne_C ((Γ.hC.le_iff.mp (h_eq_C ▸ le_sup_left : σ_b ≤ Γ.C)).resolve_left
          hσb_atom.1)
      · exact hE_le_OC.trans h_eq_k.symm.le)
    (hb₂_on := by
      -- d_a ≤ σ_b ⊔ ab. From coord_mul def, ab ≤ σ_b ⊔ d_a. CovBy closes.
      have hab_le_σbda : ab ≤ σ_b ⊔ d_a := by
        show coord_mul Γ a b ≤ σ_b ⊔ d_a; unfold coord_mul; exact inf_le_left
      have hσb_ne_da : σ_b ≠ d_a :=
        fun h => hσb_not_m (h ▸ hda_m)
      have hab_ne_σb : ab ≠ σ_b := by
        intro h
        have : σ_b ≤ Γ.O ⊔ Γ.U := h ▸ hab_l
        have hσb_eq_O : σ_b = Γ.O :=
          (Γ.hO.le_iff.mp (hkl_eq_O ▸ le_inf hσb_k this)).resolve_left hσb_atom.1
        exact hab_ne_O (h ▸ hσb_eq_O)
      have hcov : σ_b ⋖ σ_b ⊔ d_a :=
        atom_covBy_join hσb_atom hda_atom hσb_ne_da
      have h1 : σ_b ≤ σ_b ⊔ ab := le_sup_left
      have h2 : σ_b ⊔ ab ≤ σ_b ⊔ d_a := sup_le le_sup_left hab_le_σbda
      rcases hcov.eq_or_eq h1 h2 with h_eq_σb | h_eq_σbda
      · exfalso
        exact hab_ne_σb ((hσb_atom.le_iff.mp (h_eq_σb ▸ le_sup_right : ab ≤ σ_b)).resolve_left
          hab_atom.1)
      · exact h_eq_σbda ▸ le_sup_right)
    (hb₃_on := inf_le_left)
    -- Vertex distinctness within each triangle
    (ha₁₂ := by
      intro h
      apply Γ.hC_not_l
      rw [h]
      show coord_mul Γ a b ≤ Γ.O ⊔ Γ.U
      unfold coord_mul
      exact inf_le_right)
    (ha₁₃ := fun h => Γ.hC_not_l (h ▸ le_sup_right))
    (ha₂₃ := hab_ne_U)
    (hb₁₂ := by
      intro h
      have hC_ne_E : Γ.C ≠ Γ.E := fun h' => Γ.hC_not_m (h' ▸ Γ.hE_on_m)
      have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := by rw [h]; exact inf_le_left
      have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
        intro hle
        have haC_eq_aO : a ⊔ Γ.C = a ⊔ Γ.O :=
          line_eq_of_atom_le ha Γ.hC Γ.hO ha_ne_C ha_ne_O hOC.symm hle
        exact Γ.hC_not_l ((le_sup_right : Γ.C ≤ a ⊔ Γ.C).trans
          (haC_eq_aO ▸ sup_le ha_on le_sup_left : a ⊔ Γ.C ≤ Γ.O ⊔ Γ.U))
      have hinf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
        exact modular_intersection Γ.hC ha Γ.hO
          (fun h' => ha_ne_C h'.symm) hOC.symm ha_ne_O
          (by rwa [sup_comm] at hO_not_aC)
      have hE_le_C : Γ.E ≤ Γ.C := hinf_C ▸ le_inf hE_le_aC Γ.hE_le_OC
      exact hC_ne_E ((Γ.hC.le_iff.mp hE_le_C).resolve_left Γ.hE_atom.1).symm)
    (hb₁₃ := hW'_ne_E.symm)
    (hb₂₃ := hW'_ne_da.symm)
    -- Corresponding sides distinct
    (h_sides₁₂ := fun h => Γ.hC_not_m
      ((h ▸ (le_sup_left : Γ.C ≤ Γ.C ⊔ ab)).trans (sup_le hE_m hda_m)))
    (h_sides₁₃ := by
      -- (C⊔U)⊓m = U; (E⊔W')⊓m = E (since W' ∉ m); U ≠ E.
      intro h
      have hC_inf_m : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
        (Γ.hC.le_iff.mp inf_le_left).resolve_right
          (fun h' => Γ.hC_not_m (h' ▸ inf_le_right))
      have hCU_inf_m : (Γ.C ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
        rw [sup_comm Γ.C Γ.U]
        have h1 := sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)
        rw [h1, hC_inf_m]; simp
      have hW'_inf_m : W' ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
        (hW'_atom.le_iff.mp inf_le_left).resolve_right
          (fun h' => hW'_not_m (h' ▸ inf_le_right))
      have hEW'_inf_m : (Γ.E ⊔ W') ⊓ (Γ.U ⊔ Γ.V) = Γ.E := by
        have h1 := sup_inf_assoc_of_le W' hE_m
        rw [h1, hW'_inf_m]; simp
      have : Γ.U = Γ.E := by rw [← hCU_inf_m, h, hEW'_inf_m]
      exact CoordSystem.hEU this.symm)
    (h_sides₂₃ := by
      intro h
      apply hda_not_l
      have hda_le : d_a ≤ d_a ⊔ W' := le_sup_left
      rw [← h] at hda_le
      exact hda_le.trans (sup_le hab_l le_sup_right))
    -- Triangle planes = π
    (hπA := by
      calc Γ.C ⊔ ab ⊔ Γ.U
          = Γ.C ⊔ (ab ⊔ Γ.U) := sup_assoc _ _ _
        _ = Γ.C ⊔ (Γ.O ⊔ Γ.U) := by rw [habU_eq_l]
        _ = (Γ.O ⊔ Γ.U) ⊔ Γ.C := sup_comm _ _
        _ = Γ.O ⊔ Γ.U ⊔ Γ.V := hlC_eq_π)
    (_hπB := by
      -- E ⊔ d_a = m (distinct atoms on m); m ⊔ W' = π (W' ∉ m; m ⋖ π)
      have hm_covBy_π : Γ.U ⊔ Γ.V ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := Γ.m_covBy_π
      have hEda_eq_m : Γ.E ⊔ d_a = Γ.U ⊔ Γ.V := by
        have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
        have h := line_covers_its_atoms Γ.hU Γ.hV hUV Γ.hE_atom hE_m
        have h' := (atom_covBy_join Γ.hE_atom hda_atom hda_ne_E.symm).lt
        exact (h.eq_or_eq h'.le (sup_le hE_m hda_m)).resolve_left (ne_of_gt h')
      have hW'_lt : Γ.U ⊔ Γ.V < (Γ.U ⊔ Γ.V) ⊔ W' :=
        lt_of_le_of_ne le_sup_left (fun h => hW'_not_m (h ▸ le_sup_right))
      have h_le : (Γ.U ⊔ Γ.V) ⊔ W' ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := sup_le hm_π hW'_π
      have hm_sup_W' : (Γ.U ⊔ Γ.V) ⊔ W' = Γ.O ⊔ Γ.U ⊔ Γ.V :=
        (hm_covBy_π.eq_or_eq hW'_lt.le h_le).resolve_left (ne_of_gt hW'_lt)
      calc Γ.E ⊔ d_a ⊔ W' = (Γ.U ⊔ Γ.V) ⊔ W' := by rw [hEda_eq_m]
        _ = Γ.O ⊔ Γ.U ⊔ Γ.V := hm_sup_W')
    -- Center ≠ triangle vertices
    (hoa₁ := hσb_ne_C)
    (hoa₂ := by
      intro h
      exact hab_ne_O ((Γ.hO.le_iff.mp
        (hkl_eq_O ▸ le_inf (h ▸ hσb_k) hab_l)).resolve_left hab_atom.1))
    (hoa₃ := fun h => hσb_not_m (h.symm ▸ (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)))
    (hob₁ := fun h => hσb_not_m (h.symm ▸ Γ.hE_on_m))
    (hob₂ := fun h => hσb_not_m (h.symm ▸ (show d_a ≤ Γ.U ⊔ Γ.V from inf_le_right)))
    (hob₃ := hσb_ne_W')
    -- Corresponding vertices distinct (within perspectivity)
    (ha₁b₁ := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m))
    (ha₂b₂ := by
      intro h
      have hab_m : ab ≤ Γ.U ⊔ Γ.V := by rw [h]; exact inf_le_right
      exact hab_ne_U (Γ.atom_on_both_eq_U hab_atom hab_l hab_m))
    (_ha₃b₃ := hW'_ne_U.symm)
    (R := R) (hR := hR) (hR_not := hR_not)
    (h_irred := h_irred)
    -- Side lines covered by π
    (h_cov₁₂ := by
      -- C⊔ab ⋖ π: U ∉ C⊔ab; U⊔(C⊔ab) = U⊔ab⊔C = l⊔C = π.
      have hU_not_Cab : Γ.U ⊓ (Γ.C ⊔ ab) = ⊥ := by
        rcases Γ.hU.le_iff.mp inf_le_left with h | h
        · exact h
        · exfalso
          have hU_le : Γ.U ≤ Γ.C ⊔ ab := h ▸ inf_le_right
          have hab_ne_C : ab ≠ Γ.C := fun h' => Γ.hC_not_l (h' ▸ hab_l)
          have hCU : Γ.C ≠ Γ.U :=
            fun h' => Γ.hC_not_l (h' ▸ (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U))
          have habC_eq_abU : ab ⊔ Γ.C = ab ⊔ Γ.U :=
            line_eq_of_atom_le hab_atom Γ.hC Γ.hU hab_ne_C hab_ne_U hCU
              (by rw [sup_comm]; exact hU_le)
          exact Γ.hC_not_l ((le_sup_right : Γ.C ≤ ab ⊔ Γ.C).trans
            (habC_eq_abU.le.trans (sup_le hab_l (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U))))
      have h := covBy_sup_of_inf_covBy_left (hU_not_Cab ▸ Γ.hU.bot_covBy)
      -- U ⊔ (C ⊔ ab) = C ⊔ ab ⊔ U = ... = π
      have h_eq : Γ.U ⊔ (Γ.C ⊔ ab) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
        calc Γ.U ⊔ (Γ.C ⊔ ab) = Γ.C ⊔ (ab ⊔ Γ.U) := by
              simp only [sup_comm, sup_left_comm]
          _ = Γ.C ⊔ (Γ.O ⊔ Γ.U) := by rw [habU_eq_l]
          _ = (Γ.O ⊔ Γ.U) ⊔ Γ.C := sup_comm _ _
          _ = Γ.O ⊔ Γ.U ⊔ Γ.V := hlC_eq_π
      rwa [h_eq] at h)
    (_h_cov₁₃ := by
      -- C⊔U ⋖ π: V ∉ C⊔U; V⊔(C⊔U) = C⊔m = π.
      have hV_not_CU : Γ.V ⊓ (Γ.C ⊔ Γ.U) = ⊥ := by
        rcases Γ.hV.le_iff.mp inf_le_left with h | h
        · exact h
        · exfalso
          have hV_le : Γ.V ≤ Γ.C ⊔ Γ.U := h ▸ inf_le_right
          have hU_ne_C : Γ.U ≠ Γ.C :=
            fun h' => Γ.hC_not_l (h'.symm ▸ (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U))
          have hCV : Γ.C ≠ Γ.V := fun h' => Γ.hC_not_m (h' ▸ le_sup_right)
          have hUV : Γ.U ≠ Γ.V := fun h' => Γ.hV_off (h' ▸ le_sup_right)
          have hUC_eq_UV : Γ.U ⊔ Γ.C = Γ.U ⊔ Γ.V :=
            line_eq_of_atom_le Γ.hU Γ.hC Γ.hV hU_ne_C hUV hCV
              (by rw [sup_comm]; exact hV_le)
          exact Γ.hC_not_m ((le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C).trans hUC_eq_UV.le)
      have h := covBy_sup_of_inf_covBy_left (hV_not_CU ▸ Γ.hV.bot_covBy)
      have h_eq : Γ.V ⊔ (Γ.C ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
        calc Γ.V ⊔ (Γ.C ⊔ Γ.U) = Γ.C ⊔ (Γ.U ⊔ Γ.V) := by
              simp only [sup_comm, sup_left_comm]
          _ = (Γ.U ⊔ Γ.V) ⊔ Γ.C := sup_comm _ _
          _ = Γ.O ⊔ Γ.U ⊔ Γ.V := Γ.m_sup_C_eq_π
      rwa [h_eq] at h)
    (_h_cov₂₃ := habU_eq_l ▸ hl_covBy_π)

/-! ## Bridge scaffolding (session 118, 2026-04-24)

Builds on the session 114 architectural finding and the session 117
`_scratch_forward_planar_call`. Consumes the axis output and derives the
left distributivity equation modulo a concurrence hypothesis
(`h_concur : W' ≤ σ_s ⊔ d_a`).

The bridge structure encodes the session 114 plan:

  desargues_planar gives axis with three collinear points:
    P₁ = (ab⊔C)⊓m       (first return-perspectivity intermediate)
    P₂ = (ac⊔E)⊓q       (second return-perspectivity intermediate)
    P₃ = l⊓(d_a⊔W')     (the target atom on l)

  (a) P₁⊔P₂ ⋖ π (distinct atoms on distinct lines through U)
  (b) collinear_of_common_bound: P₃ ≤ P₁⊔P₂
  (c) coord_add ab ac = (P₁⊔P₂)⊓l, so P₃ = coord_add ab ac (atoms on l)
  (d) Concurrence: σ_s⊔d_a = d_a⊔W' (three atoms on line height 2)
      ⇒ coord_mul a s = (σ_s⊔d_a)⊓l = (d_a⊔W')⊓l = P₃ = coord_add ab ac

What's still required after this bridge: a standalone proof of
`h_concur`. Session 114's suggestion — derive concurrence from the
axis itself — is not realized here; the concurrence remains an
auxiliary hypothesis. See `coord_mul_left_distrib`'s `h_concurrence`
(which still has a Level 2 sub-sorry at line ~2159) for the
current direct-proof attempt.

This scaffolding contains targeted sub-sorries for each tractable
lattice step; the intent is that each is a short, self-contained
modular-lattice argument that a future session can discharge.
-/

private theorem _scratch_left_distrib_via_axis (Γ : CoordSystem L)
    (a b c : L)
    (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hs_ne_O : coord_add Γ b c ≠ Γ.O) (hs_ne_U : coord_add Γ b c ≠ Γ.U)
    (hab_ne_O : coord_mul Γ a b ≠ Γ.O) (hab_ne_U : coord_mul Γ a b ≠ Γ.U)
    (hac_ne_O : coord_mul Γ a c ≠ Γ.O) (hac_ne_U : coord_mul Γ a c ≠ Γ.U)
    (hab_ne_ac : coord_mul Γ a b ≠ coord_mul Γ a c)
    (has_ne_O : coord_mul Γ a (coord_add Γ b c) ≠ Γ.O)
    (has_ne_U : coord_mul Γ a (coord_add Γ b c) ≠ Γ.U)
    (habac_ne_O : coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) ≠ Γ.O)
    (habac_ne_U : coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) ≠ Γ.U)
    (hb_ne_I : b ≠ Γ.I)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q)
    -- Concurrence: W' ≤ σ_s ⊔ d_a (the remaining gap)
    (h_concur :
      ((Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ⊔ Γ.U) ⊓ (coord_mul Γ a c ⊔ Γ.E)
        ≤ (Γ.O ⊔ Γ.C) ⊓ (coord_add Γ b c ⊔ Γ.E_I)
            ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) :
    coord_mul Γ a (coord_add Γ b c)
      = coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) := by
  -- Shorthand for the key atoms
  set l := Γ.O ⊔ Γ.U with hl_def
  set m := Γ.U ⊔ Γ.V with hm_def
  set q := Γ.U ⊔ Γ.C with hq_def
  set k := Γ.O ⊔ Γ.C with hk_def
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ_def
  set s := coord_add Γ b c with hs_def
  set ab := coord_mul Γ a b with hab_def
  set ac := coord_mul Γ a c with hac_def
  set σ_b := (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) with hσb_def
  set σ_s := (Γ.O ⊔ Γ.C) ⊓ (s ⊔ Γ.E_I) with hσs_def
  set d_a := (a ⊔ Γ.C) ⊓ m with hda_def
  set W' := (σ_b ⊔ Γ.U) ⊓ (ac ⊔ Γ.E) with hW'_def
  -- ═══ Step 1: Invoke the scratch to obtain the axis ═══
  obtain ⟨axis, h_axis_le, h_axis_ne, h_P1_raw, h_P2_raw, h_P3_raw⟩ :=
    _scratch_forward_planar_call Γ a b c ha hb hc ha_on hb_on hc_on
      ha_ne_O hb_ne_O hc_ne_O ha_ne_U hb_ne_U hc_ne_U
      hab_ne_O hab_ne_U hac_ne_O hac_ne_U hb_ne_I
      R hR hR_not h_irred
  -- ═══ Step 2: Atomicity / non-degeneracy ═══
  have hab_atom : IsAtom ab :=
    coord_mul_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
  have hac_atom : IsAtom ac :=
    coord_mul_atom Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U
  have hs_atom : IsAtom s :=
    coord_add_atom Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U
  have hab_l : ab ≤ l := by show coord_mul Γ a b ≤ l; unfold coord_mul; exact inf_le_right
  have hac_l : ac ≤ l := by show coord_mul Γ a c ≤ l; unfold coord_mul; exact inf_le_right
  have hs_l : s ≤ l := by show coord_add Γ b c ≤ l; unfold coord_add; exact inf_le_right
  have has_l : coord_mul Γ a s ≤ l := by
    show coord_mul Γ a s ≤ l; unfold coord_mul; exact inf_le_right
  have has_atom : IsAtom (coord_mul Γ a s) :=
    coord_mul_atom Γ a s ha hs_atom ha_on hs_l ha_ne_O hs_ne_O ha_ne_U hs_ne_U
  have habac_atom : IsAtom (coord_add Γ ab ac) :=
    coord_add_atom Γ ab ac hab_atom hac_atom hab_l hac_l
      hab_ne_O hac_ne_O hab_ne_U hac_ne_U
  -- ═══ Step 3: Plane memberships (used below) ═══
  have hk_π : k ≤ π := sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane
  have hm_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hq_π : q ≤ π :=
    sup_le (le_sup_right.trans le_sup_left) (Γ.hC_plane)
  have hl_π : l ≤ π := le_sup_left
  have hE_m : Γ.E ≤ m := Γ.hE_on_m
  have hE_k : Γ.E ≤ k := Γ.hE_le_OC
  have hE_π : Γ.E ≤ π := hE_m.trans hm_π
  have hda_m : d_a ≤ m := inf_le_right
  have hσb_k : σ_b ≤ k := inf_le_left
  have hσs_k : σ_s ≤ k := inf_le_left
  have hab_π : ab ≤ π := hab_l.trans hl_π
  have hac_π : ac ≤ π := hac_l.trans hl_π
  have hU_π : Γ.U ≤ π := le_sup_right.trans le_sup_left
  have hσb_π : σ_b ≤ π := hσb_k.trans hk_π
  have hσs_π : σ_s ≤ π := hσs_k.trans hk_π
  have hda_π : d_a ≤ π := hda_m.trans hm_π
  have hW'_le_acE : W' ≤ ac ⊔ Γ.E := inf_le_right
  have hW'_π : W' ≤ π := hW'_le_acE.trans (sup_le hac_π hE_π)
  -- ═══ Step 4: Simplification identities for the axis points ═══
  -- Shared non-degeneracies used across the axis-point simplifications
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hkl_eq_O : k ⊓ l = Γ.O := by
    rw [inf_comm]; exact modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU
      (fun h => Γ.hC_not_l (h ▸ le_sup_left))
      (fun h => Γ.hC_not_l (h.symm.le.trans le_sup_right)) Γ.hC_not_l
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hUV_ne : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  -- (a) d_a ≠ E, hence E ⊔ d_a = m   (two distinct atoms on m)
  have hda_ne_E : d_a ≠ Γ.E := by
    intro h
    have ha_inf_k : a ⊓ k = ⊥ :=
      (ha.le_iff.mp inf_le_left).resolve_right
        (fun h' => ha_ne_O ((Γ.hO.le_iff.mp
          (hkl_eq_O ▸ le_inf (h' ▸ inf_le_right) ha_on)).resolve_left ha.1))
    have haC_inf_k : (a ⊔ Γ.C) ⊓ k = Γ.C := by
      rw [sup_comm, inf_comm]
      have h1 := sup_inf_assoc_of_le a (le_sup_right : Γ.C ≤ k)
      rw [ha_inf_k] at h1; simp at h1; rw [inf_comm] at h1; exact h1
    exact Γ.hC_not_m ((Γ.hC.le_iff.mp
      (haC_inf_k ▸ le_inf (h ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)) hE_k)).resolve_left
      Γ.hE_atom.1 ▸ hE_m)
  have hda_atom : IsAtom d_a :=
    perspect_atom Γ.hC ha ha_ne_C Γ.hU Γ.hV hUV_ne Γ.hC_not_m
      (sup_le (ha_on.trans (le_sup_left.trans Γ.m_sup_C_eq_π.symm.le)) le_sup_right)
  have hEda_eq_m : Γ.E ⊔ d_a = m := by
    have h := line_covers_its_atoms Γ.hU Γ.hV hUV_ne Γ.hE_atom hE_m
    exact (h.eq_or_eq (atom_covBy_join Γ.hE_atom hda_atom hda_ne_E.symm).lt.le
      (sup_le hE_m hda_m)).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hE_atom hda_atom hda_ne_E.symm).lt)
  -- (b) C ⊔ U = q
  have hCU_eq_q : Γ.C ⊔ Γ.U = q := by rw [hq_def]; exact sup_comm Γ.C Γ.U
  -- (c) σ_b atomicity and E ⊔ W' = ac ⊔ E
  have hac_ne_E : ac ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hac_l)
  have hσb_atom : IsAtom σ_b := by
    rw [show σ_b = (b ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) from inf_comm _ _]
    have hb_ne_EI : b ≠ Γ.E_I :=
      fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h ▸ Γ.hE_I_on_m))
    have hEI_sup_OC : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) = π := by
      have h_lt : Γ.O ⊔ Γ.C < Γ.E_I ⊔ (Γ.O ⊔ Γ.C) :=
        lt_of_le_of_ne le_sup_right (fun h => Γ.hE_I_not_OC (h ▸ le_sup_left))
      exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
        (sup_le (Γ.hE_I_on_m.trans hm_π) hk_π)).resolve_left (ne_of_gt h_lt)
    exact perspect_atom Γ.hE_I_atom hb hb_ne_EI Γ.hO Γ.hC hOC Γ.hE_I_not_OC
      (sup_comm (Γ.O ⊔ Γ.C) Γ.E_I ▸ hEI_sup_OC ▸
        sup_le (hb_on.trans le_sup_left) (Γ.hE_I_on_m.trans hm_π))
  have hσb_not_m : ¬ σ_b ≤ m := by
    intro h
    have hb_inf_m : b ⊓ m = ⊥ := (hb.le_iff.mp inf_le_left).resolve_right
      (fun h' => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h' ▸ inf_le_right)))
    have hbEI_inf_m : (b ⊔ Γ.E_I) ⊓ m = Γ.E_I := by
      rw [sup_comm]; have h1 := sup_inf_assoc_of_le b Γ.hE_I_on_m
      rw [h1, hb_inf_m]; simp
    exact Γ.hE_I_not_OC ((Γ.hE_I_atom.le_iff.mp
      (hbEI_inf_m ▸ le_inf (inf_le_right : σ_b ≤ b ⊔ Γ.E_I) h)).resolve_left
      hσb_atom.1 ▸ hσb_k)
  have hσb_ne_U : σ_b ≠ Γ.U := fun h => hσb_not_m (h ▸ le_sup_left)
  have hσb_inf_m : σ_b ⊓ m = ⊥ :=
    (hσb_atom.le_iff.mp inf_le_left).resolve_right
      (fun h => hσb_not_m (h ▸ inf_le_right))
  have hσbU_inf_m : (σ_b ⊔ Γ.U) ⊓ m = Γ.U := by
    rw [sup_comm]
    have h1 := sup_inf_assoc_of_le σ_b (le_sup_left : Γ.U ≤ m)
    rw [hσb_inf_m] at h1; simp at h1; exact h1
  have hU_disj_acE : Γ.U ⊓ (ac ⊔ Γ.E) = ⊥ := by
    rcases Γ.hU.le_iff.mp inf_le_left with h | h
    · exact h
    · exfalso
      have hac_sup_U : ac ⊔ Γ.U = l :=
        ((line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hac_atom hac_l).eq_or_eq
          (atom_covBy_join hac_atom Γ.hU hac_ne_U).lt.le
          (sup_le hac_l le_sup_right)).resolve_left
          (ne_of_gt (atom_covBy_join hac_atom Γ.hU hac_ne_U).lt)
      have hl_le : l ≤ ac ⊔ Γ.E := hac_sup_U ▸ sup_le le_sup_left (h ▸ inf_le_right)
      have hl_eq : l = ac ⊔ Γ.E := ((atom_covBy_join hac_atom Γ.hE_atom hac_ne_E).eq_or_eq
        hac_l hl_le).resolve_left (fun h' => hac_ne_U ((hac_atom.le_iff.mp
          (h' ▸ (le_sup_right : Γ.U ≤ l))).resolve_left Γ.hU.1).symm)
      exact CoordSystem.hE_not_l (hl_eq ▸ le_sup_right)
  have hU_not_acE : ¬ Γ.U ≤ ac ⊔ Γ.E := fun h =>
    Γ.hU.1 (le_antisymm (hU_disj_acE ▸ le_inf le_rfl h) bot_le)
  have hac_sup_U : ac ⊔ Γ.U = l :=
    ((line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hac_atom hac_l).eq_or_eq
      (atom_covBy_join hac_atom Γ.hU hac_ne_U).lt.le
      (sup_le hac_l le_sup_right)).resolve_left
      (ne_of_gt (atom_covBy_join hac_atom Γ.hU hac_ne_U).lt)
  have hV_disj_l : Γ.V ⊓ l = ⊥ :=
    (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
  have hl_covBy_π : l ⋖ π := by
    have h := covBy_sup_of_inf_covBy_left (hV_disj_l ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ l = π from by
      show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V; simp only [sup_comm, sup_left_comm]] at h
  have hl_sup_E : l ⊔ Γ.E = π :=
    (hl_covBy_π.eq_or_eq
      (lt_of_le_of_ne le_sup_left (fun h => CoordSystem.hE_not_l (h ▸ le_sup_right))).le
      (sup_le le_sup_left hE_π)).resolve_left
      (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h => CoordSystem.hE_not_l (h ▸ le_sup_right))))
  have hacE_covBy : ac ⊔ Γ.E ⋖ π := by
    have h := covBy_sup_of_inf_covBy_left (hU_disj_acE ▸ Γ.hU.bot_covBy)
    rwa [show Γ.U ⊔ (ac ⊔ Γ.E) = π from by
      calc Γ.U ⊔ (ac ⊔ Γ.E) = (ac ⊔ Γ.U) ⊔ Γ.E := by simp only [sup_assoc, sup_comm]
        _ = l ⊔ Γ.E := by rw [hac_sup_U]
        _ = π := hl_sup_E] at h
  have hσbU_not_acE : ¬ σ_b ⊔ Γ.U ≤ ac ⊔ Γ.E := fun h =>
    Γ.hU.1 (le_antisymm (hU_disj_acE ▸ le_inf le_rfl (le_sup_right.trans h)) bot_le)
  have hW'_atom : IsAtom W' := by
    have hW'_pos : ⊥ < W' := by
      rw [show W' = (ac ⊔ Γ.E) ⊓ (σ_b ⊔ Γ.U) from inf_comm _ _]
      exact bot_lt_iff_ne_bot.mpr
        (lines_meet_if_coplanar hacE_covBy (sup_le hσb_π hU_π) hσbU_not_acE hσb_atom
          (atom_covBy_join hσb_atom Γ.hU hσb_ne_U).lt)
    have hW'_lt : W' < ac ⊔ Γ.E := by
      refine lt_of_le_of_ne hW'_le_acE (fun h_eq => ?_)
      have hacE_le : ac ⊔ Γ.E ≤ σ_b ⊔ Γ.U := h_eq ▸ (inf_le_left : W' ≤ σ_b ⊔ Γ.U)
      have hE_le : Γ.E ≤ σ_b ⊔ Γ.U := le_sup_right.trans hacE_le
      exact CoordSystem.hEU ((Γ.hU.le_iff.mp
        (hσbU_inf_m ▸ le_inf hE_le hE_m)).resolve_left Γ.hE_atom.1)
    exact line_height_two hac_atom Γ.hE_atom hac_ne_E hW'_pos hW'_lt
  have hW'_le_σbU : W' ≤ σ_b ⊔ Γ.U := inf_le_left
  have hW'_ne_E : W' ≠ Γ.E := fun h =>
    CoordSystem.hEU ((Γ.hU.le_iff.mp
      (hσbU_inf_m ▸ le_inf (h ▸ hW'_le_σbU) hE_m)).resolve_left Γ.hE_atom.1)
  have hEW'_eq_acE : Γ.E ⊔ W' = ac ⊔ Γ.E := by
    have h_lt : Γ.E < Γ.E ⊔ W' :=
      lt_of_le_of_ne le_sup_left (fun h =>
        hW'_ne_E ((Γ.hE_atom.le_iff.mp (h.symm ▸ le_sup_right)).resolve_left hW'_atom.1))
    have h_le : Γ.E ⊔ W' ≤ ac ⊔ Γ.E := sup_le le_sup_right hW'_le_acE
    rw [show ac ⊔ Γ.E = Γ.E ⊔ ac from sup_comm _ _]
    have h_cov' : Γ.E ⋖ Γ.E ⊔ ac := atom_covBy_join Γ.hE_atom hac_atom hac_ne_E.symm
    exact (h_cov'.eq_or_eq h_lt.le
      (by rw [show Γ.E ⊔ ac = ac ⊔ Γ.E from sup_comm _ _]; exact h_le)).resolve_left
      (ne_of_gt h_lt)
  -- (d) ab ⊔ U = l  (distinct atoms on l)
  have habU_eq_l : ab ⊔ Γ.U = l := by
    have h1 : Γ.U ⊔ Γ.O = Γ.U ⊔ ab :=
      line_eq_of_atom_le Γ.hU Γ.hO hab_atom Γ.hOU.symm hab_ne_U.symm hab_ne_O.symm
        (le_of_le_of_eq hab_l (sup_comm _ _))
    rw [sup_comm ab Γ.U, ← h1, sup_comm Γ.U Γ.O]
  -- Simplified axis points
  set P₁ := (ab ⊔ Γ.C) ⊓ m with hP1_def
  set P₂ := (ac ⊔ Γ.E) ⊓ q with hP2_def
  set P₃ := l ⊓ (d_a ⊔ W') with hP3_def
  -- The three raw axis points simplify to P₁, P₂, P₃ using hEda_eq_m, hEW'_eq_acE,
  -- habU_eq_l, hCU_eq_q, and an inf_comm for P₂.
  have h_P1 : P₁ ≤ axis := by
    have h_eq : (Γ.C ⊔ ab) ⊓ (Γ.E ⊔ d_a) = P₁ := by
      rw [hP1_def, hEda_eq_m, sup_comm Γ.C ab]
    exact h_eq ▸ h_P1_raw
  have h_P2 : P₂ ≤ axis := by
    have h_eq : (Γ.C ⊔ Γ.U) ⊓ (Γ.E ⊔ W') = P₂ := by
      rw [hEW'_eq_acE, hCU_eq_q, hP2_def]
      exact inf_comm _ _
    exact h_eq ▸ h_P2_raw
  have h_P3 : P₃ ≤ axis := by
    have h_eq : (ab ⊔ Γ.U) ⊓ (d_a ⊔ W') = P₃ := by
      rw [hP3_def, habU_eq_l]
    exact h_eq ▸ h_P3_raw
  -- ═══ Step 5: P₁⊔P₂ ⋖ π ═══
  -- P₁ atom on m, P₂ atom on q; both distinct from U; U ≰ P₁⊔P₂
  -- (else U⊔P₁ = m and U⊔P₂ = q collapse, forcing m = q). Then
  -- P₁⊔P₂⊔U = π via P₁⊔U = m, P₂⊔U = q, m⊔q = π. Apply line_covBy_plane.
  have hm_cov : m ⋖ π := Γ.m_covBy_π
  have hUC_ne : Γ.U ≠ Γ.C :=
    fun h => Γ.hC_not_l (h.symm ▸ (le_sup_right : Γ.U ≤ l))
  have hC_inf_m : Γ.C ⊓ m = ⊥ :=
    (Γ.hC.le_iff.mp inf_le_left).resolve_right
      (fun h => Γ.hC_not_m (h ▸ inf_le_right))
  have hq_inf_m : q ⊓ m = Γ.U := by
    show (Γ.U ⊔ Γ.C) ⊓ m = Γ.U
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ m)]
    rw [hC_inf_m, sup_bot_eq]
  have hV_disj_q : Γ.V ⊓ q = ⊥ := by
    rcases Γ.hV.le_iff.mp inf_le_left with h | h
    · exact h
    · exfalso
      have hV_le_q : Γ.V ≤ q := h ▸ inf_le_right
      exact hUV_ne ((Γ.hU.le_iff.mp
        (hq_inf_m ▸ le_inf hV_le_q (le_sup_right : Γ.V ≤ m))).resolve_left Γ.hV.1).symm
  have hq_cov : q ⋖ π := by
    have hVq_eq_π : Γ.V ⊔ q = π := by
      show Γ.V ⊔ (Γ.U ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.V
      calc Γ.V ⊔ (Γ.U ⊔ Γ.C)
          = (Γ.U ⊔ Γ.V) ⊔ Γ.C := by simp only [sup_comm, sup_left_comm]
        _ = Γ.O ⊔ Γ.U ⊔ Γ.V := Γ.m_sup_C_eq_π
    exact hVq_eq_π ▸ covBy_sup_of_inf_covBy_left (hV_disj_q ▸ Γ.hV.bot_covBy)
  -- P₁ atom (from line_meets_m_at_atom applied to ab⊔C meeting m)
  have hab_ne_C : ab ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hab_l)
  have hab_not_m : ¬ ab ≤ m :=
    fun h => hab_ne_U (Γ.atom_on_both_eq_U hab_atom hab_l h)
  have hP1_atom : IsAtom P₁ := by
    rw [hP1_def]
    exact line_meets_m_at_atom hab_atom Γ.hC hab_ne_C
      (sup_le hab_π Γ.hC_plane) hm_π hm_cov hab_not_m
  -- P₂ atom (from line_meets_m_at_atom applied to ac⊔E meeting q)
  have hlq_eq_U : l ⊓ q = Γ.U := by
    rw [inf_comm, hq_inf_m.symm]
    show q ⊓ l = q ⊓ m
    rw [hq_inf_m]
    -- q ⊓ l = (U ⊔ C) ⊓ l; C ⊓ l = ⊥, so = U ⊔ ⊥ = U
    rw [hq_def, sup_inf_assoc_of_le Γ.C (le_sup_right : Γ.U ≤ l)]
    have : Γ.C ⊓ l = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right
        (fun h => Γ.hC_not_l (h ▸ inf_le_right))
    rw [this, sup_bot_eq]
  have hac_not_q : ¬ ac ≤ q := fun h => hac_ne_U
    ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf hac_l h)).resolve_left hac_atom.1)
  have hP2_atom : IsAtom P₂ := by
    rw [hP2_def]
    exact line_meets_m_at_atom hac_atom Γ.hE_atom hac_ne_E
      (sup_le hac_π hE_π) hq_π hq_cov hac_not_q
  -- P₁ ≠ U
  have hP1_ne_U : P₁ ≠ Γ.U := by
    intro h
    -- P₁ = (ab⊔C) ⊓ m = U. So U ≤ ab⊔C.
    -- (ab⊔C) ⊓ l = ab (modular, C ⊓ l = ⊥).
    -- U ≤ ab⊔C and U ≤ l, so U ≤ ab. ab atom, so ab = U. Contradiction.
    have hU_le_abC : Γ.U ≤ ab ⊔ Γ.C :=
      h ▸ (inf_le_left : P₁ ≤ ab ⊔ Γ.C)
    have hC_inf_l : Γ.C ⊓ l = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right
        (fun h' => Γ.hC_not_l (h' ▸ inf_le_right))
    have habC_inf_l : (ab ⊔ Γ.C) ⊓ l = ab := by
      have h1 := sup_inf_assoc_of_le Γ.C hab_l
      rw [hC_inf_l] at h1; simp at h1; exact h1
    have hU_le_ab : Γ.U ≤ ab :=
      habC_inf_l ▸ le_inf hU_le_abC (le_sup_right : Γ.U ≤ l)
    exact hab_ne_U ((hab_atom.le_iff.mp hU_le_ab).resolve_left Γ.hU.1).symm
  -- P₂ ≠ U
  have hP2_ne_U : P₂ ≠ Γ.U := by
    intro h
    have hU_le_acE : Γ.U ≤ ac ⊔ Γ.E :=
      h ▸ (inf_le_left : P₂ ≤ ac ⊔ Γ.E)
    exact Γ.hU.1 (le_antisymm (hU_disj_acE ▸ le_inf le_rfl hU_le_acE) bot_le)
  -- P₁ ≠ P₂
  have hP1_ne_P2 : P₁ ≠ P₂ := by
    intro h
    -- P₁ ≤ m, P₂ ≤ q; if P₁ = P₂ then P₁ ≤ m ⊓ q = U, so P₁ = U.
    have hP1_le_m : P₁ ≤ m := inf_le_right
    have hP2_le_q : P₂ ≤ q := by rw [hP2_def]; exact inf_le_right
    have hP1_le_mq : P₁ ≤ m ⊓ q := le_inf hP1_le_m (h ▸ hP2_le_q)
    have hmq_eq_U : m ⊓ q = Γ.U := by rw [inf_comm]; exact hq_inf_m
    exact hP1_ne_U ((Γ.hU.le_iff.mp (hmq_eq_U ▸ hP1_le_mq)).resolve_left hP1_atom.1)
  -- U ≰ P₁⊔P₂ (else line-uniqueness collapses m = q)
  have hU_not_P1P2 : ¬ Γ.U ≤ P₁ ⊔ P₂ := by
    intro hU_le
    -- Line U⊔P₁ contains U, P₁. Line U⊔P₂ contains U, P₂. Both ≤ P₁⊔P₂.
    -- U⊔P₁ ≤ m (both atoms on m, line height 2 → =m).
    -- U⊔P₂ ≤ q (both atoms on q, line height 2 → =q).
    -- If U, P₁, P₂ collinear (U ≤ P₁⊔P₂), then U⊔P₁ = U⊔P₂ (both lines through
    -- U containing P₁, P₂ respectively). So m = q. Contradiction.
    have hP1_le_m : P₁ ≤ m := inf_le_right
    have hP2_le_q : P₂ ≤ q := by rw [hP2_def]; exact inf_le_right
    have hUP1_le_m : Γ.U ⊔ P₁ ≤ m := sup_le le_sup_left hP1_le_m
    have hUP2_le_q : Γ.U ⊔ P₂ ≤ q := sup_le le_sup_left hP2_le_q
    have hcov_UP1 : Γ.U ⋖ Γ.U ⊔ P₁ :=
      atom_covBy_join Γ.hU hP1_atom (Ne.symm hP1_ne_U)
    have hcov_UP2 : Γ.U ⋖ Γ.U ⊔ P₂ :=
      atom_covBy_join Γ.hU hP2_atom (Ne.symm hP2_ne_U)
    -- m: U ⋖ m has height 2 (U, V atoms on m distinct)
    have hcov_Um : Γ.U ⋖ m := by
      rw [hm_def]
      exact atom_covBy_join Γ.hU Γ.hV hUV_ne
    have hcov_Uq : Γ.U ⋖ q := by
      rw [hq_def]
      exact atom_covBy_join Γ.hU Γ.hC hUC_ne
    -- U ⊔ P₁ = m via covBy
    have hUP1_eq_m : Γ.U ⊔ P₁ = m :=
      (hcov_Um.eq_or_eq hcov_UP1.lt.le hUP1_le_m).resolve_left
        (ne_of_gt hcov_UP1.lt)
    have hUP2_eq_q : Γ.U ⊔ P₂ = q :=
      (hcov_Uq.eq_or_eq hcov_UP2.lt.le hUP2_le_q).resolve_left
        (ne_of_gt hcov_UP2.lt)
    -- Line P₁⊔P₂ has height 2 (two distinct atoms)
    have hcov_P1P2 : P₁ ⋖ P₁ ⊔ P₂ :=
      atom_covBy_join hP1_atom hP2_atom hP1_ne_P2
    -- U ⊔ P₁ ≤ P₁ ⊔ P₂ (since U ≤ P₁⊔P₂ and P₁ ≤ P₁⊔P₂)
    have hUP1_le_P1P2 : Γ.U ⊔ P₁ ≤ P₁ ⊔ P₂ := sup_le hU_le le_sup_left
    -- P₁ ⋖ P₁⊔P₂ and U⊔P₁ contains P₁: so U⊔P₁ = P₁ or = P₁⊔P₂
    -- U⊔P₁ ≠ P₁ (U ≠ P₁), so U⊔P₁ = P₁⊔P₂. Hence m = P₁⊔P₂.
    have hUP1_gt_P1 : P₁ < Γ.U ⊔ P₁ :=
      lt_of_le_of_ne le_sup_right (fun h =>
        hP1_ne_U ((hP1_atom.le_iff.mp (h ▸ le_sup_left)).resolve_left Γ.hU.1).symm)
    have hm_eq_P1P2 : m = P₁ ⊔ P₂ := by
      rw [← hUP1_eq_m]
      exact (hcov_P1P2.eq_or_eq hUP1_gt_P1.le hUP1_le_P1P2).resolve_left
        (ne_of_gt hUP1_gt_P1)
    -- Similarly U⊔P₂ ≤ P₁⊔P₂ (by sup_le of hU_le and le_sup_right) and > P₂
    have hUP2_le_P1P2 : Γ.U ⊔ P₂ ≤ P₁ ⊔ P₂ := sup_le hU_le le_sup_right
    have hcov_P1P2' : P₂ ⋖ P₁ ⊔ P₂ := by
      rw [show P₁ ⊔ P₂ = P₂ ⊔ P₁ from sup_comm _ _]
      exact atom_covBy_join hP2_atom hP1_atom (Ne.symm hP1_ne_P2)
    have hUP2_gt_P2 : P₂ < Γ.U ⊔ P₂ :=
      lt_of_le_of_ne le_sup_right (fun h =>
        hP2_ne_U ((hP2_atom.le_iff.mp (h ▸ le_sup_left)).resolve_left Γ.hU.1).symm)
    have hq_eq_P1P2 : q = P₁ ⊔ P₂ := by
      rw [← hUP2_eq_q]
      exact (hcov_P1P2'.eq_or_eq hUP2_gt_P2.le hUP2_le_P1P2).resolve_left
        (ne_of_gt hUP2_gt_P2)
    -- m = P₁⊔P₂ = q → m = q → U⊔V = U⊔C → V ≤ U⊔C → contradiction via
    -- already-proven V ⊓ q = ⊥.
    have hm_eq_q : m = q := hm_eq_P1P2.trans hq_eq_P1P2.symm
    have hV_le_q : Γ.V ≤ q := hm_eq_q ▸ (le_sup_right : Γ.V ≤ m)
    exact Γ.hV.1 (le_antisymm (hV_disj_q ▸ le_inf le_rfl hV_le_q) bot_le)
  -- P₁⊔P₂⊔U = π: P₁⊔U ≥ line ⊇ m (via UP1_eq_m above), similarly q. m⊔q = π.
  have hP1P2U_eq_π : P₁ ⊔ P₂ ⊔ Γ.U = π := by
    -- From above: U⊔P₁ = m, U⊔P₂ = q.
    have hP1_le_m : P₁ ≤ m := inf_le_right
    have hP2_le_q : P₂ ≤ q := by rw [hP2_def]; exact inf_le_right
    have hcov_UP1 : Γ.U ⋖ Γ.U ⊔ P₁ :=
      atom_covBy_join Γ.hU hP1_atom (Ne.symm hP1_ne_U)
    have hcov_UP2 : Γ.U ⋖ Γ.U ⊔ P₂ :=
      atom_covBy_join Γ.hU hP2_atom (Ne.symm hP2_ne_U)
    have hcov_Um : Γ.U ⋖ m := by
      rw [hm_def]; exact atom_covBy_join Γ.hU Γ.hV hUV_ne
    have hcov_Uq : Γ.U ⋖ q := by
      rw [hq_def]; exact atom_covBy_join Γ.hU Γ.hC hUC_ne
    have hUP1_le_m : Γ.U ⊔ P₁ ≤ m := sup_le le_sup_left hP1_le_m
    have hUP2_le_q : Γ.U ⊔ P₂ ≤ q := sup_le le_sup_left hP2_le_q
    have hUP1_eq_m : Γ.U ⊔ P₁ = m :=
      (hcov_Um.eq_or_eq hcov_UP1.lt.le hUP1_le_m).resolve_left
        (ne_of_gt hcov_UP1.lt)
    have hUP2_eq_q : Γ.U ⊔ P₂ = q :=
      (hcov_Uq.eq_or_eq hcov_UP2.lt.le hUP2_le_q).resolve_left
        (ne_of_gt hcov_UP2.lt)
    -- m ⊔ q = π (using Γ.m_sup_C_eq_π)
    have hmq_eq_π : m ⊔ q = π := by
      show m ⊔ (Γ.U ⊔ Γ.C) = π
      calc m ⊔ (Γ.U ⊔ Γ.C)
          = m ⊔ Γ.C := by rw [show Γ.U ⊔ Γ.C = Γ.C ⊔ Γ.U from sup_comm _ _,
                               ← sup_assoc, show m ⊔ Γ.C = Γ.C ⊔ m from sup_comm _ _,
                               sup_assoc, sup_of_le_left (le_sup_left : Γ.U ≤ m),
                               show Γ.C ⊔ m = m ⊔ Γ.C from sup_comm _ _]
        _ = π := Γ.m_sup_C_eq_π
    have hP1_le_π : P₁ ≤ π := hP1_le_m.trans hm_π
    have hP2_le_π : P₂ ≤ π := hP2_le_q.trans hq_π
    apply le_antisymm
    · exact sup_le (sup_le hP1_le_π hP2_le_π) hU_π
    · -- π = m ⊔ q ≤ (U⊔P₁) ⊔ (U⊔P₂) ≤ P₁ ⊔ P₂ ⊔ U
      have hm_le : m ≤ P₁ ⊔ P₂ ⊔ Γ.U := by
        rw [← hUP1_eq_m]
        exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
      have hq_le : q ≤ P₁ ⊔ P₂ ⊔ Γ.U := by
        rw [← hUP2_eq_q]
        exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
      exact hmq_eq_π ▸ sup_le hm_le hq_le
  -- line_covBy_plane: P₁⊔P₂ ⋖ P₁⊔P₂⊔U; combined with = π
  have hP1P2_cov : P₁ ⊔ P₂ ⋖ π := by
    have h := line_covBy_plane hP1_atom hP2_atom Γ.hU
      hP1_ne_P2 hP1_ne_U hP2_ne_U hU_not_P1P2
    rwa [hP1P2U_eq_π] at h
  -- ═══ Step 6: P₃ ≤ P₁⊔P₂ via collinear_of_common_bound ═══
  have hP3_le_P1P2 : P₃ ≤ P₁ ⊔ P₂ :=
    collinear_of_common_bound hP1P2_cov h_axis_le h_axis_ne
      h_P1 h_P2 h_P3
  -- ═══ Step 7: coord_add ab ac = (P₁⊔P₂) ⊓ l (by definition of coord_add) ═══
  have hcoord_add_eq : coord_add Γ ab ac = (P₁ ⊔ P₂) ⊓ l := by
    unfold coord_add; rfl
  -- ═══ Step 8: Concurrence → coord_mul a s ≤ d_a ⊔ W' ═══
  -- coord_mul a s = (σ_s ⊔ d_a) ⊓ l by definition. So coord_mul a s ≤ σ_s⊔d_a.
  -- h_concur says W' ≤ σ_s⊔d_a. So d_a⊔W' ≤ σ_s⊔d_a.
  -- Both d_a⊔W' and σ_s⊔d_a strictly cover d_a (atoms W'≠d_a, σ_s≠d_a).
  -- By covBy, d_a⊔W' = σ_s⊔d_a, so coord_mul a s ≤ d_a⊔W'.
  have hσs_atom : IsAtom σ_s := by
    rw [show σ_s = (s ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) from inf_comm _ _]
    have hEI_sup_OC : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) = π := by
      have h_lt : Γ.O ⊔ Γ.C < Γ.E_I ⊔ (Γ.O ⊔ Γ.C) :=
        lt_of_le_of_ne le_sup_right (fun h => Γ.hE_I_not_OC (h ▸ le_sup_left))
      exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
        (sup_le (Γ.hE_I_on_m.trans hm_π) hk_π)).resolve_left (ne_of_gt h_lt)
    exact perspect_atom Γ.hE_I_atom hs_atom
      (fun h => hs_ne_U (Γ.atom_on_both_eq_U hs_atom hs_l (h ▸ Γ.hE_I_on_m)))
      Γ.hO Γ.hC hOC Γ.hE_I_not_OC
      (sup_comm (Γ.O ⊔ Γ.C) Γ.E_I ▸ hEI_sup_OC ▸
        sup_le (hs_l.trans le_sup_left) (Γ.hE_I_on_m.trans hm_π))
  -- k ⊓ m = E (definitional)
  have hkm_eq_E : k ⊓ m = Γ.E := by simp only [hk_def, hm_def]; rfl
  -- σ_s ≠ d_a: else σ_s ∈ k ⊓ m = E, so σ_s = E, so d_a = E, contradiction.
  have hσs_ne_da : σ_s ≠ d_a := by
    intro h
    have hσs_le_m : σ_s ≤ m := h ▸ hda_m
    have hσs_le_E : σ_s ≤ Γ.E := hkm_eq_E ▸ le_inf hσs_k hσs_le_m
    have hσs_eq_E : σ_s = Γ.E :=
      (Γ.hE_atom.le_iff.mp hσs_le_E).resolve_left hσs_atom.1
    exact hda_ne_E (h.symm.trans hσs_eq_E)
  -- W' ≠ d_a: else d_a ≤ ac⊔E, and d_a ≤ m, so d_a ≤ (ac⊔E)⊓m = E, contradiction.
  have hac_inf_m : ac ⊓ m = ⊥ :=
    (hac_atom.le_iff.mp inf_le_left).resolve_right
      (fun h' => hac_ne_U (Γ.atom_on_both_eq_U hac_atom hac_l
        (le_of_eq h'.symm |>.trans inf_le_right)))
  have hacE_inf_m : (ac ⊔ Γ.E) ⊓ m = Γ.E := by
    rw [sup_comm]
    have h1 := sup_inf_assoc_of_le ac hE_m
    rw [hac_inf_m] at h1; simp at h1; exact h1
  have hW'_ne_da : W' ≠ d_a := fun h =>
    hda_ne_E ((Γ.hE_atom.le_iff.mp
      (hacE_inf_m ▸ le_inf (h ▸ hW'_le_acE) hda_m)).resolve_left hda_atom.1)
  have hW'_le_σsda : W' ≤ σ_s ⊔ d_a := h_concur
  have has_le_daW' : coord_mul Γ a s ≤ d_a ⊔ W' := by
    have hcov_daW' : d_a ⋖ d_a ⊔ W' :=
      atom_covBy_join hda_atom hW'_atom (Ne.symm hW'_ne_da)
    have hcov_daσs : d_a ⋖ d_a ⊔ σ_s :=
      atom_covBy_join hda_atom hσs_atom (Ne.symm hσs_ne_da)
    have h_le : d_a ⊔ W' ≤ d_a ⊔ σ_s := by
      rw [show d_a ⊔ σ_s = σ_s ⊔ d_a from sup_comm _ _]
      exact sup_le le_sup_right hW'_le_σsda
    have h_eq : d_a ⊔ W' = d_a ⊔ σ_s :=
      (hcov_daσs.eq_or_eq hcov_daW'.lt.le h_le).resolve_left (ne_of_gt hcov_daW'.lt)
    have has_le_σsda : coord_mul Γ a s ≤ σ_s ⊔ d_a := by
      show coord_mul Γ a s ≤ σ_s ⊔ d_a
      unfold coord_mul; exact inf_le_left
    calc coord_mul Γ a s ≤ σ_s ⊔ d_a := has_le_σsda
      _ = d_a ⊔ σ_s := sup_comm _ _
      _ = d_a ⊔ W' := h_eq.symm
  -- ═══ Step 9: coord_mul a s ≤ P₃ and thus ≤ coord_add ab ac ═══
  have has_le_P3 : coord_mul Γ a s ≤ P₃ := by
    rw [hP3_def]; exact le_inf has_l has_le_daW'
  have has_le_sum : coord_mul Γ a s ≤ coord_add Γ ab ac :=
    hcoord_add_eq ▸ le_inf (has_le_P3.trans hP3_le_P1P2) has_l
  -- ═══ Step 10: Atoms on l → equal ═══
  exact (habac_atom.le_iff.mp has_le_sum).resolve_left has_atom.1

/-! ## The concurrence lemma and the main theorem

The forward Desargues piece and the axis-to-left-distrib bridge are discharged
above. What remains is a standalone proof of the concurrence
`W' ≤ σ_s ⊔ d_a`, stated here as `concurrence` with body `sorry`. The main
theorem `coord_mul_left_distrib` is the one-line composition of the bridge
and the concurrence lemma; it will become fully sorry-free once `concurrence`
is closed.
-/

/-- **Concurrence: `W' ≤ σ_s ⊔ d_a`.**

For triangles T1 = (σ_b, ac, σ_s), T2 = (U, E, d_a) in π, the vertex-joins
`σ_b ⊔ U`, `ac ⊔ E`, and `σ_s ⊔ d_a` meet at a common point; equivalently
`W' = (σ_b ⊔ U) ⊓ (ac ⊔ E)` lies on `σ_s ⊔ d_a`.

Both triangles are coplanar in π (T2 is even collinear on m), and the natural
axis of their side-intersections lies entirely on m. Session 114's Level-1/
Level-2 recursive lift via `desargues_converse_nonplanar` hits a structural
axis-atomicity wall at Level 2 (non-terminating). A different route is
required — e.g., a planar converse Desargues lemma, or a direct construction
exploiting that the axis = m.

Currently `sorry`. This is the sole remaining gap in left distributivity. -/
theorem concurrence (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hbc : b ≠ c)
    (hs_ne_O : coord_add Γ b c ≠ Γ.O) (hs_ne_U : coord_add Γ b c ≠ Γ.U)
    (hab_ne_O : coord_mul Γ a b ≠ Γ.O) (hab_ne_U : coord_mul Γ a b ≠ Γ.U)
    (hac_ne_O : coord_mul Γ a c ≠ Γ.O) (hac_ne_U : coord_mul Γ a c ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    ((Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ⊔ Γ.U) ⊓ (coord_mul Γ a c ⊔ Γ.E)
      ≤ (Γ.O ⊔ Γ.C) ⊓ (coord_add Γ b c ⊔ Γ.E_I)
          ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  sorry

/-- **Left distributivity: `a · (b + c) = a·b + a·c`.**

Composition of the forward-Desargues axis (`_scratch_forward_planar_call`),
the axis-to-left-distrib bridge (`_scratch_left_distrib_via_axis`), and the
concurrence lemma (`concurrence`).

The `hb_ne_I` hypothesis is required because the proof's central
perspectivity center is `σ_b = k ⊓ (b ⊔ E_I)`, which degenerates to `C`
exactly when `b = I` (see `sigma_b_eq_C_imp_b_eq_I`). Callers handling `b = I`
must case-split separately (e.g. by swapping `b` and `c` via `coord_add_comm`). -/
theorem coord_mul_left_distrib (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hbc : b ≠ c)
    (hs_ne_O : coord_add Γ b c ≠ Γ.O) (hs_ne_U : coord_add Γ b c ≠ Γ.U)
    (hab_ne_O : coord_mul Γ a b ≠ Γ.O) (hab_ne_U : coord_mul Γ a b ≠ Γ.U)
    (hac_ne_O : coord_mul Γ a c ≠ Γ.O) (hac_ne_U : coord_mul Γ a c ≠ Γ.U)
    (hab_ne_ac : coord_mul Γ a b ≠ coord_mul Γ a c)
    (has_ne_O : coord_mul Γ a (coord_add Γ b c) ≠ Γ.O)
    (has_ne_U : coord_mul Γ a (coord_add Γ b c) ≠ Γ.U)
    (habac_ne_O : coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) ≠ Γ.O)
    (habac_ne_U : coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) ≠ Γ.U)
    (hb_ne_I : b ≠ Γ.I)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_mul Γ a (coord_add Γ b c) =
      coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) :=
  _scratch_left_distrib_via_axis Γ a b c ha hb hc ha_on hb_on hc_on
    ha_ne_O hb_ne_O hc_ne_O ha_ne_U hb_ne_U hc_ne_U
    hs_ne_O hs_ne_U hab_ne_O hab_ne_U hac_ne_O hac_ne_U
    hab_ne_ac has_ne_O has_ne_U habac_ne_O habac_ne_U
    hb_ne_I R hR hR_not h_irred
    (concurrence Γ a b c ha hb hc ha_on hb_on hc_on
      ha_ne_O hb_ne_O hc_ne_O ha_ne_U hb_ne_U hc_ne_U hbc
      hs_ne_O hs_ne_U hab_ne_O hab_ne_U hac_ne_O hac_ne_U
      R hR hR_not h_irred)

end Foam.FTPGExplore
