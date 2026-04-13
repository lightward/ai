/-
# Additive inverse (coord_neg) and a + (-a) = O

## Construction
  β(a) = (U⊔C) ⊓ (a⊔E)          -- beta-image of a on q
  e_a  = (O ⊔ β(a)) ⊓ m          -- project β(a) from O onto m
  -a   = (C ⊔ e_a) ⊓ l           -- line from C through e_a hits l at -a

## Proof architecture
  coord_add a (-a) = ((a⊔C)⊓m ⊔ ((-a)⊔E)⊓q) ⊓ l.
  Set a' = (a⊔C)⊓m and D = ((-a)⊔E)⊓q.
  The proof shows:
    (1) O ≤ a' ⊔ D (O lies on the line through a' and D)
    (2) a' ⊔ D is a proper line (not the whole plane)
    (3) Therefore (a' ⊔ D) ⊓ l = O.
  The key geometric content for (1): the three perspectivity centers
  O, C, E are collinear (all on the line O⊔C), which forces the
  composition of perspectivities to close.

## Status
  0 sorry. All proven.
  The double Desargues approach (reusing coord_first/second_desargues
  with b = neg_a) superseded the cross_join_on_q approach.
  Key identity: d_{neg_a} = e_a ("double-cover alignment").
-/
import Foam.FTPGMulKeyIdentity
import Foam.FTPGAssoc

namespace Foam.FTPGExplore

universe u
variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-- The additive inverse of a coordinate.
    -a = (C ⊔ e_a) ⊓ l where e_a = (O ⊔ β(a)) ⊓ m, β(a) = (U⊔C) ⊓ (a⊔E). -/
noncomputable def coord_neg (Γ : CoordSystem L) (a : L) : L :=
  (Γ.C ⊔ (Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ Γ.U)

/-- coord_neg is on l. -/
theorem coord_neg_on_l (Γ : CoordSystem L) (a : L) :
    coord_neg Γ a ≤ Γ.O ⊔ Γ.U := by
  unfold coord_neg; exact inf_le_right

/-- l ⋖ π (reusable helper). -/
private theorem l_covBy_π (Γ : CoordSystem L) :
    (Γ.O ⊔ Γ.U) ⋖ (Γ.O ⊔ Γ.U ⊔ Γ.V) := by
  have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
    (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
  have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
  rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this

/-! ## Atom and non-degeneracy lemmas -/

/-- e_a = (O ⊔ β(a)) ⊓ m is an atom. -/
private theorem e_atom (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    IsAtom ((Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V)) := by
  have hβ := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hβ_ne_O : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≠ Γ.O :=
    fun h => beta_not_l Γ ha ha_on ha_ne_O ha_ne_U (h ▸ le_sup_left)
  exact line_meets_m_at_atom Γ.hO hβ hβ_ne_O.symm
    (sup_le (le_sup_left.trans le_sup_left) (beta_plane Γ ha_on))
    (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    Γ.m_covBy_π Γ.hO_not_m

/-- e_a is not on l. -/
private theorem e_not_l (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    ¬ (Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U := by
  have he := e_atom Γ ha ha_on ha_ne_O ha_ne_U
  intro he_l
  have he_eq_U := Γ.atom_on_both_eq_U he he_l inf_le_right
  have hU_le : Γ.U ≤ Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) :=
    le_trans (le_of_eq he_eq_U.symm) inf_le_left
  have hl_le : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := sup_le le_sup_left hU_le
  have hOβ_le_π : Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (le_sup_left.trans le_sup_left) (beta_plane Γ ha_on)
  rcases (l_covBy_π Γ).eq_or_eq hl_le hOβ_le_π with h1 | h2
  · exact beta_not_l Γ ha ha_on ha_ne_O ha_ne_U (le_sup_right.trans h1.le)
  · have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
    have hea_eq_m : (Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V) = Γ.U ⊔ Γ.V := by
      rw [h2]; exact inf_eq_right.mpr (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    have : Γ.U = Γ.U ⊔ Γ.V := he_eq_U.symm.trans hea_eq_m
    exact hUV ((Γ.hU.le_iff.mp (this ▸ le_sup_right : Γ.V ≤ Γ.U)).resolve_left Γ.hV.1).symm

/-- coord_neg is an atom on l. -/
theorem coord_neg_atom (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    IsAtom (coord_neg Γ a) := by
  show IsAtom ((Γ.C ⊔ (Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ Γ.U))
  have he := e_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hC_ne_ea : Γ.C ≠ (Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V) :=
    fun h => Γ.hC_not_m (h ▸ inf_le_right)
  have hCe_le_π : Γ.C ⊔ (Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le Γ.hC_plane (inf_le_right.trans
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  exact line_meets_m_at_atom Γ.hC he hC_ne_ea hCe_le_π
    (show Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.U ⊔ Γ.V from le_sup_left) (l_covBy_π Γ) Γ.hC_not_l

/-! ## The main theorem -/

/-- **Additive left inverse: a + (-a) = O.**

The proof needs to show that the perspectivity chain
  a →[E]→ β_a →[O]→ e_a →[C]→ -a
composes with the addition perspectivities
  a →[C]→ a' on m,  -a →[E]→ D on q
to give (a' ⊔ D) ⊓ l = O.

Key facts used:
- O, C, E are collinear (E = (O⊔C) ⊓ m)
- C-persp(neg_a) = e_a (reverse perspectivity)
- O⊔e_a = O⊔β_a (covering argument)
- (O⊔β_a) ⊓ q = β_a (modular law, O ∉ q)
-/
-- E ⊔ C = O ⊔ C (E and C are distinct atoms on line O⊔C).
private theorem EC_eq_OC (Γ : CoordSystem L) :
    Γ.E ⊔ Γ.C = Γ.O ⊔ Γ.C := by
  have hEC : Γ.E ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hE_le : Γ.E ≤ Γ.O ⊔ Γ.C := CoordSystem.hE_le_OC
  have h_le : Γ.E ⊔ Γ.C ≤ Γ.O ⊔ Γ.C := sup_le hE_le le_sup_right
  have h_lt : Γ.C < Γ.E ⊔ Γ.C :=
    lt_of_le_of_ne le_sup_right (fun h => hEC ((Γ.hC.le_iff.mp
      (le_sup_left.trans h.symm.le)).resolve_left Γ.hE_atom.1))
  have h_cov : Γ.C ⋖ Γ.O ⊔ Γ.C := by
    have := atom_covBy_join Γ.hC Γ.hO hOC.symm; rwa [sup_comm] at this
  exact (h_cov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)

-- (E ⊔ C) ⊓ l = O (the line O⊔C meets l at O).
private theorem EC_inf_l (Γ : CoordSystem L) :
    (Γ.E ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.O := by
  rw [EC_eq_OC]
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hO_le : Γ.O ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left le_sup_left
  have h_lt : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.C := by
    apply lt_of_le_of_ne inf_le_left; intro h
    exact Γ.hC_not_l (le_sup_right.trans (inf_eq_left.mp h))
  exact ((line_height_two Γ.hO Γ.hC hOC
    (lt_of_lt_of_le Γ.hO.bot_lt hO_le) h_lt).le_iff.mp hO_le).resolve_left
    Γ.hO.1 |>.symm

-- Perspectivity from m to l via center C sends E to O:
-- (E ⊔ C) ⊓ l = O.
-- Perspectivity from m to l via center C sends e_a to neg_a:
-- (e_a ⊔ C) ⊓ l = neg_a (by definition of neg_a).
-- Perspectivity from m to l via center C sends d_a to a:
-- (d_a ⊔ C) ⊓ l = a (since d_a ≤ a⊔C by definition).

-- (d_a ⊔ C) ⊓ l = a: the C-perspectivity from m to l sends d_a back to a.
private theorem d_a_persp_back (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) :
    ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = a := by
  -- d_a ⊔ C = a ⊔ C by the covering argument.
  have hAC : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have ha'_ne_bot : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≠ ⊥ := by
    have h_meet := lines_meet_if_coplanar Γ.m_covBy_π
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane)
      (fun h => Γ.hC_not_m (le_trans le_sup_right h))
      ha (lt_of_le_of_ne le_sup_left
        (fun h => hAC ((ha.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm))
    rwa [@inf_comm L _] at h_meet
  have hC_lt : Γ.C < (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ Γ.C := by
    apply lt_of_le_of_ne le_sup_right; intro h
    have ha'_le_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.C := le_sup_left.trans h.symm.le
    have ha'_le_m : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V := inf_le_right
    have hCm : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ := by
      rcases Γ.hC.le_iff.mp inf_le_left with h | h
      · exact h
      · exact absurd (h ▸ inf_le_right) Γ.hC_not_m
    exact ha'_ne_bot (le_antisymm (hCm ▸ le_inf ha'_le_C ha'_le_m) bot_le)
  have ha'C_le : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ Γ.C ≤ a ⊔ Γ.C :=
    sup_le inf_le_left le_sup_right
  have h_cov_Ca : Γ.C ⋖ a ⊔ Γ.C := by
    have := atom_covBy_join Γ.hC ha hAC.symm; rwa [sup_comm] at this
  have ha'C_eq : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ Γ.C = a ⊔ Γ.C :=
    (h_cov_Ca.eq_or_eq hC_lt.le ha'C_le).resolve_left (ne_of_gt hC_lt)
  rw [ha'C_eq]
  -- (a ⊔ C) ⊓ l = a.
  have ha_le : a ≤ (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left ha_on
  have h_lt : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro h
    have hl_le := inf_eq_right.mp h
    exact Γ.hC_not_l (((atom_covBy_join ha Γ.hC hAC).eq_or_eq
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le hl_le).resolve_left
      (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt) ▸ le_sup_right)
  exact ((line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le ha.bot_lt ha_le) h_lt
    |>.le_iff.mp ha_le).resolve_left ha.1).symm

-- ═══ Non-degeneracy: coord_neg ≠ O ═══
-- If neg_a = O then e_a = E and β_a = C, forcing a = O. Contradiction.
private theorem coord_neg_ne_O (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    coord_neg Γ a ≠ Γ.O := by
  -- If neg_a = O then e_a = E and β_a = C, forcing a = O. Contradiction.
  unfold coord_neg
  set e_a := (Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V)
  intro h
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hC_ne_e : Γ.C ≠ e_a := fun he => Γ.hC_not_m (he ▸ inf_le_right)
  have he := e_atom Γ ha ha_on ha_ne_O ha_ne_U
  -- O ≤ C ⊔ e_a
  have hO_le_Ce : Γ.O ≤ Γ.C ⊔ e_a := h ▸ inf_le_left
  -- C ⊔ e_a = O ⊔ C (covering)
  have hOC_le_Ce : Γ.O ⊔ Γ.C ≤ Γ.C ⊔ e_a := sup_le hO_le_Ce le_sup_left
  have hC_lt_OC : Γ.C < Γ.O ⊔ Γ.C := lt_of_le_of_ne le_sup_right
    (fun heq => hOC ((Γ.hC.le_iff.mp (le_sup_left.trans heq.symm.le)).resolve_left Γ.hO.1))
  have hCe_eq_OC : Γ.C ⊔ e_a = Γ.O ⊔ Γ.C :=
    ((atom_covBy_join Γ.hC he hC_ne_e).eq_or_eq hC_lt_OC.le hOC_le_Ce).resolve_left
      (ne_of_gt hC_lt_OC) |>.symm
  -- e_a = E
  have he_le_OC : e_a ≤ Γ.O ⊔ Γ.C := le_sup_right.trans hCe_eq_OC.le
  have he_le_E : e_a ≤ Γ.E := by
    unfold CoordSystem.E CoordSystem.m; exact le_inf he_le_OC inf_le_right
  have he_eq_E : e_a = Γ.E :=
    (Γ.hE_atom.le_iff.mp he_le_E).resolve_left he.1
  -- O ⊔ β = O ⊔ C
  have hβ_atom := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hβ_ne_O : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≠ Γ.O :=
    fun hb => beta_not_l Γ ha ha_on ha_ne_O ha_ne_U (hb ▸ le_sup_left)
  have hE_le_Oβ : Γ.E ≤ Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := by
    have h1 : e_a ≤ Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := inf_le_left
    rwa [he_eq_E] at h1
  have hOC_le_Oβ : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := by
    rw [← CoordSystem.OE_eq_OC]; exact sup_le le_sup_left hE_le_Oβ
  have hO_lt_OC : Γ.O < Γ.O ⊔ Γ.C := (atom_covBy_join Γ.hO Γ.hC hOC).lt
  have hOβ_eq_OC : Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) = Γ.O ⊔ Γ.C :=
    ((atom_covBy_join Γ.hO hβ_atom hβ_ne_O.symm).eq_or_eq hO_lt_OC.le hOC_le_Oβ).resolve_left
      (ne_of_gt hO_lt_OC) |>.symm
  -- β = C
  have hβ_le_C : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.C := by
    have h1 : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.O ⊔ Γ.C := le_sup_right.trans hOβ_eq_OC.le
    have h2 : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.U ⊔ Γ.C := inf_le_left
    have h3 := le_inf h1 h2
    rwa [CoordSystem.OC_inf_UC] at h3
  have hβ_eq_C : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) = Γ.C :=
    (Γ.hC.le_iff.mp hβ_le_C).resolve_left hβ_atom.1
  -- C ≤ a ⊔ E, hence O ≤ a ⊔ E
  have hC_le_aE : Γ.C ≤ a ⊔ Γ.E := by
    have h1 : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ a ⊔ Γ.E := inf_le_right
    rwa [hβ_eq_C] at h1
  have hO_le_aE : Γ.O ≤ a ⊔ Γ.E := by
    have h1 : Γ.E ⊔ Γ.C ≤ a ⊔ Γ.E := sup_le le_sup_right hC_le_aE
    rw [EC_eq_OC] at h1; exact le_sup_left.trans h1
  -- (a ⊔ E) ⊓ l is an atom; both a and O sit below it → a = O
  have ha_ne_E : a ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ ha_on)
  have ha_le_inf : a ≤ (a ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left ha_on
  have hO_le_inf : Γ.O ≤ (a ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) := le_inf hO_le_aE le_sup_left
  have h_lt_l : (a ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro heq
    have hE_le_aE : Γ.E ≤ a ⊔ Γ.E := le_sup_right
    have h_eq : a ⊔ Γ.E = Γ.O ⊔ Γ.U :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq
        (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le
        (inf_eq_right.mp heq)).resolve_left
        (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt) |>.symm
    rw [h_eq] at hE_le_aE; exact CoordSystem.hE_not_l hE_le_aE
  have h_atom := line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le ha.bot_lt ha_le_inf) h_lt_l
  have ha_eq := (h_atom.le_iff.mp ha_le_inf).resolve_left ha.1  -- a = p
  have hO_eq := (h_atom.le_iff.mp hO_le_inf).resolve_left Γ.hO.1  -- O = p
  exact ha_ne_O (ha_eq.trans hO_eq.symm)

-- ═══ Non-degeneracy: coord_neg ≠ U ═══
-- If neg_a = U then e_a = U and β_a = U, forcing a = U. Contradiction.
private theorem coord_neg_ne_U (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    coord_neg Γ a ≠ Γ.U := by
  -- If neg_a = U then e_a = U and β_a = U, forcing a = U. Contradiction.
  unfold coord_neg
  set e_a := (Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V)
  intro h
  have hC_ne_e : Γ.C ≠ e_a := fun he => Γ.hC_not_m (he ▸ inf_le_right)
  have he := e_atom Γ ha ha_on ha_ne_O ha_ne_U
  -- U ≤ C ⊔ e_a
  have hU_le_Ce : Γ.U ≤ Γ.C ⊔ e_a := h ▸ inf_le_left
  -- q ≤ C ⊔ e_a (covering: C ⊔ e_a = U ⊔ C)
  have hq_le_Ce : Γ.U ⊔ Γ.C ≤ Γ.C ⊔ e_a := sup_le hU_le_Ce le_sup_left
  have hC_lt_UC : Γ.C < Γ.U ⊔ Γ.C := by
    apply lt_of_le_of_ne le_sup_right; intro heq
    have hU_le_C : Γ.U ≤ Γ.C := le_sup_left.trans heq.symm.le
    have hU_eq_C : Γ.U = Γ.C := (Γ.hC.le_iff.mp hU_le_C).resolve_left Γ.hU.1
    exact Γ.hC_not_l (hU_eq_C.symm.le.trans le_sup_right)
  have hCe_eq_UC : Γ.C ⊔ e_a = Γ.U ⊔ Γ.C :=
    ((atom_covBy_join Γ.hC he hC_ne_e).eq_or_eq hC_lt_UC.le hq_le_Ce).resolve_left
      (ne_of_gt hC_lt_UC) |>.symm
  -- e_a ≤ q ∩ m = U → e_a = U
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hmq : (Γ.U ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.C) = Γ.U :=
    modular_intersection Γ.hU Γ.hV Γ.hC hUV
      (fun h => Γ.hC_not_l (h.symm.le.trans le_sup_right))
      (fun h => Γ.hC_not_m (h.symm.le.trans le_sup_right))
      (fun h => Γ.hC_not_m h)
  have he_le_U : e_a ≤ Γ.U := by
    rw [← hmq]; exact le_inf inf_le_right (le_sup_right.trans hCe_eq_UC.le)
  have he_eq_U : e_a = Γ.U :=
    (Γ.hU.le_iff.mp he_le_U).resolve_left he.1
  -- e_a = U → U ≤ O ⊔ β → l ≤ O ⊔ β → O ⊔ β = l
  have hβ_atom := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hβ_ne_O : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≠ Γ.O :=
    fun hb => beta_not_l Γ ha ha_on ha_ne_O ha_ne_U (hb ▸ le_sup_left)
  have hU_le_Oβ : Γ.U ≤ Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := by
    have h1 : e_a ≤ Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := inf_le_left
    rwa [he_eq_U] at h1
  have hl_le_Oβ : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) :=
    sup_le le_sup_left hU_le_Oβ
  have hOβ_eq_l : Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) = Γ.O ⊔ Γ.U :=
    ((atom_covBy_join Γ.hO hβ_atom hβ_ne_O.symm).eq_or_eq
      (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le hl_le_Oβ).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) |>.symm
  -- β ≤ l ∩ q = U → β = U
  have hlq : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U := by
    rw [sup_comm Γ.O Γ.U]
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm
      (fun h => Γ.hC_not_l (h.symm.le.trans le_sup_right))
      (fun h => CoordSystem.hO_not_UC (h.le.trans le_sup_right))
      (fun h => Γ.hC_not_l (h.trans (sup_comm _ _).le))
  have hβ_le_U : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.U := by
    have h1 : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.O ⊔ Γ.U := le_sup_right.trans hOβ_eq_l.le
    have h2 : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.U ⊔ Γ.C := inf_le_left
    have h3 := le_inf h1 h2; rwa [hlq] at h3
  have hβ_eq_U : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) = Γ.U :=
    (Γ.hU.le_iff.mp hβ_le_U).resolve_left hβ_atom.1
  -- β = U → U ≤ a ⊔ E → (a ⊔ E) ⊓ l = a → U ≤ a → U = a
  have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := by
    have h1 : (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ a ⊔ Γ.E := inf_le_right
    rwa [hβ_eq_U] at h1
  have ha_ne_E : a ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ ha_on)
  have ha_le_inf : a ≤ (a ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left ha_on
  have hU_le_inf : Γ.U ≤ (a ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) := le_inf hU_le_aE le_sup_right
  have h_lt_l : (a ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro heq
    have hE_le_aE : Γ.E ≤ a ⊔ Γ.E := le_sup_right
    have h_eq : a ⊔ Γ.E = Γ.O ⊔ Γ.U :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq
        (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le
        (inf_eq_right.mp heq)).resolve_left
        (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt) |>.symm
    rw [h_eq] at hE_le_aE; exact CoordSystem.hE_not_l hE_le_aE
  have h_atom := line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le ha.bot_lt ha_le_inf) h_lt_l
  have ha_eq := (h_atom.le_iff.mp ha_le_inf).resolve_left ha.1
  have hU_eq := (h_atom.le_iff.mp hU_le_inf).resolve_left Γ.hU.1
  exact ha_ne_U (ha_eq.trans hU_eq.symm)

-- ═══ Double-cover identity: C-persp of neg_a = e_a ═══
-- The C-perspectivity of neg_a from l to m gives back e_a.
-- This is because neg_a = (C⊔e_a)⊓l, so neg_a⊔C = C⊔e_a,
-- and (neg_a⊔C)⊓m = (C⊔e_a)⊓m = e_a.
private theorem neg_C_persp_eq_e (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    (coord_neg Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) =
    (Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V) := by
  -- neg_a = (C ⊔ e_a) ⊓ l, so neg_a ≤ C ⊔ e_a.
  -- neg_a ⊔ C ≤ C ⊔ e_a. By CovBy: neg_a ⊔ C = C ⊔ e_a.
  -- Then (C ⊔ e_a) ⊓ m = e_a by line_direction.
  unfold coord_neg
  set e_a := (Γ.O ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V)
  set neg_a := (Γ.C ⊔ e_a) ⊓ (Γ.O ⊔ Γ.U)
  -- Goal: (neg_a ⊔ C) ⊓ m = e_a
  -- Step 1: neg_a ⊔ C = C ⊔ e_a
  have he := e_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hna_le : neg_a ≤ Γ.C ⊔ e_a := inf_le_left
  have hnaC_le : neg_a ⊔ Γ.C ≤ Γ.C ⊔ e_a := sup_le hna_le le_sup_left
  have hna_ne_C : neg_a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ inf_le_right)
  have hC_ne_e : Γ.C ≠ e_a := fun h => Γ.hC_not_m (h ▸ inf_le_right)
  have hna_atom := coord_neg_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hna_lt : Γ.C < neg_a ⊔ Γ.C := lt_of_le_of_ne le_sup_right
    (fun h => hna_ne_C ((Γ.hC.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left
      hna_atom.1))
  have hnaC_eq : neg_a ⊔ Γ.C = Γ.C ⊔ e_a :=
    ((atom_covBy_join Γ.hC he hC_ne_e).eq_or_eq hna_lt.le hnaC_le).resolve_left
      (ne_of_gt hna_lt)
  -- Step 2: (C ⊔ e_a) ⊓ m = e_a by line_direction
  rw [hnaC_eq]
  exact line_direction Γ.hC Γ.hC_not_m inf_le_right

theorem coord_add_left_neg (Γ : CoordSystem L)
    (a : L) (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ a (coord_neg Γ a) = Γ.O := by
  -- ═══ Architecture: double Desargues (parallel to coord_add_comm) ═══
  -- Key identity: C-persp(neg_a) = e_a ("double-cover alignment").
  -- First Desargues (center U): T1=(a, d_a, β_a), T2=(neg_a, e_a, β_neg)
  --   gives (d_a⊔β_a) ⊓ (e_a⊔β_neg) ≤ O⊔C.
  -- Second Desargues (center = above): T1'=(C, d_a, β_neg), T2'=(E, β_a, e_a)
  --   gives (d_a⊔β_neg) ⊓ (e_a⊔β_a) ≤ l.
  -- Since e_a⊔β_a = O⊔β_a and (O⊔β_a)⊓l = O: the intersection ≤ O,
  -- forcing O ≤ d_a⊔β_neg, hence (d_a⊔β_neg)⊓l = O. QED.
  have hna_atom := coord_neg_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hna_on := coord_neg_on_l Γ a
  have hna_ne_O := coord_neg_ne_O Γ ha ha_on ha_ne_O ha_ne_U
  have hna_ne_U := coord_neg_ne_U Γ ha ha_on ha_ne_O ha_ne_U
  -- ═══ Case split: a = neg_a (char 2) or a ≠ neg_a (generic) ═══
  by_cases ha_eq_na : a = coord_neg Γ a
  · -- ── Char 2 case: a = -a, so a + a = O directly ──
    -- When a = neg_a: d_a = e_a (double-cover identity)
    -- and e_a⊔β_a = O⊔β_a (covering), (O⊔β_a)⊓l = O.
    unfold coord_add
    -- Rewrite coord_neg to a (using ha_eq_na)
    rw [← ha_eq_na]
    -- Use d_a = e_a (neg_C_persp_eq_e + a = neg_a)
    have h_d_eq_e := neg_C_persp_eq_e Γ ha ha_on ha_ne_O ha_ne_U
    rw [← ha_eq_na] at h_d_eq_e
    -- h_d_eq_e : (a ⊔ C) ⊓ m = e_a
    rw [h_d_eq_e]
    -- Normalize β to match e_a's internal β
    rw [show (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) = (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) from inf_comm _ _]
    -- Goal: (e_a ⊔ β_a) ⊓ l = O
    set β_a := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)
    set e_a := (Γ.O ⊔ β_a) ⊓ (Γ.U ⊔ Γ.V)
    -- e_a ⊔ β_a = O ⊔ β_a (covering argument)
    have he_atom := e_atom Γ ha ha_on ha_ne_O ha_ne_U
    have hβ_atom := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
    have hβ_ne_O : β_a ≠ Γ.O :=
      fun h => beta_not_l Γ ha ha_on ha_ne_O ha_ne_U (h ▸ le_sup_left)
    have he_ne_β : e_a ≠ β_a := by
      intro heq
      have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
      have hmq : (Γ.U ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.C) = Γ.U :=
        modular_intersection Γ.hU Γ.hV Γ.hC hUV
          (fun h => Γ.hC_not_l (h.symm.le.trans le_sup_right))
          (fun h => Γ.hC_not_m (h.symm.le.trans le_sup_right))
          (fun h => Γ.hC_not_m h)
      have he_le_U : e_a ≤ Γ.U := by
        rw [← hmq]; exact le_inf inf_le_right (heq ▸ inf_le_left)
      have he_eq_U : e_a = Γ.U := (Γ.hU.le_iff.mp he_le_U).resolve_left he_atom.1
      exact e_not_l Γ ha ha_on ha_ne_O ha_ne_U (he_eq_U.le.trans le_sup_right)
    have he_le_Oβ : e_a ≤ Γ.O ⊔ β_a := inf_le_left
    have hβ_lt : β_a < e_a ⊔ β_a := lt_of_le_of_ne le_sup_right
      (fun h => he_ne_β ((hβ_atom.le_iff.mp
        (le_sup_left.trans h.symm.le)).resolve_left he_atom.1))
    have heβ_eq : e_a ⊔ β_a = Γ.O ⊔ β_a := by
      have heβ_le : e_a ⊔ β_a ≤ Γ.O ⊔ β_a := sup_le he_le_Oβ le_sup_right
      have h_cov := atom_covBy_join hβ_atom Γ.hO hβ_ne_O
      rw [show Γ.O ⊔ β_a = β_a ⊔ Γ.O from sup_comm _ _] at heβ_le ⊢
      exact (h_cov.eq_or_eq hβ_lt.le heβ_le).resolve_left (ne_of_gt hβ_lt)
    -- (O ⊔ β_a) ⊓ l = O (by line_direction)
    rw [heβ_eq, show Γ.O ⊔ β_a = β_a ⊔ Γ.O from sup_comm _ _]
    exact line_direction hβ_atom (beta_not_l Γ ha ha_on ha_ne_O ha_ne_U) le_sup_left
  · -- ── Generic case: a ≠ -a, apply double Desargues ──
    have hab : a ≠ coord_neg Γ a := ha_eq_na
    -- Step 1: First Desargues — gives P₃ ≤ O⊔C
    have h1 := coord_first_desargues Γ ha hna_atom ha_on hna_on
      ha_ne_O hna_ne_O ha_ne_U hna_ne_U hab R hR hR_not h_irred
    -- Step 2: Second Desargues — gives (d_a⊔β_neg) ⊓ (d_{neg_a}⊔β_a) ≤ l
    have h2 := coord_second_desargues Γ ha hna_atom ha_on hna_on
      ha_ne_O hna_ne_O ha_ne_U hna_ne_U hab R hR hR_not h_irred h1
    unfold coord_add
    -- Goal: ((a⊔C)⊓m ⊔ (neg_a⊔E)⊓q) ⊓ l = O
    -- h2:  ((a⊔C)⊓m ⊔ (neg_a⊔E)⊓q) ⊓ ((neg_a⊔C)⊓m ⊔ (a⊔E)⊓q) ≤ l
    -- Step 3: Rewrite d_{neg_a} = e_a in h2
    have h_eq := neg_C_persp_eq_e Γ ha ha_on ha_ne_O ha_ne_U
    rw [h_eq] at h2
    -- Normalize β in h2: (a⊔E)⊓(U⊔C) → (U⊔C)⊓(a⊔E) to match e_a's definition
    rw [show (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) = (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) from inf_comm _ _] at h2
    -- Set up abbreviations (same as char 2 case)
    set β_a := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)
    set e_a := (Γ.O ⊔ β_a) ⊓ (Γ.U ⊔ Γ.V)
    -- h2 : first ⊓ (e_a ⊔ β_a) ≤ l
    -- Step 4: e_a ⊔ β_a = O ⊔ β_a (covering — same as char 2)
    have he_atom := e_atom Γ ha ha_on ha_ne_O ha_ne_U
    have hβ_atom := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
    have hβ_ne_O : β_a ≠ Γ.O :=
      fun h => beta_not_l Γ ha ha_on ha_ne_O ha_ne_U (h ▸ le_sup_left)
    have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
    have hmq : (Γ.U ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.C) = Γ.U :=
      modular_intersection Γ.hU Γ.hV Γ.hC hUV
        (fun h => Γ.hC_not_l (h.symm.le.trans le_sup_right))
        (fun h => Γ.hC_not_m (h.symm.le.trans le_sup_right))
        (fun h => Γ.hC_not_m h)
    have he_ne_β : e_a ≠ β_a := by
      intro heq
      have he_le_U : e_a ≤ Γ.U := by
        rw [← hmq]; exact le_inf inf_le_right (heq ▸ inf_le_left)
      exact e_not_l Γ ha ha_on ha_ne_O ha_ne_U
        ((Γ.hU.le_iff.mp he_le_U).resolve_left he_atom.1 |>.le.trans le_sup_right)
    have he_le_Oβ : e_a ≤ Γ.O ⊔ β_a := inf_le_left
    have hβ_lt : β_a < e_a ⊔ β_a := lt_of_le_of_ne le_sup_right
      (fun h => he_ne_β ((hβ_atom.le_iff.mp
        (le_sup_left.trans h.symm.le)).resolve_left he_atom.1))
    have heβ_eq : e_a ⊔ β_a = β_a ⊔ Γ.O := by
      have heβ_le : e_a ⊔ β_a ≤ β_a ⊔ Γ.O :=
        sup_le (he_le_Oβ.trans (sup_comm _ _).le) le_sup_left
      exact ((atom_covBy_join hβ_atom Γ.hO hβ_ne_O).eq_or_eq hβ_lt.le heβ_le).resolve_left
        (ne_of_gt hβ_lt)
    -- Step 5: (O ⊔ β_a) ⊓ l = O
    have hβ_not_l := beta_not_l Γ ha ha_on ha_ne_O ha_ne_U
    have hOβ_inf_l : (β_a ⊔ Γ.O) ⊓ (Γ.O ⊔ Γ.U) = Γ.O :=
      line_direction hβ_atom hβ_not_l le_sup_left
    -- Rewrite h2 with the covering identity
    rw [heβ_eq] at h2
    -- h2 : first ⊓ (β_a ⊔ O) ≤ l
    -- Step 6: first ⊓ (β_a ⊔ O) ≤ O
    have h_le_O : ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
        (coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (β_a ⊔ Γ.O) ≤ Γ.O := by
      have h3 := le_inf h2 inf_le_right
      rwa [show (Γ.O ⊔ Γ.U) ⊓ (β_a ⊔ Γ.O) = Γ.O from by
        rw [inf_comm]; exact hOβ_inf_l] at h3
    -- Step 7: Non-degeneracy setup
    have hAC : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
    have hd_atom : IsAtom ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) :=
      perspect_atom Γ.hC ha hAC Γ.hU Γ.hV hUV Γ.hC_not_m
        (sup_le (ha_on.trans (le_sup_left.trans Γ.m_sup_C_eq_π.symm.le)) le_sup_right)
    have hd_not_l : ¬ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U := by
      intro h
      have hd_eq_U := Γ.atom_on_both_eq_U hd_atom h inf_le_right
      have := d_a_persp_back Γ ha ha_on
      rw [hd_eq_U, show (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) =
          (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) from inf_comm _ _] at this
      have hlq : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U := by
        rw [sup_comm Γ.O Γ.U]
        exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm
          (fun h => Γ.hC_not_l (h.symm.le.trans le_sup_right))
          (fun h => CoordSystem.hO_not_UC (h.le.trans le_sup_right))
          (fun h => Γ.hC_not_l (h.trans (sup_comm _ _).le))
      rw [hlq] at this; exact ha_ne_U this.symm
    -- d_a ≠ β_neg
    have hβ_neg_atom : IsAtom ((coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) := by
      rw [inf_comm]; exact beta_atom Γ hna_atom hna_on hna_ne_O hna_ne_U
    have hd_ne_βn : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≠
        (coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) := by
      intro heq
      have hd_le_U : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U := by
        have h1 := le_inf inf_le_right (heq.le.trans inf_le_right)
        rwa [hmq] at h1
      exact hd_not_l ((Γ.hU.le_iff.mp hd_le_U).resolve_left hd_atom.1 |>.le.trans le_sup_right)
    -- d_a < first
    have hd_lt_first : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) <
        (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) :=
      lt_of_le_of_ne le_sup_left
        (fun h => hd_ne_βn ((hd_atom.le_iff.mp
          (le_sup_right.trans h.symm.le)).resolve_left hβ_neg_atom.1).symm)
    -- first ≤ π
    have hfirst_le_π : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
        (coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
      sup_le (inf_le_right.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
        (inf_le_left.trans (sup_le (hna_on.trans le_sup_left)
          (CoordSystem.hE_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))))
    -- (β_a ⊔ O) ⋖ π
    have hβ_le_π : β_a ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
      inf_le_left.trans ((sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane).trans
        (Γ.m_sup_C_eq_π ▸ le_refl _))
    have hU_not_βO : ¬ Γ.U ≤ β_a ⊔ Γ.O := by
      intro h
      -- O ⊔ U ≤ O ⊔ β_a (via sup_comm on β_a ⊔ O)
      have hl_le : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ β_a :=
        (sup_le le_sup_right h).trans (sup_comm _ _).le
      -- By covering O ⋖ O ⊔ β_a: O ⊔ U = O or O ⊔ U = O ⊔ β_a
      exact hβ_not_l (le_sup_right.trans
        (((atom_covBy_join Γ.hO hβ_atom hβ_ne_O.symm).eq_or_eq le_sup_left hl_le).resolve_left
          (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)).symm.le)
    have hβO_covBy_π : (β_a ⊔ Γ.O) ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
      have hU_disj : Γ.U ⊓ (β_a ⊔ Γ.O) = ⊥ :=
        (Γ.hU.le_iff.mp inf_le_left).resolve_right
          (fun h => hU_not_βO (h ▸ inf_le_right))
      have h_cov := covBy_sup_of_inf_covBy_left (hU_disj ▸ Γ.hU.bot_covBy)
      -- h_cov : (β_a ⊔ O) ⋖ U ⊔ (β_a ⊔ O)
      -- Show U ⊔ (β_a ⊔ O) = (O ⊔ U) ⊔ β_a = π
      have hβ_disj_l : β_a ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
        (hβ_atom.le_iff.mp inf_le_left).resolve_right
          (fun h => hβ_not_l (h ▸ inf_le_right))
      have hlβ_eq_π : (Γ.O ⊔ Γ.U) ⊔ β_a = Γ.O ⊔ Γ.U ⊔ Γ.V := by
        have hl_cov : (Γ.O ⊔ Γ.U) ⋖ (Γ.O ⊔ Γ.U) ⊔ β_a := by
          rw [show (Γ.O ⊔ Γ.U) ⊔ β_a = β_a ⊔ (Γ.O ⊔ Γ.U) from sup_comm _ _]
          exact covBy_sup_of_inf_covBy_left (hβ_disj_l ▸ hβ_atom.bot_covBy)
        exact ((l_covBy_π Γ).eq_or_eq hl_cov.lt.le
          (sup_le le_sup_left hβ_le_π)).resolve_left (ne_of_gt hl_cov.lt)
      rwa [show Γ.U ⊔ (β_a ⊔ Γ.O) = (Γ.O ⊔ Γ.U) ⊔ β_a from by
        rw [sup_comm Γ.U, sup_assoc, sup_comm β_a], hlβ_eq_π] at h_cov
    -- ¬ first ≤ β_a ⊔ O (if so, first ≤ O → d_a ≤ O → d_a = O, contradicts O ∉ m)
    -- ¬ first ≤ β_a ⊔ O (if so, first ≤ O → d_a ≤ O, contradiction)
    have hfirst_not_le : ¬ ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
        (coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ≤ β_a ⊔ Γ.O := by
      intro h
      have : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) ≤ Γ.O :=
        (inf_eq_left.mpr h) ▸ h_le_O
      exact hd_not_l ((Γ.hO.le_iff.mp (le_sup_left.trans this)).resolve_left
        hd_atom.1 |>.le.trans le_sup_left)
    -- Two coplanar lines meet
    have h_meet : ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
        (coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (β_a ⊔ Γ.O) ≠ ⊥ := by
      rw [inf_comm]
      exact lines_meet_if_coplanar hβO_covBy_π hfirst_le_π hfirst_not_le hd_atom hd_lt_first
    -- first ⊓ (β_a ⊔ O) ≤ O and ≠ ⊥ → = O → O ≤ first
    have h_eq_O := ((Γ.hO.le_iff.mp h_le_O).resolve_left h_meet).symm
    -- h_eq_O : Γ.O = first ⊓ (β_a ⊔ Γ.O)
    have hO_le_first : Γ.O ≤ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
        (coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) := h_eq_O.le.trans inf_le_left
    -- first ⊓ l = O
    have hO_le_fl : Γ.O ≤ ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
        (coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U) :=
      le_inf hO_le_first le_sup_left
    have hfl_lt_l : ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
        (coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
      apply lt_of_le_of_ne inf_le_right; intro heq
      have hl_le := heq.symm ▸ (inf_le_left :
        ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (coord_neg Γ a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U) ≤ _)
      rcases (l_covBy_π Γ).eq_or_eq (heq.symm.le.trans inf_le_left) hfirst_le_π with h | h
      · exact hd_not_l (le_sup_left.trans (le_of_eq h))
      · -- first = π: d_a ⋖ first = π, but d_a < m < π
        have hd_cov := atom_covBy_join hd_atom hβ_neg_atom hd_ne_βn
        have hd_lt_m : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) < Γ.U ⊔ Γ.V :=
          lt_of_le_of_ne inf_le_right (fun hm =>
            hd_not_l ((hd_atom.le_iff.mp (le_sup_left.trans hm.symm.le)).resolve_left
              Γ.hU.1 |>.symm.le.trans le_sup_right))
        rcases hd_cov.eq_or_eq hd_lt_m.le (Γ.m_covBy_π.lt.le.trans h.symm.le) with hm | hm
        · exact absurd hm.symm hd_lt_m.ne
        · exact absurd (hm.trans h) Γ.m_covBy_π.lt.ne
    exact ((line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le Γ.hO.bot_lt hO_le_fl) hfl_lt_l
      ).le_iff.mp hO_le_fl).resolve_left Γ.hO.1 |>.symm

/-- **Additive right inverse: (-a) + a = O.** Follows from left inverse + commutativity. -/
theorem coord_add_right_neg (Γ : CoordSystem L)
    (a : L) (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (hna_ne_O : coord_neg Γ a ≠ Γ.O) (hna_ne_U : coord_neg Γ a ≠ Γ.U)
    (ha_ne_na : a ≠ coord_neg Γ a)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ (coord_neg Γ a) a = Γ.O := by
  have hna_atom := coord_neg_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hna_on := coord_neg_on_l Γ a
  rw [coord_add_comm Γ (coord_neg Γ a) a hna_atom ha hna_on ha_on
    hna_ne_O ha_ne_O hna_ne_U ha_ne_U ha_ne_na.symm R hR hR_not h_irred]
  exact coord_add_left_neg Γ a ha ha_on ha_ne_O ha_ne_U R hR hR_not h_irred

end Foam.FTPGExplore
