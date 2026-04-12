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
  1 sorry (coord_add_left_neg).
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
theorem coord_add_left_neg (Γ : CoordSystem L)
    (a : L) (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    coord_add Γ a (coord_neg Γ a) = Γ.O := by
  -- TODO: The core geometric argument showing O ≤ a' ⊔ D.
  -- The three perspectivity centers O, C, E are collinear (on the line O⊔C).
  -- This collinearity forces the perspectivity chain to close at O.
  -- Proof strategy: compute D explicitly, show D ≤ O ⊔ a' using
  -- the modular law and the collinearity E ≤ O⊔C.
  sorry

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
  exact coord_add_left_neg Γ a ha ha_on ha_ne_O ha_ne_U

end Foam.FTPGExplore
