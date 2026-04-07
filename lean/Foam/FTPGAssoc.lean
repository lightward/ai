/-
# Associativity of coordinate addition (Part V)

The final connection: coord_add equals translation application,
then associativity follows from the translation group structure.

- `coord_add_eq_translation`: von Staudt addition = apply translation
- `key_identity`: τ_a(C_b) = C_{a+b}
- `coord_add_assoc`: (a + b) + c = a + (b + c)

## Status (session 50)

12 sorry remain: 11 in key_identity (distinctness, spanning,
well-definedness, G-on-m fallback), 1 in coord_add_assoc.
Bookkeeping sorry (hs_atom, hCs_atom, hs_ne_τ, s≠O) all closed.
-/

import Foam.FTPGCrossParallelism

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-!
## Part V: From translations to coord_add_assoc

The final connection: show coord_add equals translation application,
then associativity falls out from the translation group.

### Architecture (Gemini's "Path C", endorsed by full panel)

1. Define translation_add a b = τ_a(b) via parallelogram completion
2. Associativity is immediate from the group law
3. Prove coord_add = translation_add (the geometric equivalence)
4. coord_add_assoc follows by rewriting

### The geometric equivalence (Step 3)

coord_add Γ a b = ((a⊔C)⊓m ⊔ (b⊔E)⊓(U⊔C)) ⊓ l     -- von Staudt
translation(b)  = ((a⊔E)⊓(U⊔C) ⊔ (b⊔C)⊓m) ⊓ l       -- parallelogram

The four atoms a', D_b, C', e' are cross-perspectivities of a and b
through centers C and E:
  a' = perspect_C(a) on m       D_b = perspect_E(b) on U⊔C
  C' = perspect_E(a) on U⊔C    e'  = perspect_C(b) on m

coord_add joins C-of-a with E-of-b; translation joins E-of-a with C-of-b.
The claim: these cross-connections hit l at the same point.

Key geometric facts for the proof:
  - C, E, O are collinear (all on line O⊔C, since E = (O⊔C)⊓m)
  - The quadrilateral (a, C, b, E) has diagonals l and O⊔C meeting at O
  - Does NOT require Pappus (Desargues suffices)
  - Does NOT require the Fundamental Theorem for projectivities
  - Should follow from modular law + careful lattice computation

Status: the shape is identified, the proof is not yet closed.
-/

/-- **The geometric equivalence: von Staudt = translation.**

    coord_add Γ a b equals the parallelogram completion using
    auxiliary point C. This is the key theorem connecting the
    classical von Staudt construction to Hartshorne's translations.

    Once proved, coord_add_assoc follows immediately from the
    translation group being abelian (Parts I-IV). -/
theorem coord_add_eq_translation (Γ : CoordSystem L)
    (a b : L) (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : a ≠ b)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    let C' := parallelogram_completion Γ.O a Γ.C (Γ.U ⊔ Γ.V)
    coord_add Γ a b = parallelogram_completion Γ.C C' b (Γ.U ⊔ Γ.V) := by
  -- ═══ Proof strategy ═══
  -- After simplification, the goal reduces to (a'⊔D_b)⊓l = (C'⊔e')⊓l.
  -- Key: coord_first_desargues gives (a'⊔C')⊓(e'⊔D_b) ≤ O⊔C,
  --       coord_second_desargues gives W = (a'⊔D_b)⊓(e'⊔C') ≤ l.
  -- Then W ≤ both atoms (a'⊔D_b)⊓l and (C'⊔e')⊓l, so both equal W.
  --
  -- ═══ Setup ═══
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)
  have ha_ne_E : a ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ ha_on)
  have hb_ne_E : b ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hb_on)
  have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U :=
    modular_intersection Γ.hU Γ.hC Γ.hV hUC hUV
      (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      (fun hle => Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV hUV).lt.le (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV hUV).lt) ▸ le_sup_right))
  have hE_not_UC : ¬ Γ.E ≤ Γ.U ⊔ Γ.C := fun h => Γ.hEU ((Γ.hU.le_iff.mp
    (hUC_inf_m ▸ le_inf h Γ.hE_on_m)).resolve_left Γ.hE_atom.1)
  -- ═══ Simplify C' ═══
  have hOa_eq_l : Γ.O ⊔ a = Γ.O ⊔ Γ.U := by
    have hO_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_of_le_of_eq le_sup_right h.symm)).resolve_left ha.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt hO_lt)
  have hC'_simp : parallelogram_completion Γ.O a Γ.C (Γ.U ⊔ Γ.V) =
      (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := by
    show (Γ.C ⊔ (Γ.O ⊔ a) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (a ⊔ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) =
      (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)
    rw [hOa_eq_l, Γ.l_inf_m_eq_U, sup_comm Γ.C Γ.U]; rfl
  show coord_add Γ a b =
    parallelogram_completion Γ.C (parallelogram_completion Γ.O a Γ.C (Γ.U ⊔ Γ.V)) b (Γ.U ⊔ Γ.V)
  rw [hC'_simp]
  -- ═══ Simplify RHS to (C'⊔e')⊓l ═══
  have hCE_eq_CO : Γ.C ⊔ Γ.E = Γ.C ⊔ Γ.O := by
    have hC_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hCE ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_atom.1).symm)
    exact ((atom_covBy_join Γ.hC Γ.hO hOC.symm).eq_or_eq hC_lt.le
      (sup_le le_sup_left (Γ.hE_le_OC.trans (sup_comm Γ.O Γ.C).le))).resolve_left
      (ne_of_gt hC_lt)
  have hC_join_C' : Γ.C ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) = Γ.U ⊔ Γ.C := by
    apply le_antisymm (sup_le le_sup_right inf_le_left)
    have haEC_ge_UC : Γ.U ⊔ Γ.C ≤ a ⊔ Γ.E ⊔ Γ.C := by
      suffices Γ.U ≤ a ⊔ Γ.E ⊔ Γ.C from sup_le this le_sup_right
      calc Γ.U ≤ Γ.O ⊔ Γ.U := le_sup_right
        _ = Γ.O ⊔ a := hOa_eq_l.symm
        _ ≤ a ⊔ Γ.E ⊔ Γ.C := sup_le
            ((le_of_le_of_eq (le_sup_right : Γ.O ≤ Γ.C ⊔ Γ.O) hCE_eq_CO.symm).trans
              (sup_le le_sup_right (le_sup_right.trans le_sup_left)))
            (le_sup_left.trans le_sup_left)
    calc Γ.U ⊔ Γ.C
        ≤ (Γ.C ⊔ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.C) := le_inf
          (haEC_ge_UC.trans (show a ⊔ Γ.E ⊔ Γ.C = Γ.C ⊔ (a ⊔ Γ.E) from by ac_rfl).le) le_rfl
      _ = Γ.C ⊔ (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) :=
          sup_inf_assoc_of_le (a ⊔ Γ.E) (le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C)
      _ = Γ.C ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := by rw [inf_comm]
  have hRHS_dir : (Γ.C ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
    rw [hC_join_C', hUC_inf_m]
  have hbU_eq_l : b ⊔ Γ.U = Γ.O ⊔ Γ.U := by
    have hU_lt : Γ.U < Γ.U ⊔ b := lt_of_le_of_ne le_sup_left
      (fun h => hb_ne_U ((Γ.hU.le_iff.mp (le_of_le_of_eq le_sup_right h.symm)).resolve_left hb.1))
    calc b ⊔ Γ.U = Γ.U ⊔ b := sup_comm _ _
      _ = Γ.U ⊔ Γ.O := ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq hU_lt.le
          (sup_le le_sup_left (hb_on.trans (sup_comm Γ.O Γ.U).le))).resolve_left (ne_of_gt hU_lt)
      _ = Γ.O ⊔ Γ.U := sup_comm _ _
  show ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U) =
    (b ⊔ (Γ.C ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V)) ⊓
    ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ⊔ (Γ.C ⊔ b) ⊓ (Γ.U ⊔ Γ.V))
  rw [hRHS_dir, hbU_eq_l, sup_comm Γ.C b, inf_comm (Γ.O ⊔ Γ.U)]
  -- ═══ Key insight: the RHS is coord_add Γ b a (up to inf_comm/sup_comm) ═══
  -- After simplification, RHS = ((U⊔C)⊓(a⊔E) ⊔ (b⊔C)⊓(U⊔V)) ⊓ (O⊔U)
  --   = ((a⊔E)⊓(U⊔C) ⊔ (b⊔C)⊓(U⊔V)) ⊓ (O⊔U)  [inf_comm]
  --   = ((b⊔C)⊓(U⊔V) ⊔ (a⊔E)⊓(U⊔C)) ⊓ (O⊔U)  [sup_comm]
  --   = coord_add Γ b a
  -- And LHS = coord_add Γ a b. So the result follows from coord_add_comm.
  show ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U) =
    ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ⊔ (b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ Γ.U)
  conv_rhs => rw [show (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) = (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) from inf_comm _ _,
    show (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) ⊔ (b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) =
      (b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) from sup_comm _ _]
  exact coord_add_comm Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U hab
    R hR hR_not h_irred

/-- **Key Identity: the translation τ_a sends C_b to C_{a+b}.**

    pc(O, a, C_b, m) = C_{a+b}, where C_x = pc(O, x, C, m) = q ⊓ (x ⊔ E).

    Proof: cross-parallelism of τ_a on (b, C_b) gives
    ((a+b) ⊔ τ_a(C_b)) ⊓ m = (b ⊔ C_b) ⊓ m = E.
    Since τ_a(C_b) is on q, it's on q ⊓ ((a+b) ⊔ E) = C_{a+b}. -/
theorem key_identity (Γ : CoordSystem L)
    (a b : L) (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : a ≠ b)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    let C_b := parallelogram_completion Γ.O b Γ.C (Γ.U ⊔ Γ.V)
    let s := coord_add Γ a b
    let C_s := parallelogram_completion Γ.O s Γ.C (Γ.U ⊔ Γ.V)
    parallelogram_completion Γ.O a C_b (Γ.U ⊔ Γ.V) = C_s := by
  intro C_b s C_s
  -- ═══ Basic setup ═══
  set l := Γ.O ⊔ Γ.U
  set m := Γ.U ⊔ Γ.V
  set q := Γ.U ⊔ Γ.C
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set τ_a_C_b := parallelogram_completion Γ.O a C_b m
  -- Standard CoordSystem facts
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hb_not_m : ¬ b ≤ m := fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on h)
  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have hOa_eq_l : Γ.O ⊔ a = l := by
    have h_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
      (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt h_lt)
  have hOb_eq_l : Γ.O ⊔ b = l := by
    have h_lt : Γ.O < Γ.O ⊔ b := lt_of_le_of_ne le_sup_left
      (fun h => hb_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hb.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
      (sup_le le_sup_left hb_on)).resolve_left (ne_of_gt h_lt)
  have hm_cov : m ⋖ π := by
    -- m = U ⊔ V, π = O ⊔ U ⊔ V = O ⊔ m. O ⊓ m = ⊥ (O not on m). So m ⋖ O ⊔ m.
    show Γ.U ⊔ Γ.V ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
    have hO_inf_m : Γ.O ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hO_not_m (h ▸ inf_le_right))
    rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = Γ.O ⊔ (Γ.U ⊔ Γ.V) from sup_assoc _ _ _]
    exact covBy_sup_of_inf_covBy_left (hO_inf_m ▸ Γ.hO.bot_covBy)
  have hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m := fun x hx hle =>
    line_covers_its_atoms Γ.hU Γ.hV hUV hx hle

  -- ═══ l ⊓ q = U ═══
  have hlq_eq_U : l ⊓ q = Γ.U := by
    show (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U
    rw [sup_comm Γ.O Γ.U]
    have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
    have hOC' : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm hUC hOC'
      (fun h => Γ.hC_not_l (le_trans h (by rw [sup_comm])))

  -- ═══ C_b facts ═══
  have hCb_atom : IsAtom C_b :=
    parallelogram_completion_atom Γ.hO hb Γ.hC
      (fun h => hb_ne_O h.symm)
      hOC (fun h => Γ.hC_not_l (h ▸ hb_on))
      (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) Γ.hC_plane
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hm_cov hm_line
      Γ.hO_not_m hb_not_m Γ.hC_not_m
      (fun h => Γ.hC_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
  have hCb_le_bE : C_b ≤ b ⊔ Γ.E := (inf_le_right : C_b ≤ b ⊔ (Γ.O ⊔ Γ.C) ⊓ m)
  have hCb_le_q : C_b ≤ q := by
    have : C_b ≤ Γ.C ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
    rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this
    exact this.trans (sup_comm Γ.C Γ.U ▸ le_refl q)
  have hb_ne_Cb : b ≠ C_b := by
    intro h
    -- b = C_b → b ≤ q (since C_b ≤ q). But b ≤ l. So b ≤ l ⊓ q = l ⊓ (U ⊔ C).
    have hb_le_q : b ≤ q := h ▸ hCb_le_q
    have hb_le_lq : b ≤ l ⊓ q := le_inf hb_on hb_le_q
    rw [hlq_eq_U] at hb_le_lq
    exact hb_ne_U ((Γ.hU.le_iff.mp hb_le_lq).resolve_left hb.1)
  have hCb_not_m : ¬ C_b ≤ m := by
    intro hCb_m
    -- C_b ≤ b ⊔ E (from hCb_le_bE). With C_b ≤ m:
    -- C_b ≤ (b ⊔ E) ⊓ m = E (by line_direction, since b off m, E on m)
    have h_bE_dir : (b ⊔ Γ.E) ⊓ m = Γ.E :=
      line_direction hb hb_not_m Γ.hE_on_m
    have hCb_le_E : C_b ≤ Γ.E := by
      have : C_b ≤ (b ⊔ Γ.E) ⊓ m := le_inf hCb_le_bE hCb_m
      rwa [h_bE_dir] at this
    -- C_b atom, E atom → C_b = E
    have hCb_eq_E : C_b = Γ.E :=
      (Γ.hE_atom.le_iff.mp hCb_le_E).resolve_left hCb_atom.1
    -- But C_b ≤ q, so E ≤ q = U ⊔ C. Then E ≤ (U ⊔ C) ⊓ m.
    -- (U ⊔ C) ⊓ m: by modular law (U ≤ m): U ⊔ C ⊓ m = U ⊔ ⊥ = U
    -- (since C ⊓ m = ⊥ because C not on m)
    have hE_le_q : Γ.E ≤ q := hCb_eq_E ▸ hCb_le_q
    have hE_le_m : Γ.E ≤ m := Γ.hE_on_m
    have hE_le_qm : Γ.E ≤ q ⊓ m := le_inf hE_le_q hE_le_m
    have hqm_eq : q ⊓ m = Γ.U := by
      show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
      -- Modular law: U ≤ U ⊔ V, so (U ⊔ C) ⊓ (U ⊔ V) = U ⊔ C ⊓ (U ⊔ V)
      rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
      -- C ⊓ (U ⊔ V) = ⊥ since C is an atom not on m
      have hC_inf_m : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
        (Γ.hC.le_iff.mp inf_le_left).resolve_right
          (fun h => Γ.hC_not_m (h ▸ inf_le_right))
      rw [hC_inf_m, sup_bot_eq]
    rw [hqm_eq] at hE_le_qm
    exact Γ.hEU ((Γ.hU.le_iff.mp hE_le_qm).resolve_left Γ.hE_atom.1)

  -- ═══ Step 1: τ_a(C_b) ≤ q ═══
  have h_τ_le_q : τ_a_C_b ≤ q := by
    show (C_b ⊔ (Γ.O ⊔ a) ⊓ m) ⊓ (a ⊔ (Γ.O ⊔ C_b) ⊓ m) ≤ q
    rw [hOa_eq_l, Γ.l_inf_m_eq_U]
    exact inf_le_left.trans (sup_le hCb_le_q (le_sup_left : Γ.U ≤ q))

  -- ═══ Step 2: (b ⊔ C_b) ⊓ m = E ═══
  have h_bCb_eq_bE : b ⊔ C_b = b ⊔ Γ.E := by
    have hb_ne_E : b ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hb_on)
    have h_lt : b < b ⊔ C_b := lt_of_le_of_ne le_sup_left
      (fun h => hb_ne_Cb ((hb.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hCb_atom.1).symm)
    exact ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left hCb_le_bE)).resolve_left (ne_of_gt h_lt)
  have h_bCb_dir : (b ⊔ C_b) ⊓ m = Γ.E := by
    rw [h_bCb_eq_bE]; exact line_direction hb hb_not_m Γ.hE_on_m

  -- ═══ Step 3: Cross-parallelism gives (s ⊔ τ_a(C_b)) ⊓ m = E ═══
  have h_cross : (s ⊔ τ_a_C_b) ⊓ m = Γ.E := by
    -- Construct G off l, m, q via h_irred
    have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
    obtain ⟨G, hG_atom, hG_le_aC, hG_ne_a, hG_ne_C⟩ := h_irred a Γ.C ha Γ.hC ha_ne_C
    -- G ∉ l: (a⊔C)⊓l = a by modular law, G ≠ a
    have hG_not_l : ¬ G ≤ l := by
      intro hG_l
      have hG_le_a : G ≤ a := by
        have h_inf : G ≤ (a ⊔ Γ.C) ⊓ l := le_inf hG_le_aC hG_l
        rwa [show (a ⊔ Γ.C) ⊓ l = a from by
          rw [sup_comm, inf_comm]; exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h_inf
      exact hG_ne_a ((ha.le_iff.mp hG_le_a).resolve_left hG_atom.1)
    -- G ∉ q: (a⊔C)⊓q = C by modular law, G ≠ C
    have hG_not_q : ¬ G ≤ q := by
      intro hG_q
      have hG_le_C : G ≤ Γ.C := by
        have h_inf : G ≤ (a ⊔ Γ.C) ⊓ q := le_inf hG_le_aC hG_q
        rw [show q = Γ.C ⊔ Γ.U from sup_comm Γ.U Γ.C] at h_inf
        rwa [show (a ⊔ Γ.C) ⊓ (Γ.C ⊔ Γ.U) = Γ.C from by
          rw [inf_comm]
          have ha_not_CU : ¬ a ≤ Γ.C ⊔ Γ.U := by
            intro hle
            have hle' : a ≤ q := hle.trans (sup_comm Γ.C Γ.U).le
            have : a ≤ l ⊓ q := le_inf ha_on hle'
            rw [hlq_eq_U] at this
            exact ha_ne_U ((Γ.hU.le_iff.mp this).resolve_left ha.1)
          exact inf_sup_of_atom_not_le ha ha_not_CU
            (le_sup_left : Γ.C ≤ Γ.C ⊔ Γ.U)] at h_inf
      exact hG_ne_C ((Γ.hC.le_iff.mp hG_le_C).resolve_left hG_atom.1)
    -- G might be on m. Handle with by_cases.
    by_cases hG_not_m : ¬ G ≤ m
    · -- G off l, m, q. Proceed.
      -- G' = pc(O, a, G, m): the image of G under τ_a
      set G' := parallelogram_completion Γ.O a G m
      -- G is in π (G ≤ a⊔C ≤ π)
      have hG_le_π : G ≤ π :=
        hG_le_aC.trans (sup_le (ha_on.trans le_sup_left) Γ.hC_plane)
      -- G' is an atom
      have hG'_atom : IsAtom G' := by
        exact parallelogram_completion_atom Γ.hO ha hG_atom
          (fun h => ha_ne_O h.symm)
          (fun h => hG_not_l (h ▸ le_sup_left))
          (fun h => hG_not_l (h ▸ ha_on))
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hG_le_π
          (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hm_cov hm_line
          Γ.hO_not_m ha_not_m hG_not_m
          (fun h => hG_not_l (h.trans (hOa_eq_l ▸ le_refl l)))
      -- ═══ G' incidence facts ═══
      -- G' not on m: if G' ≤ m then G' = d = e, contradicting G ∉ l
      have hG'_not_m : ¬ G' ≤ m := by
        intro hG'_m
        set d_Oa := (Γ.O ⊔ a) ⊓ m   -- direction of O→a
        set e_OG := (Γ.O ⊔ G) ⊓ m   -- direction of O→G
        have hd_atom : IsAtom d_Oa := line_meets_m_at_atom Γ.hO ha
          (fun h => ha_ne_O h.symm)
          (sup_le (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left))
          (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
          hm_cov Γ.hO_not_m
        have hd_on_m : d_Oa ≤ m := inf_le_right
        have he_atom : IsAtom e_OG := line_meets_m_at_atom Γ.hO hG_atom
          (fun h => hG_not_l (h ▸ le_sup_left))
          (sup_le (le_sup_left.trans le_sup_left) hG_le_π)
          (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
          hm_cov Γ.hO_not_m
        have he_on_m : e_OG ≤ m := inf_le_right
        -- G' ≤ (G ⊔ d) ⊓ m = d (line_direction, G off m)
        have hG'_le_d : G' ≤ d_Oa := by
          have h1 : G' ≤ G ⊔ d_Oa := by
            show parallelogram_completion Γ.O a G m ≤ G ⊔ d_Oa
            unfold parallelogram_completion; exact inf_le_left
          have h2 : G' ≤ (G ⊔ d_Oa) ⊓ m := le_inf h1 hG'_m
          rwa [line_direction hG_atom hG_not_m hd_on_m] at h2
        -- G' ≤ (a ⊔ e) ⊓ m = e (line_direction, a off m)
        have hG'_le_e : G' ≤ e_OG := by
          have h1 : G' ≤ a ⊔ e_OG := by
            show parallelogram_completion Γ.O a G m ≤ a ⊔ e_OG
            unfold parallelogram_completion; exact inf_le_right
          have h2 : G' ≤ (a ⊔ e_OG) ⊓ m := le_inf h1 hG'_m
          rwa [line_direction ha ha_not_m he_on_m] at h2
        -- G' = d = e → d = e
        have hG'_eq_d := (hd_atom.le_iff.mp hG'_le_d).resolve_left hG'_atom.1
        have hG'_eq_e := (he_atom.le_iff.mp hG'_le_e).resolve_left hG'_atom.1
        have hd_eq_e : d_Oa = e_OG := hG'_eq_d.symm.trans hG'_eq_e
        -- d ≤ O⊔a and d ≤ O⊔G (since d = e), so d ≤ (O⊔a) ⊓ (O⊔G) = O
        have hd_le_both : d_Oa ≤ (Γ.O ⊔ a) ⊓ (Γ.O ⊔ G) :=
          le_inf inf_le_left (hd_eq_e ▸ inf_le_left)
        have hOa_inf_OG : (Γ.O ⊔ a) ⊓ (Γ.O ⊔ G) = Γ.O := by
          rw [hOa_eq_l]
          exact modular_intersection Γ.hO Γ.hU hG_atom Γ.hOU
            (fun h => hG_not_l (h ▸ le_sup_left))
            (fun h => hG_not_l (h ▸ le_sup_right))
            hG_not_l
        rw [hOa_inf_OG] at hd_le_both
        exact Γ.hO_not_m ((Γ.hO.le_iff.mp hd_le_both).resolve_left hd_atom.1 ▸ hd_on_m)

      -- G' ≤ π
      have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
      have hG'_le_π : G' ≤ π := by
        -- G' ≤ G ⊔ d (inf_le_left from pc def) ≤ π ⊔ π = π
        have h1 : G' ≤ G ⊔ (Γ.O ⊔ a) ⊓ m := by
          show parallelogram_completion Γ.O a G m ≤ _
          unfold parallelogram_completion; exact inf_le_left
        exact h1.trans (sup_le hG_le_π (inf_le_right.trans hm_le_π))

      -- ═══ Distinctness conditions ═══
      -- G ≠ G': G off m, G' = pc(O,a,G,m). If G = G' then G ≤ a ⊔ e ≤ π,
      -- and (G⊔d) ⊓ (a⊔e) = G. Then G ≤ a ⊔ e. (a⊔e)⊓m = e and G ∉ m,
      -- so G ⊔ e = a ⊔ e. By covering, a ≤ G ⊔ e. Then a ≤ (G⊔e)⊓l.
      -- G ∉ l, e on m. (G⊔e)⊓l... actually, let's use direction:
      -- G on O⊔a and G on a⊔e → direction (G⊔a)⊓m should relate d to e.
      -- Simpler: if G = G' then pc(O,a,G,m) = G. But pc gives an atom NOT on O⊔a = l
      -- (by the Q_not_PP' argument). Wait, actually G IS on the line a⊔C which isn't l.
      -- Let me think... G ≤ a⊔C. G' = pc(O,a,G,m). The "hQ_not_PP'" arg of
      -- parallelogram_completion_atom was: ¬ G ≤ O ⊔ a = l. So G ≠ G' follows from
      -- G ∉ l and G' definition. Actually no, we need G ≠ G' directly.
      -- G is off l. G' lies on a ⊔ e. If G = G' then G ≤ a ⊔ e. Also G ≤ a ⊔ C.
      -- G ∉ l means G ≠ a. So G ≤ (a⊔e) ⊓ (a⊔C) = a ⊔ e⊓(a⊔C) (modular, a ≤ a⊔C).
      -- e⊓(a⊔C) = (O⊔G)⊓m ⊓ (a⊔C). Hmm, getting complicated.
      -- Better: use that G and G' have the same direction (O⊔G)⊓m but G ∉ O⊔G' unless...
      -- Actually simplest: G ≠ G' because if G = G' then the parallelogram is degenerate.
      -- Formally: G' ≤ G ⊔ d (pc def). If G = G' then G ≤ G ⊔ d trivially — no info.
      -- G' ≤ a ⊔ e. If G = G' then G ≤ a ⊔ e = a ⊔ (O⊔G)⊓m.
      -- G off m → G ⊓ m = ⊥. By modular: (a ⊔ (O⊔G)⊓m) ⊓ (O⊔G) = ...hmm.
      -- Let me just use: G ∉ l = O⊔a. (O⊔a)⊓m = d (direction of O→a).
      -- (O⊔G)⊓m = e (direction of O→G). G' ≤ G⊔d and G' ≤ a⊔e.
      -- If G = G' → G ≤ G⊔d (trivial) and G ≤ a⊔e.
      -- a off m, e on m → (a⊔e)⊓(O⊔a) = a (modular: a ≤ O⊔a, e ∉ O⊔a... need e ∉ l).
      -- G ≠ G': if G = G' then d = U (since O⊔a = l, d = l⊓m = U).
      -- G = (G⊔U) ⊓ (a⊔e). Since G ≤ a⊔e, we also get: e ∉ l
      -- (if e ≤ l then e ≤ (O⊔U)⊓(O⊔G) = O by modular, contradiction with O ∉ m).
      -- G ≤ a⊔e and G ≤ a⊔C. Either C ∉ a⊔e (then G ≤ (a⊔e)⊓(a⊔C) = a,
      -- contradiction with G ≠ a) or C ≤ a⊔e (then a⊔C = a⊔e, and
      -- e = (a⊔C)⊓m = (O⊔G)⊓m, meaning (O⊔G)⊓m = (a⊔C)⊓m.
      -- We need: C ∉ a⊔e for a clean contradiction.
      -- C ≤ a⊔e iff (a⊔C)⊓m = e = (O⊔G)⊓m, i.e., lines a⊔C and O⊔G have
      -- the same direction. This is a non-generic condition that G satisfies
      -- only if G is specially positioned. Since G was obtained from h_irred
      -- (exists on line a⊔C, distinct from a and C), we don't have a direct
      -- guarantee. This may need an additional case split or a stronger
      -- choice of G.
      have hGG' : G ≠ G' := by sorry

      -- G ≠ b: G ≤ a⊔C, b on l, G ∉ l
      have hG_ne_b : G ≠ b := fun h => hG_not_l (h ▸ hb_on)

      -- G ≠ C_b: G ≤ a⊔C, C_b ≤ q, G ∉ q
      have hG_ne_Cb : G ≠ C_b := fun h => hG_not_q (h ▸ hCb_le_q)

      -- C_b ≤ π: C_b ≤ q = U ⊔ C ≤ π
      have hCb_le_π : C_b ≤ π :=
        hCb_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)

      -- b not on G ⊔ G': if b ≤ G ⊔ G' then since b on l and G ∉ l,
      -- b ≤ (G⊔G')⊓l. Need to show this gives contradiction.
      have hb_not_GG' : ¬ b ≤ G ⊔ G' := by sorry

      -- C_b not on G ⊔ G'
      have hCb_not_GG' : ¬ C_b ≤ G ⊔ G' := by sorry

      -- C_b not on G ⊔ b
      have hCb_not_Gb : ¬ C_b ≤ G ⊔ b := by sorry

      -- G' ≠ pc(G, G', b, m): follows from G' not on b⊔G' direction... actually
      -- this is just G' ≠ parallelogram_completion result, i.e., G' ≠ "image of b"
      have hG'_ne_b' : G' ≠ parallelogram_completion G G' b m := by sorry
      have hG'_ne_Cb' : G' ≠ parallelogram_completion G G' C_b m := by sorry
      have hb'_ne_Cb' : parallelogram_completion G G' b m ≠
                         parallelogram_completion G G' C_b m := by sorry

      -- Spanning: G ⊔ b ⊔ C_b = π
      have h_span : G ⊔ b ⊔ C_b = π := by sorry

      -- Well-definedness 1: pc(G, G', b, m) = pc(C, C_a, b, m) = s
      -- where C_a = pc(O, a, C, m) and s = coord_add a b = pc(C, C_a, b, m)
      have hwd1 : parallelogram_completion G G' b m = s := by
        sorry -- well-definedness rebase from (O, a) to (G, G') then to (C, C_a)
      -- Well-definedness 2: pc(G, G', C_b, m) = pc(O, a, C_b, m) = τ_a_C_b
      have hwd2 : parallelogram_completion G G' C_b m = τ_a_C_b := by
        sorry -- well-definedness rebase from (O, a) to (G, G')
      -- Apply cross_parallelism
      have hcp := cross_parallelism hG_atom hG'_atom hb hCb_atom
        hGG' hG_ne_b hG_ne_Cb hb_ne_Cb
        hG'_ne_b' hG'_ne_Cb' hb'_ne_Cb'
        hG_le_π hG'_le_π (hb_on.trans le_sup_left) hCb_le_π
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hm_cov hm_line
        hG_not_m hG'_not_m hb_not_m hCb_not_m
        hb_not_GG' hCb_not_GG' hCb_not_Gb
        h_span
        R hR hR_not h_irred
      -- Rewrite: (b⊔C_b)⊓m = (s⊔τ_a_C_b)⊓m
      rw [hwd1, hwd2] at hcp
      -- And (b⊔C_b)⊓m = E
      exact hcp.symm.trans h_bCb_dir
    · -- G IS on m. Need another atom. Use b and C.
      push_neg at hG_not_m
      sorry -- case: G on m. Use h_irred on b⊔C to find G₂ off m.

  -- ═══ Step 4: Conclude τ_a(C_b) = C_s ═══
  -- s = coord_add a b is an atom on l
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hs_atom : IsAtom s :=
    coord_add_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
  have hs_on_l : s ≤ l := by
    show coord_add Γ a b ≤ Γ.O ⊔ Γ.U
    exact inf_le_right
  -- O ∉ q and a ∉ q (since O, a on l, l ⊓ q = U, and O ≠ U, a ≠ U)
  have hO_not_q : ¬ Γ.O ≤ q := fun h =>
    Γ.hOU ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf le_sup_left h)).resolve_left Γ.hO.1)
  have ha_not_q : ¬ a ≤ q := fun h =>
    ha_ne_U ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf ha_on h)).resolve_left ha.1)
  have hO_ne_Cb : Γ.O ≠ C_b := fun h => hO_not_q (h ▸ hCb_le_q)
  have ha_ne_Cb : a ≠ C_b := fun h => ha_not_q (h ▸ hCb_le_q)
  have hCb_not_l : ¬ C_b ≤ l := fun h => by
    -- C_b ≤ l and C_b ≤ q → C_b ≤ l ⊓ q = U → C_b = U → U on m, contradicts C_b ∉ m? No, U IS on m.
    -- Actually: C_b = U → C_b ≤ m (since U ≤ m). Contradicts hCb_not_m.
    have : C_b ≤ l ⊓ q := le_inf h hCb_le_q
    rw [hlq_eq_U] at this
    exact hCb_not_m ((Γ.hU.le_iff.mp this).resolve_left hCb_atom.1 ▸ le_sup_left)
  have hτ_atom : IsAtom τ_a_C_b :=
    parallelogram_completion_atom Γ.hO ha hCb_atom
      (fun h => ha_ne_O h.symm) hO_ne_Cb ha_ne_Cb
      (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left)
      (hCb_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
      hm_le_π hm_cov hm_line
      Γ.hO_not_m ha_not_m hCb_not_m
      (fun h => hCb_not_l (h.trans (hOa_eq_l ▸ le_refl l)))
  -- O ⊔ E = O ⊔ C (needed in both cases below)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hOE_eq_OC : Γ.O ⊔ Γ.E = Γ.O ⊔ Γ.C := by
    have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
    have h_lt : Γ.O < Γ.O ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => CoordSystem.hOE ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    exact ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hE_le_OC)).resolve_left (ne_of_gt h_lt)

  -- ═══ Case split on s = O ═══
  -- When s = O (additive inverse), C_s = C and τ = C directly.
  -- When s ≠ O, proceed via CovBy chain.
  by_cases hs_eq_O : s = Γ.O
  · -- Case s = O: show τ = C = C_s
    -- (O ⊔ τ) ⊓ m = E (from h_cross with s = O)
    have hE_le_Oτ : Γ.E ≤ Γ.O ⊔ τ_a_C_b := by
      have := h_cross; rw [hs_eq_O] at this; exact this ▸ inf_le_left
    -- O ⊔ E ≤ O ⊔ τ, and O ⊔ E = O ⊔ C, so O ⊔ C ≤ O ⊔ τ
    have hO_ne_τ : Γ.O ≠ τ_a_C_b := fun h => hO_not_q (h ▸ h_τ_le_q)
    have hOC_le_Oτ : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ τ_a_C_b :=
      hOE_eq_OC ▸ sup_le le_sup_left hE_le_Oτ
    -- O ⊔ τ = O ⊔ C by CovBy
    have hOτ_eq_OC : Γ.O ⊔ τ_a_C_b = Γ.O ⊔ Γ.C := by
      have hOC_lt : Γ.O < Γ.O ⊔ Γ.C := lt_of_le_of_ne le_sup_left
        (fun h => hOC ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm)
      exact ((atom_covBy_join Γ.hO hτ_atom hO_ne_τ).eq_or_eq hOC_lt.le
        hOC_le_Oτ).resolve_left (ne_of_gt hOC_lt) |>.symm
    -- τ ≤ O ⊔ C and τ ≤ q. (O ⊔ C) ⊓ q = C by modular law.
    have hτ_le_C : τ_a_C_b ≤ Γ.C := by
      have hτ_le_OC_q : τ_a_C_b ≤ (Γ.O ⊔ Γ.C) ⊓ q :=
        le_inf (hOτ_eq_OC ▸ le_sup_right) h_τ_le_q
      -- (O ⊔ C) ⊓ q = (O ⊔ C) ⊓ (U ⊔ C) = C ⊔ O ⊓ (U ⊔ C) = C ⊔ ⊥ = C
      have hOC_inf_q : (Γ.O ⊔ Γ.C) ⊓ q = Γ.C := by
        have hO_inf_q : Γ.O ⊓ q = ⊥ :=
          (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => hO_not_q (h ▸ inf_le_right))
        calc (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C)
            = (Γ.C ⊔ Γ.O) ⊓ (Γ.C ⊔ Γ.U) := by rw [sup_comm Γ.O Γ.C, sup_comm Γ.U Γ.C]
          _ = Γ.C ⊔ Γ.O ⊓ (Γ.C ⊔ Γ.U) :=
              sup_inf_assoc_of_le Γ.O (le_sup_left : Γ.C ≤ Γ.C ⊔ Γ.U)
          _ = Γ.C ⊔ Γ.O ⊓ q := by rw [show Γ.C ⊔ Γ.U = q from sup_comm Γ.C Γ.U]
          _ = Γ.C := by rw [hO_inf_q, sup_bot_eq]
      exact hOC_inf_q ▸ hτ_le_OC_q
    have hτ_eq_C : τ_a_C_b = Γ.C :=
      (Γ.hC.le_iff.mp hτ_le_C).resolve_left hτ_atom.1
    -- C_s = C when s = O: pc(O, O, C, m) = C ⊓ (O ⊔ E) = C ⊓ (O ⊔ C) = C
    have hCs_eq_C : C_s = Γ.C := by
      show parallelogram_completion Γ.O s Γ.C m = Γ.C
      rw [hs_eq_O]; unfold parallelogram_completion
      have hO_inf_m : Γ.O ⊓ m = ⊥ :=
        (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hO_not_m (h ▸ inf_le_right))
      simp only [sup_idem, hO_inf_m, sup_bot_eq]
      -- Goal: Γ.C ⊓ (Γ.O ⊔ (Γ.O ⊔ Γ.C) ⊓ m) = Γ.C
      rw [show (Γ.O ⊔ Γ.C) ⊓ m = Γ.E from rfl, hOE_eq_OC]
      exact inf_eq_left.mpr le_sup_right
    exact hτ_eq_C.trans hCs_eq_C.symm

  · -- Case s ≠ O: original argument via CovBy chain
    have hs_ne_O : s ≠ Γ.O := hs_eq_O
    -- s ≠ τ (prove early — needed for s ∉ m below)
    have hs_ne_τ : s ≠ τ_a_C_b := by
      intro h
      have hτ_le_U : τ_a_C_b ≤ Γ.U := by
        rw [← hlq_eq_U]; exact le_inf (h ▸ hs_on_l) h_τ_le_q
      have hτ_eq_U := (Γ.hU.le_iff.mp hτ_le_U).resolve_left hτ_atom.1
      have hτ_le_ad : τ_a_C_b ≤ a ⊔ (Γ.O ⊔ C_b) ⊓ m := by
        show parallelogram_completion Γ.O a C_b m ≤ _
        unfold parallelogram_completion; exact inf_le_right
      have hU_le_d : Γ.U ≤ (Γ.O ⊔ C_b) ⊓ m := by
        have : Γ.U ≤ (a ⊔ (Γ.O ⊔ C_b) ⊓ m) ⊓ m :=
          le_inf (hτ_eq_U ▸ hτ_le_ad) (le_sup_left : Γ.U ≤ m)
        rwa [line_direction ha ha_not_m inf_le_right] at this
      have hl_le_OCb : l ≤ Γ.O ⊔ C_b := sup_le le_sup_left (hU_le_d.trans inf_le_left)
      rcases (atom_covBy_join Γ.hO hCb_atom hO_ne_Cb).eq_or_eq le_sup_left hl_le_OCb with h | h
      · exact absurd h (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)
      · exact hCb_not_l (le_sup_right.trans h.symm.le)
    -- s ∉ m: if s ≤ m then s = U, then (U ⊔ τ) ⊓ m = E gives E = U
    have hs_not_m : ¬ s ≤ m := by
      intro h_sm
      have hs_eq_U : s = Γ.U :=
        (Γ.hU.le_iff.mp (Γ.l_inf_m_eq_U ▸ le_inf hs_on_l h_sm)).resolve_left hs_atom.1
      have hτ_ne_U : τ_a_C_b ≠ Γ.U :=
        fun hτU => hs_ne_τ (hs_eq_U.trans hτU.symm)
      have hUτ_dir : (Γ.U ⊔ τ_a_C_b) ⊓ m = Γ.E := by
        have := h_cross; rwa [hs_eq_U] at this
      by_cases hτm : τ_a_C_b ≤ m
      · -- τ ≤ m: U ⊔ τ ≤ m, so (U ⊔ τ) ⊓ m = U ⊔ τ = E. But U < E, contradicting E atom.
        rw [inf_eq_left.mpr (sup_le le_sup_left hτm)] at hUτ_dir
        exact Γ.hEU ((Γ.hE_atom.le_iff.mp
          (hUτ_dir ▸ (atom_covBy_join Γ.hU hτ_atom hτ_ne_U.symm).lt.le)).resolve_left Γ.hU.1).symm
      · -- τ ∉ m: (τ ⊔ U) ⊓ m = U by line_direction. But = E. So E = U.
        rw [show Γ.U ⊔ τ_a_C_b = τ_a_C_b ⊔ Γ.U from sup_comm _ _,
            line_direction hτ_atom hτm (le_sup_left : Γ.U ≤ m)] at hUτ_dir
        exact Γ.hEU hUτ_dir.symm
    have hs_ne_C : s ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hs_on_l)
    have hOs_eq_l : Γ.O ⊔ s = l := by
      have h_lt : Γ.O < Γ.O ⊔ s := lt_of_le_of_ne le_sup_left
        (fun h => hs_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hs_atom.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left hs_on_l)).resolve_left (ne_of_gt h_lt)
    have hCs_atom : IsAtom C_s :=
      parallelogram_completion_atom Γ.hO hs_atom Γ.hC hs_ne_O.symm hOC hs_ne_C
        (le_sup_left.trans le_sup_left) (hs_on_l.trans le_sup_left) Γ.hC_plane
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hs_not_m Γ.hC_not_m
        (fun h => Γ.hC_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
    -- E ≤ s ⊔ τ_a_C_b (from h_cross)
    have hE_le : Γ.E ≤ s ⊔ τ_a_C_b := h_cross ▸ inf_le_left
    have hsE_le_sτ : s ⊔ Γ.E ≤ s ⊔ τ_a_C_b := sup_le le_sup_left hE_le
    -- CovBy chain: s ⊔ E = s ⊔ τ, so τ ≤ s ⊔ E
    have hs_ne_E : s ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hs_on_l)
    have h_sE_eq_sτ : s ⊔ Γ.E = s ⊔ τ_a_C_b := by
      have h_lt : s < s ⊔ Γ.E := lt_of_le_of_ne le_sup_left
        (fun h => hs_ne_E ((hs_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          Γ.hE_atom.1).symm)
      exact ((atom_covBy_join hs_atom hτ_atom hs_ne_τ).eq_or_eq h_lt.le
        hsE_le_sτ).resolve_left (ne_of_gt h_lt)
    have h_τ_le_sE : τ_a_C_b ≤ s ⊔ Γ.E := h_sE_eq_sτ ▸ le_sup_right
    -- τ ≤ C_s = q ⊓ (s ⊔ E)
    have h_τ_le_Cs : τ_a_C_b ≤ C_s := by
      show τ_a_C_b ≤ (Γ.C ⊔ (Γ.O ⊔ s) ⊓ m) ⊓ (s ⊔ (Γ.O ⊔ Γ.C) ⊓ m)
      rw [hOs_eq_l, Γ.l_inf_m_eq_U, sup_comm Γ.C Γ.U]
      exact le_inf h_τ_le_q h_τ_le_sE
    exact (hCs_atom.le_iff.mp h_τ_le_Cs).resolve_left hτ_atom.1

/-- **Associativity of coordinate addition.**

    (a + b) + c = a + (b + c)

    Proof: coord_add = translation application (coord_add_eq_translation),
    and translations form an abelian group (Parts I-IV), so composition
    is associative. -/
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
  /-
  ## Proof (session 48)

  Three ingredients:
  1. Part III parallelism: (C_b ⊔ (b+c)) ⊓ m = (C ⊔ c) ⊓ m = e_c
  2. Key Identity via cross-parallelism: τ_a(C_b) = C_{a+b}
     - Cross-parallelism of τ_a on (b, C_b) gives ((a+b) ⊔ τ_a(C_b)) ⊓ m = E
     - τ_a(C_b) on q and on (a+b)⊔E → τ_a(C_b) = q ⊓ ((a+b)⊔E) = C_{a+b}
  3. Cross-parallelism of τ_a on ((b+c), C_b) gives
     ((a+(b+c)) ⊔ C_{a+b}) ⊓ m = e_c
     → a+(b+c) ≤ C_{a+b} ⊔ e_c
     → a+(b+c) ≤ l ⊓ (C_{a+b} ⊔ e_c) = (a+b)+c
     → a+(b+c) = (a+b)+c  (both atoms)
  -/
  sorry

end Foam.FTPGExplore
