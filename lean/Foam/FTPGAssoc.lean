/-
# Associativity of coordinate addition (Part V)

The final connection: coord_add equals translation application,
then associativity follows from the translation group structure.

- `coord_add_eq_translation`: von Staudt addition = apply translation
- `key_identity`: τ_a(C_b) = C_{a+b}
- `coord_add_assoc`: (a + b) + c = a + (b + c)

## Status (session 56)

1 sorry remains: coord_add_assoc.
key_identity is fully proven (0 sorry).

Session 56: G₂ properties closed (4 sorry → 0).
G₂ = (a⊔E)⊓(b⊔C), the intersection of two lines in π.
- atom: via meet_of_lines_is_atom + veblen_young (two lines in π meet)
- ≠ b: b ≤ a⊔E → b ≤ l⊓(E⊔a) = a → b=a, contradiction
- ≠ C: C ≤ a⊔E → a⊔C = a⊔E (CovBy) → E ≤ (a⊔C)⊓(O⊔C) = C → E=C, C∉m
- ∉ m: G₂ ≤ (a⊔E)⊓m = E → G₂=⊥ or G₂=E; both contradict meet≠⊥ or E∉b⊔C
Key technique: .trans (le_of_eq ...) instead of rw to handle set abbreviations
(definitional equality works, syntactic matching doesn't across set boundaries).

Session 54: pc-distinctness (hb'_ne_Cb') closed via translation injectivity
argument. hwd2 non-collinear case closed via parallelogram_completion_well_defined
with span proof O⊔G⊔C_b=π from covBy_sup_of_inf_covBy_left + by_cases.

Session 52: G construction changed from h_irred(a,C) to h_irred(b,C).
(b⊔C) ⊓ (b⊔E) = b ensures C_b ∉ G⊔b (was unfillable with old choice).
Closed: hCb_not_Gb, h_span (7→5 sorry).
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
    -- Construct G off l, m, q via h_irred on (b, C) instead of (a, C).
    -- Key: (b⊔C) ⊓ (b⊔E) = b (since C ∉ b⊔E), so G on b⊔C avoids b⊔E,
    -- which ensures C_b ∉ G⊔b (needed for cross_parallelism).
    have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)
    obtain ⟨G, hG_atom, hG_le_bC, hG_ne_b_raw, hG_ne_C⟩ := h_irred b Γ.C hb Γ.hC hb_ne_C
    -- G ∉ l: (b⊔C)⊓l = b by modular law, G ≠ b
    have hG_not_l : ¬ G ≤ l := by
      intro hG_l
      have hG_le_b : G ≤ b := by
        have h_inf : G ≤ (b ⊔ Γ.C) ⊓ l := le_inf hG_le_bC hG_l
        rwa [show (b ⊔ Γ.C) ⊓ l = b from by
          rw [sup_comm, inf_comm]; exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on] at h_inf
      exact hG_ne_b_raw ((hb.le_iff.mp hG_le_b).resolve_left hG_atom.1)
    -- G ∉ q: (b⊔C)⊓q = C by modular law, G ≠ C
    have hG_not_q : ¬ G ≤ q := by
      intro hG_q
      have hG_le_C : G ≤ Γ.C := by
        have h_inf : G ≤ (b ⊔ Γ.C) ⊓ q := le_inf hG_le_bC hG_q
        rw [show q = Γ.C ⊔ Γ.U from sup_comm Γ.U Γ.C] at h_inf
        rwa [show (b ⊔ Γ.C) ⊓ (Γ.C ⊔ Γ.U) = Γ.C from by
          rw [inf_comm]
          have hb_not_CU : ¬ b ≤ Γ.C ⊔ Γ.U := by
            intro hle
            have hle' : b ≤ q := hle.trans (sup_comm Γ.C Γ.U).le
            have : b ≤ l ⊓ q := le_inf hb_on hle'
            rw [hlq_eq_U] at this
            exact hb_ne_U ((Γ.hU.le_iff.mp this).resolve_left hb.1)
          exact inf_sup_of_atom_not_le hb hb_not_CU
            (le_sup_left : Γ.C ≤ Γ.C ⊔ Γ.U)] at h_inf
      exact hG_ne_C ((Γ.hC.le_iff.mp hG_le_C).resolve_left hG_atom.1)
    -- G might be on m. Abstract over G to handle both cases.
    suffices hkey : ∀ G₁ : L, IsAtom G₁ → G₁ ≤ b ⊔ Γ.C → G₁ ≠ b → G₁ ≠ Γ.C →
        ¬ G₁ ≤ l → ¬ G₁ ≤ q → ¬ G₁ ≤ m → (s ⊔ τ_a_C_b) ⊓ m = Γ.E by
      by_cases hG_m : G ≤ m
      · -- G on m: construct G₂ = (a ⊔ E) ⊓ (b ⊔ C) off m
        -- G₂ is the intersection of lines a⊔E and b⊔C in π
        set G₂ := (a ⊔ (Γ.O ⊔ Γ.C) ⊓ m) ⊓ (b ⊔ Γ.C)
        -- ── Shared lemmas for G₂ properties ──
        have ha_ne_E : a ≠ (Γ.O ⊔ Γ.C) ⊓ m :=
          fun h => CoordSystem.hE_not_l ((le_of_eq h.symm).trans ha_on)
        have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l ((le_of_eq h.symm).trans ha_on)
        -- a ⊔ b = l (both atoms on l, distinct)
        have hab_eq_l : a ⊔ b = l :=
          ((line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).eq_or_eq
            le_sup_left (sup_le ha_on hb_on)).resolve_left
            (fun h => hab ((ha.le_iff.mp (le_of_le_of_eq le_sup_right h)).resolve_left hb.1).symm)
        -- E ∉ b⊔C: E ≤ O⊔C and E ≤ b⊔C → E ≤ (O⊔C)⊓(b⊔C) = C → E=C, but C∉m
        have hE_not_bC : ¬ (Γ.O ⊔ Γ.C) ⊓ m ≤ b ⊔ Γ.C := by
          intro h
          -- (C⊔O)⊓(C⊔b) = C by modular_intersection
          have h_int : (Γ.C ⊔ Γ.O) ⊓ (Γ.C ⊔ b) = Γ.C :=
            modular_intersection Γ.hC Γ.hO hb hOC.symm hb_ne_C.symm hb_ne_O.symm
              (fun hle => by
                have := (le_inf hb_on hle).trans
                  (le_of_eq (inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ l)))
                exact hb_ne_O ((Γ.hO.le_iff.mp this).resolve_left hb.1))
          -- E ≤ (O⊔C) ⊓ (b⊔C) = C
          have hE_le_C : (Γ.O ⊔ Γ.C) ⊓ m ≤ Γ.C :=
            (le_inf inf_le_left h).trans (le_of_eq (show (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.C) = Γ.C from by
              rw [show (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.C) = (Γ.C ⊔ Γ.O) ⊓ (Γ.C ⊔ b) from by
                rw [sup_comm Γ.O, sup_comm b]]; exact h_int))
          exact Γ.hC_not_m ((le_of_eq ((Γ.hC.le_iff.mp hE_le_C).resolve_left
            Γ.hE_atom.1).symm).trans CoordSystem.hE_on_m)
        -- (a⊔E) ⊓ (b⊔C) ≠ ⊥ (two lines in π meet, via Veblen-Young)
        have h_meet_ne : G₂ ≠ ⊥ := by
          show (a ⊔ (Γ.O ⊔ Γ.C) ⊓ m) ⊓ (b ⊔ Γ.C) ≠ ⊥
          rw [inf_comm]
          exact veblen_young ha hb Γ.hC Γ.hE_atom hab ha_ne_C hb_ne_C ha_ne_E
            (fun hle => Γ.hC_not_l (hle.trans (sup_le ha_on hb_on)))
            (CoordSystem.hE_le_OC.trans (sup_le
              ((le_sup_left : Γ.O ≤ l).trans (le_of_eq hab_eq_l.symm) |>.trans le_sup_left)
              le_sup_right))
            hE_not_bC
        -- ¬ a⊔E ≤ b⊔C (a ≤ b⊔C → a ≤ (b⊔C)⊓l = b → a=b)
        have h_not_le : ¬ a ⊔ (Γ.O ⊔ Γ.C) ⊓ m ≤ b ⊔ Γ.C := by
          intro h
          have : a ≤ (b ⊔ Γ.C) ⊓ l := le_inf (le_sup_left.trans h) ha_on
          rw [show (b ⊔ Γ.C) ⊓ l = b from by
            rw [sup_comm, inf_comm]
            exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on] at this
          exact hab ((hb.le_iff.mp this).resolve_left ha.1)
        -- ── G₂ properties ──
        have hG₂_atom : IsAtom G₂ :=
          meet_of_lines_is_atom ha Γ.hE_atom hb Γ.hC ha_ne_E hb_ne_C h_not_le h_meet_ne
        have hG₂_ne_b : G₂ ≠ b := by
          intro h
          -- b ≤ a⊔E and b ≤ l → b ≤ l ⊓ (E⊔a) = a → b=a
          have h_eq : l ⊓ ((Γ.O ⊔ Γ.C) ⊓ m ⊔ a) = a :=
            inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l ha_on
          have hb_le_a : b ≤ a :=
            (le_inf hb_on (((le_of_eq h.symm).trans inf_le_left).trans
              (le_of_eq (sup_comm a _)))).trans (le_of_eq h_eq)
          exact hab ((ha.le_iff.mp hb_le_a).resolve_left hb.1).symm
        have hG₂_ne_C : G₂ ≠ Γ.C := by
          intro h
          have hC_le_aE : Γ.C ≤ a ⊔ (Γ.O ⊔ Γ.C) ⊓ m := (le_of_eq h.symm).trans inf_le_left
          -- a⊔C = a⊔E by CovBy collapse
          have haE_eq_aC : a ⊔ (Γ.O ⊔ Γ.C) ⊓ m = a ⊔ Γ.C := by
            symm; exact ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq
              (atom_covBy_join ha Γ.hC ha_ne_C).lt.le
              (sup_le le_sup_left hC_le_aE)).resolve_left
              (ne_of_gt (atom_covBy_join ha Γ.hC ha_ne_C).lt)
          -- E ≤ a⊔C and E ≤ O⊔C → E ≤ (a⊔C)⊓(O⊔C) = C
          have hE_le_aC : (Γ.O ⊔ Γ.C) ⊓ m ≤ a ⊔ Γ.C :=
            le_sup_right.trans (le_of_eq haE_eq_aC)
          -- (C⊔a)⊓(C⊔O) = C by modular_intersection
          have h_int : (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.O) = Γ.C :=
            modular_intersection Γ.hC ha Γ.hO ha_ne_C.symm hOC.symm ha_ne_O
              (fun hle => by
                have := (le_inf (le_sup_left : Γ.O ≤ l) hle).trans
                  (le_of_eq (inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on))
                exact ha_ne_O ((ha.le_iff.mp this).resolve_left Γ.hO.1).symm)
          -- E ≤ (a⊔C) ⊓ (O⊔C) = C
          have hE_le_C : (Γ.O ⊔ Γ.C) ⊓ m ≤ Γ.C :=
            (le_inf hE_le_aC CoordSystem.hE_le_OC).trans (le_of_eq (show
              (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C from by
                rw [show (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.O) from by
                  rw [sup_comm a, sup_comm Γ.O]]; exact h_int))
          exact Γ.hC_not_m ((le_of_eq ((Γ.hC.le_iff.mp hE_le_C).resolve_left
            Γ.hE_atom.1).symm).trans CoordSystem.hE_on_m)
        have hG₂_not_m : ¬ G₂ ≤ m := by
          intro hG₂_m
          have hG₂_le_E : G₂ ≤ (Γ.O ⊔ Γ.C) ⊓ m :=
            (le_inf inf_le_left hG₂_m).trans
              (le_of_eq (line_direction ha ha_not_m CoordSystem.hE_on_m))
          rcases Γ.hE_atom.le_iff.mp hG₂_le_E with h | h
          · exact h_meet_ne h
          · exact hE_not_bC ((le_of_eq h.symm).trans inf_le_right)
        have hG₂_not_l : ¬ G₂ ≤ l := by
          intro h
          -- G₂ ≤ (b⊔C) ⊓ l = b (C ∉ l), so G₂ = b. Contradiction.
          have : G₂ ≤ (b ⊔ Γ.C) ⊓ l := le_inf inf_le_right h
          rw [show (b ⊔ Γ.C) ⊓ l = b from by
            rw [sup_comm, inf_comm]
            exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on] at this
          exact hG₂_ne_b ((hb.le_iff.mp this).resolve_left hG₂_atom.1)
        have hG₂_not_q : ¬ G₂ ≤ q := by
          intro h
          -- G₂ ≤ (b⊔C) ⊓ q = C (b ∉ q), so G₂ = C. Contradiction.
          have : G₂ ≤ (b ⊔ Γ.C) ⊓ q := le_inf inf_le_right h
          rw [show (b ⊔ Γ.C) ⊓ q = Γ.C from by
            rw [show q = Γ.C ⊔ Γ.U from sup_comm Γ.U Γ.C, inf_comm]
            exact inf_sup_of_atom_not_le hb (by
              intro hle; have : b ≤ l ⊓ q := le_inf hb_on (hle.trans (sup_comm Γ.C Γ.U).le)
              rw [hlq_eq_U] at this; exact hb_ne_U ((Γ.hU.le_iff.mp this).resolve_left hb.1))
              (le_sup_left : Γ.C ≤ Γ.C ⊔ Γ.U)] at this
          exact hG₂_ne_C ((Γ.hC.le_iff.mp this).resolve_left hG₂_atom.1)
        exact hkey G₂ hG₂_atom inf_le_right hG₂_ne_b hG₂_ne_C hG₂_not_l hG₂_not_q hG₂_not_m
      · exact hkey G hG_atom hG_le_bC hG_ne_b_raw hG_ne_C hG_not_l hG_not_q hG_m
    -- Prove the abstracted statement
    intro G hG_atom hG_le_bC hG_ne_b_raw hG_ne_C hG_not_l hG_not_q hG_not_m
    -- G off l, m, q. Proceed.
    -- G' = pc(O, a, G, m): the image of G under τ_a
    set G' := parallelogram_completion Γ.O a G m
    -- G is in π (G ≤ b⊔C ≤ l⊔C = π)
    have hG_le_π : G ≤ π :=
      hG_le_bC.trans (sup_le (hb_on.trans le_sup_left) Γ.hC_plane)
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
    -- G ≠ G': if G = G' then G ≤ a ⊔ (O⊔G)⊓m (from pc def, inf_le_right).
    -- Intersect with O⊔G: modular law gives G ≤ (O⊔G)⊓m ⊔ (a ⊓ (O⊔G)).
    -- a ∉ O⊔G (else G ≤ l, contradiction), so a ⊓ (O⊔G) = ⊥.
    -- Then G ≤ m, contradicting G ∉ m.
    have hGG' : G ≠ G' := by
      intro h_eq
      -- G = pc(O,a,G,m) = (G ⊔ (O⊔a)⊓m) ⊓ (a ⊔ (O⊔G)⊓m), so G ≤ a ⊔ (O⊔G)⊓m
      have hG_le_ae : G ≤ a ⊔ (Γ.O ⊔ G) ⊓ m := by
        have : G' ≤ a ⊔ (Γ.O ⊔ G) ⊓ m := by
          show parallelogram_completion Γ.O a G m ≤ _
          unfold parallelogram_completion; exact inf_le_right
        exact h_eq ▸ this
      -- G ≤ O ⊔ G trivially
      have hG_le_OG : G ≤ Γ.O ⊔ G := le_sup_right
      -- Intersect: G ≤ (a ⊔ (O⊔G)⊓m) ⊓ (O⊔G)
      have hG_le_both : G ≤ (a ⊔ (Γ.O ⊔ G) ⊓ m) ⊓ (Γ.O ⊔ G) :=
        le_inf hG_le_ae hG_le_OG
      -- Modular law: (O⊔G)⊓m ≤ O⊔G, so (((O⊔G)⊓m) ⊔ a) ⊓ (O⊔G) = (O⊔G)⊓m ⊔ a⊓(O⊔G)
      rw [sup_comm a _, sup_inf_assoc_of_le a (inf_le_left : (Γ.O ⊔ G) ⊓ m ≤ Γ.O ⊔ G)]
        at hG_le_both
      -- a ⊓ (O⊔G) = ⊥: if a ≤ O⊔G then O⊔a ≤ O⊔G; CovBy forces l = O⊔G, so G ≤ l
      have ha_inf_OG : a ⊓ (Γ.O ⊔ G) = ⊥ := by
        rcases ha.le_iff.mp (inf_le_left : a ⊓ (Γ.O ⊔ G) ≤ a) with h | h
        · exact h
        · exfalso
          have ha_le : a ≤ Γ.O ⊔ G := h ▸ inf_le_right
          have hO_ne_G : Γ.O ≠ G := fun heq => hG_not_l (heq ▸ hOa_eq_l ▸ le_sup_left)
          have hO_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
            (fun heq => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans heq.symm.le)).resolve_left ha.1))
          exact hG_not_l (hOa_eq_l ▸
            ((atom_covBy_join Γ.hO hG_atom hO_ne_G).eq_or_eq hO_lt.le
              (sup_le le_sup_left ha_le)).resolve_left (ne_of_gt hO_lt) ▸ le_sup_right)
      rw [ha_inf_OG, sup_bot_eq] at hG_le_both
      -- G ≤ (O⊔G) ⊓ m ≤ m, contradicting G ∉ m
      exact hG_not_m (hG_le_both.trans inf_le_right)

    -- G ≠ b: G ≤ a⊔C, b on l, G ∉ l
    have hG_ne_b : G ≠ b := fun h => hG_not_l (h ▸ hb_on)

    -- G ≠ C_b: G ≤ a⊔C, C_b ≤ q, G ∉ q
    have hG_ne_Cb : G ≠ C_b := fun h => hG_not_q (h ▸ hCb_le_q)

    -- C_b ≤ π: C_b ≤ q = U ⊔ C ≤ π
    have hCb_le_π : C_b ≤ π :=
      hCb_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)

    -- G' ≤ G ⊔ U: from pc def, G' ≤ G ⊔ d where d = (O⊔a)⊓m = l⊓m = U
    have hG'_le_GU : G' ≤ G ⊔ Γ.U := by
      have h1 : G' ≤ G ⊔ (Γ.O ⊔ a) ⊓ m := by
        show parallelogram_completion Γ.O a G m ≤ _
        unfold parallelogram_completion; exact inf_le_left
      exact h1.trans (sup_le le_sup_left
        (by rw [hOa_eq_l, Γ.l_inf_m_eq_U]; exact le_sup_right))
    -- So G ⊔ G' ≤ G ⊔ U
    have hGG'_le_GU : G ⊔ G' ≤ G ⊔ Γ.U := sup_le le_sup_left hG'_le_GU
    -- G ⊓ l = ⊥ (G atom, G ∉ l)
    have hG_inf_l : G ⊓ l = ⊥ :=
      (hG_atom.le_iff.mp inf_le_left).resolve_right (fun h => hG_not_l (h ▸ inf_le_right))
    -- G ⊓ q = ⊥ (G atom, G ∉ q)
    have hG_inf_q : G ⊓ q = ⊥ :=
      (hG_atom.le_iff.mp inf_le_left).resolve_right (fun h => hG_not_q (h ▸ inf_le_right))
    -- b not on G ⊔ G': b ≤ G⊔G' ≤ G⊔U → b ≤ (G⊔U)⊓l = U (modular, G∉l) → b = U
    have hb_not_GG' : ¬ b ≤ G ⊔ G' := by
      intro hb_le
      have : b ≤ (G ⊔ Γ.U) ⊓ l := le_inf (hb_le.trans hGG'_le_GU) hb_on
      rw [sup_comm G _, sup_inf_assoc_of_le G (le_sup_right : Γ.U ≤ l),
          hG_inf_l, sup_bot_eq] at this
      exact hb_ne_U ((Γ.hU.le_iff.mp this).resolve_left hb.1)
    -- C_b not on G ⊔ G': C_b ≤ G⊔G' ≤ G⊔U → C_b ≤ (G⊔U)⊓q = U (modular, G∉q) → C_b = U ≤ m
    have hCb_not_GG' : ¬ C_b ≤ G ⊔ G' := by
      intro hCb_le
      have : C_b ≤ (G ⊔ Γ.U) ⊓ q := le_inf (hCb_le.trans hGG'_le_GU) hCb_le_q
      rw [sup_comm G _, sup_inf_assoc_of_le G (le_sup_left : Γ.U ≤ q),
          hG_inf_q, sup_bot_eq] at this
      exact hCb_not_m ((Γ.hU.le_iff.mp this).resolve_left hCb_atom.1 ▸ le_sup_left)
    -- C ∉ b⊔E: if C ≤ b⊔E then C⊔E = O⊔C ≤ b⊔E, so O ≤ (b⊔E)⊓l = b, O = b.
    have hC_not_bE : ¬ Γ.C ≤ b ⊔ Γ.E := by
      intro hC_le
      have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
        have : Γ.E ≤ Γ.O ⊔ Γ.C := Γ.hE_le_OC
        have hCE_le : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right this
        have hCE_cov : Γ.C ⋖ Γ.C ⊔ Γ.E := atom_covBy_join Γ.hC Γ.hE_atom
          (fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m))
        have hOC_cov : Γ.C ⋖ Γ.C ⊔ Γ.O := atom_covBy_join Γ.hC Γ.hO
          (fun h => Γ.hC_not_l (h ▸ le_sup_left))
        rw [sup_comm] at hOC_cov
        exact (hOC_cov.eq_or_eq hCE_cov.lt.le hCE_le).resolve_left
          (ne_of_gt hCE_cov.lt)
      have hO_le_bE : Γ.O ≤ b ⊔ Γ.E := by
        have : Γ.O ⊔ Γ.C ≤ b ⊔ Γ.E := hCE_eq ▸ sup_le hC_le le_sup_right
        exact le_sup_left.trans this
      have hbE_inf_l : (b ⊔ Γ.E) ⊓ l = b := by
        rw [sup_comm, inf_comm]
        exact inf_sup_of_atom_not_le Γ.hE_atom Γ.hE_not_l hb_on
      have hO_le_b : Γ.O ≤ b := by
        have : Γ.O ≤ (b ⊔ Γ.E) ⊓ l := le_inf hO_le_bE le_sup_left
        rwa [hbE_inf_l] at this
      exact hb_ne_O ((hb.le_iff.mp hO_le_b).resolve_left Γ.hO.1).symm
    -- C_b not on G ⊔ b: if C_b ≤ G⊔b, then since C_b ≤ b⊔E and C_b ≠ b,
    -- G⊔b = b⊔E (CovBy). But G ≤ b⊔C, so G ≤ (b⊔C) ⊓ (b⊔E) = b (modular,
    -- since C ∉ b⊔E). Then G = b, contradicting G ≠ b.
    have hCb_not_Gb : ¬ C_b ≤ G ⊔ b := by
      intro hCb_le
      -- C_b ≤ G ⊔ b and C_b ≤ b ⊔ E, both cover b (C_b ≠ b), so G ⊔ b = b ⊔ E
      have hCb_le_Gb : b ⊔ C_b ≤ G ⊔ b := sup_le le_sup_right hCb_le
      have hCb_le_bE' : b ⊔ C_b ≤ b ⊔ Γ.E := h_bCb_eq_bE ▸ le_refl _
      have hGb_eq_bE : G ⊔ b = b ⊔ Γ.E := by
        have hcov1 := atom_covBy_join hb hG_atom hG_ne_b_raw.symm
        rw [sup_comm] at hcov1
        have hcov2 := atom_covBy_join hb Γ.hE_atom
          (fun h => Γ.hE_not_l (h ▸ hb_on))
        have hbCb_cov : b ⋖ b ⊔ C_b := atom_covBy_join hb hCb_atom hb_ne_Cb
        exact (hcov1.eq_or_eq hbCb_cov.lt.le hCb_le_Gb).resolve_left
          (ne_of_gt hbCb_cov.lt) |>.symm.trans
          ((hcov2.eq_or_eq hbCb_cov.lt.le hCb_le_bE').resolve_left
            (ne_of_gt hbCb_cov.lt))
      -- G ≤ b ⊔ C and G ≤ G ⊔ b = b ⊔ E, so G ≤ (b⊔C) ⊓ (b⊔E) = b
      have hG_le_bE : G ≤ b ⊔ Γ.E := hGb_eq_bE ▸ le_sup_left
      have hG_le_meet : G ≤ (b ⊔ Γ.C) ⊓ (b ⊔ Γ.E) := le_inf hG_le_bC hG_le_bE
      rw [sup_inf_assoc_of_le Γ.C (le_sup_left : b ≤ b ⊔ Γ.E)] at hG_le_meet
      have hC_inf_bE : Γ.C ⊓ (b ⊔ Γ.E) = ⊥ :=
        (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => hC_not_bE (h ▸ inf_le_right))
      rw [hC_inf_bE, sup_bot_eq] at hG_le_meet
      exact hG_ne_b_raw ((hb.le_iff.mp hG_le_meet).resolve_left hG_atom.1)

    -- G' ≠ pc(G,G',b,m): if equal, G' ≤ b ⊔ (G⊔G')⊓m.
    -- Intersect with G⊔G': modular + b∉G⊔G' gives G' ≤ m. Contradiction.
    have hG'_ne_b' : G' ≠ parallelogram_completion G G' b m := by
      intro h_eq
      have hle : G' ≤ b ⊔ (G ⊔ G') ⊓ m :=
        h_eq.le.trans (by unfold parallelogram_completion; exact inf_le_left)
      have h1 : G' ≤ (b ⊔ (G ⊔ G') ⊓ m) ⊓ (G ⊔ G') := le_inf hle le_sup_right
      rw [sup_comm b _, sup_inf_assoc_of_le b
        (inf_le_left : (G ⊔ G') ⊓ m ≤ G ⊔ G')] at h1
      have hb_inf : b ⊓ (G ⊔ G') = ⊥ :=
        (hb.le_iff.mp inf_le_left).resolve_right (fun h => hb_not_GG' (h ▸ inf_le_right))
      rw [hb_inf, sup_bot_eq] at h1
      exact hG'_not_m (h1.trans inf_le_right)
    -- G' ≠ pc(G,G',C_b,m): same pattern with C_b∉G⊔G'.
    have hG'_ne_Cb' : G' ≠ parallelogram_completion G G' C_b m := by
      intro h_eq
      have hle : G' ≤ C_b ⊔ (G ⊔ G') ⊓ m :=
        h_eq.le.trans (by unfold parallelogram_completion; exact inf_le_left)
      have h1 : G' ≤ (C_b ⊔ (G ⊔ G') ⊓ m) ⊓ (G ⊔ G') := le_inf hle le_sup_right
      rw [sup_comm C_b _, sup_inf_assoc_of_le C_b
        (inf_le_left : (G ⊔ G') ⊓ m ≤ G ⊔ G')] at h1
      have hCb_inf : C_b ⊓ (G ⊔ G') = ⊥ :=
        (hCb_atom.le_iff.mp inf_le_left).resolve_right
          (fun h => hCb_not_GG' (h ▸ inf_le_right))
      rw [hCb_inf, sup_bot_eq] at h1
      exact hG'_not_m (h1.trans inf_le_right)
    have hb'_ne_Cb' : parallelogram_completion G G' b m ≠
                       parallelogram_completion G G' C_b m := by
      intro h_eq
      -- d = (G⊔G')⊓m = U
      have hG_ne_U : G ≠ Γ.U := fun h => hG_not_m (h ▸ le_sup_left)
      have hGG'_eq_GU : G ⊔ G' = G ⊔ Γ.U :=
        ((atom_covBy_join hG_atom Γ.hU hG_ne_U).eq_or_eq
          (atom_covBy_join hG_atom hG'_atom hGG').lt.le hGG'_le_GU).resolve_left
          (ne_of_gt (atom_covBy_join hG_atom hG'_atom hGG').lt)
      have hG_inf_m : G ⊓ m = ⊥ :=
        (hG_atom.le_iff.mp inf_le_left).resolve_right
          (fun h => hG_not_m (h ▸ inf_le_right))
      have hd_eq_U : (G ⊔ G') ⊓ m = Γ.U := by
        rw [hGG'_eq_GU, sup_comm, sup_inf_assoc_of_le G (le_sup_left : Γ.U ≤ m),
            hG_inf_m, sup_bot_eq]
      -- C_b not on l
      have hCb_not_l : ¬ C_b ≤ l := by
        intro h
        have : C_b ≤ l ⊓ q := le_inf h hCb_le_q
        rw [hlq_eq_U] at this
        exact hCb_not_m ((Γ.hU.le_iff.mp this).resolve_left hCb_atom.1 ▸ le_sup_left)
      -- b' ≤ b ⊔ U (first factor of pc(G,G',b,m))
      have hb'_le_bU : parallelogram_completion G G' b m ≤ b ⊔ Γ.U := by
        have h := show parallelogram_completion G G' b m ≤ b ⊔ (G ⊔ G') ⊓ m from by
          unfold parallelogram_completion; exact inf_le_left
        rwa [hd_eq_U] at h
      -- b' ≤ C_b ⊔ U (first factor of pc(G,G',C_b,m), via h_eq)
      have hb'_le_CbU : parallelogram_completion G G' b m ≤ C_b ⊔ Γ.U := by
        have h := show parallelogram_completion G G' C_b m ≤ C_b ⊔ (G ⊔ G') ⊓ m from by
          unfold parallelogram_completion; exact inf_le_left
        rw [hd_eq_U] at h; exact h_eq.le.trans h
      -- b ⊔ U = l
      have hbU_eq_l : b ⊔ Γ.U = l := by
        show b ⊔ Γ.U = Γ.O ⊔ Γ.U
        rw [sup_comm b, sup_comm Γ.O]
        exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq
          (atom_covBy_join Γ.hU hb (fun h => hb_ne_U h.symm)).lt.le
          (sup_le le_sup_left (hb_on.trans (sup_comm Γ.O Γ.U).le))).resolve_left
          (ne_of_gt (atom_covBy_join Γ.hU hb (fun h => hb_ne_U h.symm)).lt)
      -- b' ≤ l ⊓ (C_b ⊔ U) = U (line_direction: C_b off l, U on l)
      have hb'_le_U : parallelogram_completion G G' b m ≤ Γ.U := by
        have hCbU_inf_l : (C_b ⊔ Γ.U) ⊓ l = Γ.U :=
          line_direction hCb_atom hCb_not_l (show Γ.U ≤ l from le_sup_right)
        calc parallelogram_completion G G' b m
            ≤ l ⊓ (C_b ⊔ Γ.U) := le_inf (hb'_le_bU.trans hbU_eq_l.le) hb'_le_CbU
          _ = (C_b ⊔ Γ.U) ⊓ l := inf_comm _ _
          _ = Γ.U := hCbU_inf_l
      -- b' ≤ m
      have hb'_le_m : parallelogram_completion G G' b m ≤ m :=
        hb'_le_U.trans (le_sup_left : Γ.U ≤ m)
      -- b' ≤ (G⊔b)⊓m: from second factor + b'≤m, line_direction collapse
      have hb'_le_eb : parallelogram_completion G G' b m ≤ (G ⊔ b) ⊓ m := by
        have h1 : parallelogram_completion G G' b m ≤ G' ⊔ (G ⊔ b) ⊓ m := by
          unfold parallelogram_completion; exact inf_le_right
        have h2 := le_inf h1 hb'_le_m
        rwa [line_direction hG'_atom hG'_not_m (inf_le_right : (G ⊔ b) ⊓ m ≤ m)] at h2
      -- b' ≤ (G⊔C_b)⊓m: same via h_eq
      have hb'_le_eCb : parallelogram_completion G G' b m ≤ (G ⊔ C_b) ⊓ m := by
        have h1 : parallelogram_completion G G' C_b m ≤ G' ⊔ (G ⊔ C_b) ⊓ m := by
          unfold parallelogram_completion; exact inf_le_right
        have h2 := le_inf (h_eq.le.trans h1) hb'_le_m
        rwa [line_direction hG'_atom hG'_not_m (inf_le_right : (G ⊔ C_b) ⊓ m ≤ m)] at h2
      -- (G⊔b)⊓m and (G⊔C_b)⊓m are distinct atoms on m
      have heb_atom : IsAtom ((G ⊔ b) ⊓ m) :=
        line_meets_m_at_atom hG_atom hb hG_ne_b
          (sup_le hG_le_π (hb_on.trans le_sup_left)) hm_le_π hm_cov hG_not_m
      have heCb_atom : IsAtom ((G ⊔ C_b) ⊓ m) :=
        line_meets_m_at_atom hG_atom hCb_atom hG_ne_Cb
          (sup_le hG_le_π hCb_le_π) hm_le_π hm_cov hG_not_m
      have heb_ne_eCb : (G ⊔ b) ⊓ m ≠ (G ⊔ C_b) ⊓ m := by
        intro h_eq_dir
        have heb_le_GCb : (G ⊔ b) ⊓ m ≤ G ⊔ C_b := by
          calc (G ⊔ b) ⊓ m = (G ⊔ C_b) ⊓ m := h_eq_dir
            _ ≤ G ⊔ C_b := inf_le_left
        have heb_le_G : (G ⊔ b) ⊓ m ≤ G := by
          have h := le_inf (inf_le_left : (G ⊔ b) ⊓ m ≤ G ⊔ b) heb_le_GCb
          rwa [modular_intersection hG_atom hb hCb_atom hG_ne_b hG_ne_Cb hb_ne_Cb hCb_not_Gb] at h
        exact hG_not_m ((hG_atom.le_iff.mp heb_le_G).resolve_left heb_atom.1 ▸
          (inf_le_right : (G ⊔ b) ⊓ m ≤ m))
      -- b' is an atom
      have hb'_atom : IsAtom (parallelogram_completion G G' b m) :=
        parallelogram_completion_atom hG_atom hG'_atom hb
          hGG' hG_ne_b
          (fun h => hb_not_GG' ((le_of_eq h.symm).trans le_sup_right))
          hG_le_π hG'_le_π (hb_on.trans le_sup_left)
          hm_le_π hm_cov hm_line
          hG_not_m hG'_not_m hb_not_m hb_not_GG'
      -- b' ≤ two distinct atoms → b' ≤ ⊥ → contradiction
      have h_meet_bot : (G ⊔ b) ⊓ m ⊓ ((G ⊔ C_b) ⊓ m) = ⊥ := by
        rcases heb_atom.le_iff.mp (inf_le_left) with h | h
        · exact h
        · exact absurd ((heCb_atom.le_iff.mp
            (le_of_eq h.symm |>.trans inf_le_right)).resolve_left heb_atom.1) heb_ne_eCb
      exact hb'_atom.1 (le_antisymm
        (h_meet_bot.symm ▸ le_inf hb'_le_eb hb'_le_eCb) bot_le)

    -- Spanning: G ⊔ b ⊔ C_b = π
    -- G ≤ b⊔C, so G⊔b⊔C_b ≥ b⊔C. And C_b ≤ q = U⊔C, C_b ≠ C, so C⊔C_b = q.
    -- Then G⊔b⊔C_b ≥ b⊔C⊔C_b ≥ C⊔C_b = q ≥ U. Also ≥ b. So ≥ b⊔U = l.
    -- Then ≥ l⊔C = π (C ∉ l).
    have h_span : G ⊔ b ⊔ C_b = π := by
      apply le_antisymm
      · exact sup_le (sup_le hG_le_π (hb_on.trans le_sup_left)) hCb_le_π
      · -- Show π ≤ G ⊔ b ⊔ C_b
        -- C ≤ G ⊔ b ⊔ C_b: G ≤ b⊔C and G ≠ b ⇒ G⊔b = b⊔C ⇒ C ≤ G⊔b
        have hGb_eq_bC : G ⊔ b = b ⊔ Γ.C := by
          have hGb_le : G ⊔ b ≤ b ⊔ Γ.C := sup_le hG_le_bC le_sup_left
          have hcov1 : b ⋖ b ⊔ G := atom_covBy_join hb hG_atom hG_ne_b_raw.symm
          have hcov2 : b ⋖ b ⊔ Γ.C := atom_covBy_join hb Γ.hC hb_ne_C
          rw [sup_comm] at hcov1
          exact (hcov2.eq_or_eq hcov1.lt.le hGb_le).resolve_left (ne_of_gt hcov1.lt)
        have hC_le : Γ.C ≤ G ⊔ b ⊔ C_b :=
          (le_sup_right.trans hGb_eq_bC.symm.le).trans le_sup_left
        -- C ⊔ C_b = q (both atoms on q, C ≠ C_b)
        have hC_ne_Cb : Γ.C ≠ C_b := by
          intro h; exact hC_not_bE (h ▸ hCb_le_bE)
        have hCCb_eq_q : Γ.C ⊔ C_b = q := by
          have hCCb_le : Γ.C ⊔ C_b ≤ q := sup_le (le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C) hCb_le_q
          have hcov1 : Γ.C ⋖ Γ.C ⊔ C_b := atom_covBy_join Γ.hC hCb_atom hC_ne_Cb
          have hcov2 : Γ.C ⋖ q := by
            show Γ.C ⋖ Γ.U ⊔ Γ.C; rw [sup_comm]
            exact atom_covBy_join Γ.hC Γ.hU
              (fun h => Γ.hC_not_l (h ▸ le_sup_right))
          exact (hcov2.eq_or_eq hcov1.lt.le hCCb_le).resolve_left (ne_of_gt hcov1.lt)
        -- U ≤ G ⊔ b ⊔ C_b (since U ≤ q = C ⊔ C_b ≤ G ⊔ b ⊔ C_b)
        have hU_le : Γ.U ≤ G ⊔ b ⊔ C_b := by
          have : Γ.U ≤ q := le_sup_left
          exact this.trans (hCCb_eq_q ▸ sup_le hC_le le_sup_right)
        -- l = b ⊔ U ≤ G ⊔ b ⊔ C_b
        have hl_le : l ≤ G ⊔ b ⊔ C_b := by
          have hb_le : b ≤ G ⊔ b ⊔ C_b := le_sup_right.trans le_sup_left
          have hbU : b ⊔ Γ.U ≤ G ⊔ b ⊔ C_b := sup_le hb_le hU_le
          have hbU_eq_l : b ⊔ Γ.U = l := by
            have hcov1 : Γ.U ⋖ Γ.U ⊔ b := atom_covBy_join Γ.hU hb hb_ne_U.symm
            have hcov2 : Γ.U ⋖ l := by
              show Γ.U ⋖ Γ.O ⊔ Γ.U; rw [sup_comm]
              exact atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm
            have hbU_le : Γ.U ⊔ b ≤ l := sup_le le_sup_right hb_on
            exact (sup_comm Γ.U b).symm.trans
              ((hcov2.eq_or_eq hcov1.lt.le hbU_le).resolve_left (ne_of_gt hcov1.lt))
          rwa [hbU_eq_l] at hbU
        -- π = l ⊔ C ≤ G ⊔ b ⊔ C_b (C ∉ l)
        have hlC_eq_π : l ⊔ Γ.C = π := by
          have hlC_le : l ⊔ Γ.C ≤ π := sup_le le_sup_left Γ.hC_plane
          have hl_cov : l ⋖ π := by
            have hV_inf_l : Γ.V ⊓ l = ⊥ := by
              exact (Γ.hV.le_iff.mp inf_le_left).resolve_right
                (fun h => Γ.hV_off (h ▸ inf_le_right))
            show l ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
            rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = l ⊔ Γ.V from rfl]
            rw [sup_comm l Γ.V]
            exact covBy_sup_of_inf_covBy_left (hV_inf_l ▸ Γ.hV.bot_covBy)
          have hlC_gt : l < l ⊔ Γ.C := by
            apply lt_of_le_of_ne le_sup_left
            intro h
            have hC_le_l : Γ.C ≤ l := by
              have : l ⊔ Γ.C ≤ l := h.symm.le
              exact le_sup_right.trans this
            exact Γ.hC_not_l hC_le_l
          exact (hl_cov.eq_or_eq hlC_gt.le hlC_le).resolve_left (ne_of_gt hlC_gt)
        rw [← hlC_eq_π]
        exact sup_le hl_le hC_le

    -- Well-definedness 1: pc(G, G', b, m) = pc(C, C_a, b, m) = s
    -- where C_a = pc(O, a, C, m) and s = coord_add a b = pc(C, C_a, b, m)
    have hwd1 : parallelogram_completion G G' b m = s := by
      -- s = pc(C, C_a, b, m) via coord_add_eq_translation
      set C_a := parallelogram_completion Γ.O a Γ.C m
      have hs_eq : s = parallelogram_completion Γ.C C_a b m :=
        coord_add_eq_translation Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O
          ha_ne_U hb_ne_U hab R hR hR_not h_irred
      rw [hs_eq]
      -- Unfold both pc's
      change (b ⊔ (G ⊔ G') ⊓ m) ⊓ (G' ⊔ (G ⊔ b) ⊓ m) =
             (b ⊔ (Γ.C ⊔ C_a) ⊓ m) ⊓ (C_a ⊔ (Γ.C ⊔ b) ⊓ m)
      -- ── (G⊔G')⊓m = U ──
      have hG_ne_U : G ≠ Γ.U := fun h => hG_not_m (h ▸ le_sup_left)
      have hGG'_eq_GU : G ⊔ G' = G ⊔ Γ.U :=
        ((atom_covBy_join hG_atom Γ.hU hG_ne_U).eq_or_eq
          (atom_covBy_join hG_atom hG'_atom hGG').lt.le hGG'_le_GU).resolve_left
          (ne_of_gt (atom_covBy_join hG_atom hG'_atom hGG').lt)
      have hG_inf_m : G ⊓ m = ⊥ :=
        (hG_atom.le_iff.mp inf_le_left).resolve_right
          (fun h => hG_not_m (h ▸ inf_le_right))
      have hGG'_dir : (G ⊔ G') ⊓ m = Γ.U := by
        rw [hGG'_eq_GU, sup_comm, sup_inf_assoc_of_le G (le_sup_left : Γ.U ≤ m),
            hG_inf_m, sup_bot_eq]
      -- ── G⊔b = b⊔C (CovBy, since G ≤ b⊔C) ──
      have hGb_eq_bC : G ⊔ b = b ⊔ Γ.C := by
        have hcov1 : b ⋖ b ⊔ G := atom_covBy_join hb hG_atom hG_ne_b.symm
        rw [sup_comm] at hcov1
        exact ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq hcov1.lt.le
          (sup_le hG_le_bC le_sup_left)).resolve_left (ne_of_gt hcov1.lt)
      -- ── C_a facts ──
      have hCa_le_CU : C_a ≤ Γ.C ⊔ Γ.U := by
        have h1 : C_a ≤ Γ.C ⊔ (Γ.O ⊔ a) ⊓ m := by
          show parallelogram_completion Γ.O a Γ.C m ≤ _
          unfold parallelogram_completion; exact inf_le_left
        exact h1.trans (sup_le le_sup_left
          (by rw [hOa_eq_l, Γ.l_inf_m_eq_U]; exact le_sup_right))
      have hC_ne_Ca : Γ.C ≠ C_a := by
        intro h_eq
        have hCa_le2 : C_a ≤ a ⊔ (Γ.O ⊔ Γ.C) ⊓ m := by
          show parallelogram_completion Γ.O a Γ.C m ≤ _
          unfold parallelogram_completion; exact inf_le_right
        have hC_le_both : Γ.C ≤ ((Γ.O ⊔ Γ.C) ⊓ m ⊔ a) ⊓ (Γ.O ⊔ Γ.C) :=
          le_inf (sup_comm a _ ▸ (h_eq ▸ hCa_le2)) le_sup_right
        rw [sup_inf_assoc_of_le a (inf_le_left : (Γ.O ⊔ Γ.C) ⊓ m ≤ Γ.O ⊔ Γ.C)]
          at hC_le_both
        have ha_not_OC : ¬ a ≤ Γ.O ⊔ Γ.C := by
          intro ha_le
          have hU_ne_C : Γ.U ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ le_sup_left)
          have h_lOC : l ⊓ (Γ.O ⊔ Γ.C) = Γ.O :=
            modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU hOC hU_ne_C Γ.hC_not_l
          have ha_le_O : a ≤ Γ.O := by
            have := le_inf ha_on ha_le; rw [h_lOC] at this; exact this
          exact ha_ne_O ((Γ.hO.le_iff.mp ha_le_O).resolve_left ha.1)
        have : a ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
          (ha.le_iff.mp inf_le_left).resolve_right
            (fun h => ha_not_OC (h ▸ inf_le_right))
        rw [this, sup_bot_eq] at hC_le_both
        exact Γ.hC_not_m (hC_le_both.trans inf_le_right)
      -- C_a is an atom
      have hO_ne_G : Γ.O ≠ G := fun h => hG_not_l (h ▸ le_sup_left)
      have hCa_atom : IsAtom C_a :=
        parallelogram_completion_atom Γ.hO ha Γ.hC
          (fun h => ha_ne_O h.symm) hOC
          (fun h => Γ.hC_not_l (h ▸ ha_on))
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) Γ.hC_plane
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m Γ.hC_not_m
          (fun h => Γ.hC_not_l (h.trans hOa_eq_l.le))
      -- C_a not on m
      have hCa_not_m : ¬ C_a ≤ m := by
        intro hCa_m
        -- C_a ≤ (C⊔U) ⊓ m = U (modular law, C ∉ m)
        have hCa_le_U : C_a ≤ Γ.U := by
          have h : C_a ≤ (Γ.C ⊔ Γ.U) ⊓ m := le_inf hCa_le_CU hCa_m
          rw [sup_comm, sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ m)] at h
          have hCm : Γ.C ⊓ m = ⊥ :=
            (Γ.hC.le_iff.mp inf_le_left).resolve_right
              (fun h => Γ.hC_not_m (h ▸ inf_le_right))
          rwa [hCm, sup_bot_eq] at h
        -- C_a = U (atoms)
        have hCa_eq_U : C_a = Γ.U :=
          (Γ.hU.le_iff.mp hCa_le_U).resolve_left hCa_atom.1
        -- U = C_a ≤ a ⊔ (O⊔C)⊓m (second factor of pc)
        have hCa_le2 : C_a ≤ a ⊔ (Γ.O ⊔ Γ.C) ⊓ m := by
          show parallelogram_completion Γ.O a Γ.C m ≤ _
          unfold parallelogram_completion; exact inf_le_right
        -- U ≤ a ⊔ E and U ≤ m. line_direction: (a ⊔ E) ⊓ m = E. So U ≤ E.
        have hU_le_E : Γ.U ≤ (Γ.O ⊔ Γ.C) ⊓ m := by
          have hdir : (a ⊔ (Γ.O ⊔ Γ.C) ⊓ m) ⊓ m = (Γ.O ⊔ Γ.C) ⊓ m :=
            line_direction ha ha_not_m (inf_le_right : (Γ.O ⊔ Γ.C) ⊓ m ≤ m)
          have : Γ.U ≤ (a ⊔ (Γ.O ⊔ Γ.C) ⊓ m) ⊓ m :=
            le_inf (hCa_eq_U ▸ hCa_le2) (le_sup_left : Γ.U ≤ m)
          rwa [hdir] at this
        -- U ≤ E = Γ.E. But E ≠ U.
        exact Γ.hEU ((Γ.hE_atom.le_iff.mp hU_le_E).resolve_left Γ.hU.1).symm
      -- (C ⊔ C_a) ⊓ m = U
      have hCCa_eq_CU : Γ.C ⊔ C_a = Γ.C ⊔ Γ.U := by
        have hcov1 : Γ.C ⋖ Γ.C ⊔ C_a := atom_covBy_join Γ.hC hCa_atom hC_ne_Ca
        have hcov2 : Γ.C ⋖ Γ.C ⊔ Γ.U := atom_covBy_join Γ.hC Γ.hU
          (fun h => Γ.hC_not_m (h ▸ le_sup_left))
        exact (hcov2.eq_or_eq hcov1.lt.le
          (sup_le le_sup_left hCa_le_CU)).resolve_left (ne_of_gt hcov1.lt)
      have hCCa_dir : (Γ.C ⊔ C_a) ⊓ m = Γ.U := by
        rw [hCCa_eq_CU, sup_comm, sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ m)]
        have : Γ.C ⊓ m = ⊥ :=
          (Γ.hC.le_iff.mp inf_le_left).resolve_right
            (fun h => Γ.hC_not_m (h ▸ inf_le_right))
        rw [this, sup_bot_eq]
      -- ── Rewrite direction terms ──
      rw [hGG'_dir, hCCa_dir, hGb_eq_bC, sup_comm Γ.C b]
      -- Goal: (b ⊔ U) ⊓ (G' ⊔ (b ⊔ C) ⊓ m) = (b ⊔ U) ⊓ (C_a ⊔ (b ⊔ C) ⊓ m)
      -- ── Cross-parallelism + CovBy collapse ──
      -- Suffices: G' ⊔ (b⊔C)⊓m = C_a ⊔ (b⊔C)⊓m
      have hsuff : G' ⊔ (b ⊔ Γ.C) ⊓ m = C_a ⊔ (b ⊔ Γ.C) ⊓ m := by
        -- ── Preconditions for cross_parallelism(O, a, G, C) ──
        -- a ≠ G': if equal, a ≤ G⊔U → a ≤ (G⊔U)⊓l = U → a = U
        have ha_ne_G' : a ≠ G' := by
          intro h_eq
          have : a ≤ (G ⊔ Γ.U) ⊓ l := le_inf (h_eq ▸ hG'_le_GU) ha_on
          rw [sup_comm G _, sup_inf_assoc_of_le G (le_sup_right : Γ.U ≤ l),
              hG_inf_l, sup_bot_eq] at this
          exact ha_ne_U ((Γ.hU.le_iff.mp this).resolve_left ha.1)
        -- a ≠ C_a: if equal, a ≤ C⊔U → a ≤ q⊓l = U → a = U
        have ha_ne_Ca : a ≠ C_a := by
          intro h_eq
          have : a ≤ l ⊓ q := le_inf ha_on
            ((h_eq ▸ hCa_le_CU).trans (sup_comm Γ.C Γ.U).le)
          rw [hlq_eq_U] at this
          exact ha_ne_U ((Γ.hU.le_iff.mp this).resolve_left ha.1)
        -- G' ≠ C_a: if equal, G' ≤ C⊔U ∩ G⊔U = U → G' on m
        have hG'_ne_Ca : G' ≠ C_a := by
          intro h_eq
          have hC_not_GU : ¬ Γ.C ≤ G ⊔ Γ.U := by
            intro hC_le
            have : Γ.C ≤ (G ⊔ Γ.U) ⊓ q := le_inf hC_le (le_sup_right : Γ.C ≤ q)
            rw [sup_comm G _, sup_inf_assoc_of_le G (le_sup_left : Γ.U ≤ q),
                hG_inf_q, sup_bot_eq] at this
            exact Γ.hC_not_m ((Γ.hU.le_iff.mp this).resolve_left Γ.hC.1 ▸ le_sup_left)
          have : G' ≤ (Γ.C ⊔ Γ.U) ⊓ (G ⊔ Γ.U) :=
            le_inf (h_eq ▸ hCa_le_CU) hG'_le_GU
          rw [sup_comm Γ.C _, sup_inf_assoc_of_le Γ.C (le_sup_right : Γ.U ≤ G ⊔ Γ.U)]
            at this
          have hC_inf_GU : Γ.C ⊓ (G ⊔ Γ.U) = ⊥ :=
            (Γ.hC.le_iff.mp inf_le_left).resolve_right
              (fun h => hC_not_GU (h ▸ inf_le_right))
          rw [hC_inf_GU, sup_bot_eq] at this
          exact hG'_not_m (this.trans (le_sup_left : Γ.U ≤ m))
        -- C ∉ O⊔G: O⊔G = π would give O < l ≤ π = O⊔G, contradicting O ⋖ O⊔G
        have hC_not_OG : ¬ Γ.C ≤ Γ.O ⊔ G := by
          intro hC_le
          -- G⊔C = b⊔C (CovBy)
          have hGC_eq_bC : G ⊔ Γ.C = b ⊔ Γ.C := by
            have hcov : G ⋖ b ⊔ Γ.C := by
              have := atom_covBy_join hG_atom hb hG_ne_b; rwa [hGb_eq_bC] at this
            exact (hcov.eq_or_eq le_sup_left (sup_le hG_le_bC le_sup_right)).resolve_left
              (ne_of_gt (lt_of_le_of_ne le_sup_left
                (fun h => hG_ne_C ((hG_atom.le_iff.mp
                  (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm)))
          -- O⊔G⊔C = O⊔(b⊔C) = l⊔C = π, but C ≤ O⊔G so O⊔G = π
          have hOG_eq_π : Γ.O ⊔ G = π := by
            have h_eq : Γ.O ⊔ G ⊔ Γ.C = l ⊔ Γ.C := by
              rw [sup_assoc, hGC_eq_bC, ← sup_assoc, hOb_eq_l]
            have h_col : Γ.O ⊔ G ⊔ Γ.C = Γ.O ⊔ G :=
              le_antisymm (sup_le le_rfl hC_le) le_sup_left
            -- l ⊔ C = π
            have hl_cov_π : l ⋖ π := by
              have hV_inf_l : Γ.V ⊓ l = ⊥ :=
                (Γ.hV.le_iff.mp inf_le_left).resolve_right
                  (fun h => Γ.hV_off (h ▸ inf_le_right))
              show l ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
              rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = l ⊔ Γ.V from rfl, sup_comm l Γ.V]
              exact covBy_sup_of_inf_covBy_left (hV_inf_l ▸ Γ.hV.bot_covBy)
            have hlC_eq_π : l ⊔ Γ.C = π := by
              have hlC_gt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
                (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
              exact (hl_cov_π.eq_or_eq hlC_gt.le
                (sup_le le_sup_left Γ.hC_plane)).resolve_left hlC_gt.ne'
            rw [← h_col, h_eq, hlC_eq_π]
          -- O < l ≤ O⊔G = π, contradicting O ⋖ O⊔G
          have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hOU ((Γ.hO.le_iff.mp
              (le_sup_right.trans h.symm.le)).resolve_left Γ.hU.1).symm)
          exact hG_not_l (((atom_covBy_join Γ.hO hG_atom hO_ne_G).eq_or_eq hO_lt_l.le
            (hOG_eq_π ▸ le_sup_left)).resolve_left hO_lt_l.ne' ▸ le_sup_right)
        -- O⊔G⊔C = π (span for cross_parallelism)
        have hOGC_span : Γ.O ⊔ G ⊔ Γ.C = π := by
          have hGC_eq_bC : G ⊔ Γ.C = b ⊔ Γ.C := by
            have hcov : G ⋖ b ⊔ Γ.C := by
              have := atom_covBy_join hG_atom hb hG_ne_b; rwa [hGb_eq_bC] at this
            exact (hcov.eq_or_eq le_sup_left (sup_le hG_le_bC le_sup_right)).resolve_left
              (ne_of_gt (lt_of_le_of_ne le_sup_left
                (fun h => hG_ne_C ((hG_atom.le_iff.mp
                  (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm)))
          rw [sup_assoc, hGC_eq_bC, ← sup_assoc, hOb_eq_l]
          have hl_cov_π : l ⋖ π := by
            have hV_inf_l : Γ.V ⊓ l = ⊥ :=
              (Γ.hV.le_iff.mp inf_le_left).resolve_right
                (fun h => Γ.hV_off (h ▸ inf_le_right))
            show l ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
            rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = l ⊔ Γ.V from rfl, sup_comm l Γ.V]
            exact covBy_sup_of_inf_covBy_left (hV_inf_l ▸ Γ.hV.bot_covBy)
          have hlC_gt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
          exact (hl_cov_π.eq_or_eq hlC_gt.le
            (sup_le le_sup_left Γ.hC_plane)).resolve_left hlC_gt.ne'
        -- C_a ≤ π
        have hCa_le_π : C_a ≤ π :=
          hCa_le_CU.trans (sup_le Γ.hC_plane (le_sup_right.trans le_sup_left))
        -- ── Apply cross_parallelism ──
        have hcp := cross_parallelism Γ.hO ha hG_atom Γ.hC
          (fun h => ha_ne_O h.symm) hO_ne_G hOC hG_ne_C
          ha_ne_G' ha_ne_Ca hG'_ne_Ca
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hG_le_π Γ.hC_plane
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m hG_not_m Γ.hC_not_m
          (fun h => hG_not_l (h.trans hOa_eq_l.le))
          (fun h => Γ.hC_not_l (h.trans hOa_eq_l.le))
          hC_not_OG
          hOGC_span
          R hR hR_not h_irred
        -- hcp : (G ⊔ C) ⊓ m = (G' ⊔ C_a) ⊓ m
        -- G⊔C = b⊔C (same CovBy as in hOGC_span)
        have hGC_eq_bC : G ⊔ Γ.C = b ⊔ Γ.C := by
          have hcov : G ⋖ b ⊔ Γ.C := by
            have := atom_covBy_join hG_atom hb hG_ne_b; rwa [hGb_eq_bC] at this
          exact (hcov.eq_or_eq le_sup_left (sup_le hG_le_bC le_sup_right)).resolve_left
            (ne_of_gt (lt_of_le_of_ne le_sup_left
              (fun h => hG_ne_C ((hG_atom.le_iff.mp
                (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm)))
        -- e := (b⊔C)⊓m = (G'⊔C_a)⊓m, so e ≤ G'⊔C_a
        have he_eq : (b ⊔ Γ.C) ⊓ m = (G' ⊔ C_a) ⊓ m := hGC_eq_bC ▸ hcp
        have he_le : (b ⊔ Γ.C) ⊓ m ≤ G' ⊔ C_a := he_eq ▸ inf_le_left
        -- CovBy collapse: G'⊔e = G'⊔C_a = C_a⊔G' = C_a⊔e
        have he_ne_G' : (b ⊔ Γ.C) ⊓ m ≠ G' := fun h => hG'_not_m (h ▸ inf_le_right)
        have he_ne_Ca : (b ⊔ Γ.C) ⊓ m ≠ C_a := fun h => hCa_not_m (h ▸ inf_le_right)
        have he_atom : IsAtom ((b ⊔ Γ.C) ⊓ m) := line_meets_m_at_atom hb Γ.hC hb_ne_C
          (sup_le (hb_on.trans le_sup_left) Γ.hC_plane) hm_le_π hm_cov hb_not_m
        -- G' < G'⊔e (e ≠ G' + both atoms)
        have hG'_lt : G' < G' ⊔ (b ⊔ Γ.C) ⊓ m := lt_of_le_of_ne le_sup_left
          (fun h => he_ne_G' ((hG'_atom.le_iff.mp
            (le_sup_right.trans h.symm.le)).resolve_left he_atom.1))
        -- C_a < C_a⊔e
        have hCa_lt : C_a < C_a ⊔ (b ⊔ Γ.C) ⊓ m := lt_of_le_of_ne le_sup_left
          (fun h => he_ne_Ca ((hCa_atom.le_iff.mp
            (le_sup_right.trans h.symm.le)).resolve_left he_atom.1))
        -- G'⊔e ≤ G'⊔C_a, CovBy forces G'⊔e = G'⊔C_a
        have hG'e_eq : G' ⊔ (b ⊔ Γ.C) ⊓ m = G' ⊔ C_a :=
          ((atom_covBy_join hG'_atom hCa_atom hG'_ne_Ca).eq_or_eq hG'_lt.le
            (sup_le le_sup_left he_le)).resolve_left hG'_lt.ne'
        -- C_a⊔e ≤ C_a⊔G', CovBy forces C_a⊔e = C_a⊔G'
        have hCae_le : C_a ⊔ (b ⊔ Γ.C) ⊓ m ≤ C_a ⊔ G' :=
          sup_le le_sup_left (he_le.trans (sup_comm G' C_a).le)
        have hCae_eq : C_a ⊔ (b ⊔ Γ.C) ⊓ m = C_a ⊔ G' :=
          ((atom_covBy_join hCa_atom hG'_atom hG'_ne_Ca.symm).eq_or_eq
            hCa_lt.le hCae_le).resolve_left hCa_lt.ne'
        -- Chain: G'⊔e = G'⊔C_a = C_a⊔G' = C_a⊔e
        exact hG'e_eq.trans ((sup_comm G' C_a).trans hCae_eq.symm)
      rw [hsuff]
    -- Well-definedness 2: pc(G, G', C_b, m) = pc(O, a, C_b, m) = τ_a_C_b
    -- By cases on whether O, G, C_b are collinear.
    -- Collinear case: shared direction f makes G'⊔f = a⊔f, collapsing both pc's.
    -- Non-collinear case: apply parallelogram_completion_well_defined directly.
    have hwd2 : parallelogram_completion G G' C_b m = τ_a_C_b := by
      -- Both pc's unfold to (C_b ⊔ dir) ⊓ (image ⊔ side_dir)
      -- Show both "direction" factors and "line" factors are equal
      change (C_b ⊔ (G ⊔ G') ⊓ m) ⊓ (G' ⊔ (G ⊔ C_b) ⊓ m) =
             (C_b ⊔ (Γ.O ⊔ a) ⊓ m) ⊓ (a ⊔ (Γ.O ⊔ C_b) ⊓ m)
      have hO_ne_G : Γ.O ≠ G := fun h => hG_not_l (h ▸ le_sup_left)
      have hO_ne_Cb : Γ.O ≠ C_b := by
        intro h
        have hO_le_q : Γ.O ≤ q := h ▸ hCb_le_q
        exact Γ.hOU ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf le_sup_left hO_le_q)).resolve_left Γ.hO.1)
      -- (G⊔G')⊓m = U: G⊔G' = G⊔U (CovBy), then modular law
      have hG_ne_U : G ≠ Γ.U := fun h => hG_not_m (h ▸ le_sup_left)
      have hGG'_eq_GU : G ⊔ G' = G ⊔ Γ.U := by
        have hcov1 : G ⋖ G ⊔ G' := atom_covBy_join hG_atom hG'_atom hGG'
        have hcov2 : G ⋖ G ⊔ Γ.U := atom_covBy_join hG_atom Γ.hU hG_ne_U
        exact (hcov2.eq_or_eq hcov1.lt.le hGG'_le_GU).resolve_left
          (ne_of_gt hcov1.lt)
      have hGG'_inf_m : (G ⊔ G') ⊓ m = Γ.U := by
        rw [hGG'_eq_GU, sup_comm]
        rw [sup_inf_assoc_of_le G (le_sup_left : Γ.U ≤ m)]
        have : G ⊓ m = ⊥ :=
          (hG_atom.le_iff.mp inf_le_left).resolve_right (fun h => hG_not_m (h ▸ inf_le_right))
        rw [this, sup_bot_eq]
      have hOa_inf_m : (Γ.O ⊔ a) ⊓ m = Γ.U := by
        rw [hOa_eq_l]; exact Γ.l_inf_m_eq_U
      have h_dir : (G ⊔ G') ⊓ m = (Γ.O ⊔ a) ⊓ m := by
        rw [hGG'_inf_m, hOa_inf_m]
      by_cases hCb_OG : C_b ≤ Γ.O ⊔ G
      · -- Collinear case: O, G, C_b on same line
        -- O⊔C_b = O⊔G and G⊔C_b = O⊔G (CovBy, all ≤ O⊔G)
        have hOCb_eq : Γ.O ⊔ C_b = Γ.O ⊔ G := by
          have hle : Γ.O ⊔ C_b ≤ Γ.O ⊔ G := sup_le le_sup_left hCb_OG
          have hcov1 : Γ.O ⋖ Γ.O ⊔ C_b := atom_covBy_join Γ.hO hCb_atom hO_ne_Cb
          have hcov2 : Γ.O ⋖ Γ.O ⊔ G := atom_covBy_join Γ.hO hG_atom hO_ne_G
          exact (hcov2.eq_or_eq hcov1.lt.le hle).resolve_left (ne_of_gt hcov1.lt)
        have hGCb_eq : G ⊔ C_b = Γ.O ⊔ G := by
          have hle : G ⊔ C_b ≤ Γ.O ⊔ G := sup_le le_sup_right hCb_OG
          have hcov1 : G ⋖ G ⊔ C_b := atom_covBy_join hG_atom hCb_atom hG_ne_Cb
          have hcov2 : G ⋖ Γ.O ⊔ G := by
            rw [sup_comm]; exact atom_covBy_join hG_atom Γ.hO hO_ne_G.symm
          exact (hcov2.eq_or_eq hcov1.lt.le hle).resolve_left (ne_of_gt hcov1.lt)
        -- G' ≤ a ⊔ f where f = (O⊔G)⊓m
        set f := (Γ.O ⊔ G) ⊓ m
        have hG'_le_af : G' ≤ a ⊔ f := by
          show parallelogram_completion Γ.O a G m ≤ a ⊔ f
          unfold parallelogram_completion
          rw [hOa_inf_m]
          exact inf_le_right
        -- f is an atom
        have hf_atom : IsAtom f := line_meets_m_at_atom Γ.hO hG_atom hO_ne_G
          (sup_le (le_sup_left.trans le_sup_left) hG_le_π)
          (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
          hm_cov Γ.hO_not_m
        -- G' ⊔ f = a ⊔ f (CovBy: both cover f, G'⊔f ≤ a⊔f)
        have hG'_ne_f : G' ≠ f := fun h => hG'_not_m (h ▸ inf_le_right)
        have ha_ne_f : a ≠ f := fun h => ha_not_m (h ▸ inf_le_right)
        have hG'f_eq_af : G' ⊔ f = a ⊔ f := by
          have hle : G' ⊔ f ≤ a ⊔ f := sup_le hG'_le_af le_sup_right
          have hcov1 : f ⋖ G' ⊔ f := by
            have := atom_covBy_join hf_atom hG'_atom hG'_ne_f.symm; rwa [sup_comm] at this
          have hcov2 : f ⋖ a ⊔ f := by
            have := atom_covBy_join hf_atom ha ha_ne_f.symm; rwa [sup_comm] at this
          exact (hcov2.eq_or_eq hcov1.lt.le hle).resolve_left hcov1.lt.ne'
        -- Second factors equal
        have h_line : G' ⊔ (G ⊔ C_b) ⊓ m = a ⊔ (Γ.O ⊔ C_b) ⊓ m := by
          rw [hGCb_eq, hOCb_eq]; exact hG'f_eq_af
        rw [h_dir, h_line]
      · -- Non-collinear case: apply well-definedness theorem directly
        -- Preconditions
        have ha_ne_G : a ≠ G := fun h => hG_not_l (h ▸ ha_on)
        have hCb_not_l' : ¬ C_b ≤ l := by
          intro h
          have : C_b ≤ l ⊓ q := le_inf h hCb_le_q
          rw [hlq_eq_U] at this
          exact hCb_not_m ((Γ.hU.le_iff.mp this).resolve_left hCb_atom.1 ▸ le_sup_left)
        have ha_ne_Cb : a ≠ C_b := fun h => hCb_not_l' (h ▸ ha_on)
        have hG_not_OCb : ¬ G ≤ Γ.O ⊔ C_b := by
          intro hG_le
          exact hCb_OG (le_sup_right.trans
            (((atom_covBy_join Γ.hO hCb_atom hO_ne_Cb).eq_or_eq
              (atom_covBy_join Γ.hO hG_atom hO_ne_G).lt.le
              (sup_le le_sup_left hG_le)).resolve_left
              (ne_of_gt (atom_covBy_join Γ.hO hG_atom hO_ne_G).lt)).symm.le)
        -- Span: O ⊔ G ⊔ C_b = π
        have hOG_Cb_span : Γ.O ⊔ G ⊔ C_b = π := by
          have hCb_inf_OG : C_b ⊓ (Γ.O ⊔ G) = ⊥ :=
            (hCb_atom.le_iff.mp inf_le_left).resolve_right
              (fun h => hCb_OG (h ▸ inf_le_right))
          have hd_atom : IsAtom ((Γ.O ⊔ G) ⊓ m) :=
            line_meets_m_at_atom Γ.hO hG_atom hO_ne_G
              (sup_le (le_sup_left.trans le_sup_left) hG_le_π)
              hm_le_π hm_cov Γ.hO_not_m
          have hπ_eq_Om : π = Γ.O ⊔ m := sup_assoc Γ.O Γ.U Γ.V
          have hm_OG_eq_π : m ⊔ (Γ.O ⊔ G) = π := by
            apply le_antisymm
            · exact sup_le hm_le_π (sup_le (le_sup_left.trans le_sup_left) hG_le_π)
            · rw [hπ_eq_Om]
              exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
          -- O⊔G ⋖ π
          have hOG_cov_π : Γ.O ⊔ G ⋖ π := by
            have hd_cov_m := hm_line _ hd_atom inf_le_right
            have h := covBy_sup_of_inf_covBy_left
              (show m ⊓ (Γ.O ⊔ G) ⋖ m from inf_comm m _ ▸ hd_cov_m)
            rwa [hm_OG_eq_π] at h
          -- O⊔G < O⊔G⊔C_b ≤ π, CovBy forces =
          have hOG_lt : Γ.O ⊔ G < Γ.O ⊔ G ⊔ C_b :=
            lt_of_le_of_ne le_sup_left
              (fun h => hCb_OG (le_sup_right.trans h.symm.le))
          exact (hOG_cov_π.eq_or_eq hOG_lt.le
            (sup_le (sup_le (le_sup_left.trans le_sup_left) hG_le_π) hCb_le_π)).resolve_left
            hOG_lt.ne'
        -- Apply well-definedness: pc(O,a,C_b,m) = pc(G,G',C_b,m)
        show parallelogram_completion G G' C_b m = τ_a_C_b
        exact (parallelogram_completion_well_defined Γ.hO ha hG_atom hCb_atom
          (fun h => ha_ne_O h.symm) hO_ne_G hO_ne_Cb ha_ne_G ha_ne_Cb hG_ne_Cb
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hG_le_π hCb_le_π
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m hG_not_m hCb_not_m
          (fun h => hG_not_l (hOa_eq_l ▸ h))
          (fun h => hCb_not_l' (hOa_eq_l ▸ h))
          hCb_OG hG_not_OCb hCb_not_GG'
          hOG_Cb_span
          R hR hR_not h_irred).symm
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
  ## Proof strategy (session 56)

  Key insight: C_p = pc(O, p, C, m) = (C⊔U)⊓(p⊔E) = q⊓(p⊔E) = β(p),
  where β is the E-perspectivity from l to q. So key_identity says:
  pc(O, a, β(b), m) = β(a+b), i.e., τ_a preserves the E-perspectivity.

  Both sides unfold to l ⊓ (line from q to m):
    LHS = l ⊓ (β(s) ⊔ e_c)  where s = a+b, e_c = (C⊔c)⊓m
    RHS = l ⊓ (β(a) ⊔ e_t)  where t = b+c, e_t = (C⊔t)⊓m

  By key_identity:
    β((a+b)+c) = pc(O, s, β(c), m)
    β(a+(b+c)) = pc(O, a, pc(O, b, β(c), m), m)

  So it suffices to show: pc(O, s, β(c), m) = pc(O, a, pc(O, b, β(c), m), m),
  i.e., τ_s = τ_a ∘ τ_b on β(c). Both agree at C (by key_identity), so by
  well_defined (changing base from C to an intermediate off q), they agree
  on β(c).
  -/
  sorry

end Foam.FTPGExplore
