/-
# Associativity capstone (Part V-B)

coord_add_assoc: PROVEN (session 66).

## Proof architecture (session 57)

The proof routes through q via β-injectivity:

1. key_identity reduces to O-based composition at C_c (off l).
2. Two cross-parallelism chains (at P,C and at P,C_c) + two two_lines
   arguments establish τ_s(C_c) = τ_a(τ_b(C_c)).
3. E-perspectivity recovery: β(LHS) = β(RHS) → LHS = RHS.

## Status

0 sorry. All steps proven.
-/

import Foam.FTPGAssoc

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-- **A C-based translation is determined by its parameter.**

    If pc(C, C₁, P, m) = pc(C, C₂, P, m) for some P off q and m
    in the plane π, then C₁ = C₂.

    Proof: since C_i ≤ q and C_i ≠ C, we have C⊔C_i = q, so the
    "direction" (C⊔C_i)⊓m = q⊓m = U. Thus pc(C, C_i, P, m) =
    (C_i⊔e_P) ⊓ (P⊔U), which is exactly the perspectivity from q
    to P⊔U through center e_P. Perspectivity is injective. -/
theorem translation_determined_by_param (Γ : CoordSystem L)
    {C₁ C₂ P : L} (hC₁ : IsAtom C₁) (hC₂ : IsAtom C₂) (hP : IsAtom P)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hC₁_on_q : C₁ ≤ Γ.U ⊔ Γ.C) (hC₂_on_q : C₂ ≤ Γ.U ⊔ Γ.C)
    (hC₁_ne_C : C₁ ≠ Γ.C) (hC₂_ne_C : C₂ ≠ Γ.C)
    (hP_not_q : ¬ P ≤ Γ.U ⊔ Γ.C) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (h_agree : parallelogram_completion Γ.C C₁ P (Γ.U ⊔ Γ.V) =
               parallelogram_completion Γ.C C₂ P (Γ.U ⊔ Γ.V)) :
    C₁ = C₂ := by
  -- The proof: pc(C, C_i, P, m) IS a perspectivity from q to P⊔U through e_P.
  -- Perspectivity is injective, so h_agree forces C₁ = C₂.
  set q := Γ.U ⊔ Γ.C
  set m := Γ.U ⊔ Γ.V
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set e_P := (Γ.C ⊔ P) ⊓ m
  -- ═══ Basic setup ═══
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hCP : Γ.C ≠ P := fun h => hP_not_q (h ▸ le_sup_right)
  have hPU : P ≠ Γ.U := fun h => hP_not_m (h ▸ le_sup_left)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  -- ═══ C⊔C_i = q, hence (C⊔C_i)⊓m = q⊓m = U ═══
  have hC_covBy_q : Γ.C ⋖ q := by
    show Γ.C ⋖ Γ.U ⊔ Γ.C; rw [sup_comm]; exact atom_covBy_join Γ.hC Γ.hU hUC.symm
  have hCC₁_eq_q : Γ.C ⊔ C₁ = q := by
    have hC_lt : Γ.C < Γ.C ⊔ C₁ := lt_of_le_of_ne le_sup_left
      (fun h => hC₁_ne_C ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hC₁.1))
    exact (hC_covBy_q.eq_or_eq hC_lt.le
      (sup_le le_sup_right hC₁_on_q)).resolve_left (ne_of_gt hC_lt)
  have hCC₂_eq_q : Γ.C ⊔ C₂ = q := by
    have hC_lt : Γ.C < Γ.C ⊔ C₂ := lt_of_le_of_ne le_sup_left
      (fun h => hC₂_ne_C ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hC₂.1))
    exact (hC_covBy_q.eq_or_eq hC_lt.le
      (sup_le le_sup_right hC₂_on_q)).resolve_left (ne_of_gt hC_lt)
  have hq_inf_m : q ⊓ m = Γ.U := by
    show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [this, sup_bot_eq]
  have hd₁ : (Γ.C ⊔ C₁) ⊓ m = Γ.U := by rw [hCC₁_eq_q]; exact hq_inf_m
  have hd₂ : (Γ.C ⊔ C₂) ⊓ m = Γ.U := by rw [hCC₂_eq_q]; exact hq_inf_m
  -- ═══ pc = perspectivity from q to P⊔U through e_P ═══
  -- pc(C, C_i, P, m) = (P⊔d_i) ⊓ (C_i⊔e_P) = (P⊔U) ⊓ (C_i⊔e_P) = (C_i⊔e_P) ⊓ (P⊔U)
  have h_persp_eq : (C₁ ⊔ e_P) ⊓ (P ⊔ Γ.U) = (C₂ ⊔ e_P) ⊓ (P ⊔ Γ.U) := by
    have h1 : parallelogram_completion Γ.C C₁ P m = (C₁ ⊔ e_P) ⊓ (P ⊔ Γ.U) := by
      unfold parallelogram_completion; rw [hd₁, inf_comm]
    have h2 : parallelogram_completion Γ.C C₂ P m = (C₂ ⊔ e_P) ⊓ (P ⊔ Γ.U) := by
      unfold parallelogram_completion; rw [hd₂, inf_comm]
    rw [← h1, ← h2]; exact h_agree
  -- ═══ e_P is an atom, not on q, not on P⊔U ═══
  have he_P : IsAtom e_P :=
    line_meets_m_at_atom Γ.hC hP hCP (sup_le Γ.hC_plane hP_plane) hm_le_π
      Γ.m_covBy_π Γ.hC_not_m
  -- e_P = U → U ≤ C⊔P → q ≤ C⊔P → q = C⊔P → P ∈ q, contradiction
  have he_P_ne_U : e_P ≠ Γ.U := by
    intro heq
    have hU_le : Γ.U ≤ Γ.C ⊔ P := by
      calc Γ.U = e_P := heq.symm
        _ ≤ Γ.C ⊔ P := inf_le_left
    exact hP_not_q (le_sup_right.trans (le_of_eq
      ((atom_covBy_join Γ.hC hP hCP).eq_or_eq (le_sup_right : Γ.C ≤ q)
        (sup_le hU_le le_sup_left)
      |>.resolve_left (ne_of_gt hC_covBy_q.lt)).symm))
  have he_P_not_q : ¬ e_P ≤ q := by
    intro h; apply he_P_ne_U
    have : e_P ≤ q ⊓ m := le_inf h inf_le_right; rw [hq_inf_m] at this
    exact (Γ.hU.le_iff.mp this).resolve_left he_P.1
  have he_P_not_PU : ¬ e_P ≤ P ⊔ Γ.U := by
    intro h; apply he_P_ne_U
    have h1 : e_P ≤ (Γ.U ⊔ P) ⊓ m :=
      le_inf (le_of_le_of_eq h (sup_comm P Γ.U)) inf_le_right
    rw [sup_inf_assoc_of_le P (le_sup_left : Γ.U ≤ m)] at h1
    have : P ⊓ m = ⊥ :=
      (hP.le_iff.mp inf_le_left).resolve_right (fun h => hP_not_m (h ▸ inf_le_right))
    rw [this, sup_bot_eq] at h1
    exact (Γ.hU.le_iff.mp h1).resolve_left he_P.1
  -- ═══ Coplanarity: q ⊔ e_P = (P⊔U) ⊔ e_P (both = π) ═══
  have h_coplanar : q ⊔ e_P = (P ⊔ Γ.U) ⊔ e_P := by
    -- q ⋖ π
    have hq_covBy_π : q ⋖ π := by
      have h_inf : m ⊓ q ⋖ m := by rw [inf_comm, hq_inf_m]; exact atom_covBy_join Γ.hU Γ.hV hUV
      have h1 := covBy_sup_of_inf_covBy_left h_inf  -- q ⋖ m ⊔ q
      have hmq : m ⊔ q = m ⊔ Γ.C := by
        show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
        rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
      have hmC : m ⊔ Γ.C = π :=
        (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
          (sup_le hm_le_π Γ.hC_plane)).resolve_left
          (ne_of_gt (lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
      rwa [hmq, hmC] at h1
    -- (P⊔U) ⋖ π
    have hPU_covBy_π : (P ⊔ Γ.U) ⋖ π := by
      have hV_not_PU : ¬ Γ.V ≤ P ⊔ Γ.U := by
        intro hle
        have hm_le_PU : m ≤ P ⊔ Γ.U := sup_le le_sup_right hle
        have : m = P ⊔ Γ.U := by
          have h1 := atom_covBy_join Γ.hU Γ.hV hUV  -- U ⋖ m
          have h2 : Γ.U ⋖ P ⊔ Γ.U := by
            rw [sup_comm]; exact atom_covBy_join Γ.hU hP hPU.symm
          exact (h2.eq_or_eq h1.lt.le hm_le_PU).resolve_left (ne_of_gt h1.lt)
        exact hP_not_m (le_of_le_of_eq le_sup_left this.symm)
      have hV_disj : Γ.V ⊓ (P ⊔ Γ.U) = ⊥ :=
        (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => hV_not_PU (h ▸ inf_le_right))
      have h1 := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)  -- P⊔U ⋖ V⊔(P⊔U)
      suffices Γ.V ⊔ (P ⊔ Γ.U) = π by rwa [this] at h1
      have hm_le : m ≤ Γ.V ⊔ (P ⊔ Γ.U) :=
        sup_le ((le_sup_right : Γ.U ≤ P ⊔ Γ.U).trans le_sup_right) le_sup_left
      exact (Γ.m_covBy_π.eq_or_eq hm_le
        (sup_le le_sup_right (sup_le hP_plane (le_sup_right.trans le_sup_left)))).resolve_left
        (ne_of_gt (lt_of_le_of_ne hm_le
          (fun h => hP_not_m (le_sup_left.trans (le_of_le_of_eq le_sup_right h.symm)))))
    -- Both q⊔e_P and (P⊔U)⊔e_P equal π
    have hq_e : q ⊔ e_P = π := by
      have hq_lt : q < q ⊔ e_P := lt_of_le_of_ne le_sup_left
        (fun h => he_P_not_q (le_sup_right.trans h.symm.le))
      exact (hq_covBy_π.eq_or_eq hq_lt.le (sup_le
        (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
        (inf_le_right.trans hm_le_π))).resolve_left (ne_of_gt hq_lt)
    have hPU_e : (P ⊔ Γ.U) ⊔ e_P = π := by
      have hPU_lt : P ⊔ Γ.U < (P ⊔ Γ.U) ⊔ e_P := lt_of_le_of_ne le_sup_left
        (fun h => he_P_not_PU (le_sup_right.trans h.symm.le))
      exact (hPU_covBy_π.eq_or_eq hPU_lt.le (sup_le
        (sup_le hP_plane (le_sup_right.trans le_sup_left))
        (inf_le_right.trans hm_le_π))).resolve_left (ne_of_gt hPU_lt)
    rw [hq_e, hPU_e]
  -- ═══ Conclusion: perspectivity_injective ═══
  by_contra h_ne
  have hpq : (⟨C₁, hC₁, hC₁_on_q⟩ : AtomsOn q) ≠ ⟨C₂, hC₂, hC₂_on_q⟩ :=
    fun h => h_ne (congrArg Subtype.val h)
  exact perspectivity_injective he_P Γ.hU Γ.hC hP Γ.hU hUC hPU
    he_P_not_q he_P_not_PU h_coplanar hpq (Subtype.ext h_persp_eq)

/-- **Associativity of coordinate addition.**

    (a + b) + c = a + (b + c)

    Proof strategy (session 57): route through q via β-injectivity.

    1. key_identity reduces goal to O-based composition at C_c (off l):
       pc(O, s, C_c, m) = pc(O, a, pc(O, b, C_c, m), m)

    2. Cross-parallelism chain at (P, Γ.C) gives X = τ_a(τ_b(P)) = τ_s(P).
       Cross-parallelism chain at (P, C_c) gives β(LHS) = β(RHS)
       via the two-lines argument.

    3. perspectivity_injective finishes. -/
theorem coord_add_assoc (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hab : a ≠ b) (hbc : b ≠ c) (_hac : a ≠ c)
    -- Non-degeneracy of sums (excluded: a+b=0, a+b=∞, etc.)
    (hs_ne_O : coord_add Γ a b ≠ Γ.O) (hs_ne_U : coord_add Γ a b ≠ Γ.U)
    (ht_ne_O : coord_add Γ b c ≠ Γ.O) (ht_ne_U : coord_add Γ b c ≠ Γ.U)
    (hsc : coord_add Γ a b ≠ c) (hat : a ≠ coord_add Γ b c)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ (coord_add Γ a b) c = coord_add Γ a (coord_add Γ b c) := by
  set l := Γ.O ⊔ Γ.U
  set m := Γ.U ⊔ Γ.V
  set q := Γ.U ⊔ Γ.C
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set s := coord_add Γ a b
  set t := coord_add Γ b c
  -- ═══ Step 0: Setup ═══
  have hs_atom : IsAtom s := coord_add_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
  have ht_atom : IsAtom t := coord_add_atom Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U
  have hs_on : s ≤ l := by show coord_add Γ a b ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have ht_on : t ≤ l := by show coord_add Γ b c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  -- ═══ Step 1: Key identity applications ═══
  -- C_x = pc(O, x, C, m) = E-perspectivity image of x = β(x)
  set C_c := parallelogram_completion Γ.O c Γ.C m
  set C_b := parallelogram_completion Γ.O b Γ.C m
  set C_s := parallelogram_completion Γ.O s Γ.C m
  set C_t := parallelogram_completion Γ.O t Γ.C m
  set C_LHS := parallelogram_completion Γ.O (coord_add Γ s c) Γ.C m
  set C_RHS := parallelogram_completion Γ.O (coord_add Γ a t) Γ.C m
  -- key_identity(a, b): τ_a(C_b) = C_s
  have h_ki_ab : parallelogram_completion Γ.O a C_b m = C_s :=
    key_identity Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U hab R hR hR_not h_irred
  -- key_identity(b, c): τ_b(C_c) = C_t
  have h_ki_bc : parallelogram_completion Γ.O b C_c m = C_t :=
    key_identity Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U hbc R hR hR_not h_irred
  -- key_identity(s, c): τ_s(C_c) = C_{s+c} = C_LHS
  have h_ki_sc : parallelogram_completion Γ.O s C_c m = C_LHS :=
    key_identity Γ s c hs_atom hc hs_on hc_on hs_ne_O hc_ne_O hs_ne_U hc_ne_U hsc R hR hR_not h_irred
  -- key_identity(a, t): τ_a(C_t) = C_{a+t} = C_RHS
  have h_ki_at : parallelogram_completion Γ.O a C_t m = C_RHS :=
    key_identity Γ a t ha ht_atom ha_on ht_on ha_ne_O ht_ne_O ha_ne_U ht_ne_U hat R hR hR_not h_irred
  -- ═══ Step 2: Composition law → C_LHS = C_RHS ═══
  -- Chain: C_LHS = τ_s(C_c) [h_ki_sc]
  --             = τ_a(τ_b(C_c)) [composition law, to prove]
  --             = τ_a(C_t) [h_ki_bc]
  --             = C_RHS [h_ki_at]
  -- So it suffices to prove: τ_s(C_c) = τ_a(τ_b(C_c))
  -- i.e., pc(O, s, C_c, m) = pc(O, a, pc(O, b, C_c, m), m)
  have h_beta_eq : C_LHS = C_RHS := by
    rw [← h_ki_sc, ← h_ki_at, ← h_ki_bc]
    -- Goal: τ_s(C_c) = τ_a(τ_b(C_c))
    -- Architecture: two cross-parallelism chains + two two_lines applications.
    -- Chain 1 at (P, C): establishes τ_s(P) = τ_a(τ_b(P)).
    -- Chain 2 at (P, C_c): establishes τ_s(C_c) = τ_a(τ_b(C_c)).
    -- ── Pick auxiliary P off l, m, q, in π ──
    -- P = (b ⊔ E) ⊓ (a ⊔ C): perspectivity image of b onto line a⊔C through center E.
    -- E ∉ a⊔C (distinct lines through C meet m at different atoms).
    -- P ∉ l (would force a ≤ b⊔E, then l ≤ b⊔E, then E ∈ l).
    -- P ∉ m (would force P = E ∈ a⊔C, contradicting E ∉ a⊔C).
    -- P ∉ q (would force C ∈ b⊔E, then O⊔C ≤ b⊔E, then E ∈ l).
    obtain ⟨P, hP_atom, hP_π, hP_not_l, hP_not_m, hP_not_q, hP_le_aC⟩ :
        ∃ P : L, IsAtom P ∧ P ≤ π ∧ ¬ P ≤ l ∧ ¬ P ≤ m ∧ ¬ P ≤ q ∧ P ≤ a ⊔ Γ.C := by
      have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
      have hb_ne_E : b ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hb_on)
      have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
      have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
      -- E ∉ a⊔C: if E ≤ a⊔C, then C⊔E = O⊔C ≤ a⊔C, so O ≤ (a⊔C)⊓l = a
      have hE_not_aC : ¬ Γ.E ≤ a ⊔ Γ.C := by
        intro hle
        -- E, C both ≤ a⊔C, so C⊔E ≤ a⊔C. And C⊔E = O⊔C (CovBy), so O ≤ a⊔C.
        -- Then O ≤ (a⊔C)⊓l = a, giving O = a.
        have hCE_le : Γ.C ⊔ Γ.E ≤ a ⊔ Γ.C := sup_le le_sup_right hle
        -- C⊔E = O⊔C by CovBy
        have hE_le_CO : Γ.E ≤ Γ.C ⊔ Γ.O :=
          sup_comm Γ.O Γ.C ▸ CoordSystem.hE_le_OC
        have h_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
          (fun h => hCE ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            Γ.hE_atom.1).symm)
        have h_CE : Γ.C ⊔ Γ.E = Γ.C ⊔ Γ.O :=
          ((atom_covBy_join Γ.hC Γ.hO hOC.symm).eq_or_eq h_lt.le
            (sup_le le_sup_left hE_le_CO)).resolve_left (ne_of_gt h_lt)
        -- O ≤ C⊔E ≤ a⊔C
        have hO_le_aC : Γ.O ≤ a ⊔ Γ.C :=
          calc Γ.O ≤ Γ.C ⊔ Γ.O := le_sup_right
            _ = Γ.C ⊔ Γ.E := h_CE.symm
            _ ≤ a ⊔ Γ.C := hCE_le
        -- O ≤ (a⊔C)⊓l = a
        have hO_le : Γ.O ≤ a := by
          have h := le_inf hO_le_aC (show Γ.O ≤ l from le_sup_left)
          rwa [inf_comm, sup_comm, inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h
        exact ha_ne_O ((ha.le_iff.mp hO_le).resolve_left Γ.hO.1).symm
      -- b⊔E coplanar with a⊔C: (a⊔C)⊔E = π
      -- Strategy: Da = (a⊔C)⊓m is an atom ≠ E (by hE_not_aC).
      -- Da, E on m → m ≤ Da⊔E ≤ (a⊔C)⊔E. m ⋖ π. a ∈ (a⊔C)⊔E, a ∉ m → (a⊔C)⊔E = π.
      have haCE_eq_π : (a ⊔ Γ.C) ⊔ Γ.E = π := by
        -- (a⊔C) and m are distinct lines in π, so they meet at an atom
        have haC_le_π : a ⊔ Γ.C ≤ π := sup_le (ha_on.trans le_sup_left) Γ.hC_plane
        have haC_ne_m : ¬ a ⊔ Γ.C ≤ m := fun h =>
          ha_ne_U (Γ.hU.le_iff.mp (Γ.l_inf_m_eq_U ▸ le_inf ha_on (le_sup_left.trans h))
            |>.resolve_left ha.1)
        have hD_ne_bot : (a ⊔ Γ.C) ⊓ m ≠ ⊥ := by
          rw [inf_comm]
          exact lines_meet_if_coplanar Γ.m_covBy_π haC_le_π haC_ne_m ha
            (lt_of_le_of_ne (le_sup_left : a ≤ a ⊔ Γ.C) (fun h => ha_ne_C
              ((ha.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm))
        have hD_ne_E : (a ⊔ Γ.C) ⊓ m ≠ Γ.E :=
          fun h => hE_not_aC (h ▸ inf_le_left)
        -- Da is an atom on m, distinct from E
        have hD_atom : IsAtom ((a ⊔ Γ.C) ⊓ m) :=
          line_height_two ha Γ.hC ha_ne_C (bot_lt_iff_ne_bot.mpr hD_ne_bot)
            (lt_of_le_of_ne inf_le_left (fun h => haC_ne_m (h ▸ inf_le_right)))
        -- Da ⊔ E = m (two distinct atoms on a line)
        have hDaE_eq_m : (a ⊔ Γ.C) ⊓ m ⊔ Γ.E = m := by
          have hE_cov : Γ.E ⋖ m := by
            show Γ.E ⋖ Γ.U ⊔ Γ.V
            have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
            rw [← Γ.EU_eq_m]; exact atom_covBy_join Γ.hE_atom Γ.hU CoordSystem.hEU
          have h_lt : Γ.E < (a ⊔ Γ.C) ⊓ m ⊔ Γ.E := lt_of_le_of_ne le_sup_right
            (fun h => hD_ne_E ((Γ.hE_atom.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left
              hD_atom.1))
          exact (hE_cov.eq_or_eq h_lt.le
            (sup_le (inf_le_right) CoordSystem.hE_on_m)).resolve_left (ne_of_gt h_lt)
        -- m ≤ (a⊔C)⊔E
        have hm_le : m ≤ (a ⊔ Γ.C) ⊔ Γ.E :=
          hDaE_eq_m ▸ sup_le (inf_le_left.trans le_sup_left) le_sup_right
        -- a ∉ m → (a⊔C)⊔E > m → m ⋖ π → (a⊔C)⊔E = π
        have ha_not_m : ¬ a ≤ m := fun h =>
          ha_ne_U (Γ.hU.le_iff.mp (Γ.l_inf_m_eq_U ▸ le_inf ha_on h) |>.resolve_left ha.1)
        have h_lt : m < (a ⊔ Γ.C) ⊔ Γ.E := lt_of_le_of_ne hm_le
          (fun h => ha_not_m ((le_sup_left : a ≤ a ⊔ Γ.C).trans le_sup_left |>.trans h.symm.le))
        exact (Γ.m_covBy_π.eq_or_eq h_lt.le
          (sup_le haC_le_π (CoordSystem.hE_on_m.trans hm_le_π))).resolve_left (ne_of_gt h_lt)
      have hbE_plane : b ⊔ Γ.E ≤ (a ⊔ Γ.C) ⊔ Γ.E :=
        sup_le (haCE_eq_π ▸ hb_on.trans le_sup_left) le_sup_right
      have hP_atom := perspect_atom Γ.hE_atom hb hb_ne_E ha Γ.hC ha_ne_C hE_not_aC hbE_plane
      refine ⟨_, hP_atom,
        inf_le_right.trans (sup_le (ha_on.trans le_sup_left) Γ.hC_plane), ?_, ?_, ?_, inf_le_right⟩
      · -- ¬P ≤ l: P ≤ (a⊔C)⊓l = a → P = a → a ≤ b⊔E → a ≤ l⊓(E⊔b) = b → a = b
        intro hle
        -- P ≤ (a⊔C) ⊓ l
        have hPa : (b ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ a := by
          have h : (b ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ (a ⊔ Γ.C) ⊓ l := le_inf inf_le_right hle
          have h2 : (a ⊔ Γ.C) ⊓ l = a := by
            show (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = a
            rw [inf_comm]; exact (sup_comm Γ.C a ▸
              inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on : (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) = a)
          exact h.trans (le_of_eq h2)
        -- P = a, so a ≤ b⊔E
        have ha_bE : a ≤ b ⊔ Γ.E :=
          (ha.le_iff.mp hPa).resolve_left hP_atom.1 ▸ inf_le_left
        -- a ≤ l ⊓ (E⊔b) = b
        have h_lb : (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ b) = b :=
          inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l hb_on
        have ha_b : a ≤ b := by
          have h : a ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ b) :=
            le_inf ha_on (show a ≤ Γ.E ⊔ b from (sup_comm Γ.E b).symm ▸ ha_bE)
          exact h_lb ▸ h
        exact hab (hb.le_iff.mp ha_b |>.resolve_left ha.1)
      · -- ¬P ≤ m: P ≤ (b⊔E)⊓m = E → E ≤ a⊔C, contradiction
        intro hle
        have hb_not_m : ¬ b ≤ m := fun hbm => hb_ne_U
          (Γ.hU.le_iff.mp (show b ≤ Γ.U from Γ.l_inf_m_eq_U ▸ le_inf hb_on hbm)
            |>.resolve_left hb.1)
        have hPE : (b ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ Γ.E := by
          have h : (b ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ (b ⊔ Γ.E) ⊓ m := le_inf inf_le_left hle
          have h2 : (b ⊔ Γ.E) ⊓ m = Γ.E := by
            show (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.V) = Γ.E
            rw [inf_comm]; exact (sup_comm Γ.E b ▸
              inf_sup_of_atom_not_le hb hb_not_m CoordSystem.hE_on_m :
              (Γ.U ⊔ Γ.V) ⊓ (b ⊔ Γ.E) = Γ.E)
          exact h.trans (le_of_eq h2)
        exact hE_not_aC ((Γ.hE_atom.le_iff.mp hPE).resolve_left hP_atom.1 ▸ inf_le_right)
      · -- ¬P ≤ q: P ≤ (a⊔C)⊓q = C → C ≤ b⊔E → O⊔C ≤ b⊔E → O ≤ b
        intro hle
        have ha_not_q : ¬ a ≤ q := fun haq => ha_ne_U
          (Γ.hU.le_iff.mp (show a ≤ Γ.U from by
            have h := le_inf ha_on haq
            have h2 : l ⊓ q = Γ.U := by
              show (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U
              rw [sup_comm Γ.O]
              have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
              exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm hUC hOC
                (fun hle => Γ.hC_not_l (sup_comm Γ.U Γ.O ▸ hle))
            exact h2 ▸ h) |>.resolve_left ha.1)
        have hPC : (b ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ Γ.C := by
          have h : (b ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ (a ⊔ Γ.C) ⊓ q := le_inf inf_le_right hle
          have h2 : (a ⊔ Γ.C) ⊓ q = Γ.C := by
            show (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C) = Γ.C
            rw [inf_comm]; exact (sup_comm Γ.C a ▸
              inf_sup_of_atom_not_le ha ha_not_q (le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C) :
              (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.C) = Γ.C)
          exact h.trans (le_of_eq h2)
        have hC_bE : Γ.C ≤ b ⊔ Γ.E :=
          (Γ.hC.le_iff.mp hPC).resolve_left hP_atom.1 ▸ inf_le_left
        -- C⊔E = C⊔O (CovBy), so O⊔C ≤ b⊔E
        have hOC_bE : Γ.O ⊔ Γ.C ≤ b ⊔ Γ.E := by
          have h_CE : Γ.C ⊔ Γ.E = Γ.C ⊔ Γ.O := by
            have h_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
              (fun h => hCE ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
                Γ.hE_atom.1).symm)
            exact ((atom_covBy_join Γ.hC Γ.hO hOC.symm).eq_or_eq h_lt.le
              (sup_le le_sup_left (sup_comm Γ.O Γ.C ▸ CoordSystem.hE_le_OC))).resolve_left
              (ne_of_gt h_lt)
          calc Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O := sup_comm _ _
            _ = Γ.C ⊔ Γ.E := h_CE.symm
            _ ≤ b ⊔ Γ.E := sup_le hC_bE le_sup_right
        -- O ≤ l ⊓ (E⊔b) = b
        have h_lb : (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ b) = b :=
          inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l hb_on
        have hO_b : Γ.O ≤ b := by
          have h : Γ.O ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ b) :=
            le_inf le_sup_left (show Γ.O ≤ Γ.E ⊔ b from
              (sup_comm Γ.E b).symm ▸ le_sup_left.trans hOC_bE)
          exact h_lb ▸ h
        exact hb_ne_O (hb.le_iff.mp hO_b |>.resolve_left Γ.hO.1).symm
    -- ── Translation images ──
    set τ_s_P := parallelogram_completion Γ.O s P m
    set τ_b_P := parallelogram_completion Γ.O b P m
    set τ_a_τ_b_P := parallelogram_completion Γ.O a τ_b_P m
    set τ_s_C_c := parallelogram_completion Γ.O s C_c m
    set τ_b_C_c := parallelogram_completion Γ.O b C_c m
    set τ_a_τ_b_C_c := parallelogram_completion Γ.O a τ_b_C_c m
    -- ═══ Shared infrastructure for cross_parallelism calls ═══
    have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m := fun x hx hle =>
      line_covers_its_atoms Γ.hU Γ.hV hUV hx hle
    have hm_cov : m ⋖ π := Γ.m_covBy_π
    -- O⊔s = l, O⊔b = l, O⊔a = l
    have hOs_eq_l : Γ.O ⊔ s = l := by
      have h_lt : Γ.O < Γ.O ⊔ s := lt_of_le_of_ne le_sup_left
        (fun h => hs_ne_O (Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left
          hs_atom.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left hs_on)).resolve_left (ne_of_gt h_lt)
    have hOb_eq_l : Γ.O ⊔ b = l := by
      have h_lt : Γ.O < Γ.O ⊔ b := lt_of_le_of_ne le_sup_left
        (fun h => hb_ne_O (Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left hb.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left hb_on)).resolve_left (ne_of_gt h_lt)
    have hOa_eq_l : Γ.O ⊔ a = l := by
      have h_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
        (fun h => ha_ne_O (Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left ha.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt h_lt)
    -- Not-on-m facts
    have hs_not_m : ¬ s ≤ m := fun h => hs_ne_U (Γ.atom_on_both_eq_U hs_atom hs_on h)
    have hb_not_m : ¬ b ≤ m := fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on h)
    have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
    -- O ≠ P (P not on l, O on l)
    have hO_ne_P : Γ.O ≠ P := fun h => hP_not_l (h ▸ le_sup_left)
    -- P ≠ C (P not on q, C on q)
    have hP_ne_C : P ≠ Γ.C := fun h => hP_not_q (h ▸ le_sup_right)
    -- C not on O⊔P: if C ≤ O⊔P, then (a⊔C)⊓(O⊔C) = C, and P ≤ a⊔C, so
    -- P ≤ (a⊔C) ⊓ (O⊔P) → P ≤ (a⊔C) ⊓ (O⊔C) = C (modular law), P = C. Contradiction.
    have hC_not_OP : ¬ Γ.C ≤ Γ.O ⊔ P := by
      intro hle
      -- O⊔C ≤ O⊔P (from hle). Both are lines through O.
      -- By CovBy: O⊔C = O⊔P. Then P ≤ O⊔P = O⊔C.
      -- Also P ≤ a⊔C. So P ≤ (a⊔C) ⊓ (O⊔C) = C (modular law). P = C. Contradiction.
      have hOC_le_OP : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ P := sup_le le_sup_left hle
      have hO_lt_OC : Γ.O < Γ.O ⊔ Γ.C := lt_of_le_of_ne le_sup_left
        (fun h => hOC (Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left Γ.hC.1 |>.symm))
      have hOC_eq_OP : Γ.O ⊔ Γ.C = Γ.O ⊔ P :=
        ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt_OC.le hOC_le_OP).resolve_left
          hO_lt_OC.ne'
      have hP_le_OC : P ≤ Γ.O ⊔ Γ.C := hOC_eq_OP.symm ▸ (le_sup_right : P ≤ Γ.O ⊔ P)
      -- (a⊔C) ⊓ (O⊔C) = C: use inf_sup_of_atom_not_le (a not on O⊔C)
      have ha_not_OC : ¬ a ≤ Γ.O ⊔ Γ.C := by
        intro h
        have h1 : l ⊓ (Γ.C ⊔ Γ.O) = Γ.O :=
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ l)
        have h2 : a ≤ Γ.O := (le_inf ha_on (h.trans (sup_comm Γ.O Γ.C).le)).trans h1.le
        exact ha_ne_O (Γ.hO.le_iff.mp h2 |>.resolve_left ha.1)
      have h_int : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.C) = Γ.C := by
        have := inf_sup_of_atom_not_le ha ha_not_OC (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)
        -- this : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.C) = Γ.C
        exact this
      exact hP_ne_C (Γ.hC.le_iff.mp ((le_inf hP_le_OC hP_le_aC).trans h_int.le)
        |>.resolve_left hP_atom.1)
    -- O⊔P⊔C = π: P ≤ a⊔C (from construction), so P⊔C = a⊔C (CovBy), hence O⊔P⊔C = l⊔C = π.
    have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
    -- l ⋖ π
    have hl_cov_π : l ⋖ π := by
      have hV_inf_l : Γ.V ⊓ l = ⊥ :=
        (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
      show l ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
      rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = l ⊔ Γ.V from rfl, sup_comm l Γ.V]
      exact covBy_sup_of_inf_covBy_left (hV_inf_l ▸ Γ.hV.bot_covBy)
    have hOPC_span : Γ.O ⊔ P ⊔ Γ.C = π := by
      -- P⊔C = a⊔C: both P, C ≤ a⊔C, P ≠ C, and C ⋖ a⊔C
      have hPC_eq_aC : P ⊔ Γ.C = a ⊔ Γ.C := by
        -- C ⋖ C⊔a (atom_covBy_join). C < C⊔P ≤ C⊔a. By CovBy: C⊔P = C⊔a.
        have hC_ne_a : Γ.C ≠ a := ha_ne_C.symm
        have hC_lt : Γ.C < Γ.C ⊔ P := lt_of_le_of_ne le_sup_left
          (fun h => hP_ne_C (Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left
            hP_atom.1))
        have hCP_le : Γ.C ⊔ P ≤ Γ.C ⊔ a := sup_le le_sup_left
          (hP_le_aC.trans (sup_comm a Γ.C).le)
        have hCP_eq_Ca : Γ.C ⊔ P = Γ.C ⊔ a :=
          ((atom_covBy_join Γ.hC ha hC_ne_a).eq_or_eq hC_lt.le hCP_le).resolve_left hC_lt.ne'
        calc P ⊔ Γ.C = Γ.C ⊔ P := sup_comm P Γ.C
          _ = Γ.C ⊔ a := hCP_eq_Ca
          _ = a ⊔ Γ.C := sup_comm Γ.C a
      rw [sup_assoc, hPC_eq_aC, ← sup_assoc, hOa_eq_l]
      -- l ⊔ C = π
      have hlC_gt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
        (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
      exact (hl_cov_π.eq_or_eq hlC_gt.le
        (sup_le le_sup_left Γ.hC_plane)).resolve_left hlC_gt.ne'
    -- l ⊓ q = U
    have hlq_eq_U : l ⊓ q = Γ.U := by
      show (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U
      rw [sup_comm Γ.O Γ.U]
      have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
      exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm hUC hOC
        (fun h => Γ.hC_not_l (le_trans h (by rw [sup_comm])))
    -- C_s is an atom on q
    have hCs_atom : IsAtom C_s :=
      parallelogram_completion_atom Γ.hO hs_atom Γ.hC hs_ne_O.symm hOC
        (fun h => Γ.hC_not_l (h ▸ hs_on)) (le_sup_left.trans le_sup_left)
        (hs_on.trans le_sup_left) Γ.hC_plane hm_le_π hm_cov hm_line
        Γ.hO_not_m hs_not_m Γ.hC_not_m
        (fun h => Γ.hC_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
    have hCs_le_q : C_s ≤ q := by
      have : C_s ≤ Γ.C ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
      rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this
      exact this.trans (sup_comm Γ.C Γ.U ▸ le_refl q)
    -- C_b is an atom on q
    have hCb_atom : IsAtom C_b :=
      parallelogram_completion_atom Γ.hO hb Γ.hC (fun h => hb_ne_O h.symm) hOC
        (fun h => Γ.hC_not_l (h ▸ hb_on)) (le_sup_left.trans le_sup_left)
        (hb_on.trans le_sup_left) Γ.hC_plane hm_le_π hm_cov hm_line
        Γ.hO_not_m hb_not_m Γ.hC_not_m
        (fun h => Γ.hC_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
    have hCb_le_q : C_b ≤ q := by
      have : C_b ≤ Γ.C ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
      rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this
      exact this.trans (sup_comm Γ.C Γ.U ▸ le_refl q)
    -- Shared helpers for cross_parallelism preconditions
    have hl_inf_PU : l ⊓ (P ⊔ Γ.U) = Γ.U :=
      inf_sup_of_atom_not_le hP_atom hP_not_l (le_sup_right : Γ.U ≤ l)
    have hPU_inf_q : (P ⊔ Γ.U) ⊓ q = Γ.U := by
      rw [inf_comm]; exact inf_sup_of_atom_not_le hP_atom hP_not_q (le_sup_left : Γ.U ≤ q)
    -- q ⊓ m = U (shared computation)
    have hqm_eq_U : q ⊓ m = Γ.U := by
      show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
      rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
      rw [(Γ.hC.le_iff.mp inf_le_left).resolve_right
        (fun h => Γ.hC_not_m (h ▸ inf_le_right)), sup_bot_eq]
    have hCs_not_m : ¬ C_s ≤ m := by
      intro hCs_m
      have hCs_le_E : C_s ≤ Γ.E :=
        (le_inf (show C_s ≤ s ⊔ Γ.E from inf_le_right) hCs_m).trans
          (line_direction hs_atom hs_not_m CoordSystem.hE_on_m).le
      have hCsE : C_s = Γ.E := (Γ.hE_atom.le_iff.mp hCs_le_E).resolve_left hCs_atom.1
      exact CoordSystem.hEU (Γ.hU.le_iff.mp
        ((le_inf (hCsE ▸ hCs_le_q) (hCsE ▸ hCs_le_E |>.trans CoordSystem.hE_on_m)).trans
          hqm_eq_U.le) |>.resolve_left Γ.hE_atom.1)
    have hCb_not_m : ¬ C_b ≤ m := by
      intro hCb_m
      have hCb_le_E : C_b ≤ Γ.E :=
        (le_inf (show C_b ≤ b ⊔ Γ.E from inf_le_right) hCb_m).trans
          (line_direction hb hb_not_m CoordSystem.hE_on_m).le
      have hCbE : C_b = Γ.E := (Γ.hE_atom.le_iff.mp hCb_le_E).resolve_left hCb_atom.1
      exact CoordSystem.hEU (Γ.hU.le_iff.mp
        ((le_inf (hCbE ▸ hCb_le_q) (hCbE ▸ hCb_le_E |>.trans CoordSystem.hE_on_m)).trans
          hqm_eq_U.le) |>.resolve_left Γ.hE_atom.1)
    -- ═══ Chain 1: at (P, Γ.C) → τ_s(P) = τ_a(τ_b(P)) ═══
    -- cp(τ_s, P, C): (P⊔C)⊓m = (τ_s_P ⊔ C_s)⊓m
    have hcp1 : (P ⊔ Γ.C) ⊓ m = (τ_s_P ⊔ C_s) ⊓ m := by
      -- Preconditions for cross_parallelism with P₀=O, P₀'=s, P=P, Q=C
      have hs_ne_P : s ≠ P := fun h => hP_not_l (h ▸ hs_on)
      have hs_ne_C : s ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hs_on)
      -- s ≠ τ_s_P: if s = τ_s_P then s ≤ P⊔U (from pc def), so s ≤ l⊓(P⊔U) = U
      have hs_ne_τ : s ≠ τ_s_P := by
        intro h_eq
        have hs_le_PU : s ≤ P ⊔ Γ.U := by
          have : τ_s_P ≤ P ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
          rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this; exact h_eq ▸ this
        exact hs_ne_U ((Γ.hU.le_iff.mp
          ((le_inf hs_on hs_le_PU).trans hl_inf_PU.le)).resolve_left hs_atom.1)
      -- s ≠ C_s: if s = C_s then s ≤ q (C_s on q), so s ≤ l⊓q = U
      have hs_ne_Cs : s ≠ C_s := by
        intro h_eq
        have : s ≤ l ⊓ q := le_inf hs_on (h_eq ▸ hCs_le_q)
        rw [hlq_eq_U] at this
        exact hs_ne_U ((Γ.hU.le_iff.mp this).resolve_left hs_atom.1)
      -- τ_s_P ≠ C_s: if equal, both ≤ (P⊔U)⊓q = U, so C_s ≤ m. Contradiction.
      have hτ_ne_Cs : τ_s_P ≠ C_s := by
        intro h_eq
        have hτ_le_PU : τ_s_P ≤ P ⊔ Γ.U := by
          have : τ_s_P ≤ P ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
          rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this; exact this
        exact hCs_not_m ((Γ.hU.le_iff.mp
          ((le_inf (h_eq ▸ hτ_le_PU) hCs_le_q).trans hPU_inf_q.le)).resolve_left hCs_atom.1 ▸
          (le_sup_left : Γ.U ≤ m))
      exact cross_parallelism Γ.hO hs_atom hP_atom Γ.hC
        hs_ne_O.symm hO_ne_P hOC hP_ne_C
        hs_ne_τ hs_ne_Cs hτ_ne_Cs
        (le_sup_left.trans le_sup_left) (hs_on.trans le_sup_left) hP_π Γ.hC_plane
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hs_not_m hP_not_m Γ.hC_not_m
        (fun h => hP_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
        (fun h => Γ.hC_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
        hC_not_OP hOPC_span
        R hR hR_not h_irred
    -- cp(τ_b, P, C): (P⊔C)⊓m = (τ_b_P ⊔ C_b)⊓m
    have hcp2 : (P ⊔ Γ.C) ⊓ m = (τ_b_P ⊔ C_b) ⊓ m := by
      have hb_ne_P : b ≠ P := fun h => hP_not_l (h ▸ hb_on)
      have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)
      -- b ≠ τ_b_P
      have hb_ne_τ : b ≠ τ_b_P := by
        intro h_eq
        have hb_le_PU : b ≤ P ⊔ Γ.U := by
          have : τ_b_P ≤ P ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
          rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this; exact h_eq ▸ this
        exact hb_ne_U ((Γ.hU.le_iff.mp
          ((le_inf hb_on hb_le_PU).trans hl_inf_PU.le)).resolve_left hb.1)
      -- b ≠ C_b
      have hb_ne_Cb : b ≠ C_b := by
        intro h_eq
        have : b ≤ l ⊓ q := le_inf hb_on (h_eq ▸ hCb_le_q)
        rw [hlq_eq_U] at this
        exact hb_ne_U ((Γ.hU.le_iff.mp this).resolve_left hb.1)
      -- τ_b_P ≠ C_b: same pattern as τ_s_P ≠ C_s
      have hτ_ne_Cb : τ_b_P ≠ C_b := by
        intro h_eq
        have hτ_le_PU : τ_b_P ≤ P ⊔ Γ.U := by
          have : τ_b_P ≤ P ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
          rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this; exact this
        exact hCb_not_m ((Γ.hU.le_iff.mp
          ((le_inf (h_eq ▸ hτ_le_PU) hCb_le_q).trans hPU_inf_q.le)).resolve_left hCb_atom.1 ▸
          (le_sup_left : Γ.U ≤ m))
      exact cross_parallelism Γ.hO hb hP_atom Γ.hC
        (fun h => hb_ne_O h.symm) hO_ne_P hOC hP_ne_C
        hb_ne_τ hb_ne_Cb hτ_ne_Cb
        (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) hP_π Γ.hC_plane
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hb_not_m hP_not_m Γ.hC_not_m
        (fun h => hP_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
        (fun h => Γ.hC_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
        hC_not_OP hOPC_span
        R hR hR_not h_irred
    -- ── τ_b_P facts ──
    have hτbP_atom : IsAtom τ_b_P :=
      parallelogram_completion_atom Γ.hO hb hP_atom
        (fun h => hb_ne_O h.symm) hO_ne_P (fun h => hP_not_l (h ▸ hb_on))
        (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) hP_π
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hb_not_m hP_not_m
        (fun h => hP_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
    have hτbP_le_PU : τ_b_P ≤ P ⊔ Γ.U := by
      have : τ_b_P ≤ P ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
      rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this; exact this
    have hτbP_le_bdOP : τ_b_P ≤ b ⊔ (Γ.O ⊔ P) ⊓ m :=
      inf_le_right
    -- C_b ≠ τ_b_P: C_b on q, τ_b_P not on q (since (P⊔U)⊓q = U and τ_b_P ≤ P⊔U)
    have hτbP_not_q : ¬ τ_b_P ≤ q := by
      intro h
      have hτ_le_U : τ_b_P ≤ Γ.U := (le_inf hτbP_le_PU h).trans hPU_inf_q.le
      -- τ_b_P is atom ≤ U (atom) → τ_b_P = U
      have hτbP_eq_U : τ_b_P = Γ.U :=
        (Γ.hU.le_iff.mp hτ_le_U).resolve_left hτbP_atom.1
      -- U ≤ b⊔d_OP, and (b⊔d_OP)⊓m = d_OP (line_direction), so U ≤ d_OP ≤ O⊔P
      have hU_le_OP : Γ.U ≤ Γ.O ⊔ P := by
        have h1 : Γ.U ≤ (b ⊔ (Γ.O ⊔ P) ⊓ m) ⊓ m :=
          le_inf (hτbP_eq_U ▸ hτbP_le_bdOP) (le_sup_left : Γ.U ≤ m)
        rw [line_direction hb hb_not_m inf_le_right] at h1
        exact h1.trans inf_le_left
      -- l = O⊔U ≤ O⊔P. CovBy → l = O⊔P → P ≤ l. Contradiction.
      have hl_le_OP : l ≤ Γ.O ⊔ P := sup_le le_sup_left hU_le_OP
      have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
        (fun h => Γ.hOU ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          Γ.hU.1 |>.symm))
      have hl_eq_OP : l = Γ.O ⊔ P :=
        ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt_l.le
          hl_le_OP).resolve_left (ne_of_gt hO_lt_l)
      exact hP_not_l (le_sup_right.trans (le_of_eq hl_eq_OP.symm))
    have hCb_ne_τbP : C_b ≠ τ_b_P := fun h => hτbP_not_q (h ▸ hCb_le_q)
    -- O ≠ τ_b_P: if equal, O ≤ P⊔U, O ≤ l⊓(P⊔U) = U, O = U. Contradiction.
    have hO_ne_τbP : Γ.O ≠ τ_b_P := by
      intro h
      exact Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
        (h ▸ hτbP_le_PU)).trans hl_inf_PU.le)).resolve_left Γ.hO.1)
    -- τ_b_P ∉ m: τ_b_P ≤ (P⊔U)⊓m = U → τ_b_P ∈ q. Contradiction.
    have hτbP_not_m : ¬ τ_b_P ≤ m := by
      intro h
      exact hτbP_not_q (((Γ.hU.le_iff.mp (by
        have h1 : τ_b_P ≤ (P ⊔ Γ.U) ⊓ m := le_inf hτbP_le_PU h
        rwa [sup_comm, sup_inf_assoc_of_le P (le_sup_left : Γ.U ≤ m),
          (hP_atom.le_iff.mp inf_le_left).resolve_right (fun h => hP_not_m (h ▸ inf_le_right)),
          sup_bot_eq] at h1)).resolve_left hτbP_atom.1).symm ▸ (le_sup_left : Γ.U ≤ q))
    -- τ_b_P ≤ π
    have hτbP_π : τ_b_P ≤ π := hτbP_le_PU.trans
      (sup_le hP_π (le_sup_right.trans le_sup_left))
    -- a ≠ τ_b_P: a ∈ l, τ_b_P ∉ l
    have ha_ne_τbP : a ≠ τ_b_P := fun h => hτbP_not_q
      ((le_inf (h ▸ ha_on) hτbP_le_PU).trans hl_inf_PU.le |>.trans
        (le_sup_left : Γ.U ≤ q))
    -- τ_a_τ_b_P is an atom
    have hτa_atom : IsAtom τ_a_τ_b_P :=
      parallelogram_completion_atom Γ.hO ha hτbP_atom
        (fun h => ha_ne_O h.symm) hO_ne_τbP ha_ne_τbP
        (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hτbP_π
        hm_le_π hm_cov hm_line
        Γ.hO_not_m ha_not_m hτbP_not_m
        (fun h => hτbP_not_q ((le_inf (h.trans (hOa_eq_l ▸ le_refl l))
          hτbP_le_PU).trans hl_inf_PU.le |>.trans (le_sup_left : Γ.U ≤ q)))
    -- cp(τ_a, τ_b(P), C_b): (τ_b_P⊔C_b)⊓m = (τ_a_τ_b_P ⊔ C_s)⊓m
    have hcp3 : (τ_b_P ⊔ C_b) ⊓ m = (τ_a_τ_b_P ⊔ C_s) ⊓ m := by
      -- Case split: C_b collinear with O and τ_b_P, or not.
      by_cases hCb_collinear : C_b ≤ Γ.O ⊔ τ_b_P
      · -- ═══ Collinear case: both sides = d' = (O⊔τ_b_P)⊓m ═══
        set d' := (Γ.O ⊔ τ_b_P) ⊓ m
        -- d' is an atom
        have hd'_atom : IsAtom d' :=
          line_meets_m_at_atom Γ.hO hτbP_atom hO_ne_τbP
            (sup_le (le_sup_left.trans le_sup_left) hτbP_π)
            hm_le_π hm_cov Γ.hO_not_m
        -- LHS = d': τ_b_P⊔C_b = O⊔τ_b_P by CovBy
        have hτbP_lt : τ_b_P < τ_b_P ⊔ C_b := lt_of_le_of_ne le_sup_left
          (fun h => hCb_ne_τbP ((hτbP_atom.le_iff.mp (le_sup_right.trans
            (le_of_eq h.symm))).resolve_left hCb_atom.1))
        have hLHS_line : τ_b_P ⊔ C_b = Γ.O ⊔ τ_b_P :=
          ((sup_comm τ_b_P Γ.O ▸ atom_covBy_join hτbP_atom Γ.hO
            (fun h => hO_ne_τbP h.symm)).eq_or_eq hτbP_lt.le
            (sup_le le_sup_right hCb_collinear)).resolve_left (ne_of_gt hτbP_lt)
        -- O⊔C_b = O⊔τ_b_P by CovBy
        have hO_ne_Cb : Γ.O ≠ C_b := by
          intro h; exact Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
            (h ▸ hCb_le_q)).trans hlq_eq_U.le)).resolve_left Γ.hO.1)
        have hOCb_eq : Γ.O ⊔ C_b = Γ.O ⊔ τ_b_P := by
          have hO_lt : Γ.O < Γ.O ⊔ C_b := lt_of_le_of_ne le_sup_left
            (fun h => hO_ne_Cb ((Γ.hO.le_iff.mp (le_sup_right.trans
              (le_of_eq h.symm))).resolve_left hCb_atom.1).symm)
          exact ((atom_covBy_join Γ.hO hτbP_atom hO_ne_τbP).eq_or_eq hO_lt.le
            (sup_le le_sup_left hCb_collinear)).resolve_left (ne_of_gt hO_lt)
        -- τ_a_τ_b_P ≤ a⊔d' (from pc second factor)
        have hτa_le_ad' : τ_a_τ_b_P ≤ a ⊔ d' := by
          show τ_a_τ_b_P ≤ a ⊔ (Γ.O ⊔ τ_b_P) ⊓ m; exact inf_le_right
        -- C_s ≤ a⊔d' (h_ki_ab + direction via hOCb_eq)
        have hCs_le_ad' : C_s ≤ a ⊔ d' := by
          rw [← h_ki_ab]; show parallelogram_completion Γ.O a C_b m ≤ a ⊔ d'
          show parallelogram_completion Γ.O a C_b m ≤ a ⊔ (Γ.O ⊔ τ_b_P) ⊓ m
          rw [← hOCb_eq]; exact inf_le_right
        -- (a⊔d')⊓m = d'
        have had'_dir : (a ⊔ d') ⊓ m = d' := line_direction ha ha_not_m inf_le_right
        -- RHS ≤ d'
        have hRHS_le : (τ_a_τ_b_P ⊔ C_s) ⊓ m ≤ d' :=
          (inf_le_inf_right m (sup_le hτa_le_ad' hCs_le_ad')).trans (le_of_eq had'_dir)
        -- τ_a_τ_b_P ≠ C_s
        have hτa_ne_Cs : τ_a_τ_b_P ≠ C_s := by
          intro h_eq
          have hτa_le_τU : τ_a_τ_b_P ≤ τ_b_P ⊔ Γ.U := by
            have : τ_a_τ_b_P ≤ τ_b_P ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
            rwa [hOa_eq_l, Γ.l_inf_m_eq_U] at this
          have hτU_ne : τ_b_P ≠ Γ.U := fun h => hτbP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
          have hPU_ne : P ≠ Γ.U := fun h => hP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
          have hU_lt : Γ.U < τ_b_P ⊔ Γ.U := lt_of_le_of_ne le_sup_right
            (fun h => hτU_ne ((Γ.hU.le_iff.mp (le_sup_left.trans
              (le_of_eq h.symm))).resolve_left hτbP_atom.1))
          have hτU_eq_PU : τ_b_P ⊔ Γ.U = P ⊔ Γ.U :=
            ((sup_comm Γ.U P ▸ atom_covBy_join Γ.hU hP_atom hPU_ne.symm).eq_or_eq
              hU_lt.le (sup_le hτbP_le_PU le_sup_right)).resolve_left (ne_of_gt hU_lt)
          have hCs_le_U : C_s ≤ Γ.U := (le_inf (hτU_eq_PU ▸ h_eq ▸ hτa_le_τU)
            hCs_le_q).trans hPU_inf_q.le
          exact hCs_not_m (((Γ.hU.le_iff.mp hCs_le_U).resolve_left hCs_atom.1).symm ▸
            (le_sup_left : Γ.U ≤ m))
        -- RHS meets m (coplanarity: two lines in π meet)
        have hCs_lt : C_s < τ_a_τ_b_P ⊔ C_s := lt_of_le_of_ne le_sup_right
          (fun h => hτa_ne_Cs ((hCs_atom.le_iff.mp (le_sup_left.trans
            (le_of_eq h.symm))).resolve_left hτa_atom.1))
        have hRHS_ne : m ⊓ (τ_a_τ_b_P ⊔ C_s) ≠ ⊥ :=
          lines_meet_if_coplanar hm_cov
            (sup_le (hτa_le_ad'.trans (sup_le (ha_on.trans le_sup_left)
              (inf_le_right.trans hm_le_π))) (hCs_le_ad'.trans (sup_le
              (ha_on.trans le_sup_left) (inf_le_right.trans hm_le_π))))
            (fun h => hCs_not_m (le_sup_right.trans h)) hCs_atom hCs_lt
        -- RHS ≤ d' (atom) and RHS ≠ ⊥ → RHS = d'
        have hRHS_eq : (τ_a_τ_b_P ⊔ C_s) ⊓ m = d' :=
          (hd'_atom.le_iff.mp hRHS_le).resolve_left (inf_comm m _ ▸ hRHS_ne)
        rw [hLHS_line]; exact hRHS_eq.symm
      · -- ═══ Non-collinear case: cross_parallelism ═══
        -- O ≠ C_b
        have hO_ne_Cb : Γ.O ≠ C_b := by
          intro h; exact Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
            (h ▸ hCb_le_q)).trans hlq_eq_U.le)).resolve_left Γ.hO.1)
        -- a ≠ C_b: a ∈ l, C_b ∈ q, l⊓q = U, a ≠ U
        have ha_ne_Cb : a ≠ C_b := fun h => ha_ne_U ((Γ.hU.le_iff.mp
          ((le_inf ha_on (h ▸ hCb_le_q)).trans hlq_eq_U.le)).resolve_left ha.1)
        -- q ⋖ π (from m⊓q ⋖ m → q ⋖ m⊔q = m⊔C = π)
        have hq_covBy_π : q ⋖ π := by
          have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
          have h_inf : m ⊓ q ⋖ m := by
            rw [inf_comm, hqm_eq_U]; exact atom_covBy_join Γ.hU Γ.hV hUV
          have h1 := covBy_sup_of_inf_covBy_left h_inf
          have hmq : m ⊔ q = m ⊔ Γ.C := by
            show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
            rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
          have hmC : m ⊔ Γ.C = π :=
            (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
              (sup_le hm_le_π Γ.hC_plane)).resolve_left
              (ne_of_gt (lt_of_le_of_ne le_sup_left
                (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
          rwa [hmq, hmC] at h1
        -- (O⊔τ_b_P) ⊓ q is an atom ≠ C_b (non-collinearity)
        have hO_not_q : ¬ Γ.O ≤ q := fun h =>
          Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
            h).trans hlq_eq_U.le)).resolve_left Γ.hO.1)
        have hW_atom : IsAtom ((Γ.O ⊔ τ_b_P) ⊓ q) :=
          line_meets_m_at_atom Γ.hO hτbP_atom hO_ne_τbP
            (sup_le (le_sup_left.trans le_sup_left) hτbP_π)
            (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane) hq_covBy_π
            hO_not_q
        have hW_ne_Cb : (Γ.O ⊔ τ_b_P) ⊓ q ≠ C_b := fun h =>
          hCb_collinear (h ▸ inf_le_left)
        -- Span: (O⊔τ_b_P⊔C_b) ⊓ q = C_b ⊔ ((O⊔τ_b_P) ⊓ q) = q (modular law)
        have hspan : Γ.O ⊔ τ_b_P ⊔ C_b = π := by
          -- By modular law (C_b ≤ q): (C_b ⊔ (O⊔τ_b_P)) ⊓ q = C_b ⊔ ((O⊔τ_b_P) ⊓ q)
          have h_mod : (C_b ⊔ (Γ.O ⊔ τ_b_P)) ⊓ q = C_b ⊔ ((Γ.O ⊔ τ_b_P) ⊓ q) :=
            sup_inf_assoc_of_le (Γ.O ⊔ τ_b_P) hCb_le_q
          -- C_b ⊔ W = q (CovBy: two distinct atoms on q)
          have hCb_lt : C_b < C_b ⊔ (Γ.O ⊔ τ_b_P) ⊓ q := by
            apply lt_of_le_of_ne le_sup_left; intro h
            have hW_le : (Γ.O ⊔ τ_b_P) ⊓ q ≤ C_b := le_sup_right.trans (le_of_eq h.symm)
            exact hW_ne_Cb ((hCb_atom.le_iff.mp hW_le).resolve_left hW_atom.1)
          have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
          have hCb_covBy : C_b ⋖ q := line_covers_its_atoms Γ.hU Γ.hC hUC hCb_atom hCb_le_q
          have hCbW_eq_q : C_b ⊔ (Γ.O ⊔ τ_b_P) ⊓ q = q :=
            (hCb_covBy.eq_or_eq hCb_lt.le (sup_le hCb_le_q inf_le_right)).resolve_left
              (ne_of_gt hCb_lt)
          have hq_le : q ≤ Γ.O ⊔ τ_b_P ⊔ C_b := by
            have := inf_eq_right.mp (h_mod.trans hCbW_eq_q); rwa [sup_comm] at this
          have hlC_le : l ⊔ Γ.C ≤ Γ.O ⊔ τ_b_P ⊔ C_b :=
            sup_le (sup_le (le_sup_left.trans le_sup_left)
              ((le_sup_left : Γ.U ≤ q).trans hq_le))
              ((le_sup_right : Γ.C ≤ q).trans hq_le)
          have hl_lt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
          have hlC_eq : l ⊔ Γ.C = π :=
            (hl_cov_π.eq_or_eq hl_lt.le (sup_le le_sup_left
              Γ.hC_plane)).resolve_left (ne_of_gt hl_lt)
          exact le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left) hτbP_π)
            (hCb_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)))
            (le_of_eq hlC_eq.symm |>.trans hlC_le)
        -- ── cross_parallelism preconditions ──
        have hCb_not_Oa : ¬ C_b ≤ Γ.O ⊔ a := by
          intro h; exact hCb_not_m ((Γ.hU.le_iff.mp ((le_inf (h.trans (hOa_eq_l ▸ le_refl l))
            hCb_le_q).trans hlq_eq_U.le)).resolve_left hCb_atom.1 ▸ (le_sup_left : Γ.U ≤ m))
        have ha_ne_τa : a ≠ τ_a_τ_b_P := by
          intro h_eq
          have hτa_le_τU : τ_a_τ_b_P ≤ τ_b_P ⊔ Γ.U := by
            have : τ_a_τ_b_P ≤ τ_b_P ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
            rwa [hOa_eq_l, Γ.l_inf_m_eq_U] at this
          rw [← h_eq] at hτa_le_τU
          exact ha_ne_U ((Γ.hU.le_iff.mp ((le_inf ha_on
            (hτa_le_τU.trans (sup_le hτbP_le_PU le_sup_right))).trans
            hl_inf_PU.le)).resolve_left ha.1)
        have ha_ne_Cs_cp : a ≠ parallelogram_completion Γ.O a C_b m := by
          rw [h_ki_ab]; exact fun h => ha_ne_U ((Γ.hU.le_iff.mp
            ((le_inf ha_on (h ▸ hCs_le_q)).trans hlq_eq_U.le)).resolve_left ha.1)
        have hτa_ne_Cs_cp : τ_a_τ_b_P ≠ parallelogram_completion Γ.O a C_b m := by
          rw [h_ki_ab]
          intro h_eq
          have hτa_le_τU : τ_a_τ_b_P ≤ τ_b_P ⊔ Γ.U := by
            have : τ_a_τ_b_P ≤ τ_b_P ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
            rwa [hOa_eq_l, Γ.l_inf_m_eq_U] at this
          have hτU_ne : τ_b_P ≠ Γ.U := fun h => hτbP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
          have hPU_ne : P ≠ Γ.U := fun h => hP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
          have hU_lt : Γ.U < τ_b_P ⊔ Γ.U := lt_of_le_of_ne le_sup_right
            (fun h => hτU_ne ((Γ.hU.le_iff.mp (le_sup_left.trans
              (le_of_eq h.symm))).resolve_left hτbP_atom.1))
          have hτU_eq_PU : τ_b_P ⊔ Γ.U = P ⊔ Γ.U :=
            ((sup_comm Γ.U P ▸ atom_covBy_join Γ.hU hP_atom hPU_ne.symm).eq_or_eq
              hU_lt.le (sup_le hτbP_le_PU le_sup_right)).resolve_left (ne_of_gt hU_lt)
          have hCs_le_U : C_s ≤ Γ.U := (le_inf (hτU_eq_PU ▸ h_eq ▸ hτa_le_τU)
            hCs_le_q).trans hPU_inf_q.le
          exact hCs_not_m (((Γ.hU.le_iff.mp hCs_le_U).resolve_left hCs_atom.1).symm ▸
            (le_sup_left : Γ.U ≤ m))
        -- Apply cross_parallelism
        have hcp3_raw := cross_parallelism Γ.hO ha hτbP_atom hCb_atom
          (fun h => ha_ne_O h.symm) hO_ne_τbP hO_ne_Cb (fun h => hCb_ne_τbP h.symm)
          ha_ne_τa ha_ne_Cs_cp hτa_ne_Cs_cp
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hτbP_π
          (hCb_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m hτbP_not_m hCb_not_m
          (fun h => hτbP_not_q ((le_inf (h.trans (hOa_eq_l ▸ le_refl l))
            hτbP_le_PU).trans hl_inf_PU.le |>.trans (le_sup_left : Γ.U ≤ q)))
          hCb_not_Oa
          hCb_collinear
          hspan
          R hR hR_not h_irred
        rw [h_ki_ab] at hcp3_raw; exact hcp3_raw
    -- Direction chain: (τ_s_P ⊔ C_s)⊓m = (τ_a_τ_b_P ⊔ C_s)⊓m
    have h_dir1 : (τ_s_P ⊔ C_s) ⊓ m = (τ_a_τ_b_P ⊔ C_s) ⊓ m :=
      hcp1.symm.trans (hcp2.trans hcp3)
    -- two_lines on l: τ_s_P = τ_a_τ_b_P
    -- Both on l (translations preserve l). C_s ∉ l. Shared direction via h_dir1.
    -- ── Shared facts for two_lines arguments ──
    have hτsP_atom : IsAtom τ_s_P :=
      parallelogram_completion_atom Γ.hO hs_atom hP_atom
        (fun h => hs_ne_O h.symm) hO_ne_P (fun h => hP_not_l (h ▸ hs_on))
        (le_sup_left.trans le_sup_left) (hs_on.trans le_sup_left) hP_π
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hs_not_m hP_not_m
        (fun h => hP_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
    have hτsP_le_PU : τ_s_P ≤ P ⊔ Γ.U := by
      have : τ_s_P ≤ P ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
      rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this; exact this
    have hτa_le_PU : τ_a_τ_b_P ≤ P ⊔ Γ.U := by
      have h1 : τ_a_τ_b_P ≤ τ_b_P ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
      rw [hOa_eq_l, Γ.l_inf_m_eq_U] at h1
      exact h1.trans (sup_le hτbP_le_PU le_sup_right)
    have hτsP_ne_Cs : τ_s_P ≠ C_s := by
      intro h; exact hCs_not_m (((Γ.hU.le_iff.mp ((le_inf (h ▸ hτsP_le_PU) hCs_le_q).trans
        hPU_inf_q.le)).resolve_left hCs_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
    have hτa_ne_Cs : τ_a_τ_b_P ≠ C_s := by
      intro h; exact hCs_not_m (((Γ.hU.le_iff.mp ((le_inf (h ▸ hτa_le_PU) hCs_le_q).trans
        hPU_inf_q.le)).resolve_left hCs_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
    have hCs_not_PU : ¬ C_s ≤ P ⊔ Γ.U := by
      intro h; exact hCs_not_m (((Γ.hU.le_iff.mp ((le_inf h hCs_le_q).trans
        hPU_inf_q.le)).resolve_left hCs_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
    have hP_agree : τ_s_P = τ_a_τ_b_P := by
      -- d_dir = direction on m = (τ_s_P⊔C_s)⊓m is an atom ≠ C_s
      have hτsP_π : τ_s_P ≤ π := hτsP_le_PU.trans (sup_le hP_π (le_sup_right.trans le_sup_left))
      have hCs_π : C_s ≤ π := hCs_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
      have hd_atom : IsAtom ((τ_s_P ⊔ C_s) ⊓ m) := by
        rw [sup_comm]; exact line_meets_m_at_atom hCs_atom hτsP_atom
          (fun h => hτsP_ne_Cs h.symm) (sup_le hCs_π hτsP_π) hm_le_π hm_cov hCs_not_m
      have hd_ne_Cs : (τ_s_P ⊔ C_s) ⊓ m ≠ C_s := fun h =>
        hCs_not_m (h ▸ inf_le_right)
      -- Line equality: τ_s_P⊔C_s = τ_a_τ_b_P⊔C_s (both = C_s ⊔ d_dir, CovBy)
      have hCs_covBy_1 : C_s ⋖ τ_s_P ⊔ C_s :=
        sup_comm C_s τ_s_P ▸ atom_covBy_join hCs_atom hτsP_atom hτsP_ne_Cs.symm
      have hCs_lt_d : C_s < C_s ⊔ (τ_s_P ⊔ C_s) ⊓ m := lt_of_le_of_ne le_sup_left
        (fun h => hd_ne_Cs ((hCs_atom.le_iff.mp (le_sup_right.trans
          (le_of_eq h.symm))).resolve_left hd_atom.1))
      have hCsd_eq_1 : C_s ⊔ (τ_s_P ⊔ C_s) ⊓ m = τ_s_P ⊔ C_s :=
        (hCs_covBy_1.eq_or_eq hCs_lt_d.le (sup_le le_sup_right inf_le_left)).resolve_left
          (ne_of_gt hCs_lt_d)
      have hCs_covBy_2 : C_s ⋖ τ_a_τ_b_P ⊔ C_s :=
        sup_comm C_s τ_a_τ_b_P ▸ atom_covBy_join hCs_atom hτa_atom hτa_ne_Cs.symm
      have hd_le_2 : (τ_s_P ⊔ C_s) ⊓ m ≤ τ_a_τ_b_P ⊔ C_s := h_dir1 ▸ inf_le_left
      have hCs_lt_d2 : C_s < C_s ⊔ (τ_s_P ⊔ C_s) ⊓ m := hCs_lt_d
      have hCsd_eq_2 : C_s ⊔ (τ_s_P ⊔ C_s) ⊓ m = τ_a_τ_b_P ⊔ C_s :=
        (hCs_covBy_2.eq_or_eq hCs_lt_d2.le (sup_le le_sup_right hd_le_2)).resolve_left
          (ne_of_gt hCs_lt_d2)
      -- τ_s_P ⊔ C_s = τ_a_τ_b_P ⊔ C_s
      have hline_eq : τ_s_P ⊔ C_s = τ_a_τ_b_P ⊔ C_s := hCsd_eq_1.symm.trans hCsd_eq_2
      -- τ_a_τ_b_P ≤ τ_s_P ⊔ C_s
      have hτa_on_line : τ_a_τ_b_P ≤ τ_s_P ⊔ C_s := hline_eq ▸ le_sup_left
      -- Apply two_lines: X = τ_s_P, Y = τ_a_τ_b_P, Z = C_s, l₁ = P⊔U
      have hPU_ne : P ≠ Γ.U := fun h => hP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
      exact two_lines hτsP_atom hτa_atom hCs_atom hτsP_ne_Cs
        hτsP_le_PU hτa_le_PU hτa_on_line hCs_not_PU
        (line_covers_its_atoms hP_atom Γ.hU hPU_ne hτsP_atom hτsP_le_PU)
    -- ═══ C_c infrastructure ═══
    have hOc_eq_l : Γ.O ⊔ c = l := by
      have h_lt : Γ.O < Γ.O ⊔ c := lt_of_le_of_ne le_sup_left
        (fun h => hc_ne_O (Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left hc.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left hc_on)).resolve_left (ne_of_gt h_lt)
    have hc_not_m : ¬ c ≤ m := fun h => hc_ne_U (Γ.atom_on_both_eq_U hc hc_on h)
    have hCc_atom : IsAtom C_c :=
      parallelogram_completion_atom Γ.hO hc Γ.hC (fun h => hc_ne_O h.symm) hOC
        (fun h => Γ.hC_not_l (h ▸ hc_on)) (le_sup_left.trans le_sup_left)
        (hc_on.trans le_sup_left) Γ.hC_plane hm_le_π hm_cov hm_line
        Γ.hO_not_m hc_not_m Γ.hC_not_m
        (fun h => Γ.hC_not_l (h.trans (hOc_eq_l ▸ le_refl l)))
    have hCc_le_q : C_c ≤ q := by
      have : C_c ≤ Γ.C ⊔ (Γ.O ⊔ c) ⊓ m := inf_le_left
      rw [hOc_eq_l, Γ.l_inf_m_eq_U] at this
      exact this.trans (sup_comm Γ.C Γ.U ▸ le_refl q)
    have hCc_not_m : ¬ C_c ≤ m := by
      intro hCc_m
      have hCc_le_E : C_c ≤ Γ.E :=
        (le_inf (show C_c ≤ c ⊔ Γ.E from inf_le_right) hCc_m).trans
          (line_direction hc hc_not_m CoordSystem.hE_on_m).le
      have hCcE : C_c = Γ.E := (Γ.hE_atom.le_iff.mp hCc_le_E).resolve_left hCc_atom.1
      exact CoordSystem.hEU (Γ.hU.le_iff.mp
        ((le_inf (hCcE ▸ hCc_le_q) (hCcE ▸ hCc_le_E |>.trans CoordSystem.hE_on_m)).trans
          hqm_eq_U.le) |>.resolve_left Γ.hE_atom.1)
    have hCc_π : C_c ≤ π := hCc_le_q.trans
      (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
    have hO_ne_Cc : Γ.O ≠ C_c := by
      intro h; exact Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
        (h ▸ hCc_le_q)).trans hlq_eq_U.le)).resolve_left Γ.hO.1)
    have hP_ne_Cc : P ≠ C_c := fun h => hP_not_q (h ▸ hCc_le_q)
    have hCc_not_l : ¬ C_c ≤ l := by
      intro h; exact hCc_not_m (((Γ.hU.le_iff.mp ((le_inf h hCc_le_q).trans
        hlq_eq_U.le)).resolve_left hCc_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
    -- ═══ Shared infrastructure for Chain 2 ═══
    have hPU_ne : P ≠ Γ.U := fun h => hP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
    have hCc_not_PU : ¬ C_c ≤ P ⊔ Γ.U := by
      intro h; exact hCc_not_m (((Γ.hU.le_iff.mp ((le_inf h hCc_le_q).trans
        hPU_inf_q.le)).resolve_left hCc_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
    have hs_ne_Cc : s ≠ C_c := fun h => hs_ne_U ((Γ.hU.le_iff.mp ((le_inf hs_on
      (h ▸ hCc_le_q)).trans hlq_eq_U.le)).resolve_left hs_atom.1)
    have hb_ne_Cc : b ≠ C_c := fun h => hb_ne_U ((Γ.hU.le_iff.mp ((le_inf hb_on
      (h ▸ hCc_le_q)).trans hlq_eq_U.le)).resolve_left hb.1)
    -- τ_s_C_c facts
    have hτsCc_le_CcU : τ_s_C_c ≤ C_c ⊔ Γ.U := by
      have : τ_s_C_c ≤ C_c ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
      rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this; exact this
    have hτsCc_le_q : τ_s_C_c ≤ q :=
      hτsCc_le_CcU.trans (sup_le hCc_le_q (le_sup_left : Γ.U ≤ q))
    have hτsCc_atom : IsAtom τ_s_C_c :=
      parallelogram_completion_atom Γ.hO hs_atom hCc_atom hs_ne_O.symm hO_ne_Cc hs_ne_Cc
        (le_sup_left.trans le_sup_left) (hs_on.trans le_sup_left) hCc_π
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hs_not_m hCc_not_m
        (fun h => hCc_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
    -- τ_b_C_c facts
    have hτbCc_le_CcU : τ_b_C_c ≤ C_c ⊔ Γ.U := by
      have : τ_b_C_c ≤ C_c ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
      rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this; exact this
    have hτbCc_le_q : τ_b_C_c ≤ q :=
      hτbCc_le_CcU.trans (sup_le hCc_le_q (le_sup_left : Γ.U ≤ q))
    -- τ_s_C_c ∉ m (needed for hl₂_not arguments)
    have hτsCc_not_m : ¬ τ_s_C_c ≤ m := by
      intro h
      have hτsCc_eq_U : τ_s_C_c = Γ.U :=
        (Γ.hU.le_iff.mp ((le_inf hτsCc_le_q h).trans hqm_eq_U.le)).resolve_left hτsCc_atom.1
      have h1 : Γ.U ≤ s ⊔ (Γ.O ⊔ C_c) ⊓ m := by rw [← hτsCc_eq_U]; exact inf_le_right
      have hU_le_OCc : Γ.U ≤ Γ.O ⊔ C_c :=
        ((le_inf h1 (le_sup_left : Γ.U ≤ m)).trans
          (line_direction hs_atom hs_not_m inf_le_right).le).trans inf_le_left
      have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
        (fun h' => Γ.hOU ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1).symm)
      have hl_eq : l = Γ.O ⊔ C_c :=
        ((atom_covBy_join Γ.hO hCc_atom hO_ne_Cc).eq_or_eq hO_lt_l.le
          (sup_le le_sup_left hU_le_OCc)).resolve_left hO_lt_l.ne'
      exact hCc_not_l (hl_eq ▸ le_sup_right)
    -- q ⋖ π (needed for non-collinear span proofs)
    have hq_covBy_π : q ⋖ π := by
      have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
      have h_inf : m ⊓ q ⋖ m := by
        rw [inf_comm, hqm_eq_U]; exact atom_covBy_join Γ.hU Γ.hV hUV
      have h1 := covBy_sup_of_inf_covBy_left h_inf
      have hmq : m ⊔ q = m ⊔ Γ.C := by
        show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
        rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
      have hmC : m ⊔ Γ.C = π :=
        (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
          (sup_le hm_le_π Γ.hC_plane)).resolve_left
          (ne_of_gt (lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
      rwa [hmq, hmC] at h1
    -- τ_s_P ≠ τ_s_C_c: if equal, common value ≤ (P⊔U)⊓q = U, contradiction.
    have hτsP_ne_τsCc : τ_s_P ≠ τ_s_C_c := by
      intro h_eq
      have h_q : τ_s_P ≤ q := h_eq ▸ hτsCc_le_q
      have hτsP_eq_U : τ_s_P = Γ.U :=
        (Γ.hU.le_iff.mp ((le_inf hτsP_le_PU h_q).trans hPU_inf_q.le)).resolve_left hτsP_atom.1
      have h1 : Γ.U ≤ s ⊔ (Γ.O ⊔ P) ⊓ m := by rw [← hτsP_eq_U]; exact inf_le_right
      have hU_le_OP : Γ.U ≤ Γ.O ⊔ P :=
        ((le_inf h1 (le_sup_left : Γ.U ≤ m)).trans
          (line_direction hs_atom hs_not_m inf_le_right).le).trans inf_le_left
      have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
        (fun h => Γ.hOU ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hU.1).symm)
      have hl_eq : l = Γ.O ⊔ P :=
        ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt_l.le
          (sup_le le_sup_left hU_le_OP)).resolve_left hO_lt_l.ne'
      exact hP_not_l (hl_eq ▸ le_sup_right)
    -- τ_b_P ≠ τ_b_C_c: if equal, common value ≤ (P⊔U)⊓q = U, then U ≤ m. Contradiction.
    have hτbP_ne_τbCc : τ_b_P ≠ τ_b_C_c := by
      intro h_eq
      have h_q : τ_b_P ≤ q := h_eq ▸ hτbCc_le_q
      exact hτbP_not_m (((Γ.hU.le_iff.mp ((le_inf hτbP_le_PU h_q).trans
        hPU_inf_q.le)).resolve_left hτbP_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
    -- ═══ Chain 2: at (P, C_c) → τ_s(C_c) = τ_a(τ_b(C_c)) ═══
    -- cp(τ_s, P, C_c)
    have hcp4 : (P ⊔ C_c) ⊓ m = (τ_s_P ⊔ τ_s_C_c) ⊓ m := by
      by_cases hCc_collinear : C_c ≤ Γ.O ⊔ P
      · -- ═══ Collinear case: both sides = d' = (O⊔P)⊓m ═══
        set d' := (Γ.O ⊔ P) ⊓ m
        have hd'_atom : IsAtom d' :=
          line_meets_m_at_atom Γ.hO hP_atom hO_ne_P
            (sup_le (le_sup_left.trans le_sup_left) hP_π) hm_le_π hm_cov Γ.hO_not_m
        -- LHS: P⊔C_c = O⊔P by CovBy
        have hP_lt : P < P ⊔ C_c := lt_of_le_of_ne le_sup_left
          (fun h => hP_ne_Cc ((hP_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hCc_atom.1).symm)
        have hLHS_line : P ⊔ C_c = Γ.O ⊔ P :=
          ((sup_comm P Γ.O ▸ atom_covBy_join hP_atom Γ.hO
            (fun h => hO_ne_P h.symm)).eq_or_eq hP_lt.le
            (sup_le le_sup_right hCc_collinear)).resolve_left (ne_of_gt hP_lt)
        -- O⊔C_c = O⊔P (CovBy)
        have hOCc_eq : Γ.O ⊔ C_c = Γ.O ⊔ P := by
          have hO_lt : Γ.O < Γ.O ⊔ C_c := lt_of_le_of_ne le_sup_left
            (fun h => hO_ne_Cc ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
              hCc_atom.1).symm)
          exact ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt.le
            (sup_le le_sup_left hCc_collinear)).resolve_left (ne_of_gt hO_lt)
        -- Both images ≤ s⊔d'
        have hτsP_le : τ_s_P ≤ s ⊔ d' := inf_le_right
        have hτsCc_le : τ_s_C_c ≤ s ⊔ d' := by
          have h : τ_s_C_c ≤ s ⊔ (Γ.O ⊔ C_c) ⊓ m := inf_le_right
          rw [hOCc_eq] at h; exact h
        -- (s⊔d')⊓m = d'
        have hsd'_dir : (s ⊔ d') ⊓ m = d' := line_direction hs_atom hs_not_m inf_le_right
        -- RHS ≤ d'
        have hRHS_le : (τ_s_P ⊔ τ_s_C_c) ⊓ m ≤ d' :=
          (inf_le_inf_right m (sup_le hτsP_le hτsCc_le)).trans hsd'_dir.le
        -- RHS ≠ ⊥
        have hτsP_lt : τ_s_P < τ_s_P ⊔ τ_s_C_c := lt_of_le_of_ne le_sup_left
          (fun h => hτsP_ne_τsCc ((hτsP_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hτsCc_atom.1).symm)
        have hRHS_ne : m ⊓ (τ_s_P ⊔ τ_s_C_c) ≠ ⊥ :=
          lines_meet_if_coplanar hm_cov
            (sup_le hτsP_le hτsCc_le |>.trans (sup_le (hs_on.trans le_sup_left)
              (inf_le_right.trans hm_le_π)))
            (fun h => hτsCc_not_m (le_sup_right.trans h))
            hτsP_atom hτsP_lt
        rw [hLHS_line]
        exact ((hd'_atom.le_iff.mp hRHS_le).resolve_left (inf_comm m _ ▸ hRHS_ne)).symm
      · -- ═══ Non-collinear case: cross_parallelism ═══
        -- Span: O⊔P⊔C_c = π
        have hO_not_q : ¬ Γ.O ≤ q := fun h =>
          Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l) h).trans
            hlq_eq_U.le)).resolve_left Γ.hO.1)
        have hW_atom : IsAtom ((Γ.O ⊔ P) ⊓ q) :=
          line_meets_m_at_atom Γ.hO hP_atom hO_ne_P
            (sup_le (le_sup_left.trans le_sup_left) hP_π)
            (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane) hq_covBy_π
            hO_not_q
        have hW_ne_Cc : (Γ.O ⊔ P) ⊓ q ≠ C_c := fun h => hCc_collinear (h ▸ inf_le_left)
        have hOPCc_span : Γ.O ⊔ P ⊔ C_c = π := by
          have h_mod : (C_c ⊔ (Γ.O ⊔ P)) ⊓ q = C_c ⊔ ((Γ.O ⊔ P) ⊓ q) :=
            sup_inf_assoc_of_le (Γ.O ⊔ P) hCc_le_q
          have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
          have hCc_lt : C_c < C_c ⊔ (Γ.O ⊔ P) ⊓ q := by
            apply lt_of_le_of_ne le_sup_left; intro h
            exact hW_ne_Cc ((hCc_atom.le_iff.mp (le_sup_right.trans (le_of_eq h.symm))).resolve_left
              hW_atom.1)
          have hCc_covBy : C_c ⋖ q := line_covers_its_atoms Γ.hU Γ.hC hUC hCc_atom hCc_le_q
          have hCcW_eq_q : C_c ⊔ (Γ.O ⊔ P) ⊓ q = q :=
            (hCc_covBy.eq_or_eq hCc_lt.le (sup_le hCc_le_q inf_le_right)).resolve_left
              (ne_of_gt hCc_lt)
          have hq_le : q ≤ Γ.O ⊔ P ⊔ C_c := by
            have := inf_eq_right.mp (h_mod.trans hCcW_eq_q); rwa [sup_comm] at this
          have hlC_le : l ⊔ Γ.C ≤ Γ.O ⊔ P ⊔ C_c :=
            sup_le (sup_le (le_sup_left.trans le_sup_left)
              ((le_sup_left : Γ.U ≤ q).trans hq_le))
              ((le_sup_right : Γ.C ≤ q).trans hq_le)
          have hl_lt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
          have hlC_eq : l ⊔ Γ.C = π :=
            (hl_cov_π.eq_or_eq hl_lt.le (sup_le le_sup_left Γ.hC_plane)).resolve_left
              (ne_of_gt hl_lt)
          exact le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left) hP_π) hCc_π)
            (le_of_eq hlC_eq.symm |>.trans hlC_le)
        -- cross_parallelism preconditions
        have hs_ne_τsCc : s ≠ τ_s_C_c := by
          intro h_eq
          have : s ≤ C_c ⊔ Γ.U := by
            have h : τ_s_C_c ≤ C_c ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
            rw [hOs_eq_l, Γ.l_inf_m_eq_U] at h; rwa [← h_eq] at h
          exact hs_ne_U ((Γ.hU.le_iff.mp ((le_inf hs_on
            (this.trans (sup_le hCc_le_q (le_sup_left : Γ.U ≤ q)))).trans
            hlq_eq_U.le)).resolve_left hs_atom.1)
        exact cross_parallelism Γ.hO hs_atom hP_atom hCc_atom
          hs_ne_O.symm hO_ne_P hO_ne_Cc hP_ne_Cc
          (show s ≠ τ_s_P from by
            intro h_eq
            have hs_le_PU : s ≤ P ⊔ Γ.U := by
              have : τ_s_P ≤ P ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
              rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this; exact h_eq ▸ this
            exact hs_ne_U ((Γ.hU.le_iff.mp
              ((le_inf hs_on hs_le_PU).trans hl_inf_PU.le)).resolve_left hs_atom.1))
          hs_ne_τsCc hτsP_ne_τsCc
          (le_sup_left.trans le_sup_left) (hs_on.trans le_sup_left) hP_π hCc_π
          hm_le_π hm_cov hm_line
          Γ.hO_not_m hs_not_m hP_not_m hCc_not_m
          (fun h => hP_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
          (fun h => hCc_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
          hCc_collinear hOPCc_span
          R hR hR_not h_irred
    -- cp(τ_b, P, C_c)
    have hcp5 : (P ⊔ C_c) ⊓ m = (τ_b_P ⊔ τ_b_C_c) ⊓ m := by
      by_cases hCc_collinear : C_c ≤ Γ.O ⊔ P
      · -- ═══ Collinear case: both sides = d' = (O⊔P)⊓m ═══
        set d' := (Γ.O ⊔ P) ⊓ m
        have hd'_atom : IsAtom d' :=
          line_meets_m_at_atom Γ.hO hP_atom hO_ne_P
            (sup_le (le_sup_left.trans le_sup_left) hP_π) hm_le_π hm_cov Γ.hO_not_m
        -- LHS: P⊔C_c = O⊔P by CovBy
        have hP_lt : P < P ⊔ C_c := lt_of_le_of_ne le_sup_left
          (fun h => hP_ne_Cc ((hP_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hCc_atom.1).symm)
        have hLHS_line : P ⊔ C_c = Γ.O ⊔ P :=
          ((sup_comm P Γ.O ▸ atom_covBy_join hP_atom Γ.hO
            (fun h => hO_ne_P h.symm)).eq_or_eq hP_lt.le
            (sup_le le_sup_right hCc_collinear)).resolve_left (ne_of_gt hP_lt)
        -- O⊔C_c = O⊔P (CovBy)
        have hOCc_eq : Γ.O ⊔ C_c = Γ.O ⊔ P := by
          have hO_lt : Γ.O < Γ.O ⊔ C_c := lt_of_le_of_ne le_sup_left
            (fun h => hO_ne_Cc ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
              hCc_atom.1).symm)
          exact ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt.le
            (sup_le le_sup_left hCc_collinear)).resolve_left (ne_of_gt hO_lt)
        -- Both images ≤ b⊔d'
        have hτbP_le : τ_b_P ≤ b ⊔ d' := inf_le_right
        have hτbCc_le : τ_b_C_c ≤ b ⊔ d' := by
          have h : τ_b_C_c ≤ b ⊔ (Γ.O ⊔ C_c) ⊓ m := inf_le_right
          rw [hOCc_eq] at h; exact h
        -- (b⊔d')⊓m = d'
        have hbd'_dir : (b ⊔ d') ⊓ m = d' := line_direction hb hb_not_m inf_le_right
        -- RHS ≤ d'
        have hRHS_le : (τ_b_P ⊔ τ_b_C_c) ⊓ m ≤ d' :=
          (inf_le_inf_right m (sup_le hτbP_le hτbCc_le)).trans hbd'_dir.le
        -- RHS ≠ ⊥
        have hτbCc_atom_local : IsAtom τ_b_C_c :=
          parallelogram_completion_atom Γ.hO hb hCc_atom (fun h => hb_ne_O h.symm) hO_ne_Cc
            hb_ne_Cc (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) hCc_π
            hm_le_π hm_cov hm_line Γ.hO_not_m hb_not_m hCc_not_m
            (fun h => hCc_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
        have hτbP_lt : τ_b_P < τ_b_P ⊔ τ_b_C_c := lt_of_le_of_ne le_sup_left
          (fun h => hτbP_ne_τbCc ((hτbP_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hτbCc_atom_local.1).symm)
        have hRHS_ne : m ⊓ (τ_b_P ⊔ τ_b_C_c) ≠ ⊥ :=
          lines_meet_if_coplanar hm_cov
            (sup_le hτbP_le hτbCc_le |>.trans (sup_le (hb_on.trans le_sup_left)
              (inf_le_right.trans hm_le_π)))
            (fun h => hτbP_not_m (le_sup_left.trans h))
            hτbP_atom hτbP_lt
        rw [hLHS_line]
        exact ((hd'_atom.le_iff.mp hRHS_le).resolve_left (inf_comm m _ ▸ hRHS_ne)).symm
      · -- ═══ Non-collinear case: cross_parallelism ═══
        -- Span: O⊔P⊔C_c = π (same as hcp4)
        have hO_not_q : ¬ Γ.O ≤ q := fun h =>
          Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l) h).trans
            hlq_eq_U.le)).resolve_left Γ.hO.1)
        have hW_atom : IsAtom ((Γ.O ⊔ P) ⊓ q) :=
          line_meets_m_at_atom Γ.hO hP_atom hO_ne_P
            (sup_le (le_sup_left.trans le_sup_left) hP_π)
            (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane) hq_covBy_π
            hO_not_q
        have hW_ne_Cc : (Γ.O ⊔ P) ⊓ q ≠ C_c := fun h => hCc_collinear (h ▸ inf_le_left)
        have hOPCc_span : Γ.O ⊔ P ⊔ C_c = π := by
          have h_mod : (C_c ⊔ (Γ.O ⊔ P)) ⊓ q = C_c ⊔ ((Γ.O ⊔ P) ⊓ q) :=
            sup_inf_assoc_of_le (Γ.O ⊔ P) hCc_le_q
          have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
          have hCc_lt : C_c < C_c ⊔ (Γ.O ⊔ P) ⊓ q := by
            apply lt_of_le_of_ne le_sup_left; intro h
            exact hW_ne_Cc ((hCc_atom.le_iff.mp (le_sup_right.trans (le_of_eq h.symm))).resolve_left
              hW_atom.1)
          have hCc_covBy : C_c ⋖ q := line_covers_its_atoms Γ.hU Γ.hC hUC hCc_atom hCc_le_q
          have hCcW_eq_q : C_c ⊔ (Γ.O ⊔ P) ⊓ q = q :=
            (hCc_covBy.eq_or_eq hCc_lt.le (sup_le hCc_le_q inf_le_right)).resolve_left
              (ne_of_gt hCc_lt)
          have hq_le : q ≤ Γ.O ⊔ P ⊔ C_c := by
            have := inf_eq_right.mp (h_mod.trans hCcW_eq_q); rwa [sup_comm] at this
          have hlC_le : l ⊔ Γ.C ≤ Γ.O ⊔ P ⊔ C_c :=
            sup_le (sup_le (le_sup_left.trans le_sup_left)
              ((le_sup_left : Γ.U ≤ q).trans hq_le))
              ((le_sup_right : Γ.C ≤ q).trans hq_le)
          have hl_lt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
          have hlC_eq : l ⊔ Γ.C = π :=
            (hl_cov_π.eq_or_eq hl_lt.le (sup_le le_sup_left Γ.hC_plane)).resolve_left
              (ne_of_gt hl_lt)
          exact le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left) hP_π) hCc_π)
            (le_of_eq hlC_eq.symm |>.trans hlC_le)
        -- cross_parallelism preconditions
        have hb_ne_τbCc : b ≠ τ_b_C_c := by
          intro h_eq
          have : b ≤ C_c ⊔ Γ.U := by
            have h : τ_b_C_c ≤ C_c ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
            rw [hOb_eq_l, Γ.l_inf_m_eq_U] at h; rwa [← h_eq] at h
          exact hb_ne_U ((Γ.hU.le_iff.mp ((le_inf hb_on
            (this.trans (sup_le hCc_le_q (le_sup_left : Γ.U ≤ q)))).trans
            hlq_eq_U.le)).resolve_left hb.1)
        exact cross_parallelism Γ.hO hb hP_atom hCc_atom
          (fun h => hb_ne_O h.symm) hO_ne_P hO_ne_Cc hP_ne_Cc
          (show b ≠ τ_b_P from by
            intro h_eq
            have hb_le_PU : b ≤ P ⊔ Γ.U := by
              have : τ_b_P ≤ P ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
              rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this; exact h_eq ▸ this
            exact hb_ne_U ((Γ.hU.le_iff.mp
              ((le_inf hb_on hb_le_PU).trans hl_inf_PU.le)).resolve_left hb.1))
          hb_ne_τbCc hτbP_ne_τbCc
          (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) hP_π hCc_π
          hm_le_π hm_cov hm_line
          Γ.hO_not_m hb_not_m hP_not_m hCc_not_m
          (fun h => hP_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
          (fun h => hCc_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
          hCc_collinear hOPCc_span
          R hR hR_not h_irred
    -- ═══ τ_b_C_c infrastructure for hcp6 ═══
    have hτbCc_atom : IsAtom τ_b_C_c :=
      parallelogram_completion_atom Γ.hO hb hCc_atom (fun h => hb_ne_O h.symm) hO_ne_Cc
        hb_ne_Cc (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) hCc_π
        hm_le_π hm_cov hm_line Γ.hO_not_m hb_not_m hCc_not_m
        (fun h => hCc_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
    have hτbCc_not_m : ¬ τ_b_C_c ≤ m := by
      intro h
      have hτbCc_eq_U : τ_b_C_c = Γ.U :=
        (Γ.hU.le_iff.mp ((le_inf hτbCc_le_q h).trans hqm_eq_U.le)).resolve_left hτbCc_atom.1
      have h1 : Γ.U ≤ b ⊔ (Γ.O ⊔ C_c) ⊓ m := by rw [← hτbCc_eq_U]; exact inf_le_right
      have hU_le_OCc : Γ.U ≤ Γ.O ⊔ C_c :=
        ((le_inf h1 (le_sup_left : Γ.U ≤ m)).trans
          (line_direction hb hb_not_m inf_le_right).le).trans inf_le_left
      have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
        (fun h' => Γ.hOU ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1).symm)
      have hl_eq : l = Γ.O ⊔ C_c :=
        ((atom_covBy_join Γ.hO hCc_atom hO_ne_Cc).eq_or_eq hO_lt_l.le
          (sup_le le_sup_left hU_le_OCc)).resolve_left hO_lt_l.ne'
      exact hCc_not_l (hl_eq ▸ le_sup_right)
    have hO_ne_τbCc : Γ.O ≠ τ_b_C_c := by
      intro h; exact Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
        (h ▸ hτbCc_le_q)).trans hlq_eq_U.le)).resolve_left Γ.hO.1)
    have ha_ne_τbCc : a ≠ τ_b_C_c := fun h => ha_ne_U ((Γ.hU.le_iff.mp ((le_inf ha_on
      (h ▸ hτbCc_le_q)).trans hlq_eq_U.le)).resolve_left ha.1)
    -- τ_a_τ_b_C_c facts
    have hτaτbCc_le_q : τ_a_τ_b_C_c ≤ q := by
      have : τ_a_τ_b_C_c ≤ τ_b_C_c ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
      rw [hOa_eq_l, Γ.l_inf_m_eq_U] at this
      exact this.trans (sup_le hτbCc_le_q (le_sup_left : Γ.U ≤ q))
    -- τ_a_τ_b_P ∉ q (proved via hP_agree route: τ_a_τ_b_P = U → τ_s_P = U → l ≤ O⊔P → P ∈ l)
    have hτa_not_q : ¬ τ_a_τ_b_P ≤ q := by
      intro h
      have hτa_eq_U : τ_a_τ_b_P = Γ.U :=
        (Γ.hU.le_iff.mp ((le_inf hτa_le_PU h).trans hPU_inf_q.le)).resolve_left hτa_atom.1
      have hτs_eq_U : τ_s_P = Γ.U := hP_agree ▸ hτa_eq_U
      have h1 : Γ.U ≤ s ⊔ (Γ.O ⊔ P) ⊓ m := by rw [← hτs_eq_U]; exact inf_le_right
      have hU_le_OP : Γ.U ≤ Γ.O ⊔ P :=
        ((le_inf h1 (le_sup_left : Γ.U ≤ m)).trans
          (line_direction hs_atom hs_not_m inf_le_right).le).trans inf_le_left
      have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
        (fun h' => Γ.hOU ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1).symm)
      have hl_eq : l = Γ.O ⊔ P :=
        ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt_l.le
          (sup_le le_sup_left hU_le_OP)).resolve_left (ne_of_gt hO_lt_l)
      exact hP_not_l (hl_eq ▸ le_sup_right)
    -- τ_a_τ_b_P ≠ τ_a_τ_b_C_c
    have hτa_ne_τaτbCc : τ_a_τ_b_P ≠ τ_a_τ_b_C_c := by
      intro h_eq
      exact hτa_not_q (h_eq ▸ hτaτbCc_le_q)
    -- cp(τ_a, τ_b(P), τ_b(C_c))
    have hcp6 : (τ_b_P ⊔ τ_b_C_c) ⊓ m = (τ_a_τ_b_P ⊔ τ_a_τ_b_C_c) ⊓ m := by
      by_cases hτbCc_collinear : τ_b_C_c ≤ Γ.O ⊔ τ_b_P
      · -- ═══ Collinear case: both sides = d' = (O⊔τ_b_P)⊓m ═══
        set d' := (Γ.O ⊔ τ_b_P) ⊓ m
        have hd'_atom : IsAtom d' :=
          line_meets_m_at_atom Γ.hO hτbP_atom hO_ne_τbP
            (sup_le (le_sup_left.trans le_sup_left) hτbP_π) hm_le_π hm_cov Γ.hO_not_m
        -- LHS: τ_b_P⊔τ_b_C_c = O⊔τ_b_P by CovBy
        have hτbP_lt : τ_b_P < τ_b_P ⊔ τ_b_C_c := lt_of_le_of_ne le_sup_left
          (fun h => hτbP_ne_τbCc ((hτbP_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hτbCc_atom.1).symm)
        have hLHS_line : τ_b_P ⊔ τ_b_C_c = Γ.O ⊔ τ_b_P :=
          ((sup_comm τ_b_P Γ.O ▸ atom_covBy_join hτbP_atom Γ.hO
            (fun h => hO_ne_τbP h.symm)).eq_or_eq hτbP_lt.le
            (sup_le le_sup_right hτbCc_collinear)).resolve_left (ne_of_gt hτbP_lt)
        -- O⊔τ_b_C_c = O⊔τ_b_P
        have hOτbCc_eq : Γ.O ⊔ τ_b_C_c = Γ.O ⊔ τ_b_P := by
          have hO_lt : Γ.O < Γ.O ⊔ τ_b_C_c := lt_of_le_of_ne le_sup_left
            (fun h => hO_ne_τbCc ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
              hτbCc_atom.1).symm)
          exact ((atom_covBy_join Γ.hO hτbP_atom hO_ne_τbP).eq_or_eq hO_lt.le
            (sup_le le_sup_left hτbCc_collinear)).resolve_left (ne_of_gt hO_lt)
        -- τ_a_τ_b_P ≤ a⊔d' (from pc def)
        have hτa_le : τ_a_τ_b_P ≤ a ⊔ d' := inf_le_right
        -- τ_a_τ_b_C_c ≤ a⊔d'
        have hτaτbCc_le : τ_a_τ_b_C_c ≤ a ⊔ d' := by
          have h : τ_a_τ_b_C_c ≤ a ⊔ (Γ.O ⊔ τ_b_C_c) ⊓ m := inf_le_right
          rw [hOτbCc_eq] at h; exact h
        -- (a⊔d')⊓m = d'
        have had'_dir : (a ⊔ d') ⊓ m = d' := line_direction ha ha_not_m inf_le_right
        -- RHS ≤ d'
        have hRHS_le : (τ_a_τ_b_P ⊔ τ_a_τ_b_C_c) ⊓ m ≤ d' :=
          (inf_le_inf_right m (sup_le hτa_le hτaτbCc_le)).trans had'_dir.le
        -- τ_a_τ_b_C_c is atom
        have hτaτbCc_atom : IsAtom τ_a_τ_b_C_c :=
          parallelogram_completion_atom Γ.hO ha hτbCc_atom
            (fun h => ha_ne_O h.symm) hO_ne_τbCc ha_ne_τbCc
            (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left)
            (hτbCc_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
            hm_le_π hm_cov hm_line
            Γ.hO_not_m ha_not_m hτbCc_not_m
            (fun h => hτbCc_not_m (((Γ.hU.le_iff.mp ((le_inf
              (h.trans (hOa_eq_l ▸ le_refl l)) hτbCc_le_q).trans
              hlq_eq_U.le)).resolve_left hτbCc_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m)))
        -- RHS ≠ ⊥
        have hτa_lt : τ_a_τ_b_P < τ_a_τ_b_P ⊔ τ_a_τ_b_C_c := lt_of_le_of_ne le_sup_left
          (fun h => hτa_ne_τaτbCc ((hτa_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hτaτbCc_atom.1).symm)
        have hRHS_ne : m ⊓ (τ_a_τ_b_P ⊔ τ_a_τ_b_C_c) ≠ ⊥ :=
          lines_meet_if_coplanar hm_cov
            (sup_le hτa_le hτaτbCc_le |>.trans (sup_le (ha_on.trans le_sup_left)
              (inf_le_right.trans hm_le_π)))
            (fun h => by
              -- Both images ≤ (a⊔d')⊓m = d' (atom), so both = d', contradicting ne.
              have h1 := (le_inf hτa_le (le_sup_left.trans h)).trans (line_direction ha ha_not_m inf_le_right).le
              have h2 := (le_inf hτaτbCc_le (le_sup_right.trans h)).trans (line_direction ha ha_not_m inf_le_right).le
              exact hτa_ne_τaτbCc ((hd'_atom.le_iff.mp h1).resolve_left hτa_atom.1 |>.trans
                ((hd'_atom.le_iff.mp h2).resolve_left hτaτbCc_atom.1).symm))
            hτa_atom hτa_lt
        rw [hLHS_line]
        exact ((hd'_atom.le_iff.mp hRHS_le).resolve_left (inf_comm m _ ▸ hRHS_ne)).symm
      · -- ═══ Non-collinear case: cross_parallelism ═══
        -- O ≠ C_b (for span proof: C_b on q, O ∉ q)
        have hO_ne_τbCc' : Γ.O ≠ τ_b_C_c := hO_ne_τbCc
        -- Span: O⊔τ_b_P⊔τ_b_C_c = π (same pattern as hcp3 non-collinear)
        have hW_atom : IsAtom ((Γ.O ⊔ τ_b_P) ⊓ q) :=
          line_meets_m_at_atom Γ.hO hτbP_atom hO_ne_τbP
            (sup_le (le_sup_left.trans le_sup_left) hτbP_π)
            (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane) hq_covBy_π
            (fun h => Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l) h).trans
              hlq_eq_U.le)).resolve_left Γ.hO.1))
        have hW_ne_τbCc : (Γ.O ⊔ τ_b_P) ⊓ q ≠ τ_b_C_c := fun h =>
          hτbCc_collinear (h ▸ inf_le_left)
        have hspan : Γ.O ⊔ τ_b_P ⊔ τ_b_C_c = π := by
          have h_mod : (τ_b_C_c ⊔ (Γ.O ⊔ τ_b_P)) ⊓ q = τ_b_C_c ⊔ ((Γ.O ⊔ τ_b_P) ⊓ q) :=
            sup_inf_assoc_of_le (Γ.O ⊔ τ_b_P) hτbCc_le_q
          have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
          have hτbCc_lt : τ_b_C_c < τ_b_C_c ⊔ (Γ.O ⊔ τ_b_P) ⊓ q := by
            apply lt_of_le_of_ne le_sup_left; intro h
            exact hW_ne_τbCc ((hτbCc_atom.le_iff.mp (le_sup_right.trans (le_of_eq h.symm))).resolve_left
              hW_atom.1)
          have hτbCc_covBy : τ_b_C_c ⋖ q := line_covers_its_atoms Γ.hU Γ.hC hUC hτbCc_atom hτbCc_le_q
          have hτbCcW_eq_q : τ_b_C_c ⊔ (Γ.O ⊔ τ_b_P) ⊓ q = q :=
            (hτbCc_covBy.eq_or_eq hτbCc_lt.le (sup_le hτbCc_le_q inf_le_right)).resolve_left
              (ne_of_gt hτbCc_lt)
          have hq_le : q ≤ Γ.O ⊔ τ_b_P ⊔ τ_b_C_c := by
            have := inf_eq_right.mp (h_mod.trans hτbCcW_eq_q); rwa [sup_comm] at this
          have hlC_le : l ⊔ Γ.C ≤ Γ.O ⊔ τ_b_P ⊔ τ_b_C_c :=
            sup_le (sup_le (le_sup_left.trans le_sup_left)
              ((le_sup_left : Γ.U ≤ q).trans hq_le))
              ((le_sup_right : Γ.C ≤ q).trans hq_le)
          have hl_lt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
          have hlC_eq : l ⊔ Γ.C = π :=
            (hl_cov_π.eq_or_eq hl_lt.le (sup_le le_sup_left Γ.hC_plane)).resolve_left
              (ne_of_gt hl_lt)
          exact le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left) hτbP_π)
            (hτbCc_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)))
            (le_of_eq hlC_eq.symm |>.trans hlC_le)
        -- cross_parallelism preconditions
        have hτbCc_not_Oa : ¬ τ_b_C_c ≤ Γ.O ⊔ a := by
          intro h; exact hτbCc_not_m (((Γ.hU.le_iff.mp ((le_inf (h.trans (hOa_eq_l ▸ le_refl l))
            hτbCc_le_q).trans hlq_eq_U.le)).resolve_left hτbCc_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
        have ha_ne_τa' : a ≠ τ_a_τ_b_P := by
          intro h_eq
          have hτa_le_τU : τ_a_τ_b_P ≤ τ_b_P ⊔ Γ.U := by
            have : τ_a_τ_b_P ≤ τ_b_P ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
            rwa [hOa_eq_l, Γ.l_inf_m_eq_U] at this
          rw [← h_eq] at hτa_le_τU
          exact ha_ne_U ((Γ.hU.le_iff.mp ((le_inf ha_on
            (hτa_le_τU.trans (sup_le hτbP_le_PU le_sup_right))).trans
            hl_inf_PU.le)).resolve_left ha.1)
        have ha_ne_τaτbCc : a ≠ parallelogram_completion Γ.O a τ_b_C_c m := by
          intro h; exact ha_ne_U ((Γ.hU.le_iff.mp
            ((le_inf ha_on (h ▸ hτaτbCc_le_q)).trans hlq_eq_U.le)).resolve_left ha.1)
        have hτa_ne_τaτbCc' : τ_a_τ_b_P ≠ parallelogram_completion Γ.O a τ_b_C_c m := by
          intro h_eq
          exact hτa_not_q (h_eq ▸ hτaτbCc_le_q)
        exact cross_parallelism Γ.hO ha hτbP_atom hτbCc_atom
          (fun h => ha_ne_O h.symm) hO_ne_τbP hO_ne_τbCc hτbP_ne_τbCc
          ha_ne_τa' ha_ne_τaτbCc hτa_ne_τaτbCc'
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hτbP_π
          (hτbCc_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m hτbP_not_m hτbCc_not_m
          (fun h => hτbP_not_q ((le_inf (h.trans (hOa_eq_l ▸ le_refl l))
            hτbP_le_PU).trans hl_inf_PU.le |>.trans (le_sup_left : Γ.U ≤ q)))
          hτbCc_not_Oa
          hτbCc_collinear
          hspan
          R hR hR_not h_irred
    -- Direction chain + substitute hP_agree
    have h_dir2 : (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m = (τ_a_τ_b_P ⊔ τ_a_τ_b_C_c) ⊓ m := by
      have h := hcp4.symm.trans (hcp5.trans hcp6)
      rwa [hP_agree] at h
    -- ═══ two_lines on q: τ_s_C_c = τ_a_τ_b_C_c ═══
    have hCc_agree : τ_s_C_c = τ_a_τ_b_C_c := by
      -- τ_a_τ_b_C_c is atom on q
      have hτaτbCc_atom : IsAtom τ_a_τ_b_C_c :=
        parallelogram_completion_atom Γ.hO ha hτbCc_atom
          (fun h => ha_ne_O h.symm) hO_ne_τbCc ha_ne_τbCc
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left)
          (hτbCc_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m hτbCc_not_m
          (fun h => hτbCc_not_m (((Γ.hU.le_iff.mp ((le_inf
            (h.trans (hOa_eq_l ▸ le_refl l)) hτbCc_le_q).trans
            hlq_eq_U.le)).resolve_left hτbCc_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m)))
      -- τ_s_C_c ≠ τ_a_τ_b_P
      have hτsCc_ne_τa : τ_s_C_c ≠ τ_a_τ_b_P := fun h => hτa_not_q (h ▸ hτsCc_le_q)
      -- τ_a_τ_b_P ∉ m
      have hτa_not_m : ¬ τ_a_τ_b_P ≤ m := by
        intro h; apply hτa_not_q
        -- τ_a_τ_b_P ≤ P⊔U and ≤ m. Show (P⊔U)⊓m = U via modular law.
        have hPm : P ⊓ m = ⊥ :=
          (hP_atom.le_iff.mp inf_le_left).resolve_right (fun h' => hP_not_m (h' ▸ inf_le_right))
        have hPUm : (P ⊔ Γ.U) ⊓ m = Γ.U := by
          show (P ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
          rw [sup_comm P Γ.U, sup_inf_assoc_of_le P (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V),
              hPm, sup_bot_eq]
        have : τ_a_τ_b_P ≤ Γ.U := (le_inf hτa_le_PU h).trans hPUm.le
        exact ((Γ.hU.le_iff.mp this).resolve_left hτa_atom.1).symm ▸ (le_sup_left : Γ.U ≤ q)
      -- Line equality via CovBy: τ_a_τ_b_P ⊔ τ_s_C_c = τ_a_τ_b_P ⊔ τ_a_τ_b_C_c
      have hd_atom : IsAtom ((τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m) := by
        rw [sup_comm]; exact line_meets_m_at_atom hτsCc_atom hτa_atom
          hτsCc_ne_τa (sup_le (hτsCc_le_q.trans
            (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
            (hτa_le_PU.trans (sup_le hP_π (le_sup_right.trans le_sup_left))))
          hm_le_π hm_cov hτsCc_not_m
      have hd_ne_τa : (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m ≠ τ_a_τ_b_P := fun h =>
        hτa_not_m (h ▸ inf_le_right)
      have hτa_covBy_1 : τ_a_τ_b_P ⋖ τ_a_τ_b_P ⊔ τ_s_C_c :=
        atom_covBy_join hτa_atom hτsCc_atom hτsCc_ne_τa.symm
      have hτa_lt_d : τ_a_τ_b_P < τ_a_τ_b_P ⊔ (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m :=
        lt_of_le_of_ne le_sup_left
          (fun h => hd_ne_τa ((hτa_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hd_atom.1))
      have hd_eq_1 : τ_a_τ_b_P ⊔ (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m = τ_a_τ_b_P ⊔ τ_s_C_c :=
        (hτa_covBy_1.eq_or_eq hτa_lt_d.le (sup_le le_sup_left inf_le_left)).resolve_left
          (ne_of_gt hτa_lt_d)
      have hτa_covBy_2 : τ_a_τ_b_P ⋖ τ_a_τ_b_P ⊔ τ_a_τ_b_C_c :=
        atom_covBy_join hτa_atom hτaτbCc_atom hτa_ne_τaτbCc
      have hd_le_2 : (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m ≤ τ_a_τ_b_P ⊔ τ_a_τ_b_C_c :=
        h_dir2 ▸ inf_le_left
      have hd_eq_2 : τ_a_τ_b_P ⊔ (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m = τ_a_τ_b_P ⊔ τ_a_τ_b_C_c :=
        (hτa_covBy_2.eq_or_eq hτa_lt_d.le (sup_le le_sup_left hd_le_2)).resolve_left
          (ne_of_gt hτa_lt_d)
      have hline_eq : τ_a_τ_b_P ⊔ τ_s_C_c = τ_a_τ_b_P ⊔ τ_a_τ_b_C_c :=
        hd_eq_1.symm.trans hd_eq_2
      have hτaτbCc_on_line : τ_a_τ_b_C_c ≤ τ_s_C_c ⊔ τ_a_τ_b_P :=
        sup_comm τ_s_C_c τ_a_τ_b_P ▸ hline_eq ▸ le_sup_right
      have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
      exact two_lines hτsCc_atom hτaτbCc_atom hτa_atom hτsCc_ne_τa
        hτsCc_le_q hτaτbCc_le_q hτaτbCc_on_line hτa_not_q
        (line_covers_its_atoms Γ.hU Γ.hC hUC hτsCc_atom hτsCc_le_q)
    exact hCc_agree
  -- ═══ Step 3: E-perspectivity injectivity → LHS = RHS ═══
  -- Key: (pc(O, x, C, m) ⊔ E) ⊓ l = x for any atom x on l.
  -- This recovers x from its β-image, so h_beta_eq forces LHS = RHS.
  have hLHS_atom : IsAtom (coord_add Γ s c) :=
    coord_add_atom Γ s c hs_atom hc hs_on hc_on hs_ne_O hc_ne_O hs_ne_U hc_ne_U
  have hRHS_atom : IsAtom (coord_add Γ a t) :=
    coord_add_atom Γ a t ha ht_atom ha_on ht_on ha_ne_O ht_ne_O ha_ne_U ht_ne_U
  have hE_inf_l : Γ.E ⊓ l = ⊥ :=
    (Γ.hE_atom.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hE_not_l (h ▸ inf_le_right))
  -- Recovery lemma: the E-perspectivity from l to q is inverted by (· ⊔ E) ⊓ l
  have recover : ∀ (x : L), IsAtom x → x ≤ l →
      (parallelogram_completion Γ.O x Γ.C m ⊔ Γ.E) ⊓ l = x := by
    intro x hx hx_l
    -- Strategy: show pc ⊔ E = x ⊔ E, then (x ⊔ E) ⊓ l = x by modular law.
    suffices h_eq : parallelogram_completion Γ.O x Γ.C m ⊔ Γ.E = x ⊔ Γ.E by
      rw [h_eq, sup_inf_assoc_of_le Γ.E hx_l, hE_inf_l, sup_bot_eq]
    apply le_antisymm
    · -- pc ⊔ E ≤ x ⊔ E: pc ≤ x ⊔ E (inf_le_right of pc defn), E ≤ x ⊔ E
      exact sup_le (show parallelogram_completion Γ.O x Γ.C m ≤ x ⊔ Γ.E from
        inf_le_right) le_sup_right
    · -- x ⊔ E ≤ pc ⊔ E: E ≤ pc ⊔ E (le_sup_right). x ≤ pc ⊔ E:
      -- By modular law: pc ⊔ E = ((C⊔d) ⊔ E) ⊓ (x⊔E), where d = (O⊔x)⊓m.
      -- So x ≤ pc ⊔ E iff x ≤ (C⊔d)⊔E (since x ≤ x⊔E already).
      apply sup_le _ le_sup_right
      -- Goal: x ≤ pc ⊔ E
      -- Rewrite pc ⊔ E via modular law
      have h_mod : parallelogram_completion Γ.O x Γ.C m ⊔ Γ.E =
          ((Γ.C ⊔ (Γ.O ⊔ x) ⊓ m) ⊔ Γ.E) ⊓ (x ⊔ Γ.E) := by
        -- pc = (C⊔d)⊓(x⊔E). pc⊔E = (C⊔d)⊓(x⊔E)⊔E = (E⊔(C⊔d))⊓(x⊔E) [modular, E≤x⊔E]
        show (Γ.C ⊔ (Γ.O ⊔ x) ⊓ m) ⊓ (x ⊔ Γ.E) ⊔ Γ.E =
             ((Γ.C ⊔ (Γ.O ⊔ x) ⊓ m) ⊔ Γ.E) ⊓ (x ⊔ Γ.E)
        have := sup_inf_assoc_of_le (Γ.C ⊔ (Γ.O ⊔ x) ⊓ m)
          (le_sup_right : Γ.E ≤ x ⊔ Γ.E)
        -- this : (Γ.E ⊔ (C⊔d)) ⊓ (x⊔E) = Γ.E ⊔ (C⊔d) ⊓ (x⊔E)
        rw [sup_comm] at this  -- ((C⊔d) ⊔ E) ⊓ (x⊔E) = Γ.E ⊔ (C⊔d)⊓(x⊔E)
        rw [sup_comm Γ.E _] at this  -- ((C⊔d) ⊔ E) ⊓ (x⊔E) = (C⊔d)⊓(x⊔E) ⊔ Γ.E
        exact this.symm
      rw [h_mod]
      -- Goal: x ≤ ((C ⊔ d) ⊔ E) ⊓ (x ⊔ E)
      -- x ≤ x ⊔ E (le_sup_left) and x ≤ (C⊔d)⊔E (case analysis)
      apply le_inf _ le_sup_left
      -- Goal: x ≤ (C ⊔ (O⊔x)⊓m) ⊔ E
      by_cases hx_O : x = Γ.O
      · -- x = O: (C⊔d)⊔E where d = (O⊔O)⊓m. C⊔E = O⊔C ≥ O.
        subst hx_O
        have hC_ne_E : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
        have hCE_eq_OC : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
          have hCE_le : Γ.C ⊔ Γ.E ≤ Γ.C ⊔ Γ.O :=
            (sup_comm Γ.O Γ.C) ▸ (sup_le le_sup_right Γ.hE_le_OC : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C)
          have hC_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
            (fun h => hC_ne_E ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
              Γ.hE_atom.1).symm)
          have := ((atom_covBy_join Γ.hC Γ.hO (fun h => Γ.hC_not_l (h ▸ le_sup_left))).eq_or_eq
            hC_lt.le hCE_le).resolve_left (ne_of_gt hC_lt)
          rw [sup_comm Γ.C Γ.O] at this; exact this
        calc Γ.O ≤ Γ.O ⊔ Γ.C := le_sup_left
          _ = Γ.C ⊔ Γ.E := hCE_eq_OC.symm
          _ ≤ (Γ.C ⊔ (Γ.O ⊔ Γ.O) ⊓ m) ⊔ Γ.E :=
              sup_le_sup_right (le_sup_left : Γ.C ≤ Γ.C ⊔ (Γ.O ⊔ Γ.O) ⊓ m) Γ.E
      · -- x ≠ O: O⊔x = l, d = U, (C⊔U)⊔E = q⊔E = π ≥ x
        have hOx_eq_l : Γ.O ⊔ x = l := by
          have hO_lt : Γ.O < Γ.O ⊔ x := by
            apply lt_of_le_of_ne le_sup_left; intro h
            have hx_le_O : x ≤ Γ.O := le_sup_right.trans (le_of_eq h.symm)
            exact hx_O (le_antisymm hx_le_O
              (Γ.hO.le_iff.mp hx_le_O |>.resolve_left hx.1 ▸ le_refl _))
          exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
            (sup_le le_sup_left hx_l)).resolve_left (ne_of_gt hO_lt)
        rw [hOx_eq_l, Γ.l_inf_m_eq_U]
        have hqm : q ⊓ m = Γ.U := by
          show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
          rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
          have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
            (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
          rw [this, sup_bot_eq]
        have hq_covBy_π : q ⋖ π := by
          have h_inf : m ⊓ q ⋖ m := by
            rw [inf_comm, hqm]
            exact atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))
          have hmq : m ⊔ q = π := by
            have : m ⊔ q = m ⊔ Γ.C := by
              show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
              rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
            rw [this]
            exact (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
              (sup_le hm_le_π Γ.hC_plane)).resolve_left
              (ne_of_gt (lt_of_le_of_ne le_sup_left
                (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
          have h1 := covBy_sup_of_inf_covBy_left h_inf; rwa [hmq] at h1
        have hqE_eq_π : q ⊔ Γ.E = π := by
          have hE_not_q : ¬ Γ.E ≤ q := fun hle =>
            Γ.hEU ((Γ.hU.le_iff.mp (hqm ▸ le_inf hle Γ.hE_on_m)).resolve_left Γ.hE_atom.1)
          have hq_lt : q < q ⊔ Γ.E := lt_of_le_of_ne le_sup_left
            (fun h => hE_not_q (le_sup_right.trans h.symm.le))
          exact (hq_covBy_π.eq_or_eq hq_lt.le
            (sup_le (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
              (Γ.hE_on_m.trans hm_le_π))).resolve_left (ne_of_gt hq_lt)
        calc x ≤ l := hx_l
          _ ≤ π := le_sup_left
          _ = q ⊔ Γ.E := hqE_eq_π.symm
          _ = (Γ.C ⊔ Γ.U) ⊔ Γ.E := by
              show (Γ.U ⊔ Γ.C) ⊔ Γ.E = (Γ.C ⊔ Γ.U) ⊔ Γ.E; rw [sup_comm Γ.U Γ.C]
  -- Apply recovery to both sides
  have hLHS_on_l : coord_add Γ s c ≤ l := by
    show coord_add Γ s c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hRHS_on_l : coord_add Γ a t ≤ l := by
    show coord_add Γ a t ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  calc coord_add Γ s c
      = (C_LHS ⊔ Γ.E) ⊓ l := (recover (coord_add Γ s c) hLHS_atom hLHS_on_l).symm
    _ = (C_RHS ⊔ Γ.E) ⊓ l := by rw [h_beta_eq]
    _ = coord_add Γ a t := recover (coord_add Γ a t) hRHS_atom hRHS_on_l

end Foam.FTPGExplore
