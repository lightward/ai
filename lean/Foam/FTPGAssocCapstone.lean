/-
# Associativity capstone (Part V-B)

The final sorry: coord_add_assoc.

## Proof architecture (session 57)

The proof routes through q via β-injectivity. Instead of proving the
composition law directly on l (where all tools degenerate), we:

1. Apply key_identity three times to reduce the goal to an O-based
   composition on a q-point: pc(O, s, C_c, m) = pc(O, a, pc(O, b, C_c, m), m).
   Here C_c = β(c) is on q but OFF l — so O-based translations work.

2. Prove the O-based composition at C_c via a cross-parallelism chain:
   - Pick auxiliary P off l, m, q.
   - Three cross_parallelism calls: τ_s, τ_b, τ_a applied to (P, C_c).
   - The chain gives: (X⊔β(LHS))⊓m = (X'⊔β(RHS))⊓m where X = τ_s(P),
     X' = τ_a(τ_b(P)).
   - From the (P, Γ.C) chain: X = X' (the composition agrees at P).
   - Two-lines argument: X⊔e is a single line, β(LHS) and β(RHS) both
     on this line AND on q → β(LHS) = β(RHS).

3. E-perspectivity recovery: β(LHS) = β(RHS) → LHS = RHS.

## Key lemmas

### translation_determined_by_param (session 58: PROVEN)

If pc(C, C₁, P, m) = pc(C, C₂, P, m) for P off q and m in π, then C₁ = C₂.
pc(C, C_i, P, m) IS a perspectivity from q to P⊔U through center e_P = (C⊔P)⊓m.

### E-perspectivity recovery (session 59: PROVEN)

(pc(O, x, C, m) ⊔ E) ⊓ l = x for any atom x on l.

The E-perspectivity x ↦ C_x = (C⊔d)⊓(x⊔E) from l to q is inverted by
joining with E and meeting with l. Key: pc ⊔ E = x ⊔ E (modular law +
containment x ≤ (C⊔d)⊔E), then (x⊔E) ⊓ l = x (modular law, E⊓l = ⊥).
Case split: x = O gives C⊔E = O⊔C (CovBy); x ≠ O gives (C⊔U)⊔E = π.
This closes Step 3: h_beta_eq threads through as a three-step calc.

## Status

1 sorry: coord_add_assoc (Step 2 only — the composition law at C_c).
Steps 1 and 3 proven. Key lemmas proven (0 sorry).
Remaining: 6 cross_parallelism calls + 2 two-lines arguments (~400-600 lines).
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
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
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
    -- Goal: pc(O, s, C_c, m) = pc(O, a, pc(O, b, C_c, m), m)
    -- This is the composition law at C_c, proved by cross-parallelism chain.
    sorry
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
