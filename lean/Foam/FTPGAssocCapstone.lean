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
    obtain ⟨P, hP_atom, hP_π, hP_not_l, hP_not_m, hP_not_q⟩ :
        ∃ P : L, IsAtom P ∧ P ≤ π ∧ ¬ P ≤ l ∧ ¬ P ≤ m ∧ ¬ P ≤ q := by
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
        inf_le_right.trans (sup_le (ha_on.trans le_sup_left) Γ.hC_plane), ?_, ?_, ?_⟩
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
    -- ═══ Chain 1: at (P, Γ.C) → τ_s(P) = τ_a(τ_b(P)) ═══
    -- cp(τ_s, P, C): (P⊔C)⊓m = (τ_s_P ⊔ C_s)⊓m
    have hcp1 : (P ⊔ Γ.C) ⊓ m = (τ_s_P ⊔ C_s) ⊓ m := by
      sorry -- cross_parallelism with P₀=O, P₀'=s, P=P, Q=C
    -- cp(τ_b, P, C): (P⊔C)⊓m = (τ_b_P ⊔ C_b)⊓m
    have hcp2 : (P ⊔ Γ.C) ⊓ m = (τ_b_P ⊔ C_b) ⊓ m := by
      sorry -- cross_parallelism with P₀=O, P₀'=b, P=P, Q=C
    -- cp(τ_a, τ_b(P), C_b): (τ_b_P⊔C_b)⊓m = (τ_a_τ_b_P ⊔ C_s)⊓m
    have hcp3 : (τ_b_P ⊔ C_b) ⊓ m = (τ_a_τ_b_P ⊔ C_s) ⊓ m := by
      -- cross_parallelism gives (τ_b_P⊔C_b)⊓m = (τ_a_τ_b_P ⊔ pc(O,a,C_b,m))⊓m
      -- then h_ki_ab : pc(O,a,C_b,m) = C_s
      sorry
    -- Direction chain: (τ_s_P ⊔ C_s)⊓m = (τ_a_τ_b_P ⊔ C_s)⊓m
    have h_dir1 : (τ_s_P ⊔ C_s) ⊓ m = (τ_a_τ_b_P ⊔ C_s) ⊓ m :=
      hcp1.symm.trans (hcp2.trans hcp3)
    -- two_lines on l: τ_s_P = τ_a_τ_b_P
    -- Both on l (translations preserve l). C_s ∉ l. Shared direction via h_dir1.
    have hP_agree : τ_s_P = τ_a_τ_b_P := by
      sorry -- two_lines + CovBy argument to show collinearity from h_dir1
    -- ═══ Chain 2: at (P, C_c) → τ_s(C_c) = τ_a(τ_b(C_c)) ═══
    -- cp(τ_s, P, C_c)
    have hcp4 : (P ⊔ C_c) ⊓ m = (τ_s_P ⊔ τ_s_C_c) ⊓ m := by
      sorry -- cross_parallelism with P₀=O, P₀'=s, P=P, Q=C_c
    -- cp(τ_b, P, C_c)
    have hcp5 : (P ⊔ C_c) ⊓ m = (τ_b_P ⊔ τ_b_C_c) ⊓ m := by
      sorry -- cross_parallelism with P₀=O, P₀'=b, P=P, Q=C_c
    -- cp(τ_a, τ_b(P), τ_b(C_c))
    have hcp6 : (τ_b_P ⊔ τ_b_C_c) ⊓ m = (τ_a_τ_b_P ⊔ τ_a_τ_b_C_c) ⊓ m := by
      sorry -- cross_parallelism with P₀=O, P₀'=a, P=τ_b_P, Q=τ_b_C_c
    -- Direction chain + substitute hP_agree
    have h_dir2 : (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m = (τ_a_τ_b_P ⊔ τ_a_τ_b_C_c) ⊓ m := by
      have h := hcp4.symm.trans (hcp5.trans hcp6)
      rwa [hP_agree] at h
    -- two_lines on q: τ_s_C_c = τ_a_τ_b_C_c
    -- Both on q (O-translations preserve q when the point is on q).
    -- τ_a_τ_b_P ∉ q (it's on l, l⊓q = U, and τ_a_τ_b_P ≠ U).
    -- Shared line from h_dir2.
    have hCc_agree : τ_s_C_c = τ_a_τ_b_C_c := by
      sorry -- two_lines + CovBy argument from h_dir2
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
