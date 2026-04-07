/-
# Well-definedness of translations (Part IV)

Proves that the parallelogram completion doesn't depend on the choice
of base point: if PP' ∥ QQ' (same direction), then the completions
of any R agree. This is the key use of small_desargues'.

- `parallelogram_completion_well_defined`: Hartshorne Theorem 7.6, Step 2

## Status (session 50)

0 sorry, 0 errors. Clean.
-/

import Foam.FTPGParallelogram

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-!
## Part IV: Well-definedness (the key use of small_desargues')

The parallelogram completion of Q depends on the "direction" atoms
d and e. But what if we used DIFFERENT points to define the same
translation? If P₁ gives Q₁' and P₂ gives Q₂', then Q₁' = Q₂'.

This is exactly what small_desargues' proves: if two parallelogram
constructions agree on the "directions," the results agree.

Concretely: if PP' ∥ QQ₁' and PQ ∥ P'Q₁' (first parallelogram),
and PP' ∥ QQ₂' and PQ ∥ P'Q₂' (same directions, different
construction), then Q₁' = Q₂'.

More importantly: if we use DIFFERENT base pairs (P,P') and (R,R')
defining the same translation (i.e., PP' ∥ RR' and PR ∥ P'R'),
then the completions of any Q agree. This uses small_desargues'.
-/

omit [ComplementedLattice L] in
/-- **Well-definedness of translations (Hartshorne Theorem 7.6, Step 2).**

    If Q' = parallelogram_completion P P' Q m and
    R₁ = parallelogram_completion P P' R m, then
    R₁ = parallelogram_completion Q Q' R m.

    In words: the translation defined by base pair (P,P') can equivalently
    be computed using any other pair (Q,Q') in its orbit.

    Proof sketch:
    1. From Part III: PQ ∥ P'Q' and PR ∥ P'R₁
    2. Apply small_desargues' to get QR ∥ Q'R₁
    3. R₁ is on line R⊔d (from first completion) and on line Q'⊔f
       where f = (Q⊔R)⊓m (from step 2). These are exactly the
       two lines whose intersection defines parallelogram_completion Q Q' R m.
    4. Since both are atoms, R₁ = parallelogram_completion Q Q' R m. -/
theorem parallelogram_completion_well_defined
    {P P' Q R m π : L}
    (hP : IsAtom P) (hP' : IsAtom P') (hQ : IsAtom Q) (hR : IsAtom R)
    (hPP' : P ≠ P') (hPQ : P ≠ Q) (hPR : P ≠ R) (hP'Q : P' ≠ Q)
    (hP'R : P' ≠ R) (hQR : Q ≠ R)
    -- All in π
    (hP_le : P ≤ π) (hP'_le : P' ≤ π) (hQ_le : Q ≤ π) (hR_le : R ≤ π)
    -- m is a line in π
    (hm_le : m ≤ π) (hm_cov : m ⋖ π)
    (hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m)
    -- None on m
    (hP_not : ¬ P ≤ m) (hP'_not : ¬ P' ≤ m) (hQ_not : ¬ Q ≤ m) (hR_not : ¬ R ≤ m)
    -- Non-collinearity: P, Q, R are in general position
    (hQ_not_PP' : ¬ Q ≤ P ⊔ P') (hR_not_PP' : ¬ R ≤ P ⊔ P')
    (hR_not_PQ : ¬ R ≤ P ⊔ Q) (hQ_not_PR : ¬ Q ≤ P ⊔ R)
    (hR_not_QQ' : ¬ R ≤ Q ⊔ parallelogram_completion P P' Q m)
    -- P⊔Q⊔R spans π (follows from the above + π being a plane, but stated for convenience)
    (h_span : P ⊔ Q ⊔ R = π)
    -- Height ≥ 4 and irreducibility (needed for small_desargues')
    (W : L) (hW : IsAtom W) (hW_not : ¬ W ≤ π)
    (h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b) :
    parallelogram_completion P P' R m =
    parallelogram_completion Q (parallelogram_completion P P' Q m) R m := by
  set d := (P ⊔ P') ⊓ m   -- shared direction
  set e := (P ⊔ Q) ⊓ m    -- direction of PQ
  set g := (P ⊔ R) ⊓ m    -- direction of PR
  set f := (Q ⊔ R) ⊓ m    -- direction of QR (for the conclusion)
  set Q' := parallelogram_completion P P' Q m
  set R₁ := parallelogram_completion P P' R m
  -- ═══ Step 0: Establish atoms and basic properties ═══
  have hd_atom : IsAtom d := line_meets_m_at_atom hP hP' hPP'
    (sup_le hP_le hP'_le) hm_le hm_cov hP_not
  have he_atom : IsAtom e := line_meets_m_at_atom hP hQ hPQ
    (sup_le hP_le hQ_le) hm_le hm_cov hP_not
  have hg_atom : IsAtom g := line_meets_m_at_atom hP hR hPR
    (sup_le hP_le hR_le) hm_le hm_cov hP_not
  have hQ'_atom : IsAtom Q' := parallelogram_completion_atom hP hP' hQ hPP' hPQ hP'Q
    hP_le hP'_le hQ_le hm_le hm_cov hm_line hP_not hP'_not hQ_not hQ_not_PP'
  have hR₁_atom : IsAtom R₁ := parallelogram_completion_atom hP hP' hR hPP' hPR hP'R
    hP_le hP'_le hR_le hm_le hm_cov hm_line hP_not hP'_not hR_not hR_not_PP'
  have hd_le_m : d ≤ m := inf_le_right
  -- ═══ Helpers (needed by Step 1 and Step 2) ═══
  have hde_ne : d ≠ e := by
    intro h_eq
    have hd_le_PQ : d ≤ P ⊔ Q := h_eq ▸ (inf_le_left : e ≤ P ⊔ Q)
    have hd_le_P : d ≤ P := by
      have := le_inf (inf_le_left : d ≤ P ⊔ P') hd_le_PQ
      rwa [modular_intersection hP hP' hQ hPP' hPQ hP'Q hQ_not_PP'] at this
    have hPm : P ⊓ m = ⊥ := by
      rcases hP.le_iff.mp inf_le_left with h | h
      · exact h
      · exact absurd (h ▸ inf_le_right) hP_not
    exact hd_atom.1 (le_antisymm (hPm ▸ le_inf hd_le_P hd_le_m) bot_le)
  -- Helper: d ≠ g
  have hdg_ne : d ≠ g := by
    intro h_eq
    have hd_le_PR : d ≤ P ⊔ R := h_eq ▸ (inf_le_left : g ≤ P ⊔ R)
    have hd_le_P : d ≤ P := by
      have := le_inf (inf_le_left : d ≤ P ⊔ P') hd_le_PR
      rwa [modular_intersection hP hP' hR hPP' hPR hP'R hR_not_PP'] at this
    have hPm : P ⊓ m = ⊥ := by
      rcases hP.le_iff.mp inf_le_left with h | h
      · exact h
      · exact absurd (h ▸ inf_le_right) hP_not
    exact hd_atom.1 (le_antisymm (hPm ▸ le_inf hd_le_P hd_le_m) bot_le)
  -- Helper: if an atom d on m is ≤ P'⊔x for atom x on m with P'≠x, then P' ≤ m (contradiction)
  have d_not_on_P'_line : ∀ {x : L}, IsAtom x → x ≤ m → d ≠ x → P' ≠ x →
      d ≤ P' ⊔ x → False := by
    intro x hx hx_le hdx hP'x hd_le
    have h_d_lt_dx : d < d ⊔ x := lt_of_le_of_ne le_sup_left
      (fun h => hdx ((hd_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hx.1).symm)
    have h_dx_le : d ⊔ x ≤ P' ⊔ x := sup_le hd_le le_sup_right
    have hd_cov : d ⋖ P' ⊔ x := line_covers_its_atoms hP' hx hP'x hd_atom hd_le
    rcases hd_cov.eq_or_eq h_d_lt_dx.le h_dx_le with h_eq | h_eq
    · exact absurd h_eq (ne_of_gt h_d_lt_dx)
    · exact hP'_not (le_trans le_sup_left (h_eq ▸ sup_le hd_le_m hx_le))
  have hQ'_not_m : ¬ Q' ≤ m := by
    intro h
    have hQ'_le_Qd : Q' ≤ Q ⊔ d := by
      have : Q' = (Q ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ Q) ⊓ m) := rfl
      rw [this]; exact inf_le_left
    have hQ'_le_d : Q' ≤ d := by
      calc Q' ≤ (Q ⊔ d) ⊓ m := le_inf hQ'_le_Qd h
        _ = d := line_direction hQ hQ_not hd_le_m
    have hQ'_eq_d : Q' = d := (hd_atom.le_iff.mp hQ'_le_d).resolve_left hQ'_atom.1
    have hQ'_le_P'e : Q' ≤ P' ⊔ e := by
      have : Q' = (Q ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ Q) ⊓ m) := rfl
      rw [this]; exact inf_le_right
    exact d_not_on_P'_line he_atom inf_le_right hde_ne
      (fun h => hP'_not (h ▸ inf_le_right)) (hQ'_eq_d ▸ hQ'_le_P'e)
  have hR₁_not_m : ¬ R₁ ≤ m := by
    intro h
    have hR₁_le_Rd : R₁ ≤ R ⊔ d := by
      have : R₁ = (R ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ R) ⊓ m) := rfl
      rw [this]; exact inf_le_left
    have hR₁_le_d : R₁ ≤ d := by
      calc R₁ ≤ (R ⊔ d) ⊓ m := le_inf hR₁_le_Rd h
        _ = d := line_direction hR hR_not hd_le_m
    have hR₁_eq_d : R₁ = d := (hd_atom.le_iff.mp hR₁_le_d).resolve_left hR₁_atom.1
    have hR₁_le_P'g : R₁ ≤ P' ⊔ g := by
      have : R₁ = (R ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ R) ⊓ m) := rfl
      rw [this]; exact inf_le_right
    exact d_not_on_P'_line hg_atom inf_le_right hdg_ne
      (fun h => hP'_not (h ▸ inf_le_right)) (hR₁_eq_d ▸ hR₁_le_P'g)
  -- d' = (Q ⊔ Q') ⊓ m = d (QQ' has same direction as PP')
  have hQ'_ne_Q : Q' ≠ Q := by
    intro h
    -- If Q' = Q, then Q ≤ P'⊔e (since Q' ≤ P'⊔e from the completion)
    have hQ'_le_P'e : Q' ≤ P' ⊔ e := by
      have : Q' = (Q ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ Q) ⊓ m) := rfl
      rw [this]; exact inf_le_right
    have hQ_le_P'e : Q ≤ P' ⊔ e := h ▸ hQ'_le_P'e
    -- e ≤ P⊔Q, so Q⊔e ≤ P⊔Q. Also Q⊔e ≤ P'⊔e.
    have he_le_PQ : e ≤ P ⊔ Q := inf_le_left
    have hQe_ne : Q ≠ e := fun h => hQ_not (h ▸ inf_le_right)
    -- Q⊔e ≤ P'⊔e (from Q ≤ P'⊔e)
    have hQe_le_P'e : Q ⊔ e ≤ P' ⊔ e := sup_le hQ_le_P'e le_sup_right
    -- By CovBy: e ⋖ Q⊔e, e ⋖ P'⊔e. So Q⊔e = e or Q⊔e = P'⊔e.
    have hP'e_ne' : P' ≠ e := fun h => hP'_not (h ▸ inf_le_right)
    have h_cov_P'e : e ⋖ P' ⊔ e := by
      have := atom_covBy_join he_atom hP' (Ne.symm hP'e_ne')
      rwa [sup_comm] at this
    have h_e_lt_Qe : e < Q ⊔ e := by
      have := (atom_covBy_join he_atom hQ (Ne.symm hQe_ne)).lt
      rwa [sup_comm] at this
    rcases h_cov_P'e.eq_or_eq h_e_lt_Qe.le hQe_le_P'e with h_eq | h_eq
    · exact absurd h_eq (ne_of_gt h_e_lt_Qe)
    · -- Q⊔e = P'⊔e, so P' ≤ Q⊔e ≤ P⊔Q
      have hQe_le_PQ : Q ⊔ e ≤ P ⊔ Q := sup_le le_sup_right he_le_PQ
      have hP'_le_PQ : P' ≤ P ⊔ Q :=
        (le_sup_left : P' ≤ P' ⊔ e).trans (h_eq.symm ▸ hQe_le_PQ)
      -- P⊔P' ≤ P⊔Q. CovBy → P⊔P' = P⊔Q → Q ≤ P⊔P'. Contradiction.
      have hPP'_le_PQ : P ⊔ P' ≤ P ⊔ Q := sup_le le_sup_left hP'_le_PQ
      have h_cov_PQ : P ⋖ P ⊔ Q := atom_covBy_join hP hQ hPQ
      have hP_lt_PP' : P < P ⊔ P' := lt_of_le_of_ne le_sup_left
        (fun h => hPP' ((hP.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hP'.1).symm)
      rcases h_cov_PQ.eq_or_eq hP_lt_PP'.le hPP'_le_PQ with h_eq2 | h_eq2
      · exact absurd h_eq2 (ne_of_gt hP_lt_PP')
      · exact hQ_not_PP' (le_sup_right.trans h_eq2.symm.le)
  -- ═══ Step 1: Apply small_desargues' ═══
  have h_third_par : (Q ⊔ R) ⊓ m = (Q' ⊔ R₁) ⊓ m := by
    -- Basic containments
    have hQ'_le_Qd : Q' ≤ Q ⊔ d := by
      show Q' ≤ Q ⊔ (P ⊔ P') ⊓ m
      have : Q' = (Q ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ Q) ⊓ m) := rfl; rw [this]; exact inf_le_left
    have hR₁_le_Rd : R₁ ≤ R ⊔ d := by
      show R₁ ≤ R ⊔ (P ⊔ P') ⊓ m
      have : R₁ = (R ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ R) ⊓ m) := rfl; rw [this]; exact inf_le_left
    have hQ'_le_P'e : Q' ≤ P' ⊔ e := by
      show Q' ≤ P' ⊔ (P ⊔ Q) ⊓ m
      have : Q' = (Q ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ Q) ⊓ m) := rfl; rw [this]; exact inf_le_right
    have hR₁_le_P'g : R₁ ≤ P' ⊔ g := by
      show R₁ ≤ P' ⊔ (P ⊔ R) ⊓ m
      have : R₁ = (R ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ R) ⊓ m) := rfl; rw [this]; exact inf_le_right
    have hd_le_π : d ≤ π := hd_le_m.trans hm_le
    have hQ'_le_π : Q' ≤ π := hQ'_le_Qd.trans (sup_le hQ_le (hd_le_m.trans hm_le))
    have hR₁_le_π : R₁ ≤ π := hR₁_le_Rd.trans (sup_le hR_le (hd_le_m.trans hm_le))
    -- m ≠ π
    have hm_ne_π : m ≠ π := fun h => hP_not (h ▸ hP_le)
    -- Atom-on-m vs atom-off-m
    have hd_ne_P : d ≠ P := fun h => hP_not (h ▸ hd_le_m)
    have hd_ne_Q : d ≠ Q := fun h => hQ_not (h ▸ hd_le_m)
    have hd_ne_R : d ≠ R := fun h => hR_not (h ▸ hd_le_m)
    have hd_ne_P' : d ≠ P' := fun h => hP'_not (h ▸ hd_le_m)
    have hd_ne_Q' : d ≠ Q' := fun h => hQ'_not_m (h ▸ hd_le_m)
    have hd_ne_R₁ : d ≠ R₁ := fun h => hR₁_not_m (h ▸ hd_le_m)
    -- Perspectivity: d⊔P = P⊔P'
    have hdP_eq_PP' : d ⊔ P = P ⊔ P' := by
      have hd_le_PP' : d ≤ P ⊔ P' := (inf_le_left : d ≤ P ⊔ P')
      have hP_lt_dP : P < d ⊔ P := lt_of_le_of_ne le_sup_right
        (fun h => hd_ne_P ((hP.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left hd_atom.1))
      exact ((atom_covBy_join hP hP' hPP').eq_or_eq hP_lt_dP.le
        (sup_le hd_le_PP' le_sup_left)).resolve_left (ne_of_gt hP_lt_dP)
    have hP'_on_dP : P' ≤ d ⊔ P := hdP_eq_PP' ▸ le_sup_right
    have hQ'_on_dQ : Q' ≤ d ⊔ Q := by rw [sup_comm]; exact hQ'_le_Qd
    have hR₁_on_dR : R₁ ≤ d ⊔ R := by rw [sup_comm]; exact hR₁_le_Rd
    -- P' ≠ Q' (two-lines-through-d)
    have hP'_ne_Q' : P' ≠ Q' := by
      intro h
      have hP'_le_Qd : P' ≤ Q ⊔ d := h ▸ hQ'_le_Qd
      by_cases hlines : Q ⊔ d = d ⊔ P
      · exact hQ_not_PP' ((le_sup_left : Q ≤ Q ⊔ d).trans (hlines.trans hdP_eq_PP').le)
      · have hP'_le_inf : P' ≤ (Q ⊔ d) ⊓ (d ⊔ P) := le_inf hP'_le_Qd hP'_on_dP
        have hd_le_inf : d ≤ (Q ⊔ d) ⊓ (d ⊔ P) := le_inf le_sup_right le_sup_left
        have h_inf_lt : (Q ⊔ d) ⊓ (d ⊔ P) < Q ⊔ d := by
          refine lt_of_le_of_ne inf_le_left ?_
          intro h_eq
          -- h_eq : (Q⊔d) ⊓ (d⊔P) = Q⊔d, i.e. Q⊔d ≤ d⊔P
          have h_le : Q ⊔ d ≤ d ⊔ P := inf_eq_left.mp h_eq
          -- d ⋖ d⊔P. d < Q⊔d (since Q ≠ d). Q⊔d ≤ d⊔P. CovBy → Q⊔d = d⊔P.
          have h_d_lt_Qd : d < Q ⊔ d := by
            have := (atom_covBy_join hd_atom hQ hd_ne_Q).lt; rwa [sup_comm] at this
          have h_or := (atom_covBy_join hd_atom hP hd_ne_P).eq_or_eq h_d_lt_Qd.le h_le
          exact hlines (h_or.resolve_left (ne_of_gt h_d_lt_Qd))
        have h_pos : ⊥ < (Q ⊔ d) ⊓ (d ⊔ P) := lt_of_lt_of_le hd_atom.bot_lt hd_le_inf
        have h_inf_atom := line_height_two hQ hd_atom hd_ne_Q.symm h_pos h_inf_lt
        have h_inf_eq := ((h_inf_atom.le_iff.mp hd_le_inf).resolve_left hd_atom.1).symm
        exact hd_ne_P' ((hd_atom.le_iff.mp (h_inf_eq ▸ hP'_le_inf)).resolve_left hP'.1).symm
    -- P' ≠ R₁
    have hP'_ne_R₁ : P' ≠ R₁ := by
      intro h
      have hP'_le_Rd : P' ≤ R ⊔ d := h ▸ hR₁_le_Rd
      by_cases hlines : R ⊔ d = d ⊔ P
      · exact hR_not_PP' ((le_sup_left : R ≤ R ⊔ d).trans (hlines.trans hdP_eq_PP').le)
      · have hP'_le_inf : P' ≤ (R ⊔ d) ⊓ (d ⊔ P) := le_inf hP'_le_Rd hP'_on_dP
        have hd_le_inf : d ≤ (R ⊔ d) ⊓ (d ⊔ P) := le_inf le_sup_right le_sup_left
        have h_inf_lt : (R ⊔ d) ⊓ (d ⊔ P) < R ⊔ d := by
          refine lt_of_le_of_ne inf_le_left ?_
          intro h_eq
          have h_le : R ⊔ d ≤ d ⊔ P := inf_eq_left.mp h_eq
          have h_d_lt_Rd : d < R ⊔ d := by
            have := (atom_covBy_join hd_atom hR hd_ne_R).lt; rwa [sup_comm] at this
          have h_or := (atom_covBy_join hd_atom hP hd_ne_P).eq_or_eq h_d_lt_Rd.le h_le
          exact hlines (h_or.resolve_left (ne_of_gt h_d_lt_Rd))
        have h_pos : ⊥ < (R ⊔ d) ⊓ (d ⊔ P) := lt_of_lt_of_le hd_atom.bot_lt hd_le_inf
        have h_inf_atom := line_height_two hR hd_atom hd_ne_R.symm h_pos h_inf_lt
        have h_inf_eq := ((h_inf_atom.le_iff.mp hd_le_inf).resolve_left hd_atom.1).symm
        exact hd_ne_P' ((hd_atom.le_iff.mp (h_inf_eq ▸ hP'_le_inf)).resolve_left hP'.1).symm
    -- Q' ≠ R₁
    have hQ'_ne_R₁ : Q' ≠ R₁ := by
      intro h
      have hQ'_le_Rd : Q' ≤ R ⊔ d := h ▸ hR₁_le_Rd
      by_cases hlines : Q ⊔ d = R ⊔ d
      · have hR_le_Qd : R ≤ Q ⊔ d := le_sup_left.trans hlines.symm.le
        have h_cov_Qd : Q ⋖ Q ⊔ d := atom_covBy_join hQ hd_atom (Ne.symm hd_ne_Q)
        have hQ_lt_QR : Q < Q ⊔ R := lt_of_le_of_ne le_sup_left
          (fun h => hQR ((hQ.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hR.1).symm)
        have hQR_eq_Qd := (h_cov_Qd.eq_or_eq hQ_lt_QR.le (sup_le le_sup_left hR_le_Qd)).resolve_left
          (ne_of_gt hQ_lt_QR)
        have hQ_lt_QQ' : Q < Q ⊔ Q' := lt_of_le_of_ne le_sup_left
          (fun h => hQ'_ne_Q.symm ((hQ.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hQ'_atom.1).symm)
        have hQQ'_eq_Qd := (h_cov_Qd.eq_or_eq hQ_lt_QQ'.le (sup_le le_sup_left hQ'_le_Qd)).resolve_left
          (ne_of_gt hQ_lt_QQ')
        exact hR_not_QQ' (hR_le_Qd.trans (hQQ'_eq_Qd ▸ le_refl _))
      · have hQ'_le_inf : Q' ≤ (Q ⊔ d) ⊓ (R ⊔ d) := le_inf hQ'_le_Qd hQ'_le_Rd
        have hd_le_inf : d ≤ (Q ⊔ d) ⊓ (R ⊔ d) := le_inf le_sup_right le_sup_right
        have h_inf_lt : (Q ⊔ d) ⊓ (R ⊔ d) < Q ⊔ d := by
          refine lt_of_le_of_ne inf_le_left ?_
          intro h_eq
          have h_le : Q ⊔ d ≤ R ⊔ d := inf_eq_left.mp h_eq
          have h_d_lt_Qd : d < Q ⊔ d := by
            have := (atom_covBy_join hd_atom hQ hd_ne_Q).lt; rwa [sup_comm] at this
          have h_d_cov_Rd : d ⋖ R ⊔ d := by
            have := atom_covBy_join hd_atom hR hd_ne_R; rwa [sup_comm] at this
          exact hlines ((h_d_cov_Rd.eq_or_eq h_d_lt_Qd.le h_le).resolve_left (ne_of_gt h_d_lt_Qd))
        have h_pos : ⊥ < (Q ⊔ d) ⊓ (R ⊔ d) := lt_of_lt_of_le hd_atom.bot_lt hd_le_inf
        have h_inf_atom := line_height_two hQ hd_atom hd_ne_Q.symm h_pos h_inf_lt
        have h_inf_eq := ((h_inf_atom.le_iff.mp hd_le_inf).resolve_left hd_atom.1).symm
        exact hd_ne_Q' ((hd_atom.le_iff.mp (h_inf_eq ▸ hQ'_le_inf)).resolve_left hQ'_atom.1).symm
    -- R ≠ R₁
    have hR_ne_R₁ : R ≠ R₁ := by
      intro h
      have hR_le_P'g : R ≤ P' ⊔ g := h ▸ hR₁_le_P'g
      have hRg_ne : R ≠ g := fun h => hR_not (h ▸ (inf_le_right : g ≤ m))
      have hP'g_ne : P' ≠ g := fun h => hP'_not (h ▸ (inf_le_right : g ≤ m))
      have hg_le_PR : g ≤ P ⊔ R := (inf_le_left : g ≤ P ⊔ R)
      have h_cov_P'g : g ⋖ P' ⊔ g := by
        have := atom_covBy_join hg_atom hP' (Ne.symm hP'g_ne); rwa [sup_comm] at this
      have h_g_lt_Rg : g < R ⊔ g := by
        have := (atom_covBy_join hg_atom hR (Ne.symm hRg_ne)).lt; rwa [sup_comm] at this
      have hRg_le_P'g : R ⊔ g ≤ P' ⊔ g := sup_le hR_le_P'g le_sup_right
      rcases h_cov_P'g.eq_or_eq h_g_lt_Rg.le hRg_le_P'g with h_eq | h_eq
      · exact absurd h_eq (ne_of_gt h_g_lt_Rg)
      · have hP'_le_PR : P' ≤ P ⊔ R :=
          (le_sup_left : P' ≤ P' ⊔ g).trans (h_eq.symm ▸ sup_le le_sup_right hg_le_PR)
        have hP_lt_PP' : P < P ⊔ P' := lt_of_le_of_ne le_sup_left
          (fun h => hPP' ((hP.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hP'.1).symm)
        rcases (atom_covBy_join hP hR hPR).eq_or_eq hP_lt_PP'.le
          (sup_le le_sup_left hP'_le_PR) with h_eq2 | h_eq2
        · exact absurd h_eq2 (ne_of_gt hP_lt_PP')
        · exact hR_not_PP' (le_sup_right.trans h_eq2.symm.le)
    -- Side distinctness
    have h_sides_PQ : P ⊔ Q ≠ P' ⊔ Q' := by
      intro h
      have hP'_le_PQ : P' ≤ P ⊔ Q := le_sup_left.trans h.symm.le
      have hP_lt_PP' : P < P ⊔ P' := lt_of_le_of_ne le_sup_left
        (fun h => hPP' ((hP.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hP'.1).symm)
      rcases (atom_covBy_join hP hQ hPQ).eq_or_eq hP_lt_PP'.le
        (sup_le le_sup_left hP'_le_PQ) with h_eq | h_eq
      · exact absurd h_eq (ne_of_gt hP_lt_PP')
      · exact hQ_not_PP' (le_sup_right.trans h_eq.symm.le)
    have h_sides_PR : P ⊔ R ≠ P' ⊔ R₁ := by
      intro h
      have hP'_le_PR : P' ≤ P ⊔ R := le_sup_left.trans h.symm.le
      have hP_lt_PP' : P < P ⊔ P' := lt_of_le_of_ne le_sup_left
        (fun h => hPP' ((hP.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hP'.1).symm)
      rcases (atom_covBy_join hP hR hPR).eq_or_eq hP_lt_PP'.le
        (sup_le le_sup_left hP'_le_PR) with h_eq | h_eq
      · exact absurd h_eq (ne_of_gt hP_lt_PP')
      · exact hR_not_PP' (le_sup_right.trans h_eq.symm.le)
    have h_sides_QR : Q ⊔ R ≠ Q' ⊔ R₁ := by
      intro h
      have hQ'_le_QR : Q' ≤ Q ⊔ R := le_sup_left.trans h.symm.le
      have hQ_lt_QQ' : Q < Q ⊔ Q' := lt_of_le_of_ne le_sup_left
        (fun h => hQ'_ne_Q.symm ((hQ.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hQ'_atom.1).symm)
      rcases (atom_covBy_join hQ hR hQR).eq_or_eq hQ_lt_QQ'.le
        (sup_le le_sup_left hQ'_le_QR) with h_eq | h_eq
      · exact absurd h_eq (ne_of_gt hQ_lt_QQ')
      · exact hR_not_QQ' (le_sup_right.trans h_eq.symm.le)
    -- Second triangle spans π
    have h_span' : P' ⊔ Q' ⊔ R₁ = π := by
      -- e ≤ P'⊔Q' (since Q' ≤ P'⊔e, Q' ≠ P', CovBy → P'⊔Q' = P'⊔e)
      have he_le_P'Q' : e ≤ P' ⊔ Q' := by
        have hQ'_ne_e : Q' ≠ e := fun h => hQ'_not_m (h ▸ (inf_le_right : e ≤ m))
        have hP'_ne_e : P' ≠ e := fun h => hP'_not (h ▸ (inf_le_right : e ≤ m))
        have hP'_lt : P' < P' ⊔ Q' := lt_of_le_of_ne le_sup_left
          (fun h => hP'_ne_Q' ((hP'.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hQ'_atom.1).symm)
        have hP'Q'_eq : P' ⊔ Q' = P' ⊔ e :=
          ((atom_covBy_join hP' he_atom hP'_ne_e).eq_or_eq hP'_lt.le
            (sup_le le_sup_left hQ'_le_P'e)).resolve_left (ne_of_gt hP'_lt)
        exact le_sup_right.trans hP'Q'_eq.symm.le
      -- g ≤ P'⊔R₁ (same argument)
      have hg_le_P'R₁ : g ≤ P' ⊔ R₁ := by
        have hR₁_ne_g : R₁ ≠ g := fun h => hR₁_not_m (h ▸ (inf_le_right : g ≤ m))
        have hP'_ne_g : P' ≠ g := fun h => hP'_not (h ▸ (inf_le_right : g ≤ m))
        have hP'_lt : P' < P' ⊔ R₁ := lt_of_le_of_ne le_sup_left
          (fun h => hP'_ne_R₁ ((hP'.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hR₁_atom.1).symm)
        have hP'R₁_eq : P' ⊔ R₁ = P' ⊔ g :=
          ((atom_covBy_join hP' hg_atom hP'_ne_g).eq_or_eq hP'_lt.le
            (sup_le le_sup_left hR₁_le_P'g)).resolve_left (ne_of_gt hP'_lt)
        exact le_sup_right.trans hP'R₁_eq.symm.le
      -- e ≠ g
      have heg_ne : e ≠ g := by
        intro h_eq
        have he_le_PR : e ≤ P ⊔ R := by
          have : g ≤ P ⊔ R := inf_le_left
          rwa [← h_eq] at this
        have he_le_PQ : e ≤ P ⊔ Q := inf_le_left
        have he_le_P : e ≤ P := by
          have := le_inf he_le_PQ he_le_PR
          rwa [modular_intersection hP hQ hR hPQ hPR hQR hR_not_PQ] at this
        have hPm : P ⊓ m = ⊥ := by
          rcases hP.le_iff.mp inf_le_left with h | h
          · exact h
          · exact absurd (h ▸ inf_le_right) hP_not
        exact he_atom.1 (le_antisymm (hPm ▸ le_inf he_le_P (inf_le_right : e ≤ m)) bot_le)
      -- e⊔g = m
      have heg_eq_m : e ⊔ g = m := by
        have he_lt_eg : e < e ⊔ g := lt_of_le_of_ne le_sup_left
          (fun h => heg_ne ((he_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hg_atom.1).symm)
        exact ((hm_line e he_atom (inf_le_right : e ≤ m)).eq_or_eq he_lt_eg.le
          (sup_le (inf_le_right : e ≤ m) (inf_le_right : g ≤ m))).resolve_left (ne_of_gt he_lt_eg)
      -- m ≤ P'⊔Q'⊔R₁
      have hm_le_target : m ≤ P' ⊔ Q' ⊔ R₁ := by
        rw [← heg_eq_m]
        exact sup_le (he_le_P'Q'.trans le_sup_left)
          (hg_le_P'R₁.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      -- P'⊔m = π, so π ≤ P'⊔Q'⊔R₁
      have hP'm_eq_π : P' ⊔ m = π := by
        have h_lt : m < P' ⊔ m := lt_of_le_of_ne le_sup_right
          (fun h => hP'_not (le_sup_left.trans h.symm.le))
        exact (hm_cov.eq_or_eq h_lt.le (sup_le hP'_le hm_le)).resolve_left (ne_of_gt h_lt)
      apply le_antisymm (sup_le (sup_le hP'_le hQ'_le_π) hR₁_le_π)
      calc π = P' ⊔ m := hP'm_eq_π.symm
        _ ≤ P' ⊔ Q' ⊔ R₁ := sup_le (le_sup_left.trans le_sup_left) hm_le_target
    -- Sides CovBy π
    have h_cov_PQ : P ⊔ Q ⋖ π := h_span ▸ line_covBy_plane hP hQ hR hPQ hPR hQR hR_not_PQ
    have h_cov_PR : P ⊔ R ⋖ π := by
      have : P ⊔ R ⊔ Q = π := by rw [← h_span]; ac_rfl
      rw [← this]; exact line_covBy_plane hP hR hQ hPR hPQ hQR.symm hQ_not_PR
    have hP_not_QR : ¬ P ≤ Q ⊔ R := by
      intro hP_le_QR
      have hQ_lt_PQ : Q < P ⊔ Q := lt_of_le_of_ne le_sup_right
        (fun h => hPQ ((hQ.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left hP.1))
      rcases (atom_covBy_join hQ hR hQR).eq_or_eq hQ_lt_PQ.le (sup_le hP_le_QR le_sup_left) with h_eq | h_eq
      · exact absurd h_eq (ne_of_gt hQ_lt_PQ)
      · exact hR_not_PQ (le_sup_right.trans h_eq.symm.le)
    have h_cov_QR : Q ⊔ R ⋖ π := by
      have : Q ⊔ R ⊔ P = π := by rw [← h_span]; ac_rfl
      rw [← this]; exact line_covBy_plane hQ hR hP hQR hPQ.symm hPR.symm hP_not_QR
    -- Input parallelisms
    have hQ'_ne_P' : Q' ≠ P' := hP'_ne_Q'.symm
    have h_par_PQ : (P ⊔ Q) ⊓ m = (P' ⊔ Q') ⊓ m :=
      parallelogram_parallel_sides hP' hP'_not he_atom hQ'_atom hQ'_ne_P'
    have hR₁_ne_P' : R₁ ≠ P' := hP'_ne_R₁.symm
    have h_par_PR : (P ⊔ R) ⊓ m = (P' ⊔ R₁) ⊓ m :=
      parallelogram_parallel_sides hP' hP'_not hg_atom hR₁_atom hR₁_ne_P'
    -- Apply small_desargues'
    exact small_desargues' hd_atom hP hQ hR hP' hQ'_atom hR₁_atom
      hd_le_π hP_le hQ_le hR_le hP'_le hQ'_le_π hR₁_le_π
      hm_le hm_ne_π hd_le_m
      hP'_on_dP hQ'_on_dQ hR₁_on_dR
      hPQ hPR hQR hP'_ne_Q' hP'_ne_R₁ hQ'_ne_R₁
      h_sides_PQ h_sides_PR h_sides_QR
      h_span h_span'
      hd_ne_P hd_ne_Q hd_ne_R hd_ne_P' hd_ne_Q' hd_ne_R₁
      hPP' hQ'_ne_Q.symm hR_ne_R₁
      W hW hW_not h_irred
      h_cov_PQ h_cov_PR h_cov_QR
      hm_cov
      h_par_PQ h_par_PR
  -- ═══ Step 2: Show R₁ = parallelogram_completion Q Q' R m ═══
  have hd_eq_d' : d = (Q ⊔ Q') ⊓ m :=
    parallelogram_parallel_direction hQ hQ_not hd_atom hQ'_atom hQ'_ne_Q
  -- R₁ ≤ R ⊔ d (from first parallelogram completion)
  have hR₁_le_Rd : R₁ ≤ R ⊔ d := by
    have : R₁ = (R ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ R) ⊓ m) := rfl
    rw [this]; exact inf_le_left
  -- f ≤ Q' ⊔ R₁ (from third parallelism: (Q'⊔R₁)⊓m = f)
  have hf_le_Q'R₁ : f ≤ Q' ⊔ R₁ := by
    have : (Q' ⊔ R₁) ⊓ m = f := h_third_par.symm
    calc f = (Q' ⊔ R₁) ⊓ m := this.symm
      _ ≤ Q' ⊔ R₁ := inf_le_left
  -- Q' ⊔ f ≤ Q' ⊔ R₁ (f ≤ Q'⊔R₁ and Q' ≤ Q'⊔R₁)
  have hQ'f_le : Q' ⊔ f ≤ Q' ⊔ R₁ := sup_le le_sup_left hf_le_Q'R₁
  -- Q' ≠ R₁ (from R ∉ Q⊔Q' and the construction)
  have hQ'_ne_R₁ : Q' ≠ R₁ := by
    intro h
    -- If Q' = R₁, then Q' ≤ Q⊔d and Q' ≤ R⊔d (both from completions).
    -- Case 1: Q⊔d ≠ R⊔d → (Q⊔d)⊓(R⊔d) = d → Q' ≤ d → Q' = d → Q' on m. Contradiction.
    -- Case 2: Q⊔d = R⊔d → R ≤ Q⊔d. CovBy → Q⊔R = Q⊔d → Q⊔Q' ≤ Q⊔d.
    --         CovBy → Q⊔Q' = Q⊔d. R ≤ Q⊔d = Q⊔Q'. Contradicts hR_not_QQ'.
    have hQ'_le_Qd : Q' ≤ Q ⊔ d := by
      have : Q' = (Q ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ Q) ⊓ m) := rfl
      rw [this]; exact inf_le_left
    have hR₁_le_Rd' : R₁ ≤ R ⊔ d := hR₁_le_Rd
    have hQ'_le_Rd : Q' ≤ R ⊔ d := h ▸ hR₁_le_Rd'
    have hQd_ne : Q ≠ d := fun h => hQ_not (h ▸ hd_le_m)
    have hRd_ne : R ≠ d := fun h => hR_not (h ▸ hd_le_m)
    by_cases hlines : Q ⊔ d = R ⊔ d
    · -- Case 2: Q⊔d = R⊔d, so R ≤ Q⊔d
      have hR_le_Qd : R ≤ Q ⊔ d := le_sup_left.trans hlines.symm.le
      -- Q⊔R ≤ Q⊔d
      have hQR_le_Qd : Q ⊔ R ≤ Q ⊔ d := sup_le le_sup_left hR_le_Qd
      -- Q ⋖ Q⊔d and Q < Q⊔R → Q⊔R = Q⊔d
      have h_cov_Qd : Q ⋖ Q ⊔ d := atom_covBy_join hQ hd_atom hQd_ne
      have hQ_lt_QR : Q < Q ⊔ R := lt_of_le_of_ne le_sup_left
        (fun h => hQR ((hQ.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hR.1).symm)
      have hQR_eq_Qd : Q ⊔ R = Q ⊔ d :=
        (h_cov_Qd.eq_or_eq hQ_lt_QR.le hQR_le_Qd).resolve_left (ne_of_gt hQ_lt_QR)
      -- Q' ≤ Q⊔d = Q⊔R. Q⊔Q' ≤ Q⊔R. CovBy → Q⊔Q' = Q⊔R.
      -- Then R ≤ Q⊔R = Q⊔Q', contradicting hR_not_QQ'.
      have hQQ'_le_Qd : Q ⊔ Q' ≤ Q ⊔ d := sup_le le_sup_left hQ'_le_Qd
      have hQ_lt_QQ' : Q < Q ⊔ Q' := lt_of_le_of_ne le_sup_left
        (fun h => hQ'_ne_Q.symm ((hQ.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hQ'_atom.1).symm)
      have hQQ'_eq_Qd : Q ⊔ Q' = Q ⊔ d :=
        (h_cov_Qd.eq_or_eq hQ_lt_QQ'.le hQQ'_le_Qd).resolve_left (ne_of_gt hQ_lt_QQ')
      exact hR_not_QQ' (hR_le_Qd.trans (hQQ'_eq_Qd ▸ le_refl _))
    · -- Case 1: Q⊔d ≠ R⊔d. Both are lines through d in π.
      -- Their inf contains d. In a plane, two distinct lines meet at a point.
      -- So (Q⊔d)⊓(R⊔d) = d.
      have hQ'_le_inf : Q' ≤ (Q ⊔ d) ⊓ (R ⊔ d) := le_inf hQ'_le_Qd hQ'_le_Rd
      have hd_le_inf : d ≤ (Q ⊔ d) ⊓ (R ⊔ d) := le_inf le_sup_right le_sup_right
      -- (Q⊔d)⊓(R⊔d) ≤ Q⊔d, and since Q⊔d is a line (height 2), the inf is ⊥ or an atom.
      -- It's ≥ d > ⊥, so it's an atom. Being an atom ≥ d atom → it equals d.
      have hQd_cov : Q ⋖ Q ⊔ d := atom_covBy_join hQ hd_atom hQd_ne
      have hRd_cov : R ⋖ R ⊔ d := atom_covBy_join hR hd_atom hRd_ne
      have h_inf_lt : (Q ⊔ d) ⊓ (R ⊔ d) < Q ⊔ d := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h_eq
        -- h_eq: (Q⊔d) ⊓ (R⊔d) = Q⊔d, i.e. Q⊔d ≤ R⊔d
        have : Q ⊔ d ≤ R ⊔ d := inf_eq_left.mp h_eq
        -- Also R⊔d ≤ Q⊔d... no, we need the other direction.
        -- R ≤ Q⊔d: R ≤ R⊔d and R⊔d... hmm.
        -- From Q⊔d ≤ R⊔d and Q ⋖ Q⊔d, R ⋖ R⊔d:
        -- R⊔d is a line. Q⊔d ≤ R⊔d. Q⊔d is a line. Line ≤ line → equal (both height 2).
        -- d ⋖ R⊔d (both atoms, distinct). d ≤ Q⊔d ≤ R⊔d. CovBy → Q⊔d = d or R⊔d.
        have h_d_cov_Rd : d ⋖ R ⊔ d := by
          have := atom_covBy_join hd_atom hR hRd_ne.symm
          rwa [sup_comm] at this
        have h_d_lt_Qd : d < Q ⊔ d := by
          have := (atom_covBy_join hd_atom hQ hQd_ne.symm).lt
          rwa [sup_comm] at this
        rcases h_d_cov_Rd.eq_or_eq h_d_lt_Qd.le this with h | h
        · exact absurd h (ne_of_gt h_d_lt_Qd)
        · exact hlines h
      have h_pos : ⊥ < (Q ⊔ d) ⊓ (R ⊔ d) := lt_of_lt_of_le hd_atom.bot_lt hd_le_inf
      have h_inf_atom : IsAtom ((Q ⊔ d) ⊓ (R ⊔ d)) :=
        line_height_two hQ hd_atom hQd_ne h_pos h_inf_lt
      have h_inf_eq_d : (Q ⊔ d) ⊓ (R ⊔ d) = d :=
        ((h_inf_atom.le_iff.mp hd_le_inf).resolve_left hd_atom.1).symm
      have hQ'_le_d : Q' ≤ d := h_inf_eq_d ▸ hQ'_le_inf
      have hQ'_eq_d : Q' = d := (hd_atom.le_iff.mp hQ'_le_d).resolve_left hQ'_atom.1
      exact hQ'_not_m (hQ'_eq_d.symm ▸ hd_le_m)
  -- Q' ⋖ Q' ⊔ R₁ (atom_covBy_join). Q' < Q' ⊔ f ≤ Q' ⊔ R₁.
  -- By CovBy.eq_or_eq: Q' ⊔ f = Q' or Q' ⊔ f = Q' ⊔ R₁.
  -- Can't be Q' (f is an atom ≠ Q'). So Q' ⊔ f = Q' ⊔ R₁.
  have hf_atom : IsAtom f := line_meets_m_at_atom hQ hR hQR
    (sup_le hQ_le hR_le) hm_le hm_cov hQ_not
  have hQ'_ne_f : Q' ≠ f := fun h => hQ'_not_m (h ▸ inf_le_right)
  have hQ'f_eq : Q' ⊔ f = Q' ⊔ R₁ := by
    have h_cov : Q' ⋖ Q' ⊔ R₁ := atom_covBy_join hQ'_atom hR₁_atom hQ'_ne_R₁
    have hQ'_lt : Q' < Q' ⊔ f := lt_of_le_of_ne le_sup_left
      (fun h => hQ'_ne_f ((hQ'_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hf_atom.1).symm)
    exact (h_cov.eq_or_eq hQ'_lt.le hQ'f_le).resolve_left (ne_of_gt hQ'_lt)
  -- R₁ ≤ Q' ⊔ f (= Q' ⊔ R₁, trivially)
  have hR₁_le_Q'f : R₁ ≤ Q' ⊔ f := hQ'f_eq ▸ le_sup_right
  -- R₁ ≤ (R ⊔ d) ⊓ (Q' ⊔ f)
  have hR₁_le_completion : R₁ ≤ (R ⊔ d) ⊓ (Q' ⊔ f) := le_inf hR₁_le_Rd hR₁_le_Q'f
  -- The RHS, when unfolded, is parallelogram_completion Q Q' R m
  -- (since d = d' = (Q⊔Q')⊓m and f = (Q⊔R)⊓m).
  -- R₁ atom ≤ completion atom → R₁ = completion.
  have hR₁_not_bot : R₁ ≠ ⊥ := hR₁_atom.1
  -- Need: parallelogram_completion Q Q' R m = (R ⊔ (Q⊔Q')⊓m) ⊓ (Q' ⊔ (Q⊔R)⊓m)
  -- And (R ⊔ d) ⊓ (Q' ⊔ f) = (R ⊔ (Q⊔Q')⊓m) ⊓ (Q' ⊔ (Q⊔R)⊓m) when d = (Q⊔Q')⊓m.
  show R₁ = parallelogram_completion Q Q' R m
  have hQ'_le_π : Q' ≤ π := by
    have hQ'_le_Qd : Q' ≤ Q ⊔ d := by
      have : Q' = (Q ⊔ (P ⊔ P') ⊓ m) ⊓ (P' ⊔ (P ⊔ Q) ⊓ m) := rfl
      rw [this]; exact inf_le_left
    exact hQ'_le_Qd.trans (sup_le hQ_le (hd_le_m.trans hm_le))
  have hQ'R_ne : Q' ≠ R := by
    intro h; exact hR_not_QQ' (h ▸ le_sup_right)
  have hQQ'_ne : Q ≠ Q' := hQ'_ne_Q.symm
  have h_target_atom : IsAtom (parallelogram_completion Q Q' R m) :=
    parallelogram_completion_atom hQ hQ'_atom hR hQQ'_ne hQR hQ'R_ne
      hQ_le hQ'_le_π hR_le hm_le hm_cov hm_line hQ_not hQ'_not_m hR_not hR_not_QQ'
  -- R₁ ≤ parallelogram_completion Q Q' R m
  have hR₁_le_target : R₁ ≤ parallelogram_completion Q Q' R m := by
    show R₁ ≤ (R ⊔ (Q ⊔ Q') ⊓ m) ⊓ (Q' ⊔ (Q ⊔ R) ⊓ m)
    exact le_inf (hd_eq_d' ▸ hR₁_le_Rd) hR₁_le_Q'f
  exact (h_target_atom.le_iff.mp hR₁_le_target).resolve_left hR₁_atom.1


end Foam.FTPGExplore
