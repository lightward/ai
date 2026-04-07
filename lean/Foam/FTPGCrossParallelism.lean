/-
# Cross-parallelism — translations preserve directions (Part IV-B)

A single translation preserves the "direction" of any line connecting
two points it acts on.

- `cross_parallelism`: (P⊔Q)⊓m = (P'⊔Q')⊓m

## Status

Pre-existing type errors in this section (from session 48).
These need to be resolved but do not affect Parts I–III or Part V.
-/

import Foam.FTPGWellDefined

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-!
## Part IV-B: Cross-parallelism (translations preserve parallelism)

A single translation preserves the "direction" of any line connecting
two points it acts on. This is the individual-level structural property
from which composition (and hence associativity) follows.

Statement: if P' = pc(P₀, P₀', P, m) and Q' = pc(P₀, P₀', Q, m),
then (P⊔Q)⊓m = (P'⊔Q')⊓m.

Proof: one application of small_desargues' with center d = (P₀⊔P₀')⊓m.
The triangles (P₀, P, Q) and (P₀', P', Q') are perspective from d
(since P₀⊔P₀', P⊔P', Q⊔Q' all have direction d on m).
The two input parallelisms come from the parallelogram sides:
  (P₀⊔P)⊓m = (P₀'⊔P')⊓m  and  (P₀⊔Q)⊓m = (P₀'⊔Q')⊓m.
The conclusion is the third parallelism: (P⊔Q)⊓m = (P'⊔Q')⊓m.
-/

/-- **Cross-parallelism: a translation preserves directions.**

    If P' and Q' are the images of P and Q under the translation
    defined by (P₀, P₀'), then PQ ∥ P'Q' (relative to m).

    This is the key individual-level property: each translation,
    on its own, preserves the structure of the plane. From this,
    composition of translations is a translation, and associativity
    of coord_add follows. -/
theorem cross_parallelism
    {P₀ P₀' P Q m π : L}
    (hP₀ : IsAtom P₀) (hP₀' : IsAtom P₀') (hP : IsAtom P) (hQ : IsAtom Q)
    (hP₀P₀' : P₀ ≠ P₀') (hP₀P : P₀ ≠ P) (hP₀Q : P₀ ≠ Q) (hPQ : P ≠ Q)
    (hP₀'_ne_P' : P₀' ≠ parallelogram_completion P₀ P₀' P m)
    (hP₀'_ne_Q' : P₀' ≠ parallelogram_completion P₀ P₀' Q m)
    (hP'_ne_Q' : parallelogram_completion P₀ P₀' P m ≠
                  parallelogram_completion P₀ P₀' Q m)
    -- All in π
    (hP₀_le : P₀ ≤ π) (hP₀'_le : P₀' ≤ π) (hP_le : P ≤ π) (hQ_le : Q ≤ π)
    -- m is a line in π
    (hm_le : m ≤ π) (hm_cov : m ⋖ π)
    (hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m)
    -- None on m
    (hP₀_not : ¬ P₀ ≤ m) (hP₀'_not : ¬ P₀' ≤ m) (hP_not : ¬ P ≤ m) (hQ_not : ¬ Q ≤ m)
    -- Non-collinearity
    (hP_not_PP' : ¬ P ≤ P₀ ⊔ P₀') (hQ_not_PP' : ¬ Q ≤ P₀ ⊔ P₀')
    (hQ_not_P₀P : ¬ Q ≤ P₀ ⊔ P)
    -- Spanning
    (h_span : P₀ ⊔ P ⊔ Q = π)
    -- Height ≥ 4 and irreducibility
    (W : L) (hW : IsAtom W) (hW_not : ¬ W ≤ π)
    (h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b) :
    (P ⊔ Q) ⊓ m = (parallelogram_completion P₀ P₀' P m ⊔
                     parallelogram_completion P₀ P₀' Q m) ⊓ m := by
  set d := (P₀ ⊔ P₀') ⊓ m
  set e_P := (P₀ ⊔ P) ⊓ m
  set e_Q := (P₀ ⊔ Q) ⊓ m
  set P' := parallelogram_completion P₀ P₀' P m
  set Q' := parallelogram_completion P₀ P₀' Q m
  -- ═══ Step 0: Basic atoms ═══
  have hd_atom : IsAtom d := line_meets_m_at_atom hP₀ hP₀' hP₀P₀'
    (sup_le hP₀_le hP₀'_le) hm_le hm_cov hP₀_not
  have he_P_atom : IsAtom e_P := line_meets_m_at_atom hP₀ hP hP₀P
    (sup_le hP₀_le hP_le) hm_le hm_cov hP₀_not
  have he_Q_atom : IsAtom e_Q := line_meets_m_at_atom hP₀ hQ hP₀Q
    (sup_le hP₀_le hQ_le) hm_le hm_cov hP₀_not
  have hP'_atom : IsAtom P' := parallelogram_completion_atom hP₀ hP₀' hP hP₀P₀' hP₀P
    (fun h => hP_not_PP' (h ▸ le_sup_right)) hP₀_le hP₀'_le hP_le hm_le hm_cov hm_line
    hP₀_not hP₀'_not hP_not hP_not_PP'
  have hQ'_atom : IsAtom Q' := parallelogram_completion_atom hP₀ hP₀' hQ hP₀P₀' hP₀Q
    (fun h => hQ_not_PP' (h ▸ le_sup_right)) hP₀_le hP₀'_le hQ_le hm_le hm_cov hm_line
    hP₀_not hP₀'_not hQ_not hQ_not_PP'
  have hd_le_m : d ≤ m := inf_le_right
  -- ═══ Step 1: Perspectivity from d ═══
  -- P₀' is on d ⊔ P₀ (= P₀ ⊔ P₀') since d ≤ P₀⊔P₀'
  have hP₀'_on_dP₀ : P₀' ≤ d ⊔ P₀ := by
    rw [sup_comm]; exact le_sup_right
  -- P' is on d ⊔ P (= P ⊔ P') since P⊔P' = P⊔d (covering argument)
  have hP'_on_dP : P' ≤ d ⊔ P := by
    have hP'_le_Pd : P' ≤ P ⊔ d := by
      have : P' ≤ P ⊔ (P₀ ⊔ P₀') ⊓ m := inf_le_left
      exact this
    rw [sup_comm]; exact hP'_le_Pd
  -- Q' is on d ⊔ Q (same argument)
  have hQ'_on_dQ : Q' ≤ d ⊔ Q := by
    have hQ'_le_Qd : Q' ≤ Q ⊔ d := by
      have : Q' ≤ Q ⊔ (P₀ ⊔ P₀') ⊓ m := inf_le_left
      exact this
    rw [sup_comm]; exact hQ'_le_Qd
  -- ═══ Step 2: Input parallelisms ═══
  have hP'_not_m : ¬ P' ≤ m := by
    intro h
    have hP'_le_Pd : P' ≤ P ⊔ d := by
      have : P' ≤ P ⊔ (P₀ ⊔ P₀') ⊓ m := inf_le_left; exact this
    have hP'_le_d : P' ≤ d := by
      calc P' ≤ (P ⊔ d) ⊓ m := le_inf hP'_le_Pd h
        _ = d := line_direction hP hP_not hd_le_m
    have hP'_eq_d : P' = d := (hd_atom.le_iff.mp hP'_le_d).resolve_left hP'_atom.1
    -- P' ≤ P₀'⊔e_P, so d ≤ P₀'⊔e_P. But d on m, P₀' off m, e_P on m...
    -- If d = e_P, then P ≤ P₀⊔P₀' (from modular argument). Contradiction.
    -- If d ≠ e_P, then d⊔e_P = m, and P₀' ≤ d⊔e_P = m. Contradiction.
    have hP'_le_P₀'e : P' ≤ P₀' ⊔ e_P := by
      have : P' ≤ P₀' ⊔ (P₀ ⊔ P) ⊓ m := inf_le_right; exact this
    have hd_le_P₀'e : d ≤ P₀' ⊔ e_P := hP'_eq_d ▸ hP'_le_P₀'e
    have hde_ne : d ≠ e_P := by
      intro h_eq
      have hd_le_P₀P : d ≤ P₀ ⊔ P := h_eq ▸ (inf_le_left : e_P ≤ P₀ ⊔ P)
      have hd_le_P₀ : d ≤ P₀ := by
        have := le_inf (inf_le_left : d ≤ P₀ ⊔ P₀') hd_le_P₀P
        rwa [modular_intersection hP₀ hP₀' hP hP₀P₀' hP₀P
          (fun h => hP_not_PP' (h ▸ le_sup_right)) hP_not_PP'] at this
      have hP₀m : P₀ ⊓ m = ⊥ := by
        rcases hP₀.le_iff.mp inf_le_left with h | h
        · exact h
        · exact absurd (h ▸ inf_le_right) hP₀_not
      exact hd_atom.1 (le_antisymm (hP₀m ▸ le_inf hd_le_P₀ hd_le_m) bot_le)
    have hP₀'_ne_eP : P₀' ≠ e_P := fun h => hP₀'_not (h ▸ inf_le_right)
    have h_eP_lt : e_P < P₀' ⊔ e_P := by
      have := (atom_covBy_join he_P_atom hP₀' (Ne.symm hP₀'_ne_eP)).lt
      rwa [sup_comm] at this
    have hd_lt_de : d < d ⊔ e_P := lt_of_le_of_ne le_sup_left
      (fun h => hde_ne ((hd_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        he_P_atom.1).symm)
    have hde_le : d ⊔ e_P ≤ P₀' ⊔ e_P := sup_le hd_le_P₀'e le_sup_right
    have h_cov : e_P ⋖ P₀' ⊔ e_P := by
      have := atom_covBy_join he_P_atom hP₀' (Ne.symm hP₀'_ne_eP)
      rwa [sup_comm] at this
    rcases h_cov.eq_or_eq hd_lt_de.le hde_le with h_eq | h_eq
    · exact absurd h_eq (ne_of_gt hd_lt_de)
    · exact hP₀'_not (le_trans le_sup_left (h_eq ▸ sup_le hd_le_m (inf_le_right : e_P ≤ m)))
  have hQ'_not_m : ¬ Q' ≤ m := by
    intro h
    have hQ'_le_Qd : Q' ≤ Q ⊔ d := by
      have : Q' ≤ Q ⊔ (P₀ ⊔ P₀') ⊓ m := inf_le_left; exact this
    have hQ'_le_d : Q' ≤ d := by
      calc Q' ≤ (Q ⊔ d) ⊓ m := le_inf hQ'_le_Qd h
        _ = d := line_direction hQ hQ_not hd_le_m
    have hQ'_eq_d : Q' = d := (hd_atom.le_iff.mp hQ'_le_d).resolve_left hQ'_atom.1
    have hQ'_le_P₀'e : Q' ≤ P₀' ⊔ e_Q := by
      have : Q' ≤ P₀' ⊔ (P₀ ⊔ Q) ⊓ m := inf_le_right; exact this
    have hd_le_P₀'e : d ≤ P₀' ⊔ e_Q := hQ'_eq_d ▸ hQ'_le_P₀'e
    have hde_ne : d ≠ e_Q := by
      intro h_eq
      have hd_le_P₀Q : d ≤ P₀ ⊔ Q := h_eq ▸ (inf_le_left : e_Q ≤ P₀ ⊔ Q)
      have hd_le_P₀ : d ≤ P₀ := by
        have := le_inf (inf_le_left : d ≤ P₀ ⊔ P₀') hd_le_P₀Q
        rwa [modular_intersection hP₀ hP₀' hQ hP₀P₀' hP₀Q
          (fun h => hQ_not_PP' (h ▸ le_sup_right)) hQ_not_PP'] at this
      have hP₀m : P₀ ⊓ m = ⊥ := by
        rcases hP₀.le_iff.mp inf_le_left with h | h
        · exact h
        · exact absurd (h ▸ inf_le_right) hP₀_not
      exact hd_atom.1 (le_antisymm (hP₀m ▸ le_inf hd_le_P₀ hd_le_m) bot_le)
    have hP₀'_ne_eQ : P₀' ≠ e_Q := fun h => hP₀'_not (h ▸ inf_le_right)
    have hd_lt_de : d < d ⊔ e_Q := lt_of_le_of_ne le_sup_left
      (fun h => hde_ne ((hd_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        he_Q_atom.1).symm)
    have hde_le : d ⊔ e_Q ≤ P₀' ⊔ e_Q := sup_le hd_le_P₀'e le_sup_right
    have h_cov : e_Q ⋖ P₀' ⊔ e_Q := by
      have := atom_covBy_join he_Q_atom hP₀' (Ne.symm hP₀'_ne_eQ)
      rwa [sup_comm] at this
    rcases h_cov.eq_or_eq hd_lt_de.le hde_le with h_eq | h_eq
    · exact absurd h_eq (ne_of_gt hd_lt_de)
    · exact hP₀'_not (le_trans le_sup_left (h_eq ▸ sup_le hd_le_m (inf_le_right : e_Q ≤ m)))
  -- Input parallelism 1: (P₀⊔P)⊓m = (P₀'⊔P')⊓m
  have hP'_ne_P₀' : P' ≠ P₀' := hP₀'_ne_P'.symm
  have h_par_1 : (P₀ ⊔ P) ⊓ m = (P₀' ⊔ P') ⊓ m :=
    parallelogram_parallel_sides hP₀' hP₀'_not he_P_atom hP'_atom hP'_ne_P₀'
  -- Input parallelism 2: (P₀⊔Q)⊓m = (P₀'⊔Q')⊓m
  have hQ'_ne_P₀' : Q' ≠ P₀' := hP₀'_ne_Q'.symm
  have h_par_2 : (P₀ ⊔ Q) ⊓ m = (P₀' ⊔ Q') ⊓ m :=
    parallelogram_parallel_sides hP₀' hP₀'_not he_Q_atom hQ'_atom hQ'_ne_P₀'
  -- ═══ Step 3: Non-degeneracy for small_desargues' ═══
  have hP'_le_π : P' ≤ π := by
    calc P' ≤ P ⊔ d := by
            have : P' ≤ P ⊔ (P₀ ⊔ P₀') ⊓ m := inf_le_left; exact this
      _ ≤ π := sup_le hP_le (hd_le_m.trans hm_le)
  have hQ'_le_π : Q' ≤ π := by
    calc Q' ≤ Q ⊔ d := by
            have : Q' ≤ Q ⊔ (P₀ ⊔ P₀') ⊓ m := inf_le_left; exact this
      _ ≤ π := sup_le hQ_le (hd_le_m.trans hm_le)
  have hd_le_π : d ≤ π := hd_le_m.trans hm_le
  have hm_ne_π : m ≠ π := fun h => hP₀_not (h ▸ hP₀_le)
  -- d ≠ each vertex
  have hd_ne_P₀ : d ≠ P₀ := fun h => hP₀_not (h ▸ hd_le_m)
  have hd_ne_P : d ≠ P := fun h => hP_not (h ▸ hd_le_m)
  have hd_ne_Q : d ≠ Q := fun h => hQ_not (h ▸ hd_le_m)
  have hd_ne_P₀' : d ≠ P₀' := fun h => hP₀'_not (h ▸ hd_le_m)
  have hd_ne_P' : d ≠ P' := fun h => hP'_not_m (h ▸ hd_le_m)
  have hd_ne_Q' : d ≠ Q' := fun h => hQ'_not_m (h ▸ hd_le_m)
  -- Corresponding vertices distinct
  have hP₀_ne_P₀' : P₀ ≠ P₀' := hP₀P₀'
  have hP_ne_P' : P ≠ P' := by
    intro h
    have hP_le_P₀'e : P ≤ P₀' ⊔ e_P := by
      have : P' ≤ P₀' ⊔ (P₀ ⊔ P) ⊓ m := inf_le_right
      exact h ▸ this
    have hP_le_P₀P : P ≤ P₀ ⊔ P := le_sup_right
    have he_P_le_P₀P : e_P ≤ P₀ ⊔ P := inf_le_left
    -- P₀' ⊔ e_P ≤ P₀' ⊔ (P₀ ⊔ P) = some plane. If P ≤ P₀'⊔e_P, covering gives P₀'⊔e_P = P₀⊔P
    -- or P = e_P or P = P₀'. Both impossible.
    by_cases h_lines : P₀' ⊔ e_P = P₀ ⊔ P
    · exact hP_not_PP' (le_sup_right.trans (by
        rw [show P₀ ⊔ P = P₀' ⊔ e_P from h_lines.symm]
        exact sup_le le_sup_left (inf_le_left.trans (sup_le le_sup_left le_sup_right))))
    · -- P ≤ P₀⊔P and P ≤ P₀'⊔e_P, and these are distinct lines.
      -- Their intersection is an atom. e_P is also in both. So P = e_P → P on m. ✗
      have hP_le_inf : P ≤ (P₀ ⊔ P) ⊓ (P₀' ⊔ e_P) := le_inf le_sup_right hP_le_P₀'e
      have heP_le_inf : e_P ≤ (P₀ ⊔ P) ⊓ (P₀' ⊔ e_P) := le_inf he_P_le_P₀P le_sup_right
      have h_inf_lt : (P₀ ⊔ P) ⊓ (P₀' ⊔ e_P) < P₀ ⊔ P := by
        exact lt_of_le_of_ne inf_le_left (fun h_eq => h_lines
          ((inf_eq_left.mp h_eq).antisymm
            (sup_le (le_sup_left.trans (inf_eq_left.mp h_eq).le)
              (he_P_le_P₀P.trans inf_le_left))).symm)
      have h_pos : ⊥ < (P₀ ⊔ P) ⊓ (P₀' ⊔ e_P) := lt_of_lt_of_le hP.bot_lt hP_le_inf
      have h_inf_atom := line_height_two hP₀ hP hP₀P h_pos h_inf_lt
      have hP_eq := (h_inf_atom.le_iff.mp hP_le_inf).resolve_left hP.1
      have heP_eq := (h_inf_atom.le_iff.mp heP_le_inf).resolve_left he_P_atom.1
      exact hP_not (hP_eq.trans heP_eq.symm ▸ inf_le_right)
  have hQ_ne_Q' : Q ≠ Q' := by
    intro h
    have hQ_le_P₀'e : Q ≤ P₀' ⊔ e_Q := by
      have : Q' ≤ P₀' ⊔ (P₀ ⊔ Q) ⊓ m := inf_le_right
      exact h ▸ this
    by_cases h_lines : P₀' ⊔ e_Q = P₀ ⊔ Q
    · exact hQ_not_PP' (le_sup_right.trans (by
        rw [show P₀ ⊔ Q = P₀' ⊔ e_Q from h_lines.symm]
        exact sup_le le_sup_left (inf_le_left.trans (sup_le le_sup_left le_sup_right))))
    · have heQ_le_P₀Q : e_Q ≤ P₀ ⊔ Q := inf_le_left
      have hQ_le_inf : Q ≤ (P₀ ⊔ Q) ⊓ (P₀' ⊔ e_Q) := le_inf le_sup_right hQ_le_P₀'e
      have heQ_le_inf : e_Q ≤ (P₀ ⊔ Q) ⊓ (P₀' ⊔ e_Q) := le_inf heQ_le_P₀Q le_sup_right
      have h_inf_lt : (P₀ ⊔ Q) ⊓ (P₀' ⊔ e_Q) < P₀ ⊔ Q := by
        exact lt_of_le_of_ne inf_le_left (fun h_eq => h_lines
          ((inf_eq_left.mp h_eq).antisymm
            (sup_le (le_sup_left.trans (inf_eq_left.mp h_eq).le)
              (heQ_le_P₀Q.trans inf_le_left))).symm)
      have h_pos : ⊥ < (P₀ ⊔ Q) ⊓ (P₀' ⊔ e_Q) := lt_of_lt_of_le hQ.bot_lt hQ_le_inf
      have h_inf_atom := line_height_two hP₀ hQ hP₀Q h_pos h_inf_lt
      have hQ_eq := (h_inf_atom.le_iff.mp hQ_le_inf).resolve_left hQ.1
      have heQ_eq := (h_inf_atom.le_iff.mp heQ_le_inf).resolve_left he_Q_atom.1
      exact hQ_not (hQ_eq.trans heQ_eq.symm ▸ inf_le_right)
  -- Side distinctness
  have h_sides_P₀P : P₀ ⊔ P ≠ P₀' ⊔ P' := by
    intro h
    have hP₀'_le : P₀' ≤ P₀ ⊔ P := le_sup_left.trans h.symm.le
    have hP₀_lt : P₀ < P₀ ⊔ P := lt_of_le_of_ne le_sup_left
      (fun h => hP₀P ((hP₀.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hP.1).symm)
    rcases (atom_covBy_join hP₀ hP₀' hP₀P₀').eq_or_eq hP₀_lt.le
      (sup_le hP₀'_le le_sup_left) with h_eq | h_eq
    · exact absurd h_eq (ne_of_gt hP₀_lt)
    · exact hP_not_PP' (le_sup_right.trans h_eq.symm.le)
  have h_sides_P₀Q : P₀ ⊔ Q ≠ P₀' ⊔ Q' := by
    intro h
    have hP₀'_le : P₀' ≤ P₀ ⊔ Q := le_sup_left.trans h.symm.le
    have hP₀_lt : P₀ < P₀ ⊔ Q := lt_of_le_of_ne le_sup_left
      (fun h => hP₀Q ((hP₀.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hQ.1).symm)
    rcases (atom_covBy_join hP₀ hP₀' hP₀P₀').eq_or_eq hP₀_lt.le
      (sup_le hP₀'_le le_sup_left) with h_eq | h_eq
    · exact absurd h_eq (ne_of_gt hP₀_lt)
    · exact hQ_not_PP' (le_sup_right.trans h_eq.symm.le)
  -- Handle the degenerate case P⊔Q = P'⊔Q' directly (conclusion is trivial)
  by_cases h_sides_PQ : P ⊔ Q = P' ⊔ Q'
  · exact congr_arg (· ⊓ m) h_sides_PQ
  -- P₀ ≠ Q (have hP₀Q)
  -- P₀' ≠ P' (have hP₀'_ne_P')
  -- P₀' ≠ Q' (have hP₀'_ne_Q')
  -- Spanning: P₀ ⊔ P ⊔ Q = π (have h_span)
  -- Second triangle spans π
  have h_span' : P₀' ⊔ P' ⊔ Q' = π := by
    -- e_P ≤ P₀'⊔P' (from the sides parallelism)
    have he_P_le : e_P ≤ P₀' ⊔ P' := by
      have hP'_le_P₀'e : P' ≤ P₀' ⊔ e_P := inf_le_right
      have hP₀'_lt : P₀' < P₀' ⊔ P' := lt_of_le_of_ne le_sup_left
        (fun h => hP₀'_ne_P' ((hP₀'.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hP'_atom.1).symm)
      have h_eq := ((atom_covBy_join hP₀' he_P_atom
        (fun h => hP₀'_not (h ▸ inf_le_right))).eq_or_eq hP₀'_lt.le
        (sup_le le_sup_left hP'_le_P₀'e)).resolve_left (ne_of_gt hP₀'_lt)
      exact le_sup_right.trans h_eq.symm.le
    have he_Q_le : e_Q ≤ P₀' ⊔ Q' := by
      have hQ'_le_P₀'e : Q' ≤ P₀' ⊔ e_Q := inf_le_right
      have hP₀'_lt : P₀' < P₀' ⊔ Q' := lt_of_le_of_ne le_sup_left
        (fun h => hP₀'_ne_Q' ((hP₀'.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hQ'_atom.1).symm)
      have h_eq := ((atom_covBy_join hP₀' he_Q_atom
        (fun h => hP₀'_not (h ▸ inf_le_right))).eq_or_eq hP₀'_lt.le
        (sup_le le_sup_left hQ'_le_P₀'e)).resolve_left (ne_of_gt hP₀'_lt)
      exact le_sup_right.trans h_eq.symm.le
    -- e_P ≠ e_Q (from Q not on P₀⊔P)
    have hePeQ : e_P ≠ e_Q := by
      intro h_eq
      have heP_le_P₀Q : e_P ≤ P₀ ⊔ Q := h_eq ▸ (inf_le_left : e_Q ≤ P₀ ⊔ Q)
      have heP_le_P₀ : e_P ≤ P₀ := by
        have := le_inf (inf_le_left : e_P ≤ P₀ ⊔ P) heP_le_P₀Q
        rwa [modular_intersection hP₀ hP hQ hP₀P hP₀Q hPQ hQ_not_P₀P] at this
      have hP₀m : P₀ ⊓ m = ⊥ := by
        rcases hP₀.le_iff.mp inf_le_left with h | h
        · exact h; · exact absurd (h ▸ inf_le_right) hP₀_not
      exact he_P_atom.1 (le_antisymm (hP₀m ▸ le_inf heP_le_P₀ (inf_le_right : e_P ≤ m)) bot_le)
    -- e_P ⊔ e_Q = m
    have hePeQ_eq_m : e_P ⊔ e_Q = m := by
      have heP_lt : e_P < e_P ⊔ e_Q := lt_of_le_of_ne le_sup_left
        (fun h => hePeQ ((he_P_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          he_Q_atom.1).symm)
      exact ((hm_line e_P he_P_atom (inf_le_right : e_P ≤ m)).eq_or_eq heP_lt.le
        (sup_le (inf_le_right : e_P ≤ m) (inf_le_right : e_Q ≤ m))).resolve_left
        (ne_of_gt heP_lt)
    -- m ≤ P₀'⊔P'⊔Q'
    have hm_le_target : m ≤ P₀' ⊔ P' ⊔ Q' := by
      rw [← hePeQ_eq_m]
      exact sup_le (he_P_le.trans le_sup_left)
        (he_Q_le.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
    have hP₀'m_eq_π : P₀' ⊔ m = π := by
      have h_lt : m < P₀' ⊔ m := lt_of_le_of_ne le_sup_right
        (fun h => hP₀'_not (le_sup_left.trans h.symm.le))
      exact (hm_cov.eq_or_eq h_lt.le (sup_le hP₀'_le hm_le)).resolve_left (ne_of_gt h_lt)
    apply le_antisymm (sup_le (sup_le hP₀'_le hP'_le_π) hQ'_le_π)
    calc π = P₀' ⊔ m := hP₀'m_eq_π.symm
      _ ≤ P₀' ⊔ P' ⊔ Q' := sup_le (le_sup_left.trans le_sup_left) hm_le_target
  -- Sides CovBy π
  have hP_not_P₀Q : ¬ P ≤ P₀ ⊔ Q := by
    intro hP_le_P₀Q
    have hP₀_lt_P₀P : P₀ < P₀ ⊔ P := lt_of_le_of_ne le_sup_left
      (fun h => hP₀P ((hP₀.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hP.1).symm)
    rcases (atom_covBy_join hP₀ hQ hP₀Q).eq_or_eq hP₀_lt_P₀P.le
      (sup_le le_sup_left hP_le_P₀Q) with h | h
    · exact absurd h (ne_of_gt hP₀_lt_P₀P)
    · exact hQ_not_P₀P (le_sup_right.trans h.symm.le)
  have h_cov_P₀P : P₀ ⊔ P ⋖ π := h_span ▸ line_covBy_plane hP₀ hP hQ hP₀P hP₀Q hPQ hQ_not_P₀P
  have h_cov_P₀Q : P₀ ⊔ Q ⋖ π := by
    have : P₀ ⊔ Q ⊔ P = π := by rw [← h_span]; ac_rfl
    rw [← this]; exact line_covBy_plane hP₀ hQ hP hP₀Q hP₀P hPQ.symm hP_not_P₀Q
  have h_cov_PQ : P ⊔ Q ⋖ π := by
    have : P ⊔ Q ⊔ P₀ = π := by rw [← h_span]; ac_rfl
    rw [← this]
    have hP₀_not_PQ : ¬ P₀ ≤ P ⊔ Q := by
      intro hP₀_le
      have hP_lt : P < P ⊔ Q := lt_of_le_of_ne le_sup_left
        (fun h => hPQ ((hP.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hQ.1).symm)
      rcases (atom_covBy_join hP hP₀ hP₀P.symm).eq_or_eq hP_lt.le
        (sup_le le_sup_left hP₀_le) with h | h
      · exact absurd h (ne_of_gt hP_lt)
      · exact hQ_not_P₀P (le_sup_right.trans h.symm.le)
    exact line_covBy_plane hP hQ hP₀ hPQ hP₀P.symm hP₀Q.symm hP₀_not_PQ
  -- ═══ Step 4: Apply small_desargues' ═══
  exact small_desargues' hd_atom hP₀ hP hQ hP₀' hP'_atom hQ'_atom
    hd_le_π hP₀_le hP_le hQ_le hP₀'_le hP'_le_π hQ'_le_π
    hm_le hm_ne_π hd_le_m
    hP₀'_on_dP₀ hP'_on_dP hQ'_on_dQ
    hP₀P hP₀Q hPQ hP₀'_ne_P' hP₀'_ne_Q' hP'_ne_Q'
    h_sides_P₀P h_sides_P₀Q h_sides_PQ
    h_span h_span'
    hd_ne_P₀ hd_ne_P hd_ne_Q hd_ne_P₀' hd_ne_P' hd_ne_Q'
    hP₀_ne_P₀' hP_ne_P' hQ_ne_Q'
    W hW hW_not h_irred
    h_cov_P₀P h_cov_P₀Q h_cov_PQ
    hm_cov
    h_par_1 h_par_2


end Foam.FTPGExplore
