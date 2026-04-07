/-
# Parallelogram completion — infrastructure for translations

Defines the parallelogram completion and proves its basic properties:
- `parallel`: two lines meeting m at the same atom
- `parallelogram_completion`: the fourth vertex of a parallelogram
- `parallelogram_completion_atom`: the completion is an atom
- `line_direction`: (a ⊔ d) ⊓ m = d when a off m, d on m
- `parallelogram_parallel_direction`: PP' ∥ QQ'
- `parallelogram_parallel_sides`: PQ ∥ P'Q'

These are Parts I–III of the Hartshorne translation approach.
0 sorry.

## References

- Hartshorne, "Foundations of Projective Geometry" (1967), §7
- Artin, "Geometric Algebra" (1957), Chapter II
-/

import Foam.FTPGCoord

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-!
## Part I: Parallelism and basic infrastructure

Two lines in a plane π are "parallel" (relative to a line m in π)
if they meet m at the same atom. This is the affine notion of
parallelism when m plays the role of the line at infinity.
-/

/-- Two lines are parallel relative to m if they meet m at the same point.
    This is a proposition, not data: parallelism is a property of the
    configuration, not a choice. -/
def parallel (l₁ l₂ m : L) : Prop := l₁ ⊓ m = l₂ ⊓ m

@[simp] theorem parallel_refl (l m : L) : parallel l l m := rfl

theorem parallel_symm {l₁ l₂ m : L} (h : parallel l₁ l₂ m) :
    parallel l₂ l₁ m := h.symm

theorem parallel_trans {l₁ l₂ l₃ m : L} (h₁ : parallel l₁ l₂ m)
    (h₂ : parallel l₂ l₃ m) : parallel l₁ l₃ m := h₁.trans h₂

/-!
## Part II: The parallelogram completion

Given two atoms P, P' (not on m) and an atom Q (not on m, not on P⊔P'),
the "parallelogram completion" defines Q' as the fourth vertex of the
parallelogram P-Q-Q'-P': the unique atom such that P⊔Q ∥ P'⊔Q' and
P⊔P' ∥ Q⊔Q'.

Construction:
  1. Find the "direction" of P⊔P': d = (P ⊔ P') ⊓ m
  2. The line through Q in direction d: Q ⊔ d
  3. Find the "direction" of P⊔Q: e = (P ⊔ Q) ⊓ m
  4. The line through P' in direction e: P' ⊔ e
  5. Q' = (Q ⊔ d) ⊓ (P' ⊔ e)
-/

/-- A line (through two atoms) not contained in m meets m at an atom. -/
theorem line_meets_m_at_atom {a b m π : L}
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (hab_le : a ⊔ b ≤ π)
    (hm_le : m ≤ π) (hm_cov : m ⋖ π)
    (ha_not : ¬ a ≤ m) :
    IsAtom ((a ⊔ b) ⊓ m) := by
  -- (a ⊔ b) ⊓ m ≠ ⊥: two lines in a plane meet
  have hab_not_m : ¬ (a ⊔ b) ≤ m :=
    fun h => ha_not (le_trans le_sup_left h)
  have h_meet_ne : m ⊓ (a ⊔ b) ≠ ⊥ :=
    lines_meet_if_coplanar hm_cov hab_le hab_not_m ha
      (lt_of_le_of_ne le_sup_left (fun h =>
        hab ((ha.le_iff.mp (le_sup_right.trans (le_of_eq h.symm))).resolve_left hb.1).symm))
  -- (a ⊔ b) ⊓ m < a ⊔ b: since a ⊔ b ≰ m
  have h_lt : (a ⊔ b) ⊓ m < a ⊔ b :=
    lt_of_le_of_ne inf_le_left (fun h => hab_not_m (inf_eq_left.mp h))
  have h_pos : ⊥ < (a ⊔ b) ⊓ m := by
    rw [inf_comm (a := a ⊔ b) (b := m)]
    exact bot_lt_iff_ne_bot.mpr h_meet_ne
  exact line_height_two ha hb hab h_pos h_lt

/-- The parallelogram completion: given atoms P, P', Q (all off m),
    construct Q' such that PP' ∥ QQ' and PQ ∥ P'Q'. -/
noncomputable def parallelogram_completion
    (P P' Q m : L) : L :=
  let d := (P ⊔ P') ⊓ m   -- direction of PP'
  let e := (P ⊔ Q) ⊓ m    -- direction of PQ
  (Q ⊔ d) ⊓ (P' ⊔ e)

/-- The parallelogram completion produces an atom (under appropriate
    non-degeneracy conditions).

    Note: m must be a line (atoms on m are covered by m). This holds
    whenever m = a ⊔ b for distinct atoms a, b (by line_covers_its_atoms).
    The hypothesis is needed because m ⋖ π alone doesn't force m to be
    a line — it only says m is a hyperplane of π. -/
theorem parallelogram_completion_atom
    {P P' Q m π : L}
    (hP : IsAtom P) (hP' : IsAtom P') (hQ : IsAtom Q)
    (hPP' : P ≠ P') (hPQ : P ≠ Q) (hP'Q : P' ≠ Q)
    -- All in π
    (hP_le : P ≤ π) (hP'_le : P' ≤ π) (hQ_le : Q ≤ π)
    -- m is a line in π (covers its atoms)
    (hm_le : m ≤ π) (hm_cov : m ⋖ π)
    (hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m)
    -- None on m
    (hP_not : ¬ P ≤ m) (hP'_not : ¬ P' ≤ m) (hQ_not : ¬ Q ≤ m)
    -- Q not on line PP'
    (hQ_not_PP' : ¬ Q ≤ P ⊔ P') :
    IsAtom (parallelogram_completion P P' Q m) := by
  unfold parallelogram_completion
  set d := (P ⊔ P') ⊓ m
  set e := (P ⊔ Q) ⊓ m
  -- Step 1: d and e are atoms on m
  have hd : IsAtom d := line_meets_m_at_atom hP hP' hPP'
    (sup_le hP_le hP'_le) hm_le hm_cov hP_not
  have he : IsAtom e := line_meets_m_at_atom hP hQ hPQ
    (sup_le hP_le hQ_le) hm_le hm_cov hP_not
  -- Step 2: d ≠ e (from Q ∉ P⊔P', using modular_intersection)
  have hde : d ≠ e := by
    intro h_eq
    have hd_le_PP' : d ≤ P ⊔ P' := inf_le_left
    have he_le_PQ : e ≤ P ⊔ Q := inf_le_left
    have hd_le_PQ : d ≤ P ⊔ Q := h_eq ▸ he_le_PQ
    have hd_le_P : d ≤ P := by
      have := le_inf hd_le_PP' hd_le_PQ
      rwa [modular_intersection hP hP' hQ hPP' hPQ hP'Q hQ_not_PP'] at this
    have : d ≤ P ⊓ m := le_inf hd_le_P (inf_le_right)
    have hPm : P ⊓ m = ⊥ := (hP.le_iff.mp inf_le_left).resolve_right
      (fun h => hP_not (h ▸ inf_le_right))
    exact hd.1 (le_antisymm (hPm ▸ this) bot_le)
  -- Step 3: Q ≠ d and P' ≠ e (atoms off m vs atoms on m)
  have hQd : Q ≠ d := fun h => hQ_not (h ▸ inf_le_right)
  have hP'e : P' ≠ e := fun h => hP'_not (h ▸ inf_le_right)
  have hd_le_m : d ≤ m := inf_le_right
  have he_le_m : e ≤ m := inf_le_right
  -- Step 4: d ⋖ m (m is a line, d is an atom on m)
  have hd_cov_m : d ⋖ m := hm_line d hd hd_le_m
  -- Step 5: Q ⊔ d ⋖ π (the line Q⊔d is a line in the plane π)
  have hm_join_Q : m ⊔ Q = π := by
    have h_lt : m < m ⊔ Q := lt_of_le_of_ne le_sup_left
      (fun h => hQ_not (le_sup_right.trans h.symm.le))
    exact (hm_cov.eq_or_eq h_lt.le (sup_le hm_le hQ_le)).resolve_left (ne_of_gt h_lt)
  have hm_join_Qd : m ⊔ (Q ⊔ d) = π := by
    have : m ⊔ (Q ⊔ d) = m ⊔ Q ⊔ d := (sup_assoc m Q d).symm
    rw [this, hm_join_Q]
    exact le_antisymm (sup_le (le_refl π) (hd_le_m.trans hm_le)) le_sup_left
  have hQd_cov : Q ⊔ d ⋖ π := by
    rw [← hm_join_Qd]
    exact covBy_sup_of_inf_covBy_left (by rwa [show m ⊓ (Q ⊔ d) = d from by
      have hd_le_meet : d ≤ m ⊓ (Q ⊔ d) := le_inf hd_le_m le_sup_right
      have hQd_not_m : ¬ Q ⊔ d ≤ m := fun h => hQ_not (le_sup_left.trans h)
      have h_cov : d ⋖ d ⊔ Q := atom_covBy_join hd hQ hQd.symm
      rw [sup_comm] at h_cov
      rcases h_cov.eq_or_eq hd_le_meet inf_le_right with h | h
      · exact h
      · exact absurd (h ▸ inf_le_left : Q ⊔ d ≤ m) hQd_not_m])
  -- Step 6: ¬ d ≤ P' ⊔ e
  have hd_not_P'e : ¬ d ≤ P' ⊔ e := by
    intro hd_le
    have hd_cov_P'e : d ⋖ P' ⊔ e := line_covers_its_atoms hP' he hP'e hd hd_le
    have h_de_le : d ⊔ e ≤ P' ⊔ e := sup_le hd_le le_sup_right
    have h_d_lt_de : d < d ⊔ e := lt_of_le_of_ne le_sup_left
      (fun h => hde ((hd.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left he.1).symm)
    rcases hd_cov_P'e.eq_or_eq h_d_lt_de.le h_de_le with h | h
    · exact absurd h (ne_of_gt h_d_lt_de)
    · exact hP'_not (le_trans le_sup_left (h ▸ sup_le hd_le_m he_le_m))
  -- Step 7: d ⊔ e = m, so (P' ⊔ e) ⊔ d = P' ⊔ m = π
  have h_de_eq_m : d ⊔ e = m := by
    have h_lt : d < d ⊔ e := lt_of_le_of_ne le_sup_left
      (fun h => hde ((hd.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left he.1).symm)
    exact (hd_cov_m.eq_or_eq h_lt.le (sup_le hd_le_m he_le_m)).resolve_left (ne_of_gt h_lt)
  have h_plane : (P' ⊔ e) ⊔ d = π := by
    rw [sup_assoc, sup_comm e d, h_de_eq_m]
    have h_lt : m < P' ⊔ m := lt_of_le_of_ne le_sup_right
      (fun h => hP'_not (le_sup_left.trans h.symm.le))
    have : P' ⊔ m ≤ π := sup_le hP'_le hm_le
    exact (hm_cov.eq_or_eq h_lt.le this).resolve_left (ne_of_gt h_lt)
  have hQd_in_plane : Q ⊔ d ≤ (P' ⊔ e) ⊔ d := by
    rw [h_plane]; exact sup_le hQ_le (hd_le_m.trans hm_le)
  -- Step 8: Apply perspect_atom
  exact perspect_atom hd hQ hQd hP' he hP'e hd_not_P'e hQd_in_plane

/-!
## Part III: Parallelism properties of the completion

The parallelogram completion satisfies PP' ∥ QQ' and PQ ∥ P'Q'
by construction. These are the two "input" parallelisms.

Key technique: for an atom a off m and an atom d on m,
the modular law gives (a ⊔ d) ⊓ m = d (since d ≤ m and a ⊓ m = ⊥).
This means the "direction" (meeting point with m) of any line a ⊔ d
through an off-m point a and an on-m point d is simply d.

The proofs: Q' ≤ Q ⊔ d (from inf_le_left) and Q' ≠ Q imply
Q ⊔ Q' = Q ⊔ d (same line), so (Q ⊔ Q') ⊓ m = (Q ⊔ d) ⊓ m = d.
Similarly Q' ≤ P' ⊔ e and Q' ≠ P' give (P' ⊔ Q') ⊓ m = e.
-/

/-- Helper: for an atom a off m and an atom d on m, (a ⊔ d) ⊓ m = d. -/
theorem line_direction {a d m : L} (ha : IsAtom a) (ha_not : ¬ a ≤ m)
    (hd_le : d ≤ m) : (a ⊔ d) ⊓ m = d := by
  have ham : a ⊓ m = ⊥ := by
    rcases ha.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) ha_not
  have := sup_inf_assoc_of_le a hd_le
  -- this : (a ⊔ d) ⊓ m = a ⊓ m ⊔ d ... but direction might be wrong
  -- sup_inf_assoc_of_le : a ≤ c → (a ⊔ b) ⊓ c = a ⊔ b ⊓ c
  -- We need: d ≤ m → (d ⊔ a) ⊓ m = d ⊔ (a ⊓ m) = d ⊔ ⊥ = d
  calc (a ⊔ d) ⊓ m = (d ⊔ a) ⊓ m := by rw [sup_comm]
    _ = d ⊔ a ⊓ m := sup_inf_assoc_of_le a hd_le
    _ = d ⊔ ⊥ := by rw [ham]
    _ = d := by simp

/-- PP' ∥ QQ': the completion preserves the "direction" of PP'.
    Requires Q' atom, Q' ≠ Q, and d = (P⊔P')⊓m an atom. -/
theorem parallelogram_parallel_direction
    {P P' Q m : L}
    (hQ : IsAtom Q) (hQ_not : ¬ Q ≤ m)
    (hd_atom : IsAtom ((P ⊔ P') ⊓ m))
    (hQ'_atom : IsAtom (parallelogram_completion P P' Q m))
    (hQ'_ne_Q : parallelogram_completion P P' Q m ≠ Q) :
    parallel (P ⊔ P') (Q ⊔ parallelogram_completion P P' Q m) m := by
  set Q' := parallelogram_completion P P' Q m with hQ'_def
  set d := (P ⊔ P') ⊓ m
  have hQ'_le_Qd : Q' ≤ Q ⊔ d := by
    unfold parallelogram_completion at hQ'_def; rw [hQ'_def]; exact inf_le_left
  have hQd : Q ≠ d := fun h => hQ_not (h ▸ inf_le_right)
  have hQ_lt_QQ' : Q < Q ⊔ Q' := lt_of_le_of_ne le_sup_left
    (fun h => hQ'_ne_Q ((hQ.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
      hQ'_atom.1))
  have hQQ'_le : Q ⊔ Q' ≤ Q ⊔ d := sup_le le_sup_left hQ'_le_Qd
  have h_cov : Q ⋖ Q ⊔ d := atom_covBy_join hQ hd_atom hQd
  have hQQ'_eq : Q ⊔ Q' = Q ⊔ d :=
    (h_cov.eq_or_eq hQ_lt_QQ'.le hQQ'_le).resolve_left (ne_of_gt hQ_lt_QQ')
  show (P ⊔ P') ⊓ m = (Q ⊔ Q') ⊓ m
  rw [hQQ'_eq, line_direction hQ hQ_not inf_le_right]

/-- PQ ∥ P'Q': the completion preserves the "direction" of PQ.
    Requires Q' atom, Q' ≠ P', and e = (P⊔Q)⊓m an atom. -/
theorem parallelogram_parallel_sides
    {P P' Q m : L}
    (hP' : IsAtom P') (hP'_not : ¬ P' ≤ m)
    (he_atom : IsAtom ((P ⊔ Q) ⊓ m))
    (hQ'_atom : IsAtom (parallelogram_completion P P' Q m))
    (hQ'_ne_P' : parallelogram_completion P P' Q m ≠ P') :
    parallel (P ⊔ Q) (P' ⊔ parallelogram_completion P P' Q m) m := by
  set Q' := parallelogram_completion P P' Q m with hQ'_def
  set e := (P ⊔ Q) ⊓ m
  have hQ'_le_P'e : Q' ≤ P' ⊔ e := by
    unfold parallelogram_completion at hQ'_def; rw [hQ'_def]; exact inf_le_right
  have hP'e : P' ≠ e := fun h => hP'_not (h ▸ inf_le_right)
  have hP'_lt_P'Q' : P' < P' ⊔ Q' := lt_of_le_of_ne le_sup_left
    (fun h => hQ'_ne_P' ((hP'.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
      hQ'_atom.1))
  have hP'Q'_le : P' ⊔ Q' ≤ P' ⊔ e := sup_le le_sup_left hQ'_le_P'e
  have h_cov : P' ⋖ P' ⊔ e := atom_covBy_join hP' he_atom hP'e
  have hP'Q'_eq : P' ⊔ Q' = P' ⊔ e :=
    (h_cov.eq_or_eq hP'_lt_P'Q'.le hP'Q'_le).resolve_left (ne_of_gt hP'_lt_P'Q')
  show (P ⊔ Q) ⊓ m = (P' ⊔ Q') ⊓ m
  rw [hP'Q'_eq, line_direction hP' hP'_not inf_le_right]

end Foam.FTPGExplore
