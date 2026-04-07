/-
# Translations — The Hartshorne approach to associativity

Rather than proving coord_add_assoc by diagram-chasing (which requires
the "parallel return centers" lemma and 4+ atoms per line), we follow
Hartshorne's "Foundations of Projective Geometry" §7:

1. Define translations as lattice automorphisms fixing m pointwise
2. Prove existence/uniqueness from small_desargues'
3. Prove translations form an abelian group
4. Show coord_add a b = τ_a(b)
5. Associativity falls out from the group law

## Why this works

A translation is a global symmetry of the plane. The von Staudt
addition computes a *local* construction that happens to equal
"apply the translation." By proving the global structure first
(translations form an abelian group), we get associativity for free.

The key advantage: small_desargues' is used for well-definedness
(the parallelogram completion doesn't depend on choices), not for
algebraic identities. The algebra falls out from the group structure.

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
  have hm_cov : m ⋖ π := atom_covBy_join Γ.hU Γ.hV hUV
  have hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m := fun x hx hle =>
    line_covers_its_atoms Γ.hU Γ.hV hUV hx hle

  -- ═══ C_b facts ═══
  have hCb_atom : IsAtom C_b :=
    parallelogram_completion_atom Γ.hO hb Γ.hC
      (fun h => hb_ne_O (h ▸ rfl).symm |>.elim)
      hOC (fun h => Γ.hC_not_l (h ▸ hb_on))
      (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) Γ.hC_plane
      (le_sup_right.trans le_sup_left) hm_cov hm_line
      Γ.hO_not_m hb_not_m Γ.hC_not_m
      (fun h => Γ.hC_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
  have hCb_le_bE : C_b ≤ b ⊔ Γ.E := (inf_le_right : C_b ≤ b ⊔ (Γ.O ⊔ Γ.C) ⊓ m)
  have hCb_le_q : C_b ≤ q := by
    have : C_b ≤ Γ.C ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
    rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this
    exact this.trans (sup_comm Γ.C Γ.U ▸ le_refl q)
  have hb_ne_Cb : b ≠ C_b := by
    intro h; exact hb_not_m (Γ.atom_on_both_eq_U hb hb_on (h ▸ hCb_le_q |>.trans
      sorry) ▸ le_sup_left) -- need q ≤ m... no, this is wrong. b on l, C_b on q. b = C_b → b ≤ q → b ≤ l⊓q = U.
  have hCb_not_m : ¬ C_b ≤ m := by
    sorry -- standard: if C_b on m then C_b ≤ q⊓m = U, C_b atom → C_b = U, but C_b ≠ U

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
    sorry -- THE KEY SORRY: cross-parallelism application via general-position G

  -- ═══ Step 4: Conclude τ_a(C_b) = C_s ═══
  -- s = coord_add a b is an atom on l
  have hs_atom : IsAtom s := by sorry -- coord_add produces atoms (perspect_atom)
  have hs_on_l : s ≤ l := by sorry -- coord_add lands on l (from the definition)
  have hτ_atom : IsAtom τ_a_C_b := by sorry -- parallelogram_completion_atom
  have hCs_atom : IsAtom C_s := by sorry -- parallelogram_completion_atom

  -- E ≤ s ⊔ τ_a_C_b (from h_cross)
  have hE_le : Γ.E ≤ s ⊔ τ_a_C_b := h_cross ▸ inf_le_left
  -- s ⊔ E ≤ s ⊔ τ_a_C_b
  have hsE_le_sτ : s ⊔ Γ.E ≤ s ⊔ τ_a_C_b := sup_le le_sup_left hE_le
  -- s ≠ τ (s on l, τ on q, l⊓q = U, s ≠ U)
  have hs_ne_τ : s ≠ τ_a_C_b := by
    intro h; exact sorry -- s on l, τ on q → s ≤ l⊓q = U → s = U
  -- CovBy: s ⋖ s⊔τ. s⊔E ≤ s⊔τ. So s⊔E = s⊔τ. Then τ ≤ s⊔E.
  have hs_ne_E : s ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hs_on_l)
  have h_sE_eq_sτ : s ⊔ Γ.E = s ⊔ τ_a_C_b := by
    have h_lt : s < s ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hs_ne_E ((hs_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    exact ((atom_covBy_join hs_atom hτ_atom hs_ne_τ).eq_or_eq h_lt.le
      hsE_le_sτ).resolve_left (ne_of_gt h_lt)
  have h_τ_le_sE : τ_a_C_b ≤ s ⊔ Γ.E := h_sE_eq_sτ ▸ le_sup_right

  -- τ_a(C_b) ≤ C_s = q ⊓ (s ⊔ E)
  have h_τ_le_Cs : τ_a_C_b ≤ C_s := by
    show τ_a_C_b ≤ (Γ.C ⊔ (Γ.O ⊔ s) ⊓ m) ⊓ (s ⊔ (Γ.O ⊔ Γ.C) ⊓ m)
    have hOs_eq_l : Γ.O ⊔ s = l := by
      have h_lt : Γ.O < Γ.O ⊔ s := lt_of_le_of_ne le_sup_left
        (fun h => sorry) -- s ≠ O
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left hs_on_l)).resolve_left (ne_of_gt h_lt)
    rw [hOs_eq_l, Γ.l_inf_m_eq_U, sup_comm Γ.C Γ.U]
    exact le_inf h_τ_le_q h_τ_le_sE
  -- Both atoms → equal
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
