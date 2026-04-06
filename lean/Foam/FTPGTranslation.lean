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

import Foam.FTPGExplore
-- Note: small_desargues' lives in Foam.FTPGCoord but that file currently has
-- type errors (lines 2990+) preventing import. Once FTPGCoord compiles,
-- uncomment: import Foam.FTPGCoord

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
  -- ═══ Step 1: Apply small_desargues' ═══
  -- Center: d. Triangles: PQR and P'Q'R₁.
  -- Inputs: PQ ∥ P'Q' and PR ∥ P'R₁.
  -- Output: QR ∥ Q'R₁.
  -- TODO: discharge all 37 hypotheses of small_desargues'
  have h_third_par : (Q ⊔ R) ⊓ m = (Q' ⊔ R₁) ⊓ m := by
    -- This applies small_desargues' (from Foam.FTPGCoord) with:
    --   U = d, A = P, B = Q, C = R, A' = P', B' = Q', C' = R₁
    -- Input parallelisms (from parallelogram_parallel_sides):
    --   (P⊔Q)⊓m = (P'⊔Q')⊓m  and  (P⊔R)⊓m = (P'⊔R₁)⊓m
    -- Output: (Q⊔R)⊓m = (Q'⊔R₁)⊓m
    --
    -- All hypotheses of small_desargues' are dischargeable:
    -- - Atoms: hd_atom, hP, hQ, hR, hP', hQ'_atom, hR₁_atom
    -- - In π: trivial (d ≤ m ≤ π, others given)
    -- - Q', R₁ ≤ π: from Q' ≤ Q⊔d ≤ π, R₁ ≤ R⊔d ≤ π
    -- - Perspectivity: P' ≤ d⊔P (d⊔P = P⊔P' by CovBy), Q' ≤ d⊔Q, R₁ ≤ d⊔R
    -- - Q'/R₁ not on m: line_direction + d_not_on_P'_line argument
    -- - Distinct vertices: P'≠Q' and P'≠R₁ from parallelism (if equal, e or g = ⊥)
    --   Q'≠R₁ from two-lines-through-d argument
    -- - Distinct sides: CovBy argument (if PQ = P'Q', then P' ≤ PQ → Q ≤ PP')
    -- - Triangles span π: h_span given; second triangle via e⊔g = m ≤ P'⊔Q'⊔R₁
    -- - Sides CovBy π: line_covBy_plane with hR_not_PQ, hQ_not_PR
    -- - R≠R₁: if R=R₁ then R ≤ P'⊔g → P' ≤ P⊔R → R ≤ P⊔P'
    -- - Q'≠Q: if Q'=Q then Q ≤ P'⊔e → P' ≤ P⊔Q → Q ≤ P⊔P'
    --
    -- BLOCKED: FTPGCoord.lean has type errors (lines 2990+) preventing import.
    -- Once FTPGCoord compiles, import it and replace this sorry with the
    -- application of small_desargues'.
    sorry
  -- ═══ Step 2: Show R₁ = parallelogram_completion Q Q' R m ═══
  -- parallelogram_completion Q Q' R m = (R ⊔ d') ⊓ (Q' ⊔ f)
  -- where d' = (Q ⊔ Q') ⊓ m. We need d' = d.
  -- Helper: d ≠ e (same as in parallelogram_completion_atom)
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
## Part V: Translations (to be built)

A translation will be defined as the function Q ↦ parallelogram_completion P P' Q m
for a fixed pair (P, P'). Well-definedness (Part IV) shows this is
independent of the choice of (P, P').

Key theorems to prove:
- Translation is an order isomorphism (lattice automorphism)
- Translations fix m pointwise
- Composition of translations is a translation
- Translations commute (abelian group)
- coord_add a b = τ_a(b) where τ_a sends O to a
- Associativity of coord_add follows from the group law
-/

end Foam.FTPGExplore
