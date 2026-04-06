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
    non-degeneracy conditions). -/
theorem parallelogram_completion_atom
    {P P' Q m π : L}
    (hP : IsAtom P) (hP' : IsAtom P') (hQ : IsAtom Q)
    (hPP' : P ≠ P') (hPQ : P ≠ Q) (hP'Q : P' ≠ Q)
    -- All in π
    (hP_le : P ≤ π) (hP'_le : P' ≤ π) (hQ_le : Q ≤ π)
    -- m is a line in π
    (hm_le : m ≤ π) (hm_cov : m ⋖ π)
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
    -- d = e means (P⊔P')⊓m = (P⊔Q)⊓m. Both d,e ≤ P⊔P' and P⊔Q resp.
    -- d ≤ (P⊔P') ⊓ (P⊔Q) = P (by modular_intersection, since Q ∉ P⊔P')
    have hd_le_PP' : d ≤ P ⊔ P' := inf_le_left
    have he_le_PQ : e ≤ P ⊔ Q := inf_le_left
    have hd_le_PQ : d ≤ P ⊔ Q := h_eq ▸ he_le_PQ
    have hd_le_P : d ≤ P := by
      have := le_inf hd_le_PP' hd_le_PQ
      rwa [modular_intersection hP hP' hQ hPP' hPQ hP'Q hQ_not_PP'] at this
    -- d ≤ P and d ≤ m, but P ∉ m, so d ≤ P ⊓ m = ⊥
    have : d ≤ P ⊓ m := le_inf hd_le_P (inf_le_right)
    have hPm : P ⊓ m = ⊥ := (hP.le_iff.mp inf_le_left).resolve_right
      (fun h => hP_not (h ▸ inf_le_right))
    exact hd.1 (le_antisymm (hPm ▸ this) bot_le)
  -- Step 3: Q ≠ d and P' ≠ e (atoms off m vs atoms on m)
  have hQd : Q ≠ d := fun h => hQ_not (h ▸ inf_le_right)
  have hP'e : P' ≠ e := fun h => hP'_not (h ▸ inf_le_right)
  -- Step 4: d ∉ P'⊔e (if d,e both on P'⊔e then m ≤ P'⊔e, forcing P' ∈ m ✗)
  -- Step 5: coplanarity (both lines in π = P'⊔m ≤ P'⊔e⊔d)
  -- Step 6: perspect_atom gives the result
  -- Proof sketch is clear; individual steps are lattice-routine.
  exact perspect_atom hd hQ hQd hP' he hP'e (by
    intro hd_le
    have : d ⊔ e ≤ P' ⊔ e := sup_le hd_le le_sup_right
    have : d ⊔ e ≤ m := sup_le inf_le_right inf_le_right
    sorry -- d⊔e = m, so m ≤ P'⊔e, so P'⊔e = m, so P' ≤ m ✗
  ) (by
    suffices Q ⊔ d ≤ π by
      sorry -- π = P'⊔m ≤ P'⊔e⊔d
    exact sup_le hQ_le (inf_le_right.trans hm_le)
  )

/-!
## Part III: Parallelism properties of the completion

The parallelogram completion satisfies PP' ∥ QQ' and PQ ∥ P'Q'
by construction. These are the two "input" parallelisms.
-/

/-- PP' ∥ QQ': the completion preserves the "direction" of PP'. -/
theorem parallelogram_parallel_direction
    {P P' Q m : L}
    (hP : IsAtom P) (hP' : IsAtom P') (hQ : IsAtom Q)
    (hP_not : ¬ P ≤ m) (hP'_not : ¬ P' ≤ m) (hQ_not : ¬ Q ≤ m) :
    let Q' := parallelogram_completion P P' Q m
    parallel (P ⊔ P') (Q ⊔ Q') m := by
  -- By construction: Q' = (Q ⊔ d) ⊓ (P' ⊔ e) where d = (P⊔P')⊓m.
  -- Q' ≤ Q ⊔ d, so Q ⊔ Q' ≤ Q ⊔ d.
  -- (Q ⊔ d) ⊓ m ≥ d = (P ⊔ P') ⊓ m.
  -- So (Q ⊔ Q') ⊓ m ≥ (P ⊔ P') ⊓ m... but need equality.
  sorry

/-- PQ ∥ P'Q': the completion preserves the "direction" of PQ. -/
theorem parallelogram_parallel_sides
    {P P' Q m : L}
    (hP : IsAtom P) (hP' : IsAtom P') (hQ : IsAtom Q)
    (hP_not : ¬ P ≤ m) (hP'_not : ¬ P' ≤ m) (hQ_not : ¬ Q ≤ m) :
    let Q' := parallelogram_completion P P' Q m
    parallel (P ⊔ Q) (P' ⊔ Q') m := by
  sorry

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

-- The well-definedness theorem will go here.
-- It will invoke small_desargues' to show that the parallelogram
-- completion is independent of the choice of base pair.

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
