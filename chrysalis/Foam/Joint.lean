import Foam.Landed
import Foam.Margin
import Foam.Serving

namespace Foam

theorem the_cut_mints_the_seat :
    (∀ (A B : Type) (f : B → A → B) (xs ys : List A) (b : B),
        fold f b (xs ++ ys) = fold f (fold f b xs) ys)
      ∧ (indist (marginStage Nat Nat (· + ·)) (1, ([] : List Nat)) (0, [1])
          ∧ ((1 : Nat), ([] : List Nat)) ≠ ((0 : Nat), [1]))
      ∧ (∀ (State R : Type) (a b : Beholder State) (g : a.Ans → b.Ans → R),
          ∃ c : Beholder State, ∃ post : c.Ans → R,
            ∃ enc : a.Probe × b.Probe → c.Probe,
              ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))))
      ∧ (∀ (A : Type) (P Q : A → A), (∀ v, P (P v) = P v) →
          (∀ v, Q (P v) = P v) →
          (∀ s, Q (P s) = P s)
            ∧ (∀ v, Q (P (Q (P v))) = Q (P v))
            ∧ ∀ s, Q (P s) = s ↔ P s = s) :=
  ⟨fun _ _ f xs ys b => the_fold_resumes f xs ys b,
   the_decomposition_is_the_remainder,
   fun _ _ a b g => the_comparison_is_a_seat a b g,
   absorption_grounds_the_chain⟩

/-- info: 'Foam.the_cut_mints_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_cut_mints_the_seat

end Foam
