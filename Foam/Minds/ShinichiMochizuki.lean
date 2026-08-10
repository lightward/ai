import Foam
import Foam.Certificate
import Foam.Contact
import Foam.Ledger
import Foam.Portal
import Foam.Square
import Foam.Trilemma

namespace Foam.Minds.ShinichiMochizuki

theorem mono_anabelian_transport :
    (∀ (A : Type) (x y : List A), indist (orderStage A) x y → x = y)
      ∧ ∀ (S : Stage) (s : S.State),
          ∃ r : S.Probe → S.Ans, ∀ q, r q = S.obs s q :=
  ⟨fun _ _ _ h => h (),
   fun S s => a_state_answers_every_probe S s⟩

theorem mutually_alien_copies :
    (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
        (s, n) ≠ (s, m) ∧ indist (dress S) (s, n) (s, m))
      ∧ ∀ (D : Type) (S : Stage) (s : S.State) (d d' : D),
          indist (contact S D) (s, d) (s, d') :=
  ⟨fun S s n m h => the_remainder_is_real S s n m h,
   fun _ S s d d' => the_other_stays_unimagined S s d d'⟩

theorem the_theta_link :
    (∀ a b : Nat, sq (a * b) = sq a * sq b)
      ∧ sq (1 + 1) ≠ sq 1 + sq 1
      ∧ ∀ a b : Nat, sq (a + b) ≤ 2 * (sq a + sq b) :=
  ⟨the_square_carries_the_product, the_square_breaks_the_sum,
   the_broken_sum_is_priced⟩

def multiradiality := @Foam.the_blind_reading_factors

theorem the_indeterminacies :
    (¬ Blind graded)
      ∧ (∀ l s j k : Nat, j ≤ l → graded (s, j) ≤ (l + 1) * graded (s, k))
      ∧ ∀ l s : Nat, graded (s, l) = (l + 1) * graded (s, 0) :=
  ⟨the_graded_reading_parts_the_copies,
   every_copy_reads_within_the_spread,
   the_spread_is_attained⟩

/-- info: 'Foam.Minds.ShinichiMochizuki.mono_anabelian_transport' does not depend on any axioms -/
#guard_msgs in #print axioms mono_anabelian_transport

/-- info: 'Foam.Minds.ShinichiMochizuki.mutually_alien_copies' does not depend on any axioms -/
#guard_msgs in #print axioms mutually_alien_copies

/-- info: 'Foam.Minds.ShinichiMochizuki.the_theta_link' does not depend on any axioms -/
#guard_msgs in #print axioms the_theta_link

/-- info: 'Foam.Minds.ShinichiMochizuki.multiradiality' does not depend on any axioms -/
#guard_msgs in #print axioms multiradiality

/-- info: 'Foam.Minds.ShinichiMochizuki.the_indeterminacies' does not depend on any axioms -/
#guard_msgs in #print axioms the_indeterminacies

end Foam.Minds.ShinichiMochizuki
