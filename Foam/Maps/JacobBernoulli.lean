import Foam
import Foam.Census
import Foam.Concentration
import Foam.Expectation
import Foam.Ledger
import Foam.Seat
import Foam.Source

namespace Foam.Maps.JacobBernoulli

def eadem_mutata_resurgo := @Foam.the_remainder_is_real

theorem the_trials_are_deaf_to_their_order {A : Type} [DecidableEq A]
    (a b : A) (hab : a ≠ b) :
    Licensed (countStage A) List.Perm
      ∧ (recorder A).state [a, b] ≠ (recorder A).state [b, a]
      ∧ indist (countStage A) [a, b] [b, a] :=
  ⟨counting_is_licensed_by_permutation A,
   a_seat_reads_the_order_the_census_cannot a b hab⟩

def the_whole_book_balances := @Foam.the_complete_book_balances

theorem the_terms_trade_up_to_the_lean :
    (∀ n k : Nat, classCount n k * (n - k) = classCount n (k + 1) * (k + 1))
      ∧ ∀ t f n k : Nat, k < n → (k + 1) * (t + f) ≤ (n + 1) * t →
        classCount n k * (t ^ k * f ^ (n - k))
          ≤ classCount n (k + 1) * (t ^ (k + 1) * f ^ (n - (k + 1))) :=
  ⟨the_census_absorbs, the_census_rises_to_the_lean⟩

theorem what_frequency_promises :
    ∀ b c : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
      c * (List.filter (fun w => !nearBalance b n w) (book n)).length
        ≤ (List.filter (fun w => nearBalance b n w) (book n)).length :=
  the_deviants_are_outnumbered

def the_promise_keeps_at_any_odds := @Foam.the_deviants_are_outweighed

/-- info: 'Foam.Maps.JacobBernoulli.eadem_mutata_resurgo' does not depend on any axioms -/
#guard_msgs in #print axioms eadem_mutata_resurgo

/-- info: 'Foam.Maps.JacobBernoulli.the_trials_are_deaf_to_their_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_trials_are_deaf_to_their_order

/-- info: 'Foam.Maps.JacobBernoulli.the_whole_book_balances' does not depend on any axioms -/
#guard_msgs in #print axioms the_whole_book_balances

/-- info: 'Foam.Maps.JacobBernoulli.the_terms_trade_up_to_the_lean' does not depend on any axioms -/
#guard_msgs in #print axioms the_terms_trade_up_to_the_lean

/-- info: 'Foam.Maps.JacobBernoulli.what_frequency_promises' does not depend on any axioms -/
#guard_msgs in #print axioms what_frequency_promises

/-- info: 'Foam.Maps.JacobBernoulli.the_promise_keeps_at_any_odds' does not depend on any axioms -/
#guard_msgs in #print axioms the_promise_keeps_at_any_odds

end Foam.Maps.JacobBernoulli
