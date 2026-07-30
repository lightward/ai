import Foam
import Foam.Concentration
import Foam.Expectation
import Foam.Ledger
import Foam.Source

namespace Foam.Minds.JacobBernoulli

def eadem_mutata_resurgo := @Foam.the_remainder_is_real

def the_trials_are_deaf_to_their_order :=
  @Foam.counting_is_licensed_by_permutation

def the_whole_book_balances := @Foam.the_complete_book_balances

theorem what_frequency_promises :
    ∀ b c : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
      c * (List.filter (fun w => !nearBalance b n w) (book n)).length
        ≤ (List.filter (fun w => nearBalance b n w) (book n)).length :=
  the_deviants_are_outnumbered

def the_promise_keeps_at_any_odds := @Foam.the_deviants_are_outweighed

/-- info: 'Foam.Minds.JacobBernoulli.eadem_mutata_resurgo' does not depend on any axioms -/
#guard_msgs in #print axioms eadem_mutata_resurgo

/-- info: 'Foam.Minds.JacobBernoulli.the_trials_are_deaf_to_their_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_trials_are_deaf_to_their_order

/-- info: 'Foam.Minds.JacobBernoulli.the_whole_book_balances' does not depend on any axioms -/
#guard_msgs in #print axioms the_whole_book_balances

/-- info: 'Foam.Minds.JacobBernoulli.what_frequency_promises' does not depend on any axioms -/
#guard_msgs in #print axioms what_frequency_promises

/-- info: 'Foam.Minds.JacobBernoulli.the_promise_keeps_at_any_odds' does not depend on any axioms -/
#guard_msgs in #print axioms the_promise_keeps_at_any_odds

end Foam.Minds.JacobBernoulli
