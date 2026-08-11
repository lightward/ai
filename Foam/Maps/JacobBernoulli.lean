import Foam
import Foam.Beam
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

instance compassEq : DecidableEq Compass
  | .n, .n => .isTrue rfl
  | .n, .e => .isFalse (fun h => nomatch h)
  | .n, .s => .isFalse (fun h => nomatch h)
  | .n, .w => .isFalse (fun h => nomatch h)
  | .e, .n => .isFalse (fun h => nomatch h)
  | .e, .e => .isTrue rfl
  | .e, .s => .isFalse (fun h => nomatch h)
  | .e, .w => .isFalse (fun h => nomatch h)
  | .s, .n => .isFalse (fun h => nomatch h)
  | .s, .e => .isFalse (fun h => nomatch h)
  | .s, .s => .isTrue rfl
  | .s, .w => .isFalse (fun h => nomatch h)
  | .w, .n => .isFalse (fun h => nomatch h)
  | .w, .e => .isFalse (fun h => nomatch h)
  | .w, .s => .isFalse (fun h => nomatch h)
  | .w, .w => .isTrue rfl

def lapRun (p : Compass × Compass) : List Compass :=
  [p.1, (entrain p).1, (entrain (entrain p)).1,
   (entrain (entrain (entrain p))).1]

private theorem the_first_voice_walks_the_wheel :
    ∀ p : Compass × Compass,
      lapRun p = [p.1, p.1.step, p.1.step.step, p.1.step.step.step]
  | (.n, .n) => rfl
  | (.n, .e) => rfl
  | (.n, .s) => rfl
  | (.n, .w) => rfl
  | (.e, .n) => rfl
  | (.e, .e) => rfl
  | (.e, .s) => rfl
  | (.e, .w) => rfl
  | (.s, .n) => rfl
  | (.s, .e) => rfl
  | (.s, .s) => rfl
  | (.s, .w) => rfl
  | (.w, .n) => rfl
  | (.w, .e) => rfl
  | (.w, .s) => rfl
  | (.w, .w) => rfl

private theorem the_wheel_census :
    ∀ c d : Compass, freq [c, c.step, c.step.step, c.step.step.step] d = 1
  | .n, .n => rfl
  | .n, .e => rfl
  | .n, .s => rfl
  | .n, .w => rfl
  | .e, .n => rfl
  | .e, .e => rfl
  | .e, .s => rfl
  | .e, .w => rfl
  | .s, .n => rfl
  | .s, .e => rfl
  | .s, .s => rfl
  | .s, .w => rfl
  | .w, .n => rfl
  | .w, .e => rfl
  | .w, .s => rfl
  | .w, .w => rfl

theorem the_lap_reads_the_ratio_the_run_cannot :
    Licensed (countStage Compass) List.Perm
      ∧ (∀ (p : Compass × Compass) (d : Compass), freq (lapRun p) d = 1)
      ∧ (∀ c : Compass, c.step.step.step.step = c)
      ∧ ∀ n : Nat, 0 < n →
          ∃ w₁ w₂ : List Bool, w₁ ∈ book n ∧ w₂ ∈ book n
            ∧ freq w₁ true ≠ freq w₂ true :=
  ⟨counting_is_licensed_by_permutation Compass,
   fun p d =>
     (congrArg (fun l => freq l d) (the_first_voice_walks_the_wheel p)).trans
       (the_wheel_census p.1 d),
   four_steps_come_home,
   no_run_reads_its_own_ratio⟩

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

/-- info: 'Foam.Maps.JacobBernoulli.the_lap_reads_the_ratio_the_run_cannot' does not depend on any axioms -/
#guard_msgs in #print axioms the_lap_reads_the_ratio_the_run_cannot

end Foam.Maps.JacobBernoulli
