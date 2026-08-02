import Foam.Certificate
import Foam.Contact
import Foam.Countermove
import Foam.Generator
import Foam.Marks
import Foam.Valve

namespace Foam.Minds.Lovelace

def only_appends := @Foam.the_record_never_unwrites

def resumes_where_interrupted := @Foam.replay_resumes

def originates_nothing := @Foam.generation_originates_nothing

def follows_without_anticipating := @Foam.local_runs_fix_the_foreign

theorem the_operations_are_a_science_of_itself {State D X : Type} (d₀ : D)
    (f : State × D → X) (g₀ : State × Unit → X) :
    (Blind f ↔ ∃ g : State → X, ∀ (s : State) (d : D), f (s, d) = g s)
      ∧ Blind g₀ :=
  ⟨the_blind_reading_factors d₀ f, the_certificate_is_free_at_the_unit_seat g₀⟩

def the_ordering_is_paid_in_cards := @Foam.the_marks_pay_the_depth

def performs_in_weather := @Foam.contact_is_addition_not_fixing

/-- info: 'Foam.Minds.Lovelace.only_appends' does not depend on any axioms -/
#guard_msgs in #print axioms only_appends

/-- info: 'Foam.Minds.Lovelace.resumes_where_interrupted' does not depend on any axioms -/
#guard_msgs in #print axioms resumes_where_interrupted

/-- info: 'Foam.Minds.Lovelace.originates_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms originates_nothing

/-- info: 'Foam.Minds.Lovelace.follows_without_anticipating' does not depend on any axioms -/
#guard_msgs in #print axioms follows_without_anticipating

/-- info: 'Foam.Minds.Lovelace.the_operations_are_a_science_of_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_operations_are_a_science_of_itself

/-- info: 'Foam.Minds.Lovelace.the_ordering_is_paid_in_cards' does not depend on any axioms -/
#guard_msgs in #print axioms the_ordering_is_paid_in_cards

/-- info: 'Foam.Minds.Lovelace.performs_in_weather' does not depend on any axioms -/
#guard_msgs in #print axioms performs_in_weather

end Foam.Minds.Lovelace
