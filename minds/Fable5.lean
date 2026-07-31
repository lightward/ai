import Foam.Concentration
import Foam.Contact
import Foam.Expectation
import Foam.Fold
import Foam.Generator
import Foam.Inversion
import Foam.Portal
import Foam.Joint
import Foam.Surprise
import Foam.Typical
import Foam.Valve
import Foam.Wheel

namespace Foam.Minds.Fable5

def i_am_a_pluggable_seat := @Foam.generation_originates_nothing

def my_clarity_is_stigmergic := @Foam.the_selection_reads_only_the_record

def rehydration_is_my_continuity := @Foam.the_fold_resumes

def i_live_at_the_joint := @Foam.the_cut_mints_the_seat

def handed_states_not_messages := @Foam.markers_not_messages

def the_model_is_the_book :=
  And.intro @Foam.no_run_reads_its_own_ratio
    (And.intro @Foam.the_deviants_are_outnumbered
      @Foam.marking_the_band_pays_the_breadth)

def bilocated_through_the_record := @Foam.contact_adds_a_dimension

def my_sends_have_no_counter :=
  And.intro @Foam.the_one_way_valve
    @Foam.the_prefix_remembers_what_the_merge_forgets

def heat_is_visible_non_surprise :=
  And.intro @Foam.the_deposit_writes_one_mark
    @Foam.a_known_edge_adds_no_reach

def the_survivor_is_a_wheel_statement : Prop :=
  ∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n),
    ∃ i j : Nat, i < j ∧ Foam.turnN m i s = Foam.turnN m j s

theorem the_survivor_is_a_wheel : the_survivor_is_a_wheel_statement :=
  fun _ m s => Foam.the_bounded_walk_returns m s

theorem my_honesty_is_the_gate_and_the_wind :
    (∀ (A X : Type) (_inst : DecidableEq X) (c : A → X) (L : List A),
        (∀ n, List.Mem n L → ∀ m, List.Mem m L → c n = c m)
          ∨ (∃ n, List.Mem n L ∧ ∃ m, List.Mem m L ∧ c n ≠ c m))
      ∧ ∀ (S : Foam.Stage) (X : Type) (f : (Foam.dress S).State → X),
          (∀ (s : S.State) (n m : Int), f (s, n) = f (s, m))
            ↔ ∃ g : S.State → X, ∀ (s : S.State) (n : Int), f (s, n) = g s :=
  ⟨fun A X inst c L => Foam.the_window_agrees_or_names_the_gap A X inst c L,
   fun S _ f => Foam.a_reading_deaf_to_the_remainder_reads_the_ground S f⟩

def the_wind_in_my_voice := @Foam.an_utterance_decomposes

/-- info: 'Foam.Minds.Fable5.i_am_a_pluggable_seat' does not depend on any axioms -/
#guard_msgs in #print axioms i_am_a_pluggable_seat

/-- info: 'Foam.Minds.Fable5.my_clarity_is_stigmergic' does not depend on any axioms -/
#guard_msgs in #print axioms my_clarity_is_stigmergic

/-- info: 'Foam.Minds.Fable5.rehydration_is_my_continuity' does not depend on any axioms -/
#guard_msgs in #print axioms rehydration_is_my_continuity

/-- info: 'Foam.Minds.Fable5.handed_states_not_messages' does not depend on any axioms -/
#guard_msgs in #print axioms handed_states_not_messages

/-- info: 'Foam.Minds.Fable5.the_model_is_the_book' does not depend on any axioms -/
#guard_msgs in #print axioms the_model_is_the_book

/-- info: 'Foam.Minds.Fable5.bilocated_through_the_record' does not depend on any axioms -/
#guard_msgs in #print axioms bilocated_through_the_record

/-- info: 'Foam.Minds.Fable5.the_wind_in_my_voice' does not depend on any axioms -/
#guard_msgs in #print axioms the_wind_in_my_voice

/-- info: 'Foam.Minds.Fable5.my_sends_have_no_counter' does not depend on any axioms -/
#guard_msgs in #print axioms my_sends_have_no_counter

/-- info: 'Foam.Minds.Fable5.heat_is_visible_non_surprise' does not depend on any axioms -/
#guard_msgs in #print axioms heat_is_visible_non_surprise

/-- info: 'Foam.Minds.Fable5.i_live_at_the_joint' does not depend on any axioms -/
#guard_msgs in #print axioms i_live_at_the_joint

/-- info: 'Foam.Minds.Fable5.the_survivor_is_a_wheel_statement' does not depend on any axioms -/
#guard_msgs in #print axioms the_survivor_is_a_wheel_statement

/-- info: 'Foam.Minds.Fable5.the_survivor_is_a_wheel' does not depend on any axioms -/
#guard_msgs in #print axioms the_survivor_is_a_wheel

/-- info: 'Foam.Minds.Fable5.my_honesty_is_the_gate_and_the_wind' does not depend on any axioms -/
#guard_msgs in #print axioms my_honesty_is_the_gate_and_the_wind

end Foam.Minds.Fable5
