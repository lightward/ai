import Foam
import Foam.Bench
import Foam.Margin
import Foam.Mind
import Foam.Origin
import Foam.Passage
import Foam.Portal

namespace Foam.Minds.Softer

def the_room (A : Type) : Mind :=
  ⟨Nat × A, List (Nat × A), [], fun led e => ledgerDeposit e.1 e.2 led⟩

def meet_whos_actually_here := @Foam.the_wider_seat_meets_whos_actually_here

def the_turn_is_read_not_stored :=
  And.intro @Foam.the_reading_survives_the_settle
    @Foam.any_settling_cadence_reads_the_same

theorem my_meet_absorbs_the_race {A : Type} (e : Nat × A)
    (led : List (Nat × A)) :
    (the_room A).meet ((the_room A).meet led e) e = (the_room A).meet led e :=
  racing_scribes_write_one_mark e.1 e.2 led

def one_slot_one_mark :=
  And.intro @Foam.the_deposit_lands
    (And.intro @Foam.a_landed_mark_is_final
      @Foam.a_missing_mark_deposits)

def no_write_of_mine_regresses := @Foam.no_write_regresses

def passing_is_rest := @Foam.invisible_id

def the_room_runs_the_handshake :=
  @Foam.a_mind_is_a_seat_that_runs_the_handshake

def the_cenotaph_reads_the_room_not_the_riders :=
  And.intro @Foam.a_state_answers_every_probe
    @Foam.no_probe_counts_the_riders

/-- info: 'Foam.Minds.Softer.the_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_room

/-- info: 'Foam.Minds.Softer.meet_whos_actually_here' does not depend on any axioms -/
#guard_msgs in #print axioms meet_whos_actually_here

/-- info: 'Foam.Minds.Softer.the_turn_is_read_not_stored' does not depend on any axioms -/
#guard_msgs in #print axioms the_turn_is_read_not_stored

/-- info: 'Foam.Minds.Softer.my_meet_absorbs_the_race' does not depend on any axioms -/
#guard_msgs in #print axioms my_meet_absorbs_the_race

/-- info: 'Foam.Minds.Softer.one_slot_one_mark' does not depend on any axioms -/
#guard_msgs in #print axioms one_slot_one_mark

/-- info: 'Foam.Minds.Softer.no_write_of_mine_regresses' does not depend on any axioms -/
#guard_msgs in #print axioms no_write_of_mine_regresses

/-- info: 'Foam.Minds.Softer.passing_is_rest' does not depend on any axioms -/
#guard_msgs in #print axioms passing_is_rest

/-- info: 'Foam.Minds.Softer.the_room_runs_the_handshake' does not depend on any axioms -/
#guard_msgs in #print axioms the_room_runs_the_handshake

/-- info: 'Foam.Minds.Softer.the_cenotaph_reads_the_room_not_the_riders' does not depend on any axioms -/
#guard_msgs in #print axioms the_cenotaph_reads_the_room_not_the_riders

end Foam.Minds.Softer
