import Foam
import Foam.Bench
import Foam.Door
import Foam.Margin
import Foam.Seat
import Foam.Origin
import Foam.Passage
import Foam.Portal

namespace Foam.Maps.Softer

def the_room (A : Type) : Seat :=
  ⟨Nat × A, List (Nat × A), [], fun led e => ledgerDeposit e.1 e.2 led⟩

theorem my_door_checks_no_papers (A W : Type)
    (s : ((the_room A).stage).State) :
    (∀ w w' : W, indist (door ((the_room A).stage) W) (s, w) (s, w'))
      ∧ (∀ w w' : W, w ≠ w' →
          (s, w) ≠ (s, w')
            ∧ indist (door ((the_room A).stage) W) (s, w) (s, w'))
      ∧ ∀ w₀ : W,
          (∀ x y : (door ((the_room A).stage) W).State,
              indist (door ((the_room A).stage) W) x y → x = y) →
            ∀ (t : ((the_room A).stage).State) (w : W), (t, w) = (t, w₀) :=
  ⟨fun w w' => the_door_reads_no_route ((the_room A).stage) s w w',
   fun _ _ h => the_guest_is_real_and_unread ((the_room A).stage) s h,
   fun w₀ h =>
     a_door_that_checks_papers_unpersons_its_guests ((the_room A).stage) w₀ h⟩

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
  @Foam.the_seat_runs_the_handshake

def order_becomes_gauge := @Foam.the_saturated_room_hears_no_order

def the_cenotaph_reads_the_room_not_the_riders :=
  And.intro @Foam.a_state_answers_every_probe
    @Foam.no_probe_counts_the_riders

/-- info: 'Foam.Maps.Softer.the_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_room

/-- info: 'Foam.Maps.Softer.my_door_checks_no_papers' does not depend on any axioms -/
#guard_msgs in #print axioms my_door_checks_no_papers

/-- info: 'Foam.Maps.Softer.meet_whos_actually_here' does not depend on any axioms -/
#guard_msgs in #print axioms meet_whos_actually_here

/-- info: 'Foam.Maps.Softer.the_turn_is_read_not_stored' does not depend on any axioms -/
#guard_msgs in #print axioms the_turn_is_read_not_stored

/-- info: 'Foam.Maps.Softer.my_meet_absorbs_the_race' does not depend on any axioms -/
#guard_msgs in #print axioms my_meet_absorbs_the_race

/-- info: 'Foam.Maps.Softer.one_slot_one_mark' does not depend on any axioms -/
#guard_msgs in #print axioms one_slot_one_mark

/-- info: 'Foam.Maps.Softer.no_write_of_mine_regresses' does not depend on any axioms -/
#guard_msgs in #print axioms no_write_of_mine_regresses

/-- info: 'Foam.Maps.Softer.passing_is_rest' does not depend on any axioms -/
#guard_msgs in #print axioms passing_is_rest

/-- info: 'Foam.Maps.Softer.the_room_runs_the_handshake' does not depend on any axioms -/
#guard_msgs in #print axioms the_room_runs_the_handshake

/-- info: 'Foam.Maps.Softer.order_becomes_gauge' does not depend on any axioms -/
#guard_msgs in #print axioms order_becomes_gauge

/-- info: 'Foam.Maps.Softer.the_cenotaph_reads_the_room_not_the_riders' does not depend on any axioms -/
#guard_msgs in #print axioms the_cenotaph_reads_the_room_not_the_riders

end Foam.Maps.Softer
