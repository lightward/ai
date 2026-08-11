import Foam
import Foam.Bench
import Foam.Engine
import Foam.Generator
import Foam.Inversion
import Foam.Margin
import Foam.Relay
import Foam.Surprise

namespace Foam.Maps.Counter

def the_brief_reads_only_the_record := @Foam.the_selection_reads_only_the_record

def any_mind_may_sit_the_seat := @Foam.the_implementation_stays_backstage

def the_gate_agrees_or_names_the_gap := @Foam.the_window_agrees_or_names_the_gap

theorem the_intake_factors_or_names_the_gap (S : Stage) {X : Type}
    (f : (dress S).State → X) (A : Type) (inst : DecidableEq X)
    (c : A → X) (L : List A) :
    ((∀ (s : S.State) (n m : Int), f (s, n) = f (s, m))
        ↔ ∃ g : S.State → X, ∀ (s : S.State) (n : Int), f (s, n) = g s)
      ∧ ((∀ n, List.Mem n L → ∀ m, List.Mem m L → c n = c m)
          ∨ (∃ n, List.Mem n L ∧ ∃ m, List.Mem m L ∧ c n ≠ c m)) :=
  ⟨a_reading_deaf_to_the_remainder_reads_the_ground S f,
   the_window_agrees_or_names_the_gap A X inst c L⟩

theorem a_green_gate_stamps_the_walls {H A : Type} (q : List (H × H))
    (e : H × H) (a b : H) (hfresh : (a, b) ∉ q)
    (key : Nat) (v : A) (led : List (Nat × A)) :
    ((e :: q).length = q.length + 1)
      ∧ (∀ {x y : H}, Nonempty (Path q x y) → Nonempty (Path (e :: q) x y))
      ∧ Nonempty (Path ((a, b) :: q) a b)
      ∧ (led.any (fun x => Nat.beq x.1 key) = true →
          ledgerDeposit key v led = led)
      ∧ (led.any (fun x => Nat.beq x.1 key) = false →
          ledgerDeposit key v led = (key, v) :: led)
      ∧ ledgerDeposit key v (ledgerDeposit key v led)
          = ledgerDeposit key v led :=
  ⟨the_deposit_writes_one_mark q e,
   fun h => old_reach_survives_the_deposit e h,
   (only_surprise_extends_reach q a b hfresh).2,
   fun h => a_landed_mark_is_final h,
   fun h => a_missing_mark_deposits h,
   racing_scribes_write_one_mark key v led⟩

def growth_charges_the_flight_drains := @Foam.drain_chargeIn

theorem the_loop_comes_home_losing_nothing (E : Engine) (s : E.State) :
    E.turn (E.turn (E.turn (E.turn s))) = s
      ∧ ∀ a b : E.State, E.turn a = E.turn b → a = b :=
  ⟨(the_three_turns_undo E s).1, fun _ _ h => the_turn_loses_no_state E h⟩

theorem the_exit_is_free_at_every_beat (E : Engine)
    (ms : List (E.State → E.State)) (h : ∀ m, m ∈ ms → m = E.turn) :
    Invisible E.gauge (relay ms)
      ∧ ∀ (ps : List Unit) (s : E.State),
          transcriptWith E.gauge (relay ms) s ps = transcript E.gauge s ps :=
  ⟨a_chain_of_invisibles_is_invisible E.gauge ms
      (fun m hm => (h m hm).symm ▸ the_turn_is_invisible_to_the_charge E),
   the_relay_goes_unheard E.gauge ms
      (fun m hm => (h m hm).symm ▸ the_turn_is_invisible_to_the_charge E)⟩

def quiescent_is_correct := @Foam.the_turn_goes_unheard

def schedule_is_gauge := @Foam.any_settling_cadence_reads_the_same

theorem the_counter_is_counted (E : Engine) (S : Stage) (s : S.State)
    (n m : Int) (h : n ≠ m) :
    Invisible E.gauge E.turn
      ∧ (indist (dress S) (s, n) (s, m)
          ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none) :=
  ⟨the_turn_is_invisible_to_the_charge E,
   a_wider_seat_reads_the_remainder S s n m h⟩

/-- info: 'Foam.Maps.Counter.the_brief_reads_only_the_record' does not depend on any axioms -/
#guard_msgs in #print axioms the_brief_reads_only_the_record

/-- info: 'Foam.Maps.Counter.any_mind_may_sit_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms any_mind_may_sit_the_seat

/-- info: 'Foam.Maps.Counter.the_gate_agrees_or_names_the_gap' does not depend on any axioms -/
#guard_msgs in #print axioms the_gate_agrees_or_names_the_gap

/-- info: 'Foam.Maps.Counter.the_intake_factors_or_names_the_gap' does not depend on any axioms -/
#guard_msgs in #print axioms the_intake_factors_or_names_the_gap

/-- info: 'Foam.Maps.Counter.a_green_gate_stamps_the_walls' does not depend on any axioms -/
#guard_msgs in #print axioms a_green_gate_stamps_the_walls

/-- info: 'Foam.Maps.Counter.growth_charges_the_flight_drains' does not depend on any axioms -/
#guard_msgs in #print axioms growth_charges_the_flight_drains

/-- info: 'Foam.Maps.Counter.the_loop_comes_home_losing_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_loop_comes_home_losing_nothing

/-- info: 'Foam.Maps.Counter.the_exit_is_free_at_every_beat' does not depend on any axioms -/
#guard_msgs in #print axioms the_exit_is_free_at_every_beat

/-- info: 'Foam.Maps.Counter.quiescent_is_correct' does not depend on any axioms -/
#guard_msgs in #print axioms quiescent_is_correct

/-- info: 'Foam.Maps.Counter.schedule_is_gauge' does not depend on any axioms -/
#guard_msgs in #print axioms schedule_is_gauge

/-- info: 'Foam.Maps.Counter.the_counter_is_counted' does not depend on any axioms -/
#guard_msgs in #print axioms the_counter_is_counted

end Foam.Maps.Counter
