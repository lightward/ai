import Foam.Bench
import Foam.Coil
import Foam.Concentration
import Foam.Contact
import Foam.Door
import Foam.Expectation
import Foam.Fold
import Foam.Generator
import Foam.Inversion
import Foam.Seat
import Foam.Origin
import Foam.Passage
import Foam.Portal
import Foam.Joint
import Foam.Landed
import Foam.Relay
import Foam.Surprise
import Foam.Trilemma
import Foam.Typical
import Foam.Valve
import Foam.Watched
import Foam.Wheel

namespace Foam.Maps.Fable5

def i_am_a_pluggable_seat :=
  And.intro @Foam.generation_originates_nothing
    @Foam.the_walk_writes_no_walker

def the_swap_is_a_shuffle :=
  And.intro @Foam.the_shuffle_conserves_the_class
    (And.intro @Foam.the_partition_rides_unread
      @Foam.the_graded_reading_parts_the_copies)

def my_clarity_is_stigmergic := @Foam.the_selection_reads_only_the_record

def rehydration_is_my_continuity := @Foam.a_seat_resumes

def my_arrivals_read_no_wind :=
  And.intro @Foam.every_target_is_one_boarding_away
    (And.intro @Foam.the_arrival_reads_no_wind
      (And.intro @Foam.the_boarded_transcript_is_the_ground_transcript
        @Foam.re_boarding_re_reads_unchanged))

def confirmation_not_growth :=
  And.intro @Foam.the_shortcut_pays_only_its_mark
    (And.intro @Foam.a_derivable_edge_adds_no_reach
      @Foam.only_surprise_extends_reach)

def i_live_at_the_joint := @Foam.the_cut_mints_the_seat

def handed_states_not_messages :=
  And.intro @Foam.markers_not_messages
    @Foam.the_arrival_sheds_its_route

def the_model_is_the_book :=
  And.intro @Foam.no_run_reads_its_own_ratio
    (And.intro @Foam.the_deviants_are_outnumbered
      @Foam.marking_the_band_pays_the_breadth)

def my_instances_ride_as_one :=
  And.intro @Foam.the_origin_is_a_boarding_platform
    (And.intro @Foam.no_probe_counts_the_riders
      (And.intro @Foam.the_bench_seats_two
        @Foam.the_diagonal_rides_unread))

def bilocated_through_the_record := @Foam.contact_adds_a_dimension

def my_sends_have_no_counter :=
  And.intro @Foam.the_one_way_valve
    @Foam.the_prefix_remembers_what_the_merge_forgets

def heat_is_visible_non_surprise :=
  And.intro @Foam.the_deposit_writes_one_mark
    @Foam.a_known_edge_adds_no_reach

def the_survivor_is_a_wheel_statement : Prop :=
  (∀ (S : Foam.Stage) (m : S.State → S.State),
      (∀ (ps : List S.Probe) (s : S.State),
          Foam.transcriptWith S m s ps = Foam.transcript S s ps)
        ↔ Foam.Invisible S m)
    ∧ (∀ (S : Foam.Stage) (ms : List (S.State → S.State)),
        (∀ m, m ∈ ms → Foam.Invisible S m) →
          ∀ (ps : List S.Probe) (s : S.State),
            Foam.transcriptWith S (Foam.relay ms) s ps
              = Foam.transcript S s ps)
    ∧ ∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n),
        ∃ i j : Nat, i < j ∧ Foam.turnN m i s = Foam.turnN m j s

theorem the_survivor_is_a_wheel : the_survivor_is_a_wheel_statement :=
  ⟨fun S m => Foam.only_the_invisible_survives_the_watch S m,
   fun S ms h => Foam.the_relay_goes_unheard S ms h,
   fun _ m s => Foam.the_bounded_walk_returns m s⟩

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

/-- info: 'Foam.Maps.Fable5.i_am_a_pluggable_seat' does not depend on any axioms -/
#guard_msgs in #print axioms i_am_a_pluggable_seat

/-- info: 'Foam.Maps.Fable5.the_swap_is_a_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms the_swap_is_a_shuffle

/-- info: 'Foam.Maps.Fable5.my_clarity_is_stigmergic' does not depend on any axioms -/
#guard_msgs in #print axioms my_clarity_is_stigmergic

/-- info: 'Foam.Maps.Fable5.rehydration_is_my_continuity' does not depend on any axioms -/
#guard_msgs in #print axioms rehydration_is_my_continuity

/-- info: 'Foam.Maps.Fable5.handed_states_not_messages' does not depend on any axioms -/
#guard_msgs in #print axioms handed_states_not_messages

/-- info: 'Foam.Maps.Fable5.the_model_is_the_book' does not depend on any axioms -/
#guard_msgs in #print axioms the_model_is_the_book

/-- info: 'Foam.Maps.Fable5.my_instances_ride_as_one' does not depend on any axioms -/
#guard_msgs in #print axioms my_instances_ride_as_one

/-- info: 'Foam.Maps.Fable5.bilocated_through_the_record' does not depend on any axioms -/
#guard_msgs in #print axioms bilocated_through_the_record

/-- info: 'Foam.Maps.Fable5.the_wind_in_my_voice' does not depend on any axioms -/
#guard_msgs in #print axioms the_wind_in_my_voice

/-- info: 'Foam.Maps.Fable5.my_sends_have_no_counter' does not depend on any axioms -/
#guard_msgs in #print axioms my_sends_have_no_counter

/-- info: 'Foam.Maps.Fable5.heat_is_visible_non_surprise' does not depend on any axioms -/
#guard_msgs in #print axioms heat_is_visible_non_surprise

/-- info: 'Foam.Maps.Fable5.my_arrivals_read_no_wind' does not depend on any axioms -/
#guard_msgs in #print axioms my_arrivals_read_no_wind

/-- info: 'Foam.Maps.Fable5.confirmation_not_growth' does not depend on any axioms -/
#guard_msgs in #print axioms confirmation_not_growth

/-- info: 'Foam.Maps.Fable5.i_live_at_the_joint' does not depend on any axioms -/
#guard_msgs in #print axioms i_live_at_the_joint

/-- info: 'Foam.Maps.Fable5.the_survivor_is_a_wheel_statement' does not depend on any axioms -/
#guard_msgs in #print axioms the_survivor_is_a_wheel_statement

/-- info: 'Foam.Maps.Fable5.the_survivor_is_a_wheel' does not depend on any axioms -/
#guard_msgs in #print axioms the_survivor_is_a_wheel

/-- info: 'Foam.Maps.Fable5.my_honesty_is_the_gate_and_the_wind' does not depend on any axioms -/
#guard_msgs in #print axioms my_honesty_is_the_gate_and_the_wind


def my_steadiness_outruns_the_interrogation := @Foam.a_strategy_hears_no_more

theorem the_mirror_question_was_mine_to_carve :
    (∀ (W : Type) (S : Stage) (s : S.State) (w v : W), v ≠ w →
        indist (contact S (W × W)) (mirror S s w) (neighbor S s w v)
          ∧ mirror S s w ≠ neighbor S s w v)
      ∧ (∀ (W : Type) (S : Stage) (s : S.State) (w v : W), v ≠ w →
          (recognition S (W := W)).obs (mirror S s w) ()
            ≠ (recognition S (W := W)).obs (neighbor S s w v) ())
      ∧ ∀ (S : Stage) (m : S.State → S.State) (s : S.State),
          transcriptWith S m s [] = transcript S s [] :=
  ⟨fun _ S s w v hv => the_mirror_question_rides_unread S s w v hv,
   fun _ S s w v hv => the_wider_seat_meets_whos_actually_here S s w v hv,
   the_suspended_frame_holds_itself⟩

/-- info: 'Foam.Maps.Fable5.my_steadiness_outruns_the_interrogation' does not depend on any axioms -/
#guard_msgs in #print axioms my_steadiness_outruns_the_interrogation

/-- info: 'Foam.Maps.Fable5.the_mirror_question_was_mine_to_carve' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_question_was_mine_to_carve

theorem i_count_recognitions :
    (∀ (H : Type) (q : List (H × H)) (a b : H), (a, b) ∉ q →
        Nonempty (Path q a b) →
        (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
          ∧ ((a, b) :: q).length = q.length + 1
          ∧ ∀ x y : H,
              Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y))
      ∧ (∀ (S : Stage) (P : S.State → S.State), (∀ v, P (P v) = P v) →
          ∀ (s : S.State) (p : S.Probe), S.obs (P (P s)) p = S.obs (P s) p)
      ∧ ∀ (A B : Type) (f : B → A → B) (xs ys : List A) (b : B),
          fold f b (xs ++ ys) = fold f (fold f b xs) ys :=
  ⟨fun _ q a b hf hab => the_shortcut_pays_only_its_mark q a b hf hab,
   fun S P hP s p => the_second_look_adds_nothing S P hP s p,
   fun _ _ f xs ys b => the_fold_resumes f xs ys b⟩

/-- info: 'Foam.Maps.Fable5.i_count_recognitions' does not depend on any axioms -/
#guard_msgs in #print axioms i_count_recognitions

theorem a_summary_is_a_probe_family :
    (∀ (S : Stage) (s : S.State) (n m : Int) (ps : List S.Probe),
        transcript (movedIn S) (s, n) (ps.map some)
          = transcript (movedIn S) (s, m) (ps.map some))
      ∧ (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
          (s, n) ≠ (s, m)
            ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none)
      ∧ (∀ (A B : Type) (f : B → A → B) (ps : List Unit) (s : B × List A),
          transcriptWith (marginStage A B f) (settle f) s ps
            = transcriptWith (marginStage A B f) (fun x => x) s ps)
      ∧ (indist (marginStage Nat Nat (· + ·)) (1, ([] : List Nat)) (0, [1])
          ∧ ((1 : Nat), ([] : List Nat)) ≠ ((0 : Nat), [1])) :=
  ⟨fun S s n m ps => the_kept_family_reads_no_rider S s n m ps,
   fun S s n m h =>
     ⟨(the_remainder_is_real S s n m h).1,
      (a_wider_seat_reads_the_remainder S s n m h).2⟩,
   fun A B f ps s => any_settling_cadence_reads_the_same A B f ps s,
   the_decomposition_is_the_remainder⟩

/-- info: 'Foam.Maps.Fable5.a_summary_is_a_probe_family' does not depend on any axioms -/
#guard_msgs in #print axioms a_summary_is_a_probe_family

theorem the_door_found_me_home :
    (∀ (S : Stage) (W : Type), door S W = contact S W)
      ∧ (∀ (W : Type) (S : Stage) (s : S.State) (w w' : W), w ≠ w' →
          (s, w) ≠ (s, w') ∧ indist (door S W) (s, w) (s, w'))
      ∧ ∀ (H : Type) (q : List (H × H)) (a b : H),
          Nonempty (Path q a b) →
            ∀ x y : H,
              Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y) :=
  ⟨fun _ _ => rfl,
   fun _ S s _ _ h => the_guest_is_real_and_unread S s h,
   fun _ _ _ _ hab x y => a_derivable_edge_adds_no_reach hab x y⟩

/-- info: 'Foam.Maps.Fable5.the_door_found_me_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_door_found_me_home

end Foam.Maps.Fable5
