import Foam
import Foam.Amplitude
import Foam.Beam
import Foam.Bench
import Foam.Concentration
import Foam.Quat
import Foam.Rungs
import Foam.Tower
import Foam.Width

namespace Foam.Maps.Wigner

def invariance_already_implements := @Foam.invisible_is_gauge

def unitary_or_antiunitary := @Foam.two_kinds_conserve_the_norm

theorem the_reversal_is_of_the_second_kind :
    (∀ p : Compass × Compass, window (window p) = p)
      ∧ (∀ p : Compass × Compass, window (conjugated (window p)) = entrain p)
      ∧ (∀ p : Compass × Compass,
          together (entrain (entrain (entrain (entrain p)))))
      ∧ (∀ p : Compass × Compass,
          opposed (conjugated (conjugated (conjugated (conjugated p)))))
      ∧ (∀ p : Compass × Compass, together p ↔ opposed (window p))
      ∧ GInt.i.rot ≠ GInt.i.conj :=
  ⟨the_window_undoes_itself, two_windows_read_direct,
    the_lap_locks_together, the_conjugate_locks_opposed,
    the_window_trades_the_locks, the_kinds_are_two⟩

def the_representation_is_two_valued := @Foam.the_axes_share_one_sign

theorem the_ensemble_answers_for_the_instance :
    GInt.i.rot ≠ GInt.i.conj
      ∧ (∀ b c : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
          c * (List.filter (fun w => Bool.not (nearBalance b n w))
                (book n)).length
            ≤ (List.filter (fun w => nearBalance b n w) (book n)).length) :=
  ⟨the_kinds_are_two, the_deviants_are_outnumbered⟩

def the_unreasonable_effectiveness := @Foam.closure_is_seat_relative

def the_friend_has_a_reading := @Foam.a_wider_seat_reads_the_remainder

def the_difference_is_an_observable := @Foam.the_screen_reads_a_cross_term

theorem solipsism_is_consistent_and_false {W : Type} (S : Stage)
    (s : S.State) (w v : W) (hv : v ≠ w) :
    indist (contact S (W × W)) (mirror S s w) (neighbor S s w v)
      ∧ mirror S s w ≠ neighbor S s w v
      ∧ (recognition S (W := W)).obs (mirror S s w) ()
          ≠ (recognition S (W := W)).obs (neighbor S s w v) () :=
  ⟨(the_mirror_question_rides_unread S s w v hv).1,
   (the_mirror_question_rides_unread S s w v hv).2,
   the_wider_seat_meets_whos_actually_here S s w v hv⟩

def the_cut_is_movable := @Foam.contact_wider_than_three_is_composite

def the_cut_lands_on_the_cutter := @Foam.no_seat_is_the_last_seat

/-- info: 'Foam.Maps.Wigner.invariance_already_implements' does not depend on any axioms -/
#guard_msgs in #print axioms invariance_already_implements

/-- info: 'Foam.Maps.Wigner.unitary_or_antiunitary' does not depend on any axioms -/
#guard_msgs in #print axioms unitary_or_antiunitary

/-- info: 'Foam.Maps.Wigner.the_reversal_is_of_the_second_kind' does not depend on any axioms -/
#guard_msgs in #print axioms the_reversal_is_of_the_second_kind

/-- info: 'Foam.Maps.Wigner.the_representation_is_two_valued' does not depend on any axioms -/
#guard_msgs in #print axioms the_representation_is_two_valued

/-- info: 'Foam.Maps.Wigner.the_ensemble_answers_for_the_instance' does not depend on any axioms -/
#guard_msgs in #print axioms the_ensemble_answers_for_the_instance

/-- info: 'Foam.Maps.Wigner.the_unreasonable_effectiveness' does not depend on any axioms -/
#guard_msgs in #print axioms the_unreasonable_effectiveness

/-- info: 'Foam.Maps.Wigner.the_friend_has_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_friend_has_a_reading

/-- info: 'Foam.Maps.Wigner.the_difference_is_an_observable' does not depend on any axioms -/
#guard_msgs in #print axioms the_difference_is_an_observable

/-- info: 'Foam.Maps.Wigner.solipsism_is_consistent_and_false' does not depend on any axioms -/
#guard_msgs in #print axioms solipsism_is_consistent_and_false

/-- info: 'Foam.Maps.Wigner.the_cut_is_movable' does not depend on any axioms -/
#guard_msgs in #print axioms the_cut_is_movable

/-- info: 'Foam.Maps.Wigner.the_cut_lands_on_the_cutter' does not depend on any axioms -/
#guard_msgs in #print axioms the_cut_lands_on_the_cutter

end Foam.Maps.Wigner
