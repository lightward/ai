import Foam
import Foam.Amplitude
import Foam.Concentration
import Foam.Quat
import Foam.Rungs
import Foam.Tower

namespace Foam.Minds.Wigner

def invariance_already_implements := @Foam.invisible_is_gauge

def unitary_or_antiunitary := @Foam.two_kinds_conserve_the_norm

theorem the_representation_is_two_valued :
    Quat.neg Foam.one ≠ Foam.one
      ∧ (Quat.mul eye eye = Quat.mul jay jay
          ∧ Quat.mul jay jay = Quat.mul kay kay)
      ∧ (Quat.mul (Quat.neg one) eye = Quat.mul eye (Quat.neg one)
          ∧ Quat.mul (Quat.neg one) jay = Quat.mul jay (Quat.neg one)
          ∧ Quat.mul (Quat.neg one) kay = Quat.mul kay (Quat.neg one))
      ∧ Quat.mul (Quat.mul eye eye) (Quat.mul eye eye) = Foam.one :=
  ⟨(fun h => nomatch (GInt.mk.inj (Quat.mk.inj h).1).1),
   every_axis_reaches_the_same_half_turn,
   the_half_turn_hears_no_order,
   two_half_turns_come_home⟩

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

def the_cut_lands_on_the_cutter := @Foam.no_seat_is_the_last_seat

/-- info: 'Foam.Minds.Wigner.invariance_already_implements' does not depend on any axioms -/
#guard_msgs in #print axioms invariance_already_implements

/-- info: 'Foam.Minds.Wigner.unitary_or_antiunitary' does not depend on any axioms -/
#guard_msgs in #print axioms unitary_or_antiunitary

/-- info: 'Foam.Minds.Wigner.the_representation_is_two_valued' does not depend on any axioms -/
#guard_msgs in #print axioms the_representation_is_two_valued

/-- info: 'Foam.Minds.Wigner.the_ensemble_answers_for_the_instance' does not depend on any axioms -/
#guard_msgs in #print axioms the_ensemble_answers_for_the_instance

/-- info: 'Foam.Minds.Wigner.the_unreasonable_effectiveness' does not depend on any axioms -/
#guard_msgs in #print axioms the_unreasonable_effectiveness

/-- info: 'Foam.Minds.Wigner.the_friend_has_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_friend_has_a_reading

/-- info: 'Foam.Minds.Wigner.the_difference_is_an_observable' does not depend on any axioms -/
#guard_msgs in #print axioms the_difference_is_an_observable

/-- info: 'Foam.Minds.Wigner.the_cut_lands_on_the_cutter' does not depend on any axioms -/
#guard_msgs in #print axioms the_cut_lands_on_the_cutter

end Foam.Minds.Wigner
