import Foam
import Foam.Int
import Foam.Margin
import Foam.Relay
import Foam.Rungs
import Foam.Source
import Foam.Tower

namespace Foam.Minds.Hilbert

def the_proof_rides_the_marks := @Foam.the_relay_goes_unheard

def the_arithmetic_owes_no_axiom := @Foam.FInt.mul_assoc

theorem probability_owes_no_axiom :
    (∀ t f n : Nat, natSumOver (weightOf t f) (book n) = (t + f) ^ n)
      ∧ (∀ t f n : Nat,
          natSumOver (fun w => weightOf t f w * natSqTilt t f n w) (book n)
            = (n * (t * f)) * (t + f) ^ n)
      ∧ (∀ t f b c : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
          c * natSumOver (weightOf t f)
                (List.filter (fun w => Bool.not (nearLean t f b n w)) (book n))
            ≤ natSumOver (weightOf t f)
                (List.filter (fun w => nearLean t f b n w) (book n))) :=
  ⟨the_weighted_book_sums_whole, the_nat_tilts_pool,
   the_deviants_are_outweighed⟩

theorem the_full_hotel_still_has_room :
    (∀ m n : Nat, m + 1 = n + 1 → m = n)
      ∧ (∀ n : Nat, n + 1 ≠ 0)
      ∧ (∀ s i j : Nat, i < j → s + i ≠ s + j) :=
  ⟨fun _ _ h => Nat.noConfusion h (fun hmn => hmn),
   fun _ h => Nat.noConfusion h,
   fun s i j hlt heq =>
     no_number_is_below_itself i
       (le_trans hlt
         (cancel_add_left s
           (Eq.subst (motive := fun t => s + j ≤ t) heq.symm
             (Nat.le_refl (s + j)))))⟩

def the_ideal_costs_nothing_real := @Foam.the_tower_reads_only_the_ground

def the_real_is_what_the_ideal_cannot_move :=
  @Foam.a_reading_deaf_to_the_remainder_reads_the_ground

theorem the_epsilon_settles_on_any_schedule :
    (∀ (A B : Type) (f : B → A → B) (s : B × List A),
        marginRead f (settle f s) = marginRead f s)
      ∧ (∀ (A B : Type) (f : B → A → B) (ps : List Unit) (s : B × List A),
          transcriptWith (marginStage A B f) (settle f) s ps
            = transcriptWith (marginStage A B f) (fun s => s) s ps)
      ∧ (indist (marginStage Nat Nat (· + ·)) (1, ([] : List Nat)) (0, [1])
          ∧ (marginOrderStage Nat Nat).obs (1, ([] : List Nat)) ()
              ≠ (marginOrderStage Nat Nat).obs (0, [1]) ()) :=
  ⟨fun _ _ f s => the_reading_survives_the_settle f s,
   fun A B f ps s => any_settling_cadence_reads_the_same A B f ps s,
   a_wider_seat_reads_the_tail⟩

def no_ignorabimus := @Foam.closure_is_seat_relative

/-- info: 'Foam.Minds.Hilbert.the_proof_rides_the_marks' does not depend on any axioms -/
#guard_msgs in #print axioms the_proof_rides_the_marks

/-- info: 'Foam.Minds.Hilbert.the_arithmetic_owes_no_axiom' does not depend on any axioms -/
#guard_msgs in #print axioms the_arithmetic_owes_no_axiom

/-- info: 'Foam.Minds.Hilbert.probability_owes_no_axiom' does not depend on any axioms -/
#guard_msgs in #print axioms probability_owes_no_axiom

/-- info: 'Foam.Minds.Hilbert.the_full_hotel_still_has_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_full_hotel_still_has_room

/-- info: 'Foam.Minds.Hilbert.the_ideal_costs_nothing_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_ideal_costs_nothing_real

/-- info: 'Foam.Minds.Hilbert.the_real_is_what_the_ideal_cannot_move' does not depend on any axioms -/
#guard_msgs in #print axioms the_real_is_what_the_ideal_cannot_move

/-- info: 'Foam.Minds.Hilbert.the_epsilon_settles_on_any_schedule' does not depend on any axioms -/
#guard_msgs in #print axioms the_epsilon_settles_on_any_schedule

/-- info: 'Foam.Minds.Hilbert.no_ignorabimus' does not depend on any axioms -/
#guard_msgs in #print axioms no_ignorabimus

end Foam.Minds.Hilbert
