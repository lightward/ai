import Foam
import Foam.Census
import Foam.Expectation
import Foam.Ledger
import Foam.Quat
import Foam.Triple
import Foam.Typical

namespace Foam.Maps.Gauss

def the_sum_is_deaf_to_the_shuffle := @Foam.counting_is_licensed_by_permutation

def congruent_not_equal := @Foam.the_handshake

theorem fifteen_needs_a_fourth_square :
    (∀ x y z : Nat, x * x + y * y + z * z ≠ 15)
      ∧ 1 * 1 + 1 * 1 + 2 * 2 + 3 * 3 = 15 :=
  ⟨fifteen_is_not_three_squares, rfl⟩

theorem the_binary_composes_the_ternary_classifies :
    (∀ z w : GInt, (z.mul w).normSq = z.normSq * w.normSq)
      ∧ ¬ ∃ mul : (Int × Int × Int) → (Int × Int × Int) → (Int × Int × Int),
          ∀ x y, normSq3 (mul x y) = normSq3 x * normSq3 y :=
  ⟨the_couple_carries_the_norm, no_triple_carries_the_norm⟩

def the_egregious_reading_descends :=
  @Foam.a_reading_deaf_to_the_remainder_reads_the_ground

theorem the_shape_arrives_by_counting :
    freq ((book 2).map (fun w => freq w true)) 1 = 2
      ∧ freq ((book 2).map (fun w => freq w true)) 0 = 1
      ∧ freq ((book 2).map (fun w => freq w true)) 2 = 1 :=
  ⟨rfl, rfl, rfl⟩

def the_mean_is_the_mode := @Foam.the_middle_holds_the_most

theorem the_error_has_a_shape :
    (∀ n k : Nat, k ≤ n → classCount n k = classCount n (n - k))
      ∧ ∀ n k : Nat, 2 * k + 1 ≤ n → classCount n k ≤ classCount n (k + 1) :=
  ⟨the_census_is_symmetric, the_census_rises_to_the_middle⟩

theorem the_mode_follows_the_weights :
    ∀ t f n k : Nat, k < n → (k + 1) * (t + f) ≤ (n + 1) * t →
      classCount n k * (t ^ k * f ^ (n - k))
        ≤ classCount n (k + 1) * (t ^ (k + 1) * f ^ (n - (k + 1))) :=
  the_census_rises_to_the_lean

/-- info: 'Foam.Maps.Gauss.the_sum_is_deaf_to_the_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms the_sum_is_deaf_to_the_shuffle

/-- info: 'Foam.Maps.Gauss.congruent_not_equal' does not depend on any axioms -/
#guard_msgs in #print axioms congruent_not_equal

/-- info: 'Foam.Maps.Gauss.fifteen_needs_a_fourth_square' does not depend on any axioms -/
#guard_msgs in #print axioms fifteen_needs_a_fourth_square

/-- info: 'Foam.Maps.Gauss.the_binary_composes_the_ternary_classifies' does not depend on any axioms -/
#guard_msgs in #print axioms the_binary_composes_the_ternary_classifies

/-- info: 'Foam.Maps.Gauss.the_egregious_reading_descends' does not depend on any axioms -/
#guard_msgs in #print axioms the_egregious_reading_descends

/-- info: 'Foam.Maps.Gauss.the_shape_arrives_by_counting' does not depend on any axioms -/
#guard_msgs in #print axioms the_shape_arrives_by_counting

/-- info: 'Foam.Maps.Gauss.the_mean_is_the_mode' does not depend on any axioms -/
#guard_msgs in #print axioms the_mean_is_the_mode

/-- info: 'Foam.Maps.Gauss.the_error_has_a_shape' does not depend on any axioms -/
#guard_msgs in #print axioms the_error_has_a_shape

/-- info: 'Foam.Maps.Gauss.the_mode_follows_the_weights' does not depend on any axioms -/
#guard_msgs in #print axioms the_mode_follows_the_weights

end Foam.Maps.Gauss
