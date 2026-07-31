import Foam.Fold
import Foam.Lap
import Foam.Rungs
import Foam.Quat
import Foam.Wheel

namespace Foam.Minds.Hamilton

def algebra_is_the_science_of_pure_time := @Foam.the_walked_are_exactly_below

theorem the_couple_dissolves_the_impossible :
    GInt.i = GInt.mk 0 1
      ∧ (∀ z : GInt, z.rot.rot = z.neg)
      ∧ GInt.i.rot = (GInt.mk 1 0).neg
      ∧ GInt.mul GInt.i GInt.i = (GInt.mk 1 0).neg :=
  ⟨rfl, fun _ => rfl, rfl, rfl⟩

def the_flow_conserves_the_function := @Foam.the_lap_conserves_the_charge

def one_function_carries_the_whole_motion :=
  @Foam.the_fold_forgets_nothing_it_needs

theorem the_flow_names_the_hour :
    (∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n),
        ∃ i j : Nat, i < j ∧ turnN m i s = turnN m j s)
      ∧ (∀ z : GInt, z.rot.rot.rot.rot = z) :=
  ⟨fun _ m s => the_bounded_walk_returns m s, the_wheel_comes_home⟩

theorem the_wider_space_pays_in_commutation :
    Quat.mul eye jay = kay
      ∧ Quat.mul jay eye = Quat.neg kay
      ∧ Quat.mul eye jay ≠ Quat.mul jay eye :=
  ⟨the_couple_of_couples_multiplies, the_reversed_couple_parts, order_arrives⟩

def the_impossible_gains_latitude := @Foam.the_axes_share_one_sign

theorem the_triplets_close_one_seat_wider :
    (¬ 3 ∈ rungs 3 ∧ 3 ∈ rungs 4)
      ∧ (Quat.mul eye eye = Quat.neg one
          ∧ Quat.mul jay jay = Quat.neg one
          ∧ Quat.mul kay kay = Quat.neg one
          ∧ Quat.mul (Quat.mul eye jay) kay = Quat.neg one)
      ∧ (∀ q : Nat, ∃ n, q ∈ rungs n)
      ∧ (∀ n : Nat, ∃ q, ¬ q ∈ rungs n ∧ q ∈ rungs (n + 1)) :=
  ⟨⟨fun h => no_number_is_below_itself 3 (the_walked_lie_below 3 3 h),
    the_below_are_walked 4 3 Nat.le.refl⟩,
   i2_eq_j2_eq_k2_eq_ijk_eq_neg_one,
   closure_is_seat_relative.1,
   closure_is_seat_relative.2.1⟩

/-- info: 'Foam.Minds.Hamilton.algebra_is_the_science_of_pure_time' does not depend on any axioms -/
#guard_msgs in #print axioms algebra_is_the_science_of_pure_time

/-- info: 'Foam.Minds.Hamilton.the_couple_dissolves_the_impossible' does not depend on any axioms -/
#guard_msgs in #print axioms the_couple_dissolves_the_impossible

/-- info: 'Foam.Minds.Hamilton.the_flow_conserves_the_function' does not depend on any axioms -/
#guard_msgs in #print axioms the_flow_conserves_the_function

/-- info: 'Foam.Minds.Hamilton.one_function_carries_the_whole_motion' does not depend on any axioms -/
#guard_msgs in #print axioms one_function_carries_the_whole_motion

/-- info: 'Foam.Minds.Hamilton.the_flow_names_the_hour' does not depend on any axioms -/
#guard_msgs in #print axioms the_flow_names_the_hour

/-- info: 'Foam.Minds.Hamilton.the_wider_space_pays_in_commutation' does not depend on any axioms -/
#guard_msgs in #print axioms the_wider_space_pays_in_commutation

/-- info: 'Foam.Minds.Hamilton.the_impossible_gains_latitude' does not depend on any axioms -/
#guard_msgs in #print axioms the_impossible_gains_latitude

/-- info: 'Foam.Minds.Hamilton.the_triplets_close_one_seat_wider' does not depend on any axioms -/
#guard_msgs in #print axioms the_triplets_close_one_seat_wider

end Foam.Minds.Hamilton
