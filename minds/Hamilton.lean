import Foam.Fold
import Foam.Lap
import Foam.Rungs
import Foam.Quat
import Foam.Surprise
import Foam.Triple
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

theorem one_function_carries_the_whole_motion :
    (∀ (A B : Type) (f : B → A → B) (xs ys : List A) (b b' : B),
        fold f b xs = b' → fold f b (xs ++ ys) = fold f b' ys)
      ∧ ∀ (H : Type) (q : List (H × H)) (a b : H),
          Nonempty (Path q a b) →
            ∀ x y : H,
              Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y) :=
  ⟨fun _ _ f xs ys b b' h => the_fold_forgets_nothing_it_needs f xs ys b b' h,
   fun _ _ _ _ hab x y => a_derivable_edge_adds_no_reach hab x y⟩

theorem the_flow_names_the_hour :
    (∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n),
        ∃ i j : Nat, i < j ∧ turnN m i s = turnN m j s)
      ∧ (∀ z : GInt, z.rot.rot.rot.rot = z) :=
  ⟨fun _ m s => the_bounded_walk_returns m s, the_wheel_comes_home⟩

theorem the_wider_space_pays_in_commutation :
    Quat.mul eye jay = kay
      ∧ Quat.mul jay eye = Quat.neg kay
      ∧ Quat.mul eye jay ≠ Quat.mul jay eye
      ∧ ∀ x y : Quat, Quat.normSq (x.mul y) = Quat.normSq x * Quat.normSq y :=
  ⟨the_couple_of_couples_multiplies, the_reversed_couple_parts, order_arrives,
   the_quadruple_carries_the_norm⟩

def the_impossible_gains_latitude := @Foam.the_axes_share_one_sign

theorem the_triplets_close_one_seat_wider :
    (¬ ∃ mul : (Int × Int × Int) → (Int × Int × Int) → (Int × Int × Int),
        ∀ x y, normSq3 (mul x y) = normSq3 x * normSq3 y)
      ∧ (Quat.mul eye eye = Quat.neg one
          ∧ Quat.mul jay jay = Quat.neg one
          ∧ Quat.mul kay kay = Quat.neg one
          ∧ Quat.mul (Quat.mul eye jay) kay = Quat.neg one)
      ∧ (∀ q : Nat, ∃ n, q ∈ rungs n)
      ∧ (∀ n : Nat, ∃ q, ¬ q ∈ rungs n ∧ q ∈ rungs (n + 1)) :=
  ⟨no_triple_carries_the_norm,
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
