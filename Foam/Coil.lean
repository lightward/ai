import Foam.Amplitude
import Foam.Seat

namespace Foam

def coil : Seat where
  Mark := Int ⊕ Int
  Held := Int × Int
  rest := (0, 0)
  meet := fun h m =>
    match m with
    | .inl d => (h.1 - d, h.2 + d)
    | .inr s => (h.1 + s, h.2)

def coilClass (h : Int × Int) : Int := h.1 + h.2

theorem the_relaxed_state : coilClass coil.rest = 0 := rfl

theorem the_shuffle_conserves_the_class (h : Int × Int) (d : Int) :
    coilClass (coil.meet h (Sum.inl d)) = coilClass h := by
  show (h.1 - d) + (h.2 + d) = h.1 + h.2
  rw [Int.sub_eq_add_neg, swap_mid h.1 (-d) h.2 d,
      FInt.add_left_neg d, Int.add_zero]

theorem the_stroke_moves_the_class_by_its_size (h : Int × Int) (s : Int) :
    coilClass (coil.meet h (Sum.inr s)) = coilClass h + s := by
  show (h.1 + s) + h.2 = (h.1 + h.2) + s
  rw [FInt.add_assoc h.1 s h.2, int_add_comm s h.2,
      ← FInt.add_assoc h.1 h.2 s]

theorem the_held_stroke_comes_home (h : Int × Int) (s : Int) :
    coilClass (coil.meet (coil.meet h (Sum.inr s)) (Sum.inr (-s)))
      = coilClass h := by
  rw [the_stroke_moves_the_class_by_its_size,
      the_stroke_moves_the_class_by_its_size,
      FInt.add_assoc, FInt.add_right_neg, Int.add_zero]

theorem the_return_pays_two_marks (s : Int) :
    coilClass (coil.state [Sum.inr s, Sum.inr (-s)]) = coilClass coil.rest
      ∧ ([Sum.inr s, Sum.inr (-s)] : List coil.Mark) ≠ [] :=
  ⟨the_held_stroke_comes_home coil.rest s, fun h => nomatch h⟩

theorem the_partition_rides_unread :
    coilClass (1, -1) = coilClass (0, 0)
      ∧ ((1 : Int), (-1 : Int)) ≠ ((0 : Int), (0 : Int)) :=
  ⟨rfl, fun h => nomatch Int.ofNat.inj (congrArg Prod.fst h)⟩

/-- info: 'Foam.the_relaxed_state' does not depend on any axioms -/
#guard_msgs in #print axioms the_relaxed_state

/-- info: 'Foam.the_shuffle_conserves_the_class' does not depend on any axioms -/
#guard_msgs in #print axioms the_shuffle_conserves_the_class

/-- info: 'Foam.the_stroke_moves_the_class_by_its_size' does not depend on any axioms -/
#guard_msgs in #print axioms the_stroke_moves_the_class_by_its_size

/-- info: 'Foam.the_held_stroke_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_held_stroke_comes_home

/-- info: 'Foam.the_return_pays_two_marks' does not depend on any axioms -/
#guard_msgs in #print axioms the_return_pays_two_marks

/-- info: 'Foam.the_partition_rides_unread' does not depend on any axioms -/
#guard_msgs in #print axioms the_partition_rides_unread

end Foam
