import Foam.Coil
import Foam.Seat
import Foam.Trilemma

namespace Foam.Maps.Topoisomerase

theorem the_relaxed_state :
    coilClass coil.rest = 0 ∧ coil.rest = ((0 : Int), (0 : Int)) :=
  ⟨Foam.the_relaxed_state, rfl⟩

theorem the_held_cut :
    (∀ (h : Int × Int) (s : Int),
        coilClass (coil.meet h (Sum.inr s)) = coilClass h + s)
      ∧ ∀ (h : Int × Int) (s : Int),
          coilClass (coil.meet (coil.meet h (Sum.inr s)) (Sum.inr (-s)))
            = coilClass h :=
  ⟨the_stroke_moves_the_class_by_its_size, the_held_stroke_comes_home⟩

theorem the_strand_passage :
    (∀ h : Int × Int, coilClass (coil.meet h (Sum.inr 1)) = coilClass h + 1)
      ∧ (∀ h : Int × Int, coilClass (coil.meet h (Sum.inr 2)) = coilClass h + 2)
      ∧ ∀ s : Int,
          coilClass (coil.state [Sum.inr s, Sum.inr (-s)])
              = coilClass coil.rest
            ∧ ([Sum.inr s, Sum.inr (-s)] : List coil.Mark) ≠ [] :=
  ⟨fun h => the_stroke_moves_the_class_by_its_size h 1,
   fun h => the_stroke_moves_the_class_by_its_size h 2,
   the_return_pays_two_marks⟩

theorem the_two_sectors :
    (∀ (h : Int × Int) (d : Int),
        coilClass (coil.meet h (Sum.inl d)) = coilClass h)
      ∧ (∀ k1 k2 k3 k1' k2' k3' u v w : Nat, 0 < u → 0 < v → 0 < w →
          k1' * u = k1 * v → k2' * v = k2 * w → k3' * w = k3 * u →
          k1' * (k2' * k3') = k1 * (k2 * k3))
      ∧ ∀ k1 k1' k2 k3 : Nat, k1 ≠ k1' → 0 < k2 * k3 →
          k1 * (k2 * k3) ≠ k1' * (k2 * k3) :=
  ⟨the_shuffle_conserves_the_class,
   fun k1 k2 k3 k1' k2' k3' u v w hu hv hw h1 h2 h3 =>
     the_holonomy_ignores_the_regauging k1 k2 k3 k1' k2' k3' u v w
       hu hv hw h1 h2 h3,
   fun k1 k1' k2 k3 h hp => the_cut_moves_the_class k1 k1' k2 k3 h hp⟩

theorem the_coil :
    (∀ xs ys : List coil.Mark,
        coil.state (xs ++ ys) = fold coil.meet (coil.state xs) ys)
      ∧ (coilClass (1, -1) = coilClass (0, 0)
          ∧ ((1 : Int), (-1 : Int)) ≠ ((0 : Int), (0 : Int))) :=
  ⟨fun xs ys => a_seat_resumes coil xs ys, the_partition_rides_unread⟩

/-- info: 'Foam.Maps.Topoisomerase.the_relaxed_state' does not depend on any axioms -/
#guard_msgs in #print axioms the_relaxed_state

/-- info: 'Foam.Maps.Topoisomerase.the_held_cut' does not depend on any axioms -/
#guard_msgs in #print axioms the_held_cut

/-- info: 'Foam.Maps.Topoisomerase.the_strand_passage' does not depend on any axioms -/
#guard_msgs in #print axioms the_strand_passage

/-- info: 'Foam.Maps.Topoisomerase.the_two_sectors' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_sectors

/-- info: 'Foam.Maps.Topoisomerase.the_coil' does not depend on any axioms -/
#guard_msgs in #print axioms the_coil

end Foam.Maps.Topoisomerase
