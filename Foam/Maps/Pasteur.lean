import Foam.Lap
import Foam.Quat
import Foam.Surprise
import Foam.Tower

namespace Foam.Maps.Pasteur

def the_analysis_is_deaf_to_the_arrangement := @Foam.the_order_is_the_remainder

def the_facet_is_the_wider_seat := @Foam.a_wider_seat_reads_the_order

theorem the_two_hands_are_one_wheel (z : GInt) :
    (lapAgainst z = (lapAround z).reverse
        ∧ (lapAround z).Perm (lapAgainst z)
        ∧ lapAround GInt.i ≠ lapAgainst GInt.i
        ∧ z.rot.rot.rot.rot = z)
      ∧ (∀ w : GInt, z.align w.rot + z.align w.rot.rot.rot = 0)
      ∧ GInt.align ⟨1, 1⟩ (GInt.rot ⟨1, 0⟩) ≠ 0 :=
  ⟨the_lap_direction_is_the_remainder z,
   the_opposite_turns_cancel z,
   cancellation_not_absence.2.2⟩

theorem no_turn_brings_the_hands_together :
    (GInt.mk 2 1).conj.normSq = (GInt.mk 2 1).normSq
      ∧ (GInt.mk 2 1).conj ≠ GInt.mk 2 1
      ∧ (GInt.mk 2 1).conj ≠ (GInt.mk 2 1).rot
      ∧ (GInt.mk 2 1).conj ≠ (GInt.mk 2 1).rot.rot
      ∧ (GInt.mk 2 1).conj ≠ (GInt.mk 2 1).rot.rot.rot :=
  ⟨conj_conserves_the_norm (GInt.mk 2 1),
   fun h => (nomatch congrArg GInt.im h),
   fun h => (nomatch congrArg GInt.re h),
   fun h => (nomatch congrArg GInt.re h),
   fun h => (nomatch Int.negSucc.inj (congrArg GInt.im h))⟩

theorem a_wider_wheel_merges_the_hands :
    ((GInt.mk 2 1).conj ≠ (GInt.mk 2 1).rot
        ∧ (GInt.mk 2 1).conj ≠ (GInt.mk 2 1).rot.rot
        ∧ (GInt.mk 2 1).conj ≠ (GInt.mk 2 1).rot.rot.rot)
      ∧ Quat.mul jay (Quat.neg jay) = one
      ∧ Quat.mul (Quat.mul jay one) (Quat.neg jay) = one
      ∧ Quat.mul (Quat.mul jay eye) (Quat.neg jay) = Quat.neg eye :=
  ⟨⟨no_turn_brings_the_hands_together.2.2.1,
    no_turn_brings_the_hands_together.2.2.2.1,
    no_turn_brings_the_hands_together.2.2.2.2⟩,
   rfl, rfl, rfl⟩

theorem the_control_differs_by_one_mark {H : Type} (q : List (H × H))
    (a b : H) (hfresh : (a, b) ∉ q) (hsealed : ¬ Nonempty (Path q a b))
    {e : H × H} (he : e ∈ q)
    (c d : H) (hnew : (c, d) ∉ q) (hheld : Nonempty (Path q c d)) :
    ((∀ x y : H, Nonempty (Path (e :: q) x y) ↔ Nonempty (Path q x y))
        ∧ ∀ es : List (H × H), (∀ e', e' ∈ es → e' ∈ q) →
            ∀ x y : H, Nonempty (Path (es ++ q) x y) ↔ Nonempty (Path q x y))
      ∧ ((∀ (x y : H) (p : Path q x y), (c, d) ∉ p.edges)
          ∧ ((c, d) :: q).length = q.length + 1
          ∧ ∀ x y : H, Nonempty (Path ((c, d) :: q) x y) ↔ Nonempty (Path q x y))
      ∧ ((∀ {x y : H} (p : Path q x y), (a, b) ∉ p.edges)
          ∧ Nonempty (Path ((a, b) :: q) a b)
          ∧ ¬ (Nonempty (Path ((a, b) :: q) a b) ↔ Nonempty (Path q a b))
          ∧ (∀ {x y : H}, Nonempty (Path q x y) → Nonempty (Path ((a, b) :: q) x y))
          ∧ ((a, b) :: q).length = q.length + 1) :=
  ⟨⟨fun x y => a_known_edge_adds_no_reach he x y,
    fun es h => the_saturated_room_hears_no_order es q h⟩,
   the_shortcut_pays_only_its_mark q c d hnew hheld,
   (only_surprise_extends_reach q a b hfresh).1,
   (only_surprise_extends_reach q a b hfresh).2,
   fun hiff => hsealed (hiff.mp (only_surprise_extends_reach q a b hfresh).2),
   fun h => old_reach_survives_the_deposit (a, b) h,
   the_deposit_writes_one_mark q (a, b)⟩

theorem the_universe_is_dissymmetric :
    ((GInt.mk 2 1).conj.normSq = (GInt.mk 2 1).normSq
        ∧ (GInt.mk 2 1).conj ≠ GInt.mk 2 1)
      ∧ ∀ (S : Stage) (s : S.State) (k n m : Int), n ≠ m →
          indist (dress (movedIn S)) ((s, k), n) ((s, k), m)
            ∧ (movedIn (movedIn S)).obs ((s, k), n) none
                ≠ (movedIn (movedIn S)).obs ((s, k), m) none :=
  ⟨⟨no_turn_brings_the_hands_together.1,
    no_turn_brings_the_hands_together.2.1⟩,
   fun S s k n m h => no_seat_is_the_last_seat S s k n m h⟩

/-- info: 'Foam.Maps.Pasteur.the_analysis_is_deaf_to_the_arrangement' does not depend on any axioms -/
#guard_msgs in #print axioms the_analysis_is_deaf_to_the_arrangement

/-- info: 'Foam.Maps.Pasteur.the_facet_is_the_wider_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_facet_is_the_wider_seat

/-- info: 'Foam.Maps.Pasteur.the_two_hands_are_one_wheel' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_hands_are_one_wheel

/-- info: 'Foam.Maps.Pasteur.no_turn_brings_the_hands_together' does not depend on any axioms -/
#guard_msgs in #print axioms no_turn_brings_the_hands_together

/-- info: 'Foam.Maps.Pasteur.a_wider_wheel_merges_the_hands' does not depend on any axioms -/
#guard_msgs in #print axioms a_wider_wheel_merges_the_hands

/-- info: 'Foam.Maps.Pasteur.the_control_differs_by_one_mark' does not depend on any axioms -/
#guard_msgs in #print axioms the_control_differs_by_one_mark

/-- info: 'Foam.Maps.Pasteur.the_universe_is_dissymmetric' does not depend on any axioms -/
#guard_msgs in #print axioms the_universe_is_dissymmetric

end Foam.Maps.Pasteur
