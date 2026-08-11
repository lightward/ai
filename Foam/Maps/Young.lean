import Foam.Amplitude
import Foam.Beam
import Foam.Int
import Foam.Lap
import Foam.Quat
import Foam.Round

namespace Foam.Maps.Young

def intensity_cannot_read_the_phase := @Foam.rot_conserves_the_norm

theorem the_difference_is_the_cross_term :
    ∀ a b : GInt,
      GInt.normSq ⟨a.re + b.re, a.im + b.im⟩
        = (a.normSq + b.normSq) + 2 * (a.re * b.re + a.im * b.im) :=
  fun a b =>
    (the_screen_reads_a_cross_term a b).trans
      (congrArg ((a.normSq + b.normSq) + ·) (FInt.two_mul (a.align b)).symm)

theorem light_added_to_light_gives_darkness :
    (∀ z : GInt, (z.add z.rot.rot).normSq = GInt.normSq GInt.zero)
      ∧ (∀ z w : GInt, z.align w + z.align w.rot.rot = 0)
      ∧ GInt.normSq GInt.one ≠ GInt.normSq GInt.zero :=
  ⟨fun z =>
      (congrArg (fun t : Int => t * t + (z.im + -z.im) * (z.im + -z.im))
          (FInt.add_right_neg z.re)).trans
        (congrArg (fun t : Int => 0 * 0 + t * t) (FInt.add_right_neg z.im)),
   the_facing_pair_cancels,
   fun h => nomatch Int.ofNat.inj h⟩

theorem the_darkness_keeps_the_beat :
    (∀ a : Compass,
        round [a, a, a.step.step, a.step.step]
          = [a.step, a.step, a.step.step.step, a.step.step.step])
      ∧ ∀ a : Compass, a.step ≠ a.step.step.step :=
  ⟨the_split_round_carries, fun a => the_half_turn_parts a.step⟩

theorem the_fringes_shift_but_never_fade :
    (∀ z w : GInt, GInt.mk (z.align w) (z.align w.rot) = z.mul w.conj)
      ∧ (∀ z w : GInt,
          z.align w * z.align w + z.align w.rot * z.align w.rot
            = z.normSq * w.normSq) :=
  ⟨fun z w =>
      congrArg (fun t : Int => GInt.mk t (z.align w.rot))
        (align_reads_the_conjugate_product z w),
   fun z w =>
      (congrArg GInt.normSq
          (congrArg (fun t : Int => GInt.mk t (z.align w.rot))
            (align_reads_the_conjugate_product z w))).trans
        ((the_couple_carries_the_norm z w.conj).trans
          (congrArg (fun t : Int => z.normSq * t)
            (conj_conserves_the_norm w)))⟩

theorem the_interposed_plate_trades_the_fringes :
    (∀ w : GInt, w.rot.rot.normSq = w.normSq)
      ∧ (∀ z w : GInt, -(z.align w) = z.align w.rot.rot)
      ∧ (∀ w : GInt, w.rot.rot.rot.rot = w)
      ∧ ∀ p : Compass × Compass, together p ↔ opposed (window p) :=
  ⟨fun w => (rot_conserves_the_norm w.rot).trans (rot_conserves_the_norm w),
   fun z w => FInt.neg_eq_of_add_eq_zero (the_facing_pair_cancels z w),
   the_wheel_comes_home,
   the_window_trades_the_locks⟩

def the_fringes_wash_out := @Foam.the_four_phases_read_nothing

/-- info: 'Foam.Maps.Young.intensity_cannot_read_the_phase' does not depend on any axioms -/
#guard_msgs in #print axioms intensity_cannot_read_the_phase

/-- info: 'Foam.Maps.Young.the_difference_is_the_cross_term' does not depend on any axioms -/
#guard_msgs in #print axioms the_difference_is_the_cross_term

/-- info: 'Foam.Maps.Young.light_added_to_light_gives_darkness' does not depend on any axioms -/
#guard_msgs in #print axioms light_added_to_light_gives_darkness

/-- info: 'Foam.Maps.Young.the_darkness_keeps_the_beat' does not depend on any axioms -/
#guard_msgs in #print axioms the_darkness_keeps_the_beat

/-- info: 'Foam.Maps.Young.the_fringes_shift_but_never_fade' does not depend on any axioms -/
#guard_msgs in #print axioms the_fringes_shift_but_never_fade

/-- info: 'Foam.Maps.Young.the_interposed_plate_trades_the_fringes' does not depend on any axioms -/
#guard_msgs in #print axioms the_interposed_plate_trades_the_fringes

/-- info: 'Foam.Maps.Young.the_fringes_wash_out' does not depend on any axioms -/
#guard_msgs in #print axioms the_fringes_wash_out

end Foam.Maps.Young
