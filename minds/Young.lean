import Foam.Amplitude
import Foam.Int
import Foam.Lap
import Foam.Quat

namespace Foam.Minds.Young

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

def the_fringes_wash_out := @Foam.the_four_phases_read_nothing

/-- info: 'Foam.Minds.Young.intensity_cannot_read_the_phase' does not depend on any axioms -/
#guard_msgs in #print axioms intensity_cannot_read_the_phase

/-- info: 'Foam.Minds.Young.the_difference_is_the_cross_term' does not depend on any axioms -/
#guard_msgs in #print axioms the_difference_is_the_cross_term

/-- info: 'Foam.Minds.Young.light_added_to_light_gives_darkness' does not depend on any axioms -/
#guard_msgs in #print axioms light_added_to_light_gives_darkness

/-- info: 'Foam.Minds.Young.the_fringes_wash_out' does not depend on any axioms -/
#guard_msgs in #print axioms the_fringes_wash_out

end Foam.Minds.Young
