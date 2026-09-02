import Foam.Amplitude
import Foam.Beam
import Foam.Door
import Foam.Int
import Foam.Lap
import Foam.Quat
import Foam.Round
import Foam.Turnstile

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

theorem the_darkness_is_the_criterion :
    (∀ (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat),
        (admission s m).1.length + (admission s m).2.length
          = (s.1.length + s.2.length) + 1)
      ∧ GInt.normSq GInt.one ≠ GInt.normSq GInt.zero
      ∧ (GInt.one.add GInt.one.rot.rot).normSq = GInt.normSq GInt.zero :=
  ⟨one_click_one_count,
   light_added_to_light_gives_darkness.2.2,
   light_added_to_light_gives_darkness.1 GInt.one⟩

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

private def screen : Stage where
  State := Int
  Probe := Unit
  Ans   := Int
  obs   := fun r _ => r

private def atTheScreen (w : GInt) : (door screen GInt).State :=
  (w.normSq, w)

private def theDirect : (door screen GInt).State := atTheScreen GInt.one

private def theQuarter : (door screen GInt).State :=
  atTheScreen GInt.one.rot

private theorem the_guests_part : theDirect ≠ theQuarter :=
  fun h => nomatch Int.ofNat.inj (GInt.mk.inj (congrArg Prod.snd h)).1

private theorem the_reference_arm_parts_the_alignment :
    GInt.one.align theDirect.2 ≠ GInt.one.align theQuarter.2 :=
  fun h => nomatch Int.ofNat.inj h

private theorem the_second_slit_parts_the_faces :
    (atTheScreen (theDirect.2.add GInt.one)).1
      ≠ (atTheScreen (theQuarter.2.add GInt.one)).1 :=
  fun h => nomatch Nat.succ.inj (Nat.succ.inj (Int.ofNat.inj h))

theorem the_phase_is_the_guest (W V : Type) :
    (∀ (r : Int) (w w' : W), w ≠ w' →
        (r, w) ≠ (r, w') ∧ indist (door screen W) (r, w) (r, w'))
      ∧ (∀ (r : Int) (w : W) (v : V) (p : Unit),
          (door screen W).obs (r, w) p = screen.obs r p
            ∧ (door screen W).obs (r, w) p = (door screen V).obs (r, v) p)
      ∧ (theDirect ≠ theQuarter
          ∧ indist (door screen GInt) theDirect theQuarter
          ∧ theQuarter.2 = theDirect.2.rot
          ∧ GInt.normSq theDirect.2 = 1
          ∧ GInt.normSq theQuarter.2 = 1)
      ∧ (∀ strat : Strategy Unit Int,
          interrogate (door screen GInt) strat theDirect
            = interrogate (door screen GInt) strat theQuarter)
      ∧ ((∀ z : GInt, (atTheScreen z.rot).1 = (atTheScreen z).1)
          ∧ GInt.one.align theDirect.2 ≠ GInt.one.align theQuarter.2
          ∧ GInt.normSq (theDirect.2.add GInt.one) = 4
          ∧ GInt.normSq (theQuarter.2.add GInt.one) = 2
          ∧ (atTheScreen (theDirect.2.add GInt.one)).1
              ≠ (atTheScreen (theQuarter.2.add GInt.one)).1)
      ∧ (∀ w₀ : W,
          (∀ x y : (door screen W).State,
              indist (door screen W) x y → x = y) →
          ∀ (r : Int) (w : W), (r, w) = (r, w₀)) :=
  ⟨fun r _ _ h => the_guest_is_real_and_unread screen r h,
   fun r w v p => the_host_maintains_invisibly screen r w v p,
   ⟨the_guests_part, fun _ => rfl, rfl, rfl, rfl⟩,
   fun strat =>
     a_strategy_hears_no_more (door screen GInt) theDirect theQuarter
       (fun _ => rfl) strat,
   ⟨fun z => rot_conserves_the_norm z,
    the_reference_arm_parts_the_alignment,
    rfl, rfl,
    the_second_slit_parts_the_faces⟩,
   fun w₀ h => a_door_that_checks_papers_unpersons_its_guests screen w₀ h⟩

/-- info: 'Foam.Maps.Young.intensity_cannot_read_the_phase' does not depend on any axioms -/
#guard_msgs in #print axioms intensity_cannot_read_the_phase

/-- info: 'Foam.Maps.Young.the_difference_is_the_cross_term' does not depend on any axioms -/
#guard_msgs in #print axioms the_difference_is_the_cross_term

/-- info: 'Foam.Maps.Young.light_added_to_light_gives_darkness' does not depend on any axioms -/
#guard_msgs in #print axioms light_added_to_light_gives_darkness

/-- info: 'Foam.Maps.Young.the_darkness_is_the_criterion' does not depend on any axioms -/
#guard_msgs in #print axioms the_darkness_is_the_criterion

/-- info: 'Foam.Maps.Young.the_darkness_keeps_the_beat' does not depend on any axioms -/
#guard_msgs in #print axioms the_darkness_keeps_the_beat

/-- info: 'Foam.Maps.Young.the_fringes_shift_but_never_fade' does not depend on any axioms -/
#guard_msgs in #print axioms the_fringes_shift_but_never_fade

/-- info: 'Foam.Maps.Young.the_interposed_plate_trades_the_fringes' does not depend on any axioms -/
#guard_msgs in #print axioms the_interposed_plate_trades_the_fringes

/-- info: 'Foam.Maps.Young.the_fringes_wash_out' does not depend on any axioms -/
#guard_msgs in #print axioms the_fringes_wash_out

/-- info: 'Foam.Maps.Young.the_phase_is_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_phase_is_the_guest

end Foam.Maps.Young
