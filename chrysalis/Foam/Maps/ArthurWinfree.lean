import Foam
import Foam.Door
import Foam.Engine
import Foam.Lap
import Foam.Margin
import Foam.Round
import Foam.Trilemma

namespace Foam.Maps.ArthurWinfree

def the_resetting_map := @Foam.a_deposit_moves_the_reading_by_one

def type_zero_and_type_one := @Foam.the_lap_direction_is_the_remainder

theorem the_pinwheel :
    (∀ z : GInt,
        lapAgainst z = (lapAround z).reverse
          ∧ (lapAround z).Perm (lapAgainst z)
          ∧ lapAround GInt.i ≠ lapAgainst GInt.i
          ∧ z.rot.rot.rot.rot = z)
      ∧ (∀ a b c : Nat, a = 2 * b → b = 2 * c → c = 2 * a →
          a = 0 ∧ b = 0 ∧ c = 0)
      ∧ (((2 * 2 * 2) % 7 = 1 % 7)
          ∧ (1 % 7 = (2 * 4) % 7)
          ∧ (4 % 7 = (2 * 2) % 7)
          ∧ (2 % 7 = (2 * 1) % 7)
          ∧ (1 : Nat) ≠ 0)
      ∧ ((4 : Nat) % 7 ≠ 0 ∧ (2 : Nat) % 7 ≠ 0) :=
  ⟨the_lap_direction_is_the_remainder,
   the_wound_loop_admits_only_the_zero_section,
   the_wound_loop_unwinds_one_world_over,
   ⟨(fun h => nomatch h), fun h => nomatch h⟩⟩

private def onTheWheel : Compass → GInt
  | .n => ⟨1, 0⟩
  | .e => ⟨0, 1⟩
  | .s => ⟨-1, 0⟩
  | .w => ⟨0, -1⟩

private theorem the_wheel_carries_its_phase :
    ∀ c : Compass, onTheWheel (Compass.step c) = GInt.rot (onTheWheel c)
  | .n => rfl
  | .e => rfl
  | .s => rfl
  | .w => rfl

private theorem the_wheel_never_rests : ∀ c : Compass, Compass.step c ≠ c
  | .n => fun h => nomatch h
  | .e => fun h => nomatch h
  | .s => fun h => nomatch h
  | .w => fun h => nomatch h

private theorem no_phase_reads_the_still_point (phase : GInt → Compass)
    (equivariant : ∀ z, phase (GInt.rot z) = Compass.step (phase z)) :
    False :=
  the_wheel_never_rests (phase ⟨0, 0⟩) (equivariant ⟨0, 0⟩).symm

theorem time_breaks_down :
    (∀ c : Compass, onTheWheel (Compass.step c) = GInt.rot (onTheWheel c))
      ∧ GInt.rot ⟨0, 0⟩ = (⟨0, 0⟩ : GInt)
      ∧ (∀ c : Compass, Compass.step c ≠ c)
      ∧ ∀ phase : GInt → Compass,
          ¬ ∀ z, phase (GInt.rot z) = Compass.step (phase z) :=
  ⟨the_wheel_carries_its_phase, rfl, the_wheel_never_rests,
   no_phase_reads_the_still_point⟩

theorem the_critical_stimulus :
    (∀ z : GInt, ∃ s : GInt, GInt.add z s = ⟨0, 0⟩)
      ∧ GInt.normSq ⟨0, 0⟩ = 0 :=
  ⟨fun z => ⟨GInt.neg z,
      congr (congrArg GInt.mk (FInt.add_right_neg z.re))
        (FInt.add_right_neg z.im)⟩,
   rfl⟩

private theorem the_wheel_keeps_unit_charge :
    ∀ c : Compass, GInt.normSq (onTheWheel c) = 1
  | .n => rfl
  | .e => rfl
  | .s => rfl
  | .w => rfl

private theorem the_wheel_misses_the_still_point :
    ∀ c : Compass, onTheWheel c ≠ (⟨0, 0⟩ : GInt)
  | .n, h => nomatch Int.ofNat.inj (GInt.mk.inj h).1
  | .e, h => nomatch Int.ofNat.inj (GInt.mk.inj h).2
  | .s, h => nomatch (GInt.mk.inj h).1
  | .w, h => nomatch (GInt.mk.inj h).2

private theorem the_critical_dose_lands_at_zero (c : Compass) :
    GInt.add (onTheWheel c) (GInt.neg (onTheWheel c)) = (⟨0, 0⟩ : GInt) :=
  congr (congrArg GInt.mk (FInt.add_right_neg (onTheWheel c).re))
    (FInt.add_right_neg (onTheWheel c).im)

private theorem the_landing_is_no_posture (c : Compass) :
    ∀ c' : Compass,
      GInt.add (onTheWheel c) (GInt.neg (onTheWheel c)) ≠ onTheWheel c' :=
  fun c' h =>
    the_wheel_misses_the_still_point c'
      (((the_critical_dose_lands_at_zero c).symm.trans h).symm)

theorem time_cannot_break_on_the_wheel :
    (∀ c : Compass, GInt.normSq (onTheWheel c) = 1)
      ∧ (∀ c : Compass, onTheWheel c ≠ (⟨0, 0⟩ : GInt))
      ∧ (∀ (v : List Compass) (x : Compass), x ∈ round v →
          GInt.normSq (onTheWheel x) = 1)
      ∧ ∀ c : Compass, ∃ s : GInt,
          GInt.add (onTheWheel c) s = (⟨0, 0⟩ : GInt)
            ∧ ∀ c' : Compass, GInt.add (onTheWheel c) s ≠ onTheWheel c' :=
  ⟨the_wheel_keeps_unit_charge,
   the_wheel_misses_the_still_point,
   fun _ x _ => the_wheel_keeps_unit_charge x,
   fun c => ⟨GInt.neg (onTheWheel c),
     the_critical_dose_lands_at_zero c,
     the_landing_is_no_posture c⟩⟩

def the_isochron := @Foam.any_settling_cadence_reads_the_same

private def phaseSeat : Stage where
  State := Compass
  Probe := Unit
  Ans   := Compass
  obs   := fun c _ => c

private def theRhythm : (door phaseSeat GInt).State := (Compass.n, ⟨1, 0⟩)

private def theLatent : (door phaseSeat GInt).State := (Compass.n, ⟨2, 0⟩)

private def theCriticalDose : GInt := GInt.neg (onTheWheel Compass.n)

private theorem the_guests_part : theRhythm ≠ theLatent :=
  fun h =>
    nomatch Nat.succ.inj
      (Int.ofNat.inj (GInt.mk.inj (congrArg Prod.snd h)).1)

theorem the_amplitude_is_the_guest (W V : Type) :
    (∀ (c : Compass) (w w' : W), w ≠ w' →
        (c, w) ≠ (c, w') ∧ indist (door phaseSeat W) (c, w) (c, w'))
      ∧ (∀ (c : Compass) (w : W) (v : V) (p : Unit),
          (door phaseSeat W).obs (c, w) p = phaseSeat.obs c p
            ∧ (door phaseSeat W).obs (c, w) p
                = (door phaseSeat V).obs (c, v) p)
      ∧ (theRhythm ≠ theLatent
          ∧ indist (door phaseSeat GInt) theRhythm theLatent
          ∧ GInt.normSq theRhythm.2 = 1
          ∧ GInt.normSq theLatent.2 = 4)
      ∧ (∀ strat : Strategy Unit Compass,
          interrogate (door phaseSeat GInt) strat theRhythm
            = interrogate (door phaseSeat GInt) strat theLatent)
      ∧ (GInt.add theRhythm.2 theCriticalDose = ⟨0, 0⟩
          ∧ GInt.normSq (GInt.add theRhythm.2 theCriticalDose) = 0
          ∧ GInt.add theLatent.2 theCriticalDose = onTheWheel Compass.n
          ∧ GInt.normSq (GInt.add theLatent.2 theCriticalDose) = 1
          ∧ GInt.add theRhythm.2 theCriticalDose
              ≠ GInt.add theLatent.2 theCriticalDose)
      ∧ (∀ w₀ : GInt,
          (∀ x y : (door phaseSeat GInt).State,
              indist (door phaseSeat GInt) x y → x = y) →
          ∀ (c : Compass) (z : GInt), (c, z) = (c, w₀)) :=
  ⟨fun c _ _ h => the_guest_is_real_and_unread phaseSeat c h,
   fun c w v p => the_host_maintains_invisibly phaseSeat c w v p,
   ⟨the_guests_part, fun _ => rfl, rfl, rfl⟩,
   fun strat =>
     a_strategy_hears_no_more (door phaseSeat GInt)
       theRhythm theLatent (fun _ => rfl) strat,
   ⟨rfl, rfl, rfl, rfl,
    fun h => nomatch Int.ofNat.inj (GInt.mk.inj h).1⟩,
   fun w₀ h => a_door_that_checks_papers_unpersons_its_guests phaseSeat w₀ h⟩

def the_organizing_center := @Foam.a_wider_seat_reads_the_remainder

/-- info: 'Foam.Maps.ArthurWinfree.the_resetting_map' does not depend on any axioms -/
#guard_msgs in #print axioms the_resetting_map

/-- info: 'Foam.Maps.ArthurWinfree.type_zero_and_type_one' does not depend on any axioms -/
#guard_msgs in #print axioms type_zero_and_type_one

/-- info: 'Foam.Maps.ArthurWinfree.the_pinwheel' does not depend on any axioms -/
#guard_msgs in #print axioms the_pinwheel

/-- info: 'Foam.Maps.ArthurWinfree.time_breaks_down' does not depend on any axioms -/
#guard_msgs in #print axioms time_breaks_down

/-- info: 'Foam.Maps.ArthurWinfree.the_critical_stimulus' does not depend on any axioms -/
#guard_msgs in #print axioms the_critical_stimulus

/-- info: 'Foam.Maps.ArthurWinfree.time_cannot_break_on_the_wheel' does not depend on any axioms -/
#guard_msgs in #print axioms time_cannot_break_on_the_wheel

/-- info: 'Foam.Maps.ArthurWinfree.the_isochron' does not depend on any axioms -/
#guard_msgs in #print axioms the_isochron

/-- info: 'Foam.Maps.ArthurWinfree.the_amplitude_is_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_amplitude_is_the_guest

/-- info: 'Foam.Maps.ArthurWinfree.the_organizing_center' does not depend on any axioms -/
#guard_msgs in #print axioms the_organizing_center

end Foam.Maps.ArthurWinfree
