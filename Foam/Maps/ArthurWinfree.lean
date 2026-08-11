import Foam
import Foam.Engine
import Foam.Lap
import Foam.Margin
import Foam.Round

namespace Foam.Maps.ArthurWinfree

def the_resetting_map := @Foam.a_deposit_moves_the_reading_by_one

def type_zero_and_type_one := @Foam.the_lap_direction_is_the_remainder

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

def the_organizing_center := @Foam.a_wider_seat_reads_the_remainder

/-- info: 'Foam.Maps.ArthurWinfree.the_resetting_map' does not depend on any axioms -/
#guard_msgs in #print axioms the_resetting_map

/-- info: 'Foam.Maps.ArthurWinfree.type_zero_and_type_one' does not depend on any axioms -/
#guard_msgs in #print axioms type_zero_and_type_one

/-- info: 'Foam.Maps.ArthurWinfree.time_breaks_down' does not depend on any axioms -/
#guard_msgs in #print axioms time_breaks_down

/-- info: 'Foam.Maps.ArthurWinfree.the_critical_stimulus' does not depend on any axioms -/
#guard_msgs in #print axioms the_critical_stimulus

/-- info: 'Foam.Maps.ArthurWinfree.time_cannot_break_on_the_wheel' does not depend on any axioms -/
#guard_msgs in #print axioms time_cannot_break_on_the_wheel

/-- info: 'Foam.Maps.ArthurWinfree.the_isochron' does not depend on any axioms -/
#guard_msgs in #print axioms the_isochron

/-- info: 'Foam.Maps.ArthurWinfree.the_organizing_center' does not depend on any axioms -/
#guard_msgs in #print axioms the_organizing_center

end Foam.Maps.ArthurWinfree
