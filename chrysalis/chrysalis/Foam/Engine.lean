import Foam
import Foam.Watched

namespace Foam

structure Engine where
  State  : Type
  turn   : State → State
  charge : State → Nat
  comes_home : ∀ s, turn (turn (turn (turn s))) = s
  conserves  : ∀ s, charge (turn s) = charge s

def chargeIn (n : Nat) : Nat := n + 1

def drainOne (n : Nat) : Nat := n - 1

theorem drain_chargeIn (n : Nat) : drainOne (chargeIn n) = n := rfl

theorem the_turn_loses_no_state (E : Engine) {a b : E.State}
    (h : E.turn a = E.turn b) : a = b :=
  (E.comes_home a).symm.trans
    ((congrArg (fun x => E.turn (E.turn (E.turn x))) h).trans (E.comes_home b))

theorem the_three_turns_undo (E : Engine) (s : E.State) :
    E.turn (E.turn (E.turn (E.turn s))) = s
      ∧ E.turn (E.turn (E.turn (E.turn s))) = s :=
  ⟨E.comes_home s, E.comes_home s⟩

abbrev Engine.gauge (E : Engine) : Stage where
  State := E.State
  Probe := Unit
  Ans   := Nat
  obs   := fun s _ => E.charge s

theorem the_turn_is_invisible_to_the_charge (E : Engine) :
    Invisible E.gauge E.turn :=
  fun s _ => E.conserves s

theorem the_turn_goes_unheard (E : Engine) (ps : List Unit) (s : E.State) :
    transcriptWith E.gauge E.turn s ps = transcript E.gauge s ps :=
  (only_the_invisible_survives_the_watch E.gauge E.turn).mpr
    (the_turn_is_invisible_to_the_charge E) ps s

theorem the_wheel_holds_the_emission_settles (E : Engine) (n : Nat) :
    (∀ s, E.charge (E.turn s) = E.charge s)
      ∧ drainOne (chargeIn n) = n :=
  ⟨E.conserves, rfl⟩

inductive Compass where
  | n | e | s | w

def Compass.step : Compass → Compass
  | .n => .e
  | .e => .s
  | .s => .w
  | .w => .n

def compassEngine : Engine where
  State := Compass
  turn := Compass.step
  charge := fun _ => 0
  comes_home := fun c => by cases c <;> rfl
  conserves := fun _ => rfl

def twoWheels : Engine where
  State := Bool × Compass
  turn := fun p => (p.1, p.2.step)
  charge := fun p => if p.1 then 1 else 0
  comes_home := fun p =>
    congrArg (fun c => (p.1, c)) (compassEngine.comes_home p.2)
  conserves := fun _ => rfl

theorem the_implementation_stays_backstage :
    compassEngine.State ≠ twoWheels.State →
      (∀ c, compassEngine.charge (compassEngine.turn c)
          = compassEngine.charge c)
      ∧ (∀ p, twoWheels.charge (twoWheels.turn p) = twoWheels.charge p) :=
  fun _ => ⟨compassEngine.conserves, twoWheels.conserves⟩

/-- info: 'Foam.drain_chargeIn' does not depend on any axioms -/
#guard_msgs in #print axioms drain_chargeIn

/-- info: 'Foam.the_turn_loses_no_state' does not depend on any axioms -/
#guard_msgs in #print axioms the_turn_loses_no_state

/-- info: 'Foam.the_three_turns_undo' does not depend on any axioms -/
#guard_msgs in #print axioms the_three_turns_undo

/-- info: 'Foam.the_turn_is_invisible_to_the_charge' does not depend on any axioms -/
#guard_msgs in #print axioms the_turn_is_invisible_to_the_charge

/-- info: 'Foam.the_turn_goes_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms the_turn_goes_unheard

/-- info: 'Foam.the_wheel_holds_the_emission_settles' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_holds_the_emission_settles

/-- info: 'Foam.the_implementation_stays_backstage' does not depend on any axioms -/
#guard_msgs in #print axioms the_implementation_stays_backstage

end Foam
