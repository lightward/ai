import Foam
import Foam.Engine
import Foam.Expectation
import Foam.Measure
import Foam.Source

namespace Foam.Minds.YoshikiKuramoto

def the_oscillator_is_its_phase := @Foam.the_implementation_stays_backstage

private def inPhase (p : Compass × Compass) : Prop := p.2 = p.1

private def spinAll (p : Compass × Compass) : Compass × Compass :=
  (p.1.step, p.2.step)

private def couple : Compass × Compass → Compass × Compass
  | (.n, .n) => (.e, .e)
  | (.n, .e) => (.e, .e)
  | (.n, .s) => (.e, .s)
  | (.n, .w) => (.e, .w)
  | (.e, .n) => (.s, .n)
  | (.e, .e) => (.s, .s)
  | (.e, .s) => (.s, .s)
  | (.e, .w) => (.s, .w)
  | (.s, .n) => (.w, .n)
  | (.s, .e) => (.w, .e)
  | (.s, .s) => (.w, .w)
  | (.s, .w) => (.w, .w)
  | (.w, .n) => (.n, .n)
  | (.w, .e) => (.n, .e)
  | (.w, .s) => (.n, .s)
  | (.w, .w) => (.n, .n)

private theorem the_turn_commutes : ∀ p : Compass × Compass,
    couple (spinAll p) = spinAll (couple p)
  | (.n, .n) => rfl
  | (.n, .e) => rfl
  | (.n, .s) => rfl
  | (.n, .w) => rfl
  | (.e, .n) => rfl
  | (.e, .e) => rfl
  | (.e, .s) => rfl
  | (.e, .w) => rfl
  | (.s, .n) => rfl
  | (.s, .e) => rfl
  | (.s, .s) => rfl
  | (.s, .w) => rfl
  | (.w, .n) => rfl
  | (.w, .e) => rfl
  | (.w, .s) => rfl
  | (.w, .w) => rfl

private theorem step_ne : ∀ c : Compass, Compass.step c ≠ c
  | .n => fun h => nomatch h
  | .e => fun h => nomatch h
  | .s => fun h => nomatch h
  | .w => fun h => nomatch h

private theorem the_turn_moves_every_posture :
    ∀ p : Compass × Compass, spinAll p ≠ p :=
  fun p h => step_ne p.1 (congrArg Prod.fst h)

theorem the_absolute_phase_is_the_remainder :
    (∀ p : Compass × Compass, couple (spinAll p) = spinAll (couple p))
      ∧ ∀ p : Compass × Compass, spinAll p ≠ p :=
  ⟨the_turn_commutes, the_turn_moves_every_posture⟩

private theorem lock_is_bare_ticking : ∀ p : Compass × Compass,
    inPhase p → couple p = (Compass.step p.1, Compass.step p.2)
  | (.n, .n), _ => rfl
  | (.e, .e), _ => rfl
  | (.s, .s), _ => rfl
  | (.w, .w), _ => rfl
  | (.n, .e), h => nomatch h
  | (.n, .s), h => nomatch h
  | (.n, .w), h => nomatch h
  | (.e, .n), h => nomatch h
  | (.e, .s), h => nomatch h
  | (.e, .w), h => nomatch h
  | (.s, .n), h => nomatch h
  | (.s, .e), h => nomatch h
  | (.s, .w), h => nomatch h
  | (.w, .n), h => nomatch h
  | (.w, .e), h => nomatch h
  | (.w, .s), h => nomatch h

private theorem the_lock_holds : ∀ p : Compass × Compass,
    inPhase p → inPhase (couple p)
  | (.n, .n), _ => rfl
  | (.e, .e), _ => rfl
  | (.s, .s), _ => rfl
  | (.w, .w), _ => rfl
  | (.n, .e), h => nomatch h
  | (.n, .s), h => nomatch h
  | (.n, .w), h => nomatch h
  | (.e, .n), h => nomatch h
  | (.e, .s), h => nomatch h
  | (.e, .w), h => nomatch h
  | (.s, .n), h => nomatch h
  | (.s, .e), h => nomatch h
  | (.s, .w), h => nomatch h
  | (.w, .n), h => nomatch h
  | (.w, .e), h => nomatch h
  | (.w, .s), h => nomatch h

private theorem one_lap_locks : ∀ p : Compass × Compass,
    inPhase (couple (couple (couple (couple p))))
  | (.n, .n) => rfl
  | (.n, .e) => rfl
  | (.n, .s) => rfl
  | (.n, .w) => rfl
  | (.e, .n) => rfl
  | (.e, .e) => rfl
  | (.e, .s) => rfl
  | (.e, .w) => rfl
  | (.s, .n) => rfl
  | (.s, .e) => rfl
  | (.s, .s) => rfl
  | (.s, .w) => rfl
  | (.w, .n) => rfl
  | (.w, .e) => rfl
  | (.w, .s) => rfl
  | (.w, .w) => rfl

theorem self_entrainment :
    (∀ p : Compass × Compass,
        inPhase p → couple p = (Compass.step p.1, Compass.step p.2))
      ∧ (∀ p : Compass × Compass, inPhase p → inPhase (couple p))
      ∧ ∀ p : Compass × Compass,
          inPhase (couple (couple (couple (couple p)))) :=
  ⟨lock_is_bare_ticking, the_lock_holds, one_lap_locks⟩

def the_order_parameter_is_a_reading := @Foam.aggregation_reads_the_reading

def the_drifting_tail_is_outweighed := @Foam.the_deviants_are_outweighed

def no_run_keeps_the_collective_time := @Foam.no_run_reads_its_own_ratio

/-- info: 'Foam.Minds.YoshikiKuramoto.the_oscillator_is_its_phase' does not depend on any axioms -/
#guard_msgs in #print axioms the_oscillator_is_its_phase

/-- info: 'Foam.Minds.YoshikiKuramoto.the_absolute_phase_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_absolute_phase_is_the_remainder

/-- info: 'Foam.Minds.YoshikiKuramoto.self_entrainment' does not depend on any axioms -/
#guard_msgs in #print axioms self_entrainment

/-- info: 'Foam.Minds.YoshikiKuramoto.the_order_parameter_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_order_parameter_is_a_reading

/-- info: 'Foam.Minds.YoshikiKuramoto.the_drifting_tail_is_outweighed' does not depend on any axioms -/
#guard_msgs in #print axioms the_drifting_tail_is_outweighed

/-- info: 'Foam.Minds.YoshikiKuramoto.no_run_keeps_the_collective_time' does not depend on any axioms -/
#guard_msgs in #print axioms no_run_keeps_the_collective_time

end Foam.Minds.YoshikiKuramoto
