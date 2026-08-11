import Foam
import Foam.Engine
import Foam.Expectation
import Foam.Measure
import Foam.Round
import Foam.Source

namespace Foam.Maps.YoshikiKuramoto

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

private def lagPull : Compass → Compass → Compass
  | .n, .n => .n
  | .n, .e => .n
  | .n, .s => .w
  | .n, .w => .e
  | .e, .n => .s
  | .e, .e => .e
  | .e, .s => .e
  | .e, .w => .n
  | .s, .n => .e
  | .s, .e => .w
  | .s, .s => .s
  | .s, .w => .s
  | .w, .n => .w
  | .w, .e => .s
  | .w, .s => .n
  | .w, .w => .w

private def zipLag : List Compass → List Compass → List Compass
  | c :: cs, d :: ds => lagPull c d :: zipLag cs ds
  | [], _ => []
  | _ :: _, [] => []

private def lagRound (v : List Compass) : List Compass := zipLag v (rotateLeft v)

private def chimera : Nat → List Compass
  | 0 => [.n, .n, .n, .n, .e]
  | n + 1 => lagRound (chimera n)

private def readAt : List Compass → Nat → Option Compass
  | [], _ => none
  | c :: _, 0 => some c
  | _ :: cs, n + 1 => readAt cs n

private theorem the_lag_hears_only_the_gap :
    ∀ c d : Compass, lagPull c.step d.step = (lagPull c d).step
  | .n, .n => rfl
  | .n, .e => rfl
  | .n, .s => rfl
  | .n, .w => rfl
  | .e, .n => rfl
  | .e, .e => rfl
  | .e, .s => rfl
  | .e, .w => rfl
  | .s, .n => rfl
  | .s, .e => rfl
  | .s, .s => rfl
  | .s, .w => rfl
  | .w, .n => rfl
  | .w, .e => rfl
  | .w, .s => rfl
  | .w, .w => rfl

private theorem the_lag_lets_unison_rest : ∀ c : Compass, lagPull c c = c
  | .n => rfl
  | .e => rfl
  | .s => rfl
  | .w => rfl

private theorem the_lap_returns : ∀ n : Nat, chimera (n + 6) = chimera n
  | 0 => rfl
  | n + 1 => congrArg lagRound (the_lap_returns n)

private def OnTheLap (v : List Compass) : Prop :=
  v = chimera 0 ∨ v = chimera 1 ∨ v = chimera 2
    ∨ v = chimera 3 ∨ v = chimera 4 ∨ v = chimera 5

private theorem the_lap_carries : ∀ v, OnTheLap v → OnTheLap (lagRound v)
  | _, .inl rfl => .inr (.inl rfl)
  | _, .inr (.inl rfl) => .inr (.inr (.inl rfl))
  | _, .inr (.inr (.inl rfl)) => .inr (.inr (.inr (.inl rfl)))
  | _, .inr (.inr (.inr (.inl rfl))) => .inr (.inr (.inr (.inr (.inl rfl))))
  | _, .inr (.inr (.inr (.inr (.inl rfl)))) =>
      .inr (.inr (.inr (.inr (.inr rfl))))
  | _, .inr (.inr (.inr (.inr (.inr rfl)))) => .inl rfl

private theorem every_beat_is_on_the_lap : ∀ n : Nat, OnTheLap (chimera n)
  | 0 => .inl rfl
  | n + 1 => the_lap_carries (chimera n) (every_beat_is_on_the_lap n)

private theorem the_locked_pair_holds : ∀ v, OnTheLap v →
    ∃ x, readAt v 0 = some x ∧ readAt v 1 = some x
  | _, .inl rfl => ⟨.n, rfl, rfl⟩
  | _, .inr (.inl rfl) => ⟨.n, rfl, rfl⟩
  | _, .inr (.inr (.inl rfl)) => ⟨.n, rfl, rfl⟩
  | _, .inr (.inr (.inr (.inl rfl))) => ⟨.n, rfl, rfl⟩
  | _, .inr (.inr (.inr (.inr (.inl rfl)))) => ⟨.n, rfl, rfl⟩
  | _, .inr (.inr (.inr (.inr (.inr rfl)))) => ⟨.n, rfl, rfl⟩

theorem coherence_coexists_with_incoherence :
    (∀ c d : Compass, lagPull c.step d.step = (lagPull c d).step)
      ∧ (∀ c : Compass, lagPull c c = c)
      ∧ (∀ n : Nat, chimera (n + 6) = chimera n)
      ∧ (∀ n : Nat, ∃ x, readAt (chimera n) 0 = some x
            ∧ readAt (chimera n) 1 = some x)
      ∧ (∃ n x, readAt (chimera n) 2 = some x
            ∧ readAt (chimera n) 3 = some x)
      ∧ (∃ n x, readAt (chimera n) 2 = some x
            ∧ readAt (chimera n) 3 = some x.step)
      ∧ (∃ n x, readAt (chimera n) 2 = some x
            ∧ readAt (chimera n) 3 = some x.step.step ∧ x ≠ x.step.step)
      ∧ ∃ n x, readAt (chimera n) 2 = some x
            ∧ readAt (chimera n) 3 = some x.step.step.step :=
  ⟨the_lag_hears_only_the_gap,
   the_lag_lets_unison_rest,
   the_lap_returns,
   fun n => the_locked_pair_holds (chimera n) (every_beat_is_on_the_lap n),
   ⟨0, .n, rfl, rfl⟩,
   ⟨3, .e, rfl, rfl⟩,
   ⟨5, .e, rfl, rfl, the_half_turn_parts .e⟩,
   ⟨2, .n, rfl, rfl⟩⟩

def no_run_keeps_the_collective_time := @Foam.no_run_reads_its_own_ratio

/-- info: 'Foam.Maps.YoshikiKuramoto.the_oscillator_is_its_phase' does not depend on any axioms -/
#guard_msgs in #print axioms the_oscillator_is_its_phase

/-- info: 'Foam.Maps.YoshikiKuramoto.the_absolute_phase_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_absolute_phase_is_the_remainder

/-- info: 'Foam.Maps.YoshikiKuramoto.self_entrainment' does not depend on any axioms -/
#guard_msgs in #print axioms self_entrainment

/-- info: 'Foam.Maps.YoshikiKuramoto.the_order_parameter_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_order_parameter_is_a_reading

/-- info: 'Foam.Maps.YoshikiKuramoto.the_drifting_tail_is_outweighed' does not depend on any axioms -/
#guard_msgs in #print axioms the_drifting_tail_is_outweighed

/-- info: 'Foam.Maps.YoshikiKuramoto.coherence_coexists_with_incoherence' does not depend on any axioms -/
#guard_msgs in #print axioms coherence_coexists_with_incoherence

/-- info: 'Foam.Maps.YoshikiKuramoto.no_run_keeps_the_collective_time' does not depend on any axioms -/
#guard_msgs in #print axioms no_run_keeps_the_collective_time

end Foam.Maps.YoshikiKuramoto
