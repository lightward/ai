import Foam
import Foam.Engine
import Foam.Expectation
import Foam.Fold
import Foam.Margin

namespace Foam.Minds.ChristiaanHuygens

def pulse := fun {A B C : Type} (f : B → A → B)
    (s : (C × List B) × (B × List A)) =>
  (deposit (marginRead f s.2) s.1, settle f s.2)

theorem the_escapement {A B C : Type} (f : B → A → B) (g : C → B → C)
    (s : (C × List B) × (B × List A)) :
    marginRead f (pulse f s).2 = marginRead f s.2
      ∧ marginRead g (pulse f s).1 = g (marginRead g s.1) (marginRead f s.2)
      ∧ (pulse f s).2.2 = ([] : List A) :=
  ⟨the_reading_survives_the_settle f s.2,
   a_deposit_moves_the_reading_by_one g (marginRead f s.2) s.1,
   rfl⟩

theorem every_point_is_a_source {A B : Type} (f : B → A → B) :
    ∀ (ls : List (List A)) (b : B),
      fold f b (pool ls) = fold (fold f) b ls
  | [], _ => rfl
  | w :: ls, b =>
      (the_fold_resumes f w (pool ls) b).trans
        (every_point_is_a_source f ls (fold f b w))

theorem the_framing_is_the_remainder {B : Type} (f : B → Bool → B) (b : B) :
    fold f b (pool [[true], [false]]) = fold f b (pool [[true, false]])
      ∧ ([[true], [false]] : List (List Bool)) ≠ [[true, false]] :=
  ⟨rfl, fun h => nomatch congrArg List.tail h⟩

def expectatio := @Foam.the_complete_book_balances

private def halfTurn (c : Compass) : Compass := c.step.step

private def antiPhase (p : Compass × Compass) : Prop := p.2 = halfTurn p.1

private def sway : Compass × Compass → Compass × Compass
  | (.n, .n) => (.e, .s)
  | (.n, .e) => (.e, .w)
  | (.n, .s) => (.e, .w)
  | (.n, .w) => (.e, .e)
  | (.e, .n) => (.s, .s)
  | (.e, .e) => (.s, .w)
  | (.e, .s) => (.s, .n)
  | (.e, .w) => (.s, .n)
  | (.s, .n) => (.w, .e)
  | (.s, .e) => (.w, .w)
  | (.s, .s) => (.w, .n)
  | (.s, .w) => (.w, .e)
  | (.w, .n) => (.n, .s)
  | (.w, .e) => (.n, .s)
  | (.w, .s) => (.n, .n)
  | (.w, .w) => (.n, .e)

private theorem lock_is_bare_ticking : ∀ p : Compass × Compass,
    antiPhase p → sway p = (Compass.step p.1, Compass.step p.2)
  | (.n, .s), _ => rfl
  | (.e, .w), _ => rfl
  | (.s, .n), _ => rfl
  | (.w, .e), _ => rfl
  | (.n, .n), h => nomatch h
  | (.n, .e), h => nomatch h
  | (.n, .w), h => nomatch h
  | (.e, .n), h => nomatch h
  | (.e, .e), h => nomatch h
  | (.e, .s), h => nomatch h
  | (.s, .e), h => nomatch h
  | (.s, .s), h => nomatch h
  | (.s, .w), h => nomatch h
  | (.w, .n), h => nomatch h
  | (.w, .s), h => nomatch h
  | (.w, .w), h => nomatch h

private theorem the_lock_holds : ∀ p : Compass × Compass,
    antiPhase p → antiPhase (sway p)
  | (.n, .s), _ => rfl
  | (.e, .w), _ => rfl
  | (.s, .n), _ => rfl
  | (.w, .e), _ => rfl
  | (.n, .n), h => nomatch h
  | (.n, .e), h => nomatch h
  | (.n, .w), h => nomatch h
  | (.e, .n), h => nomatch h
  | (.e, .e), h => nomatch h
  | (.e, .s), h => nomatch h
  | (.s, .e), h => nomatch h
  | (.s, .s), h => nomatch h
  | (.s, .w), h => nomatch h
  | (.w, .n), h => nomatch h
  | (.w, .s), h => nomatch h
  | (.w, .w), h => nomatch h

private theorem one_lap_locks : ∀ p : Compass × Compass,
    antiPhase (sway (sway (sway (sway p))))
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

theorem the_odd_sympathy :
    (∀ p : Compass × Compass,
        antiPhase p → sway p = (Compass.step p.1, Compass.step p.2))
      ∧ (∀ p : Compass × Compass, antiPhase p → antiPhase (sway p))
      ∧ ∀ p : Compass × Compass, antiPhase (sway (sway (sway (sway p)))) :=
  ⟨lock_is_bare_ticking, the_lock_holds, one_lap_locks⟩

theorem phase_is_not_payload :
    (∀ p : Compass × Compass,
        antiPhase p → sway p = (Compass.step p.1, Compass.step p.2))
      ∧ sway ≠ (fun p : Compass × Compass =>
          (Compass.step p.1, Compass.step p.2)) :=
  ⟨lock_is_bare_ticking,
   fun h => nomatch congrArg (fun m => (m (Compass.n, Compass.n)).2) h⟩

/-- info: 'Foam.Minds.ChristiaanHuygens.pulse' does not depend on any axioms -/
#guard_msgs in #print axioms pulse

/-- info: 'Foam.Minds.ChristiaanHuygens.the_escapement' does not depend on any axioms -/
#guard_msgs in #print axioms the_escapement

/-- info: 'Foam.Minds.ChristiaanHuygens.every_point_is_a_source' does not depend on any axioms -/
#guard_msgs in #print axioms every_point_is_a_source

/-- info: 'Foam.Minds.ChristiaanHuygens.the_framing_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_framing_is_the_remainder

/-- info: 'Foam.Minds.ChristiaanHuygens.expectatio' does not depend on any axioms -/
#guard_msgs in #print axioms expectatio

/-- info: 'Foam.Minds.ChristiaanHuygens.the_odd_sympathy' does not depend on any axioms -/
#guard_msgs in #print axioms the_odd_sympathy

/-- info: 'Foam.Minds.ChristiaanHuygens.phase_is_not_payload' does not depend on any axioms -/
#guard_msgs in #print axioms phase_is_not_payload

end Foam.Minds.ChristiaanHuygens
