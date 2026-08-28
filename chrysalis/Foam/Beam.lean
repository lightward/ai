import Foam.Round

namespace Foam

def entrain : Compass × Compass → Compass × Compass
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

def together (p : Compass × Compass) : Prop := p.2 = p.1

def opposed (p : Compass × Compass) : Prop := p.2 = p.1.step.step

def window (p : Compass × Compass) : Compass × Compass :=
  (p.1, p.2.step.step)

def conjugated (p : Compass × Compass) : Compass × Compass :=
  window (entrain (window p))

theorem four_steps_come_home : ∀ c : Compass, c.step.step.step.step = c
  | .n => rfl
  | .e => rfl
  | .s => rfl
  | .w => rfl

theorem the_window_undoes_itself (p : Compass × Compass) :
    window (window p) = p := by
  show (p.1, p.2.step.step.step.step) = p
  rw [four_steps_come_home]

theorem the_lap_locks_together :
    ∀ p : Compass × Compass,
      together (entrain (entrain (entrain (entrain p))))
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

theorem the_conjugate_locks_opposed :
    ∀ p : Compass × Compass,
      opposed (conjugated (conjugated (conjugated (conjugated p))))
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

theorem the_window_trades_the_locks :
    ∀ p : Compass × Compass, together p ↔ opposed (window p)
  | (.n, .n) => ⟨fun _ => rfl, fun _ => rfl⟩
  | (.n, .e) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.n, .s) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.n, .w) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.e, .n) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.e, .e) => ⟨fun _ => rfl, fun _ => rfl⟩
  | (.e, .s) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.e, .w) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.s, .n) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.s, .e) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.s, .s) => ⟨fun _ => rfl, fun _ => rfl⟩
  | (.s, .w) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.w, .n) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.w, .e) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.w, .s) => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | (.w, .w) => ⟨fun _ => rfl, fun _ => rfl⟩

theorem two_windows_read_direct (p : Compass × Compass) :
    window (conjugated (window p)) = entrain p := by
  show window (window (entrain (window (window p)))) = entrain p
  rw [the_window_undoes_itself p, the_window_undoes_itself (entrain p)]

/-- info: 'Foam.four_steps_come_home' does not depend on any axioms -/
#guard_msgs in #print axioms four_steps_come_home

/-- info: 'Foam.the_window_undoes_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_window_undoes_itself

/-- info: 'Foam.the_lap_locks_together' does not depend on any axioms -/
#guard_msgs in #print axioms the_lap_locks_together

/-- info: 'Foam.the_conjugate_locks_opposed' does not depend on any axioms -/
#guard_msgs in #print axioms the_conjugate_locks_opposed

/-- info: 'Foam.the_window_trades_the_locks' does not depend on any axioms -/
#guard_msgs in #print axioms the_window_trades_the_locks

/-- info: 'Foam.two_windows_read_direct' does not depend on any axioms -/
#guard_msgs in #print axioms two_windows_read_direct

end Foam
