import Foam.Countermove

namespace Foam

theorem a_merge_admits_no_counter {X : Type} (f : X → X) {a b : X}
    (hab : a ≠ b) (hf : f a = f b) :
    ¬ ∃ g : X → X, ∀ x, g (f x) = x :=
  fun ⟨g, hg⟩ => hab ((hg a).symm.trans ((congrArg g hf).trans (hg b)))

theorem every_move_keeps_the_state {X : Type} (m : Move X) {a b : X}
    (h : m.fwd a = m.fwd b) : a = b :=
  (m.bwd_fwd a).symm.trans ((congrArg m.bwd h).trans (m.bwd_fwd b))

def runLocal {A B : Type} : List (A → A) → A × B → A × B
  | [], p => p
  | m :: ms, p => runLocal ms (m p.1, p.2)

theorem local_runs_fix_the_foreign {A B : Type} :
    ∀ (ms : List (A → A)) (p : A × B), (runLocal ms p).2 = p.2
  | [], _ => rfl
  | m :: ms, p => local_runs_fix_the_foreign ms (m p.1, p.2)

theorem no_local_counter_reaches_the_foreign_record {A B : Type}
    (send : A × B → A × B) (p : A × B) (hs : (send p).2 ≠ p.2) :
    ¬ ∃ ms : List (A → A), runLocal ms (send p) = p :=
  fun ⟨ms, hms⟩ =>
    hs ((local_runs_fix_the_foreign ms (send p)).symm.trans
      (congrArg Prod.snd hms))

theorem the_one_way_valve {X A B : Type} (f : X → X) {a b : X}
    (hab : a ≠ b) (hf : f a = f b) (m : Move X)
    (send : A × B → A × B) (p : A × B) (hs : (send p).2 ≠ p.2) :
    (¬ ∃ g : X → X, ∀ x, g (f x) = x)
      ∧ (∀ {c d : X}, m.fwd c = m.fwd d → c = d)
      ∧ ¬ ∃ ms : List (A → A), runLocal ms (send p) = p :=
  ⟨a_merge_admits_no_counter f hab hf,
   fun h => every_move_keeps_the_state m h,
   no_local_counter_reaches_the_foreign_record send p hs⟩

/-- info: 'Foam.a_merge_admits_no_counter' does not depend on any axioms -/
#guard_msgs in #print axioms a_merge_admits_no_counter

/-- info: 'Foam.every_move_keeps_the_state' does not depend on any axioms -/
#guard_msgs in #print axioms every_move_keeps_the_state

/-- info: 'Foam.local_runs_fix_the_foreign' does not depend on any axioms -/
#guard_msgs in #print axioms local_runs_fix_the_foreign

/-- info: 'Foam.no_local_counter_reaches_the_foreign_record' does not depend on any axioms -/
#guard_msgs in #print axioms no_local_counter_reaches_the_foreign_record

/-- info: 'Foam.the_one_way_valve' does not depend on any axioms -/
#guard_msgs in #print axioms the_one_way_valve

end Foam
