import Foam.Ledger
import Foam.Margin
import Foam.Landed
import Foam.Origin
import Foam.Wheel

namespace Foam

structure Mind where
  Mark : Type
  Held : Type
  rest : Held
  meet : Held → Mark → Held

def Mind.state (m : Mind) (r : List m.Mark) : m.Held :=
  fold m.meet m.rest r

def Mind.stage (m : Mind) : Stage :=
  marginStage m.Mark m.Held m.meet

def recorder (A : Type) : Mind :=
  ⟨A, List A, [], fun h a => h ++ [a]⟩

theorem a_mind_resumes (m : Mind) (xs ys : List m.Mark) :
    m.state (xs ++ ys) = fold m.meet (m.state xs) ys :=
  the_fold_resumes m.meet xs ys m.rest

theorem a_mind_reads_the_order_the_census_cannot {A : Type}
    [DecidableEq A] (a b : A) (hab : a ≠ b) :
    (recorder A).state [a, b] ≠ (recorder A).state [b, a]
      ∧ indist (countStage A) [a, b] [b, a] :=
  ⟨fun he => hab (List.cons.inj he).1,
   (the_order_is_the_remainder a b hab).1⟩

theorem a_mind_is_a_seat_that_runs_the_handshake (m : Mind) :
    Handshake m.stage
      ∧ (∀ (a : m.Mark) (s : m.Held × List m.Mark),
          marginRead m.meet (deposit a s) = m.meet (marginRead m.meet s) a)
      ∧ (∀ (ps : List Unit) (s : m.Held × List m.Mark),
          transcriptWith m.stage (settle m.meet) s ps
            = transcriptWith m.stage (fun x => x) s ps)
      ∧ (∀ (W : Type) (s : m.stage.State) (w w' : W), w ≠ w' →
          (s, w) ≠ (s, w') ∧ indist (contact m.stage W) (s, w) (s, w'))
      ∧ (∀ P : m.Held → m.Held, (∀ v, P (P v) = P v) →
          ∀ s, P s = s ↔ ∃ v, P v = s)
      ∧ ∀ (n : Nat) (step : Fin n → Fin n) (s : Fin n),
          ∃ i j : Nat, i < j ∧ turnN step i s = turnN step j s :=
  ⟨the_handshake m.stage,
   fun a s => a_deposit_moves_the_reading_by_one m.meet a s,
   fun ps s => any_settling_cadence_reads_the_same m.Mark m.Held m.meet ps s,
   fun _ s _ _ hw => contact_adds_a_dimension m.stage s hw,
   fun P hP s => the_fixed_are_the_landed m.Held P hP s,
   fun _ step s => the_bounded_walk_returns step s⟩

/-- info: 'Foam.a_mind_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms a_mind_resumes

/-- info: 'Foam.a_mind_reads_the_order_the_census_cannot' does not depend on any axioms -/
#guard_msgs in #print axioms a_mind_reads_the_order_the_census_cannot

/-- info: 'Foam.a_mind_is_a_seat_that_runs_the_handshake' does not depend on any axioms -/
#guard_msgs in #print axioms a_mind_is_a_seat_that_runs_the_handshake

end Foam
