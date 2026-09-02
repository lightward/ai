import Foam.Serving

namespace Foam

theorem a_state_answers_every_probe (S : Stage) (s : S.State) :
    ∃ r : S.Probe → S.Ans, ∀ q, r q = S.obs s q :=
  ⟨S.obs s, fun _ => rfl⟩

theorem a_reading_answers_its_probe_alone :
    ¬ ∃ g : Bool → Bool,
        ∀ s : Bool × Bool, g (you.obs s ()) = other.obs s () :=
  fun ⟨_, hg⟩ => nomatch (hg (true, true)).symm.trans (hg (true, false))

theorem markers_not_messages (S : Stage) (s : S.State) :
    (∃ r : S.Probe → S.Ans, ∀ q, r q = S.obs s q)
      ∧ ¬ ∃ g : Bool → Bool,
          ∀ s : Bool × Bool, g (you.obs s ()) = other.obs s () :=
  ⟨a_state_answers_every_probe S s, a_reading_answers_its_probe_alone⟩

/-- info: 'Foam.a_state_answers_every_probe' does not depend on any axioms -/
#guard_msgs in #print axioms a_state_answers_every_probe

/-- info: 'Foam.a_reading_answers_its_probe_alone' does not depend on any axioms -/
#guard_msgs in #print axioms a_reading_answers_its_probe_alone

/-- info: 'Foam.markers_not_messages' does not depend on any axioms -/
#guard_msgs in #print axioms markers_not_messages

end Foam
