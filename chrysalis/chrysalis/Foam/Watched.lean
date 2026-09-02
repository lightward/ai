import Foam

namespace Foam

theorem only_the_invisible_survives_the_watch (S : Stage)
    (m : S.State → S.State) :
    (∀ (ps : List S.Probe) (s : S.State),
        transcriptWith S m s ps = transcript S s ps)
      ↔ Invisible S m :=
  ⟨fun h s p => (List.cons.inj (h [p] s)).1,
   fun hm => invisible_is_gauge S m hm⟩

/-- info: 'Foam.only_the_invisible_survives_the_watch' does not depend on any axioms -/
#guard_msgs in #print axioms only_the_invisible_survives_the_watch

end Foam
