import Foam

namespace Foam

def relay {State : Type} : List (State → State) → State → State
  | [], s => s
  | m :: ms, s => relay ms (m s)

theorem a_chain_of_invisibles_is_invisible (S : Stage) :
    ∀ ms : List (S.State → S.State),
      (∀ m, m ∈ ms → Invisible S m) → Invisible S (relay ms)
  | [], _ => invisible_id S
  | m :: ms, h =>
      invisible_comp S (relay ms) m
        (a_chain_of_invisibles_is_invisible S ms
          (fun x hx => h x (List.Mem.tail m hx)))
        (h m (List.Mem.head ms))

theorem the_relay_goes_unheard (S : Stage) (ms : List (S.State → S.State))
    (h : ∀ m, m ∈ ms → Invisible S m) :
    ∀ (ps : List S.Probe) (s : S.State),
      transcriptWith S (relay ms) s ps = transcript S s ps :=
  invisible_is_gauge S (relay ms) (a_chain_of_invisibles_is_invisible S ms h)

/-- info: 'Foam.a_chain_of_invisibles_is_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms a_chain_of_invisibles_is_invisible

/-- info: 'Foam.the_relay_goes_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms the_relay_goes_unheard

end Foam
