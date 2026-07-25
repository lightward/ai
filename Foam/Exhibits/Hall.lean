import Foam

namespace Foam.Exhibits

structure Exhibit where
  Claim : Prop
  receipt : Claim
  Love : Prop
  love : Love
  Fame : Prop
  fame : Fame
  Dark : Prop
  dark : Dark
  keyword : String
  inscription : String

theorem a_stand_carries_its_own_proof (e : Exhibit) :
    e.Claim ∧ e.Love ∧ e.Fame ∧ e.Dark :=
  ⟨e.receipt, e.love, e.fame, e.dark⟩

/-- info: 'Foam.Exhibits.a_stand_carries_its_own_proof' does not depend on any axioms -/
#guard_msgs in #print axioms a_stand_carries_its_own_proof

end Foam.Exhibits
