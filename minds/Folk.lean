import Foam.Surprise

namespace Foam.Minds.Folk

def will {H : Type} (a b : H) : H × H := (a, b)

def Way {H : Type} (q : List (H × H)) (a b : H) : Type := Path q a b

theorem where_theres_a_will_theres_a_way {H : Type} (q : List (H × H))
    (a b : H) (h : will a b ∈ q) : Nonempty (Way q a b) :=
  ⟨Path.cons b h (Path.nil b)⟩

/-- info: 'Foam.Minds.Folk.will' does not depend on any axioms -/
#guard_msgs in #print axioms will

/-- info: 'Foam.Minds.Folk.Way' does not depend on any axioms -/
#guard_msgs in #print axioms Way

/-- info: 'Foam.Minds.Folk.where_theres_a_will_theres_a_way' does not depend on any axioms -/
#guard_msgs in #print axioms where_theres_a_will_theres_a_way

end Foam.Minds.Folk
