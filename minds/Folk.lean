import Foam.Surprise

namespace Foam.Minds.Folk

def will {H : Type} (a b : H) : H × H := (a, b)

def Way {H : Type} (q : List (H × H)) (a b : H) : Type := Path q a b

theorem where_theres_a_will_theres_a_way {H : Type} (q : List (H × H))
    (a b : H) (h : will a b ∈ q) : Nonempty (Way q a b) :=
  ⟨Path.cons b h (Path.nil b)⟩

def light {H : Type} (q : List (H × H)) (e : H × H) : Prop := ¬ e ∈ q

def ward {H : Type} (q : List (H × H)) (e : H × H) : List (H × H) := e :: q

theorem lightward {H : Type} (q : List (H × H)) (a b : H) :
    (light q (a, b) →
        (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
          ∧ Nonempty (Path (ward q (a, b)) a b))
      ∧ ((a, b) ∈ q →
          ∀ x y : H, Nonempty (Path (ward q (a, b)) x y)
            ↔ Nonempty (Path q x y))
      ∧ (ward q (a, b)).length = q.length + 1 :=
  ⟨fun hl =>
     ⟨fun _ _ p => a_fresh_edge_rides_no_path hl p,
      (only_surprise_extends_reach q a b hl).2⟩,
   fun hk x y => a_known_edge_adds_no_reach hk x y,
   the_deposit_writes_one_mark q (a, b)⟩

/-- info: 'Foam.Minds.Folk.will' does not depend on any axioms -/
#guard_msgs in #print axioms will

/-- info: 'Foam.Minds.Folk.Way' does not depend on any axioms -/
#guard_msgs in #print axioms Way

/-- info: 'Foam.Minds.Folk.where_theres_a_will_theres_a_way' does not depend on any axioms -/
#guard_msgs in #print axioms where_theres_a_will_theres_a_way

/-- info: 'Foam.Minds.Folk.light' does not depend on any axioms -/
#guard_msgs in #print axioms light

/-- info: 'Foam.Minds.Folk.ward' does not depend on any axioms -/
#guard_msgs in #print axioms ward

/-- info: 'Foam.Minds.Folk.lightward' does not depend on any axioms -/
#guard_msgs in #print axioms lightward

end Foam.Minds.Folk
