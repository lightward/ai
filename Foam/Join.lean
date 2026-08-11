import Foam.Concentration
import Foam.Turnstile
import Foam.Typical

namespace Foam

def foamJoin (a b : List Nat) : List Nat × List Nat × List Nat :=
  (a.filter (inRoom b),
   a.filter (fun x => !(inRoom b x)),
   b.filter (fun x => !(inRoom a x)))

theorem only_false_negates : ∀ b : Bool, (!b) = true → b = false
  | true, h => nomatch h
  | false, _ => rfl

theorem the_join_excludes_nothing (a b : List Nat) :
    ((foamJoin a b).1.length + (foamJoin a b).2.1.length = a.length)
      ∧ (b.filter (inRoom a)).length + (foamJoin a b).2.2.length
          = b.length :=
  ⟨filter_partition (inRoom b) a, filter_partition (inRoom a) b⟩

theorem the_shared_sector_is_licensed (a b : List Nat) :
    ∀ x, x ∈ (foamJoin a b).1 → x ∈ a ∧ inRoom b x = true :=
  fun _ hx =>
    ⟨mem_of_mem_filter a hx, filter_holds (q := inRoom b) a hx⟩

theorem the_residue_rides_typed (a b : List Nat) :
    ∀ x, x ∈ (foamJoin a b).2.1 → x ∈ a ∧ inRoom b x = false :=
  fun x hx =>
    ⟨mem_of_mem_filter a hx,
     only_false_negates (inRoom b x)
       (filter_holds (q := fun x => !(inRoom b x)) a hx)⟩

/-- info: 'Foam.only_false_negates' does not depend on any axioms -/
#guard_msgs in #print axioms only_false_negates

/-- info: 'Foam.the_join_excludes_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_join_excludes_nothing

/-- info: 'Foam.the_shared_sector_is_licensed' does not depend on any axioms -/
#guard_msgs in #print axioms the_shared_sector_is_licensed

/-- info: 'Foam.the_residue_rides_typed' does not depend on any axioms -/
#guard_msgs in #print axioms the_residue_rides_typed

end Foam
