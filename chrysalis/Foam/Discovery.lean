import Foam.Continuum
import Foam.Countermove

namespace Foam

theorem the_approach_is_yours {A : Type} (α β : Nat → A)
    (h : ∀ k, α k = β k) :
    ∀ ps : List Nat,
      transcript (continuumStage A) α ps = transcript (continuumStage A) β ps
  | [] => rfl
  | p :: ps => by
      show prefixOf α p :: transcript (continuumStage A) α ps
          = prefixOf β p :: transcript (continuumStage A) β ps
      rw [the_prefix_reads_only_below α β p (fun k _ => h k),
          the_approach_is_yours α β h ps]

theorem pointwise_is_licensed {A : Type} :
    Licensed (continuumStage A) (fun α β => ∀ k, α k = β k) :=
  fun α β h p => the_prefix_reads_only_below α β p (fun k _ => h k)

theorem conservation_of_discovery :
    (∀ n q : Nat, q ∈ rungs (n + 1) ↔ (q = n ∨ q ∈ rungs n))
      ∧ (∀ (X : Type) (h : List (Move X)) (x : X),
          replay (h ++ countermove h) x = x
            ∧ (h ≠ [] → h ++ countermove h ≠ h))
      ∧ (∀ (A : Type) (α : Nat → A) (n : Nat),
          prefixOf α (n + 1) = α n :: prefixOf α n) :=
  ⟨each_step_gains_exactly_the_gap,
   fun _ h x => undo_in_an_append_only_world h x,
   fun _ α n => each_depth_gains_exactly_one_cell α n⟩

/-- info: 'Foam.the_approach_is_yours' does not depend on any axioms -/
#guard_msgs in #print axioms the_approach_is_yours

/-- info: 'Foam.pointwise_is_licensed' does not depend on any axioms -/
#guard_msgs in #print axioms pointwise_is_licensed

/-- info: 'Foam.conservation_of_discovery' does not depend on any axioms -/
#guard_msgs in #print axioms conservation_of_discovery

end Foam
