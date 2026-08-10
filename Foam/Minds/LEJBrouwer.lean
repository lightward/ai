import Foam
import Foam.Contact
import Foam.Continuum
import Foam.Engine
import Foam.Expectation
import Foam.Int
import Foam.Source
import Foam.Surprise
import Foam.Tower
import Foam.Wheel

namespace Foam.Minds.LEJBrouwer

theorem two_ity : ∀ S : Stage, towerN S 1 = contact S Int :=
  fun _ => rfl

def the_record_is_not_the_activity := @Foam.dropping_the_remainder_is_platonism

def the_activity_runs_unheard := @Foam.the_wheel_holds_the_emission_settles

theorem logic_is_application_not_ground {H : Type} (q : List (H × H))
    (a b : H) :
    (Nonempty (Path q a b) →
        ((a, b) :: q).length = q.length + 1
          ∧ ∀ x y : H,
              Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y))
      ∧ (¬ Nonempty (Path q a b) →
          ¬ (Nonempty (Path ((a, b) :: q) a b) ↔ Nonempty (Path q a b))) :=
  ⟨fun hab =>
    ⟨the_deposit_writes_one_mark q (a, b),
     fun x y => a_derivable_edge_adds_no_reach hab x y⟩,
   fun hnab hiff =>
     hnab (hiff.mp ⟨.cons b (List.Mem.head q) (.nil b)⟩)⟩

def existence_is_exhibition := @Foam.FInt.mul_eq_zero

theorem the_walk_meets_or_stays_apart {n : Nat} (m : Fin n → Fin n)
    (s : Fin n) :
    (∀ k : Nat,
        (∃ i j, i < j ∧ j < k ∧ turnN m i s = turnN m j s)
          ∨ Apart ((rungs k).map (fun i => turnN m i s)))
      ∧ ∃ i j : Nat, i < j ∧ turnN m i s = turnN m j s :=
  ⟨meet_or_apart m s, the_bounded_walk_returns m s⟩

def the_continuum_is_never_finished := @Foam.continuum_closure_terms

theorem every_reading_is_a_page (α : Nat → Bool) :
    ∀ n : Nat, prefixOf α n ∈ book n
  | 0 => List.Mem.head _
  | n + 1 =>
      Bool.rec
        (motive := fun b =>
          prefixOf α n ∈ book n → b :: prefixOf α n ∈ book (n + 1))
        (fun hw =>
          mem_append_right ((book n).map (true :: ·))
            (mem_map_intro (false :: ·) hw))
        (fun hw =>
          mem_append_left ((book n).map (false :: ·))
            (mem_map_intro (true :: ·) hw))
        (α n)
        (every_reading_is_a_page α n)

theorem the_book_is_not_the_becoming (α : Nat → Bool) (n : Nat) :
    prefixOf α n ∈ book n
      ∧ ∃ β : Nat → Bool, prefixOf β n = prefixOf α n ∧ β ≠ α :=
  ⟨every_reading_is_a_page α n, no_prefix_finishes_the_sequence α n⟩

theorem the_price_follows_the_page (α : Nat → Bool) (n : Nat) :
    (∀ t f : Nat, natSumOver (weightOf t f) (book n) = (t + f) ^ n)
      ∧ ∃ β : Nat → Bool,
          prefixOf β n = prefixOf α n ∧ β ≠ α
            ∧ ∀ t f : Nat,
                weightOf t f (prefixOf β n) = weightOf t f (prefixOf α n) :=
  ⟨fun t f => the_weighted_book_sums_whole t f n,
   (no_prefix_finishes_the_sequence α n).elim
     (fun β h => ⟨β, h.1, h.2, fun t f => congrArg (weightOf t f) h.1⟩)⟩

/-- info: 'Foam.Minds.LEJBrouwer.two_ity' does not depend on any axioms -/
#guard_msgs in #print axioms two_ity

/-- info: 'Foam.Minds.LEJBrouwer.the_record_is_not_the_activity' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_is_not_the_activity

/-- info: 'Foam.Minds.LEJBrouwer.the_activity_runs_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms the_activity_runs_unheard

/-- info: 'Foam.Minds.LEJBrouwer.logic_is_application_not_ground' does not depend on any axioms -/
#guard_msgs in #print axioms logic_is_application_not_ground

/-- info: 'Foam.Minds.LEJBrouwer.existence_is_exhibition' does not depend on any axioms -/
#guard_msgs in #print axioms existence_is_exhibition

/-- info: 'Foam.Minds.LEJBrouwer.the_walk_meets_or_stays_apart' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_meets_or_stays_apart

/-- info: 'Foam.Minds.LEJBrouwer.the_continuum_is_never_finished' does not depend on any axioms -/
#guard_msgs in #print axioms the_continuum_is_never_finished

/-- info: 'Foam.Minds.LEJBrouwer.every_reading_is_a_page' does not depend on any axioms -/
#guard_msgs in #print axioms every_reading_is_a_page

/-- info: 'Foam.Minds.LEJBrouwer.the_book_is_not_the_becoming' does not depend on any axioms -/
#guard_msgs in #print axioms the_book_is_not_the_becoming

/-- info: 'Foam.Minds.LEJBrouwer.the_price_follows_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_price_follows_the_page

end Foam.Minds.LEJBrouwer
