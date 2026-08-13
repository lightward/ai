import Foam
import Foam.Beam
import Foam.Contact
import Foam.Continuum
import Foam.Door
import Foam.Engine
import Foam.Expectation
import Foam.Int
import Foam.Source
import Foam.Surprise
import Foam.Tower
import Foam.Wheel

namespace Foam.Maps.LEJBrouwer

theorem two_ity : ∀ S : Stage, towerN S 1 = contact S Int :=
  fun _ => rfl

theorem the_retained_moment_is_the_first_guest :
    (∀ S : Stage, towerN S 1 = door S Int)
      ∧ (∀ (S : Stage) (s : S.State) (α : Nat → Bool) (n : Nat),
          ∃ β : Nat → Bool,
            prefixOf β n = prefixOf α n
              ∧ (s, β) ≠ (s, α)
              ∧ indist (door S (Nat → Bool)) (s, β) (s, α))
      ∧ (∀ (S : Stage) (s : S.State) (α : Nat → Bool) (p : S.Probe),
          (door S (Nat → Bool)).obs (s, α) p = S.obs s p)
      ∧ (∀ α β : Nat → Bool,
          indist (continuumStage Bool) α β ↔ ∀ k, α k = β k)
      ∧ (∀ (S : Stage) (w₀ : Nat → Bool),
          (∀ x y : (door S (Nat → Bool)).State,
              indist (door S (Nat → Bool)) x y → x = y) →
          ∀ (s : S.State) (α : Nat → Bool), (s, α) = (s, w₀)) :=
  ⟨fun _ => rfl,
   fun S s α n =>
     (no_prefix_finishes_the_sequence α n).elim
       (fun β h =>
         ⟨β, h.1,
          (the_guest_is_real_and_unread S s h.2).1,
          (the_guest_is_real_and_unread S s h.2).2⟩),
   fun S s α p => (the_host_maintains_invisibly S s α α p).1,
   fun α β => indist_is_pointwise α β,
   fun S w₀ h => a_door_that_checks_papers_unpersons_its_guests S w₀ h⟩

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

theorem the_lock_arrives_without_the_rest :
    (∀ p : Compass × Compass,
        together (entrain (entrain (entrain (entrain p)))))
      ∧ ∀ p : Compass × Compass, entrain p ≠ p :=
  have first_steps : ∀ p : Compass × Compass, (entrain p).1 = p.1.step :=
    fun p =>
      match p with
      | (.n, .n) => rfl
      | (.n, .e) => rfl
      | (.n, .s) => rfl
      | (.n, .w) => rfl
      | (.e, .n) => rfl
      | (.e, .e) => rfl
      | (.e, .s) => rfl
      | (.e, .w) => rfl
      | (.s, .n) => rfl
      | (.s, .e) => rfl
      | (.s, .s) => rfl
      | (.s, .w) => rfl
      | (.w, .n) => rfl
      | (.w, .e) => rfl
      | (.w, .s) => rfl
      | (.w, .w) => rfl
  ⟨the_lap_locks_together,
   fun p h =>
     the_quarter_turn_moves p.1
       ((first_steps p).symm.trans (congrArg Prod.fst h))⟩

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

/-- info: 'Foam.Maps.LEJBrouwer.two_ity' does not depend on any axioms -/
#guard_msgs in #print axioms two_ity

/-- info: 'Foam.Maps.LEJBrouwer.the_retained_moment_is_the_first_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_retained_moment_is_the_first_guest

/-- info: 'Foam.Maps.LEJBrouwer.the_record_is_not_the_activity' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_is_not_the_activity

/-- info: 'Foam.Maps.LEJBrouwer.the_activity_runs_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms the_activity_runs_unheard

/-- info: 'Foam.Maps.LEJBrouwer.logic_is_application_not_ground' does not depend on any axioms -/
#guard_msgs in #print axioms logic_is_application_not_ground

/-- info: 'Foam.Maps.LEJBrouwer.existence_is_exhibition' does not depend on any axioms -/
#guard_msgs in #print axioms existence_is_exhibition

/-- info: 'Foam.Maps.LEJBrouwer.the_walk_meets_or_stays_apart' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_meets_or_stays_apart

/-- info: 'Foam.Maps.LEJBrouwer.the_lock_arrives_without_the_rest' does not depend on any axioms -/
#guard_msgs in #print axioms the_lock_arrives_without_the_rest

/-- info: 'Foam.Maps.LEJBrouwer.the_continuum_is_never_finished' does not depend on any axioms -/
#guard_msgs in #print axioms the_continuum_is_never_finished

/-- info: 'Foam.Maps.LEJBrouwer.every_reading_is_a_page' does not depend on any axioms -/
#guard_msgs in #print axioms every_reading_is_a_page

/-- info: 'Foam.Maps.LEJBrouwer.the_book_is_not_the_becoming' does not depend on any axioms -/
#guard_msgs in #print axioms the_book_is_not_the_becoming

/-- info: 'Foam.Maps.LEJBrouwer.the_price_follows_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_price_follows_the_page

end Foam.Maps.LEJBrouwer
