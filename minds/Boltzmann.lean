import Foam
import Foam.Countermove
import Foam.Ledger
import Foam.Log
import Foam.Roles
import Foam.Source
import Foam.Typical
import Foam.Wheel

namespace Foam.Minds.Boltzmann

theorem each_complexion_counts_once (n : Nat) :
    (book n).length = 2 ^ n ∧ AllDiff (book n) :=
  ⟨the_book_has_two_to_the_n n, the_book_repeats_no_word n⟩

theorem a_macrostate_is_a_derived_role (S : Stage) (s : S.State) :
    ((∀ (p : S.Probe) (Q : S.Ans → Prop), Derived S (fun t => Q (S.obs t p)))
        ∧ ¬ Derived (dress S) (fun x => x.2 = 0))
      ∧ ∀ (P : (dress S).State → Prop), Derived (dress S) P →
          ∀ (t : S.State) (n m : Int), P (t, n) ↔ P (t, m) :=
  ⟨a_role_is_conduct_not_costume S s,
   fun P hP t n m => a_derived_role_cannot_read_the_badge S P hP t n m⟩

theorem entropy_is_the_price_of_the_name (k n S W : Nat)
    (hW : W = (book n).length) (hS : S = k * n) :
    S = k * logTwo W
      ∧ natSumOver List.length (book n)
          = (book n).length * logTwo ((book n).length)
      ∧ ∀ (L : Nat) (ms : List (List Bool)), AllDiff ms →
          (∀ m, m ∈ ms → m ∈ book L) → ms.length ≤ 2 ^ L :=
  ⟨S_eq_k_log_W k n S W hW hS,
   the_price_is_the_log n,
   fun L ms hd hin => a_class_marked_into_a_book_is_counted L ms hd hin⟩

theorem equilibrium_is_the_biggest_room (n : Nat) :
    (∀ k : Nat, k ≤ 2 * n → classCount (2 * n) k ≤ classCount (2 * n) n)
      ∧ 2 ^ (2 * n) ≤ (2 * n + 1) * classCount (2 * n) n :=
  ⟨the_middle_holds_the_most n, the_middle_shelf_holds_its_share n⟩

theorem the_arrow_rides_the_count {X : Type} :
    (∀ (h : List (Move X)) (x : X),
        replay (countermove h) (replay h x) = x)
      ∧ (∀ b c : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
          c * (List.filter (fun w => Bool.not (nearBalance b n w))
                (book n)).length
            ≤ (List.filter (fun w => nearBalance b n w) (book n)).length) :=
  ⟨the_countermove_comes_home, the_deviants_are_outnumbered⟩

theorem the_return_does_not_tip_the_count :
    (∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n),
        ∃ i j : Nat, i < j ∧ turnN m i s = turnN m j s)
      ∧ (∀ b c : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
          c * (List.filter (fun w => Bool.not (nearBalance b n w))
                (book n)).length
            ≤ (List.filter (fun w => nearBalance b n w) (book n)).length) :=
  ⟨fun _ m s => the_bounded_walk_returns m s, the_deviants_are_outnumbered⟩

theorem the_most_probable_distribution :
    (∀ t f n k : Nat, k < n → (k + 1) * (t + f) ≤ (n + 1) * t →
        classCount n k * (t ^ k * f ^ (n - k))
          ≤ classCount n (k + 1) * (t ^ (k + 1) * f ^ (n - (k + 1))))
      ∧ ∀ t f b c : Nat, 0 < t → 0 < f →
          ∃ N : Nat, ∀ n : Nat, N ≤ n →
            c * natSumOver (fun w => t ^ freq w true * f ^ freq w false)
                  (List.filter
                    (fun w => Bool.not (Bool.and
                      (Nat.ble (b * (t * n)) (n + b * ((t + f) * freq w true)))
                      (Nat.ble (b * ((t + f) * freq w true)) (n + b * (t * n)))))
                    (book n))
              ≤ natSumOver (fun w => t ^ freq w true * f ^ freq w false)
                  (List.filter
                    (fun w => Bool.and
                      (Nat.ble (b * (t * n)) (n + b * ((t + f) * freq w true)))
                      (Nat.ble (b * ((t + f) * freq w true)) (n + b * (t * n))))
                    (book n)) :=
  ⟨the_census_rises_to_the_lean,
   fun t f b c _ _ => the_deviants_are_outweighed t f b c⟩

def no_seat_inside_the_fluctuation := @Foam.no_run_reads_its_own_ratio

/-- info: 'Foam.Minds.Boltzmann.each_complexion_counts_once' does not depend on any axioms -/
#guard_msgs in #print axioms each_complexion_counts_once

/-- info: 'Foam.Minds.Boltzmann.a_macrostate_is_a_derived_role' does not depend on any axioms -/
#guard_msgs in #print axioms a_macrostate_is_a_derived_role

/-- info: 'Foam.Minds.Boltzmann.entropy_is_the_price_of_the_name' does not depend on any axioms -/
#guard_msgs in #print axioms entropy_is_the_price_of_the_name

/-- info: 'Foam.Minds.Boltzmann.equilibrium_is_the_biggest_room' does not depend on any axioms -/
#guard_msgs in #print axioms equilibrium_is_the_biggest_room

/-- info: 'Foam.Minds.Boltzmann.the_arrow_rides_the_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_arrow_rides_the_count

/-- info: 'Foam.Minds.Boltzmann.the_return_does_not_tip_the_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_return_does_not_tip_the_count

/-- info: 'Foam.Minds.Boltzmann.the_most_probable_distribution' does not depend on any axioms -/
#guard_msgs in #print axioms the_most_probable_distribution

/-- info: 'Foam.Minds.Boltzmann.no_seat_inside_the_fluctuation' does not depend on any axioms -/
#guard_msgs in #print axioms no_seat_inside_the_fluctuation

end Foam.Minds.Boltzmann
