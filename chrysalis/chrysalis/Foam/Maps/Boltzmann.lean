import Foam
import Foam.Coil
import Foam.Countermove
import Foam.Door
import Foam.Ledger
import Foam.Log
import Foam.Seat
import Foam.Roles
import Foam.Source
import Foam.Typical
import Foam.Wheel

namespace Foam.Maps.Boltzmann

theorem each_complexion_counts_once (n : Nat) :
    (book n).length = 2 ^ n ∧ AllDiff (book n) :=
  ⟨the_book_has_two_to_the_n n, the_book_repeats_no_word n⟩

theorem a_macrostate_is_a_derived_role (S : Stage) (s : S.State)
    {A : Type} [DecidableEq A] (a b : A) (hab : a ≠ b) :
    (((∀ (p : S.Probe) (Q : S.Ans → Prop), Derived S (fun t => Q (S.obs t p)))
        ∧ ¬ Derived (dress S) (fun x => x.2 = 0))
      ∧ ∀ (P : (dress S).State → Prop), Derived (dress S) P →
          ∀ (t : S.State) (n m : Int), P (t, n) ↔ P (t, m))
      ∧ ((recorder A).state [a, b] ≠ (recorder A).state [b, a]
          ∧ indist (countStage A) [a, b] [b, a]) :=
  ⟨⟨a_role_is_conduct_not_costume S s,
    fun P hP t n m => a_derived_role_cannot_read_the_badge S P hP t n m⟩,
   a_seat_reads_the_order_the_census_cannot a b hab⟩

private def Complexion : Type := List Bool

private def shelf (w : Complexion) : Nat := freq w true

private def shelfSeat : Stage where
  State := Nat
  Probe := Unit
  Ans   := Nat
  obs   := fun k _ => k

private def board (w : Complexion) : (door shelfSeat Complexion).State :=
  (shelf w, w)

private def hotCold : Complexion := [true, false]

private def coldHot : Complexion := [false, true]

private theorem the_spins_part : true ≠ false := fun h => nomatch h

private theorem the_complexions_part : hotCold ≠ coldHot :=
  fun h => the_spins_part (congrArg (fun l => List.headD l false) h)

theorem the_complexion_is_the_guest (W V : Type) :
    (∀ (k : Nat) (w w' : W), w ≠ w' →
        (k, w) ≠ (k, w') ∧ indist (door shelfSeat W) (k, w) (k, w'))
      ∧ (∀ (k : Nat) (w : W) (v : V) (p : Unit),
          (door shelfSeat W).obs (k, w) p = shelfSeat.obs k p
            ∧ (door shelfSeat W).obs (k, w) p = (door shelfSeat V).obs (k, v) p)
      ∧ (shelf hotCold = shelf coldHot
          ∧ swapTop hotCold = coldHot
          ∧ hotCold ∈ book 2
          ∧ coldHot ∈ book 2
          ∧ hotCold ≠ coldHot
          ∧ board hotCold ≠ board coldHot
          ∧ indist (door shelfSeat Complexion) (board hotCold) (board coldHot))
      ∧ (∀ (X : Type) (weighting : Nat → X),
          weighting (shelf hotCold) = weighting (shelf coldHot))
      ∧ (∀ strat : Strategy Unit Nat,
          interrogate (door shelfSeat Complexion) strat (board hotCold)
            = interrogate (door shelfSeat Complexion) strat (board coldHot))
      ∧ ((∀ n k : Nat, classCount n k
            = (List.filter (fun w => Nat.beq (shelf w) k) (book n)).length)
          ∧ classCount 2 (shelf hotCold) = 2
          ∧ ∀ n k : Nat, k ≤ 2 * n →
              classCount (2 * n) k ≤ classCount (2 * n) n)
      ∧ (((recorder Bool).state hotCold ≠ (recorder Bool).state coldHot
            ∧ indist (countStage Bool) hotCold coldHot)
          ∧ ∀ w₀ : Complexion,
              (∀ x y : (door shelfSeat Complexion).State,
                  indist (door shelfSeat Complexion) x y → x = y) →
              ∀ (k : Nat) (w : Complexion), (k, w) = (k, w₀)) :=
  ⟨fun k _ _ h => the_guest_is_real_and_unread shelfSeat k h,
   fun k w v p => the_host_maintains_invisibly shelfSeat k w v p,
   ⟨rfl, rfl,
    List.Mem.tail _ (List.Mem.head _),
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
    the_complexions_part,
    (the_guest_is_real_and_unread shelfSeat (shelf hotCold) the_complexions_part).1,
    (the_guest_is_real_and_unread shelfSeat (shelf hotCold) the_complexions_part).2⟩,
   fun _ _ => rfl,
   fun strat =>
     a_strategy_hears_no_more (door shelfSeat Complexion)
       (board hotCold) (board coldHot) (fun _ => rfl) strat,
   ⟨fun _ _ => rfl, rfl, the_middle_holds_the_most⟩,
   ⟨a_seat_reads_the_order_the_census_cannot true false the_spins_part,
    fun w₀ h => a_door_that_checks_papers_unpersons_its_guests shelfSeat w₀ h⟩⟩

theorem heat_moves_what_the_collision_cannot :
    (∀ (h : Int × Int) (d : Int),
        coilClass (coil.meet h (Sum.inl d)) = coilClass h)
      ∧ (∀ (h : Int × Int) (s : Int),
          coilClass (coil.meet h (Sum.inr s)) = coilClass h + s)
      ∧ (∀ s : Int,
          coilClass (coil.state [Sum.inr s, Sum.inr (-s)])
              = coilClass coil.rest
            ∧ ([Sum.inr s, Sum.inr (-s)] : List coil.Mark) ≠ [])
      ∧ (coilClass (1, -1) = coilClass (0, 0)
          ∧ ((1 : Int), (-1 : Int)) ≠ ((0 : Int), (0 : Int))) :=
  ⟨the_shuffle_conserves_the_class,
   the_stroke_moves_the_class_by_its_size,
   the_return_pays_two_marks,
   the_partition_rides_unread⟩

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

/-- info: 'Foam.Maps.Boltzmann.each_complexion_counts_once' does not depend on any axioms -/
#guard_msgs in #print axioms each_complexion_counts_once

/-- info: 'Foam.Maps.Boltzmann.a_macrostate_is_a_derived_role' does not depend on any axioms -/
#guard_msgs in #print axioms a_macrostate_is_a_derived_role

/-- info: 'Foam.Maps.Boltzmann.the_complexion_is_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_complexion_is_the_guest

/-- info: 'Foam.Maps.Boltzmann.heat_moves_what_the_collision_cannot' does not depend on any axioms -/
#guard_msgs in #print axioms heat_moves_what_the_collision_cannot

/-- info: 'Foam.Maps.Boltzmann.entropy_is_the_price_of_the_name' does not depend on any axioms -/
#guard_msgs in #print axioms entropy_is_the_price_of_the_name

/-- info: 'Foam.Maps.Boltzmann.equilibrium_is_the_biggest_room' does not depend on any axioms -/
#guard_msgs in #print axioms equilibrium_is_the_biggest_room

/-- info: 'Foam.Maps.Boltzmann.the_arrow_rides_the_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_arrow_rides_the_count

/-- info: 'Foam.Maps.Boltzmann.the_return_does_not_tip_the_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_return_does_not_tip_the_count

/-- info: 'Foam.Maps.Boltzmann.the_most_probable_distribution' does not depend on any axioms -/
#guard_msgs in #print axioms the_most_probable_distribution

/-- info: 'Foam.Maps.Boltzmann.no_seat_inside_the_fluctuation' does not depend on any axioms -/
#guard_msgs in #print axioms no_seat_inside_the_fluctuation

end Foam.Maps.Boltzmann
