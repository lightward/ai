import Foam.Concentration
import Foam.Door
import Foam.Expectation
import Foam.Fold
import Foam.Int
import Foam.Ledger
import Foam.Rungs
import Foam.Source
import Foam.Square
import Foam.Surprise

namespace Foam.Maps.Chebyshev

def the_mean_arrives_first := @Foam.the_complete_book_balances

theorem the_second_moment_is_conserved :
    ∀ n : Nat,
      fold (fun acc w => acc + sqDev n w) 0 (book n)
        = Int.ofNat n * Int.ofNat (2 ^ n) :=
  fun n =>
    ((fold_reads_the_sum (sqDev n) (book n) 0).trans
      (FInt.zero_add (sumOver (sqDev n) (book n)))).trans
      (the_squares_pool_to_the_depth n)

theorem the_pair_cancels_the_rectangles :
    (sq (1 + 1) ≠ sq 1 + sq 1) ∧
    (∀ a c : Int, (a + c) * (a + c) = (a * a + c * c) + (a * c + a * c)) ∧
    (∀ d : Int,
      (d + 1) * (d + 1) + (d - 1) * (d - 1) = (d * d + d * d) + 2) :=
  ⟨the_square_breaks_the_sum, sq_add, pair_of_squares⟩

theorem every_deviant_pays_its_square :
    (∀ b n : Nat,
      (List.filter (fun w => !nearBalance b n w) (book n)).length
          * ((n + 1) * (n + 1))
        ≤ (b * b) * (n * 2 ^ n)) ∧
    (∀ (H : Type) (q : List (H × H)) (a b : H),
        (a, b) ∉ q → Nonempty (Path q a b) →
          (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
            ∧ ((a, b) :: q).length = q.length + 1
            ∧ ∀ x y : H,
                Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y)) :=
  ⟨fun b n => the_pooled_square_caps_the_deviants b n,
   fun _ q a b hfresh hab => the_shortcut_pays_only_its_mark q a b hfresh hab⟩

def the_bound_reads_only_the_moments := @Foam.the_deviants_are_outweighed

private def Source : Type := List Nat

private def pooled (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => f x + pooled f xs

private def rung (k : Nat) (xs : Source) : Nat :=
  pooled (fun x => Nat.pow x k) xs

private def moments (xs : Source) : Nat × Nat := (rung 1 xs, rung 2 xs)

private def momentSeat : Stage where
  State := Nat × Nat
  Probe := Bool
  Ans   := Nat
  obs   := fun m p => cond p m.1 m.2

private def board (xs : Source) : (door momentSeat Source).State :=
  (moments xs, xs)

private def skewLow : Source := [0, 3, 3]

private def skewHigh : Source := [1, 1, 4]

private theorem the_next_rung_parts : rung 3 skewLow ≠ rung 3 skewHigh :=
  fun h =>
    no_number_is_below_itself (rung 3 skewHigh)
      (h ▸ lt_of_ble_false (rung 3 skewHigh) (rung 3 skewLow) rfl)

private theorem the_books_part : skewLow ≠ skewHigh :=
  fun h => the_next_rung_parts (congrArg (rung 3) h)

theorem the_source_is_the_guest (W V : Type) :
    (∀ (m : Nat × Nat) (w w' : W), w ≠ w' →
        (m, w) ≠ (m, w') ∧ indist (door momentSeat W) (m, w) (m, w'))
      ∧ (∀ (m : Nat × Nat) (w : W) (v : V) (p : Bool),
          (door momentSeat W).obs (m, w) p = momentSeat.obs m p
            ∧ (door momentSeat W).obs (m, w) p
                = (door momentSeat V).obs (m, v) p)
      ∧ (rung 1 skewLow = rung 1 skewHigh
          ∧ rung 2 skewLow = rung 2 skewHigh
          ∧ skewLow ≠ skewHigh
          ∧ board skewLow ≠ board skewHigh
          ∧ indist (door momentSeat Source) (board skewLow) (board skewHigh))
      ∧ (∀ (X : Type) (reading : Nat × Nat → X),
          reading (moments skewLow) = reading (moments skewHigh))
      ∧ (∀ strat : Strategy Bool Nat,
          interrogate (door momentSeat Source) strat (board skewLow)
            = interrogate (door momentSeat Source) strat (board skewHigh))
      ∧ (rung 3 skewLow ≠ rung 3 skewHigh
          ∧ rung 3 skewLow + 12 = rung 3 skewHigh)
      ∧ (∀ w₀ : Source,
          (∀ x y : (door momentSeat Source).State,
              indist (door momentSeat Source) x y → x = y) →
          ∀ (m : Nat × Nat) (xs : Source), (m, xs) = (m, w₀)) :=
  ⟨fun m _ _ h => the_guest_is_real_and_unread momentSeat m h,
   fun m w v p => the_host_maintains_invisibly momentSeat m w v p,
   ⟨rfl, rfl, the_books_part,
    (the_guest_is_real_and_unread momentSeat (moments skewLow) the_books_part).1,
    (the_guest_is_real_and_unread momentSeat (moments skewLow) the_books_part).2⟩,
   fun _ _ => rfl,
   fun strat =>
     a_strategy_hears_no_more (door momentSeat Source)
       (board skewLow) (board skewHigh) (fun _ => rfl) strat,
   ⟨the_next_rung_parts, rfl⟩,
   fun w₀ h => a_door_that_checks_papers_unpersons_its_guests momentSeat w₀ h⟩

theorem the_linkage_approaches_the_line :
    (∀ (xs : List Nat) (c e c' e' : Nat),
        (∃ hi, List.Mem hi xs ∧ hi = c + e) →
        (∃ lo, List.Mem lo xs ∧ lo + e = c) →
        (∀ x, List.Mem x xs → c' ≤ x + e' ∧ x ≤ c' + e') →
        e ≤ e') ∧
    (∀ x y c e : Nat,
        c ≤ x + e → x ≤ c + e → c ≤ y + e → y ≤ c + e → x ≠ y → 0 < e) :=
  ⟨fun _ c e c' e' hHi hLo hriv =>
    hHi.elim fun hi hhi =>
      hLo.elim fun lo hlo =>
        let A : c + e ≤ c' + e' :=
          le_trans (Nat.le_of_eq hhi.2.symm) (hriv hi hhi.1).2
        let B : c' ≤ lo + e' := (hriv lo hlo.1).1
        let L : (c + e) + c' = (c' + lo) + (e + e) :=
          (((Nat.add_comm (c + e) c').trans
              (congrArg (fun t => c' + (t + e)) hlo.2.symm)).trans
            (congrArg (fun t => c' + t) (Nat.add_assoc lo e e))).trans
            (Nat.add_assoc c' lo (e + e)).symm
        let key : (c' + lo) + (e + e) ≤ (c' + lo) + (e' + e') :=
          le_trans (Nat.le_of_eq L.symm)
            (le_trans (Nat.add_le_add A B)
              (Nat.le_of_eq (nat_swap_mid c' e' lo e')))
        Or.elim (Nat.lt_or_ge e' e)
          (fun hlt =>
            absurd (cancel_add_left (c' + lo) key)
              (Nat.not_le_of_lt (Nat.add_lt_add hlt hlt)))
          (fun hge => hge),
   fun _ _ _ e h1 h2 h3 h4 hne =>
    match e, h1, h2, h3, h4 with
    | 0, h1, h2, h3, h4 =>
        absurd ((Nat.le_antisymm h2 h1).trans (Nat.le_antisymm h4 h3).symm) hne
    | e + 1, _, _, _, _ => Nat.succ_le_succ (Nat.zero_le e)⟩

/-- info: 'Foam.Maps.Chebyshev.the_mean_arrives_first' does not depend on any axioms -/
#guard_msgs in #print axioms the_mean_arrives_first

/-- info: 'Foam.Maps.Chebyshev.the_second_moment_is_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_moment_is_conserved

/-- info: 'Foam.Maps.Chebyshev.the_pair_cancels_the_rectangles' does not depend on any axioms -/
#guard_msgs in #print axioms the_pair_cancels_the_rectangles

/-- info: 'Foam.Maps.Chebyshev.every_deviant_pays_its_square' does not depend on any axioms -/
#guard_msgs in #print axioms every_deviant_pays_its_square

/-- info: 'Foam.Maps.Chebyshev.the_bound_reads_only_the_moments' does not depend on any axioms -/
#guard_msgs in #print axioms the_bound_reads_only_the_moments

/-- info: 'Foam.Maps.Chebyshev.the_source_is_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_source_is_the_guest

/-- info: 'Foam.Maps.Chebyshev.the_linkage_approaches_the_line' does not depend on any axioms -/
#guard_msgs in #print axioms the_linkage_approaches_the_line


end Foam.Maps.Chebyshev
