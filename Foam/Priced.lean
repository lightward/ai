import Foam.Log
import Foam.Source

namespace Foam

theorem freq_splits_the_length :
    ∀ w : List Bool, freq w true + freq w false = w.length
  | [] => rfl
  | true :: w => by
      show (1 + freq w true) + (0 + freq w false) = w.length + 1
      rw [nothing_added, Nat.add_comm 1 (freq w true), succ_adds,
          freq_splits_the_length w]
  | false :: w => by
      show (0 + freq w true) + (1 + freq w false) = w.length + 1
      rw [nothing_added, Nat.add_comm 1 (freq w false), adding_associates,
          freq_splits_the_length w]

theorem natSumOver_filter_le (v : List Bool → Nat) (q : List Bool → Bool) :
    ∀ l : List (List Bool), natSumOver v (List.filter q l) ≤ natSumOver v l
  | [] => Nat.le_refl 0
  | w :: l => by
      cases hq : q w with
      | true =>
          rw [List.filter_cons_of_pos (l := l) hq]
          exact Nat.add_le_add_left (natSumOver_filter_le v q l) (v w)
      | false =>
          rw [List.filter_cons_of_neg (l := l) (ne_true_of_eq_false hq)]
          exact le_trans (natSumOver_filter_le v q l) (Nat.le_add_left _ _)

theorem class_members_weigh_alike (t f n k : Nat) :
    ∀ w, w ∈ List.filter (fun w => Nat.beq (freq w true) k) (book n) →
      weightOf t f w = t ^ k * f ^ (n - k) := by
  intro w hw
  have hq := @filter_holds (List Bool) (fun w => Nat.beq (freq w true) k) w
    (book n) hw
  have hk : freq w true = k := eq_of_beq' _ _ hq
  have hlen : w.length = n := book_words_have_length n w (mem_of_mem_filter _ hw)
  have hf : freq w false = n - k := by
    have hs := freq_splits_the_length w
    rw [hk, hlen] at hs
    rw [← hs, FInt.add_sub_cancel_left]
  show t ^ freq w true * f ^ freq w false = t ^ k * f ^ (n - k)
  rw [hk, hf]

theorem the_weighted_class_is_within_the_book (t f n k : Nat) :
    classCount n k * (t ^ k * f ^ (n - k)) ≤ (t + f) ^ n := by
  have hsum : natSumOver (weightOf t f)
      (List.filter (fun w => Nat.beq (freq w true) k) (book n))
      = classCount n k * (t ^ k * f ^ (n - k)) := by
    rw [natSumOver_congr_mem
          (List.filter (fun w => Nat.beq (freq w true) k) (book n))
          (class_members_weigh_alike t f n k),
        natSumOver_const]
    rfl
  rw [← hsum, ← the_weighted_book_sums_whole t f n]
  exact natSumOver_filter_le (weightOf t f) _ (book n)

/-- info: 'Foam.freq_splits_the_length' does not depend on any axioms -/
#guard_msgs in #print axioms freq_splits_the_length

/-- info: 'Foam.natSumOver_filter_le' does not depend on any axioms -/
#guard_msgs in #print axioms natSumOver_filter_le

/-- info: 'Foam.class_members_weigh_alike' does not depend on any axioms -/
#guard_msgs in #print axioms class_members_weigh_alike

/-- info: 'Foam.the_weighted_class_is_within_the_book' does not depend on any axioms -/
#guard_msgs in #print axioms the_weighted_class_is_within_the_book

end Foam
