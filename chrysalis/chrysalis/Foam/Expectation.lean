import Foam.Measure

namespace Foam

def book : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (book n).map (true :: ·) ++ (book n).map (false :: ·)

def pool {A : Type} : List (List A) → List A
  | [] => []
  | w :: B => w ++ pool B

def runOf (c : Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => c :: runOf c n

theorem list_append_assoc {A : Type} :
    ∀ (x y z : List A), (x ++ y) ++ z = x ++ (y ++ z)
  | [], _, _ => rfl
  | a :: x, y, z => congrArg (a :: ·) (list_append_assoc x y z)

theorem pool_append {A : Type} :
    ∀ (X Y : List (List A)), pool (X ++ Y) = pool X ++ pool Y
  | [], _ => rfl
  | w :: X, Y => by
      show w ++ pool (X ++ Y) = (w ++ pool X) ++ pool Y
      rw [pool_append X Y, list_append_assoc]

theorem freq_adds (x : Bool) (X Y : List Bool) :
    freq (X ++ Y) x = freq X x + freq Y x :=
  a_seat_reads_the_sum x X Y

theorem nat_swap_mid (p q r s : Nat) :
    (p + q) + (r + s) = (p + r) + (q + s) := by
  rw [← adding_associates p q (r + s), adding_associates q r s,
      Nat.add_comm q r, ← adding_associates r q s,
      adding_associates p r (q + s)]

theorem freq_pool_map_cons (c x : Bool) :
    ∀ B : List (List Bool),
      freq (pool (B.map (c :: ·))) x
        = (if c = x then B.length else 0) + freq (pool B) x
  | [] => by
      by_cases hc : c = x
      · rw [if_pos hc]
        rfl
      · rw [if_neg hc]
        rfl
  | w :: B => by
      show freq ((c :: w) ++ pool (B.map (c :: ·))) x
          = (if c = x then B.length + 1 else 0) + freq (w ++ pool B) x
      rw [freq_adds x (c :: w) (pool (B.map (c :: ·))),
          freq_adds x w (pool B)]
      show ((if c = x then 1 else 0) + freq w x)
            + freq (pool (B.map (c :: ·))) x
          = (if c = x then B.length + 1 else 0)
            + (freq w x + freq (pool B) x)
      rw [freq_pool_map_cons c x B]
      by_cases hc : c = x
      · rw [if_pos hc, if_pos hc, if_pos hc,
            nat_swap_mid 1 (freq w x) B.length (freq (pool B) x),
            Nat.add_comm 1 B.length]
      · rw [if_neg hc, if_neg hc, if_neg hc,
            nat_swap_mid 0 (freq w x) 0 (freq (pool B) x)]

theorem the_complete_book_balances :
    ∀ n : Nat, freq (pool (book n)) true = freq (pool (book n)) false
  | 0 => rfl
  | n + 1 => by
      show freq (pool ((book n).map (true :: ·) ++ (book n).map (false :: ·)))
            true
          = freq (pool ((book n).map (true :: ·) ++ (book n).map (false :: ·)))
            false
      rw [pool_append, freq_adds true, freq_adds false,
          freq_pool_map_cons true true (book n),
          freq_pool_map_cons false true (book n),
          freq_pool_map_cons true false (book n),
          freq_pool_map_cons false false (book n),
          if_pos rfl, if_pos rfl,
          if_neg (fun h => nomatch h : ¬ false = true),
          if_neg (fun h => nomatch h : ¬ true = false),
          the_complete_book_balances n,
          Nat.add_comm ((book n).length + freq (pool (book n)) false)
            (0 + freq (pool (book n)) false)]

theorem mem_map_intro {A B : Type} (f : A → B) :
    ∀ {w : A} {L : List A}, w ∈ L → f w ∈ L.map f
  | _, _ :: _, List.Mem.head _ => List.Mem.head _
  | _, _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_map_intro f h)

theorem mem_append_left {A : Type} {w : A} :
    ∀ {X : List A} (Y : List A), w ∈ X → w ∈ X ++ Y
  | _ :: _, _, List.Mem.head _ => List.Mem.head _
  | _ :: _, Y, List.Mem.tail _ h => List.Mem.tail _ (mem_append_left Y h)

theorem the_true_run_is_in_the_book :
    ∀ n : Nat, runOf true n ∈ book n
  | 0 => List.Mem.head _
  | n + 1 =>
      mem_append_left ((book n).map (false :: ·))
        (mem_map_intro (true :: ·) (the_true_run_is_in_the_book n))

theorem mem_append_right {A : Type} {w : A} :
    ∀ (X : List A) {Y : List A}, w ∈ Y → w ∈ X ++ Y
  | [], _, h => h
  | _ :: X, _, h => List.Mem.tail _ (mem_append_right X h)

theorem the_false_run_is_in_the_book :
    ∀ n : Nat, runOf false n ∈ book n
  | 0 => List.Mem.head _
  | n + 1 =>
      mem_append_right ((book n).map (true :: ·))
        (mem_map_intro (false :: ·) (the_false_run_is_in_the_book n))

theorem the_true_run_counts_full :
    ∀ n : Nat, freq (runOf true n) true = n
  | 0 => rfl
  | n + 1 => by
      show 1 + freq (runOf true n) true = n + 1
      rw [the_true_run_counts_full n, Nat.add_comm]

theorem the_false_run_counts_none :
    ∀ n : Nat, freq (runOf false n) true = 0
  | 0 => rfl
  | n + 1 => by
      show 0 + freq (runOf false n) true = 0
      rw [the_false_run_counts_none n]

theorem no_run_reads_its_own_ratio (n : Nat) (hn : 0 < n) :
    ∃ w₁ w₂ : List Bool, w₁ ∈ book n ∧ w₂ ∈ book n
      ∧ freq w₁ true ≠ freq w₂ true :=
  ⟨runOf true n, runOf false n,
   the_true_run_is_in_the_book n,
   the_false_run_is_in_the_book n,
   fun h => by
     rw [the_true_run_counts_full n, the_false_run_counts_none n] at h
     cases n with
     | zero => exact nomatch hn
     | succ k => exact nomatch h⟩

/-- info: 'Foam.list_append_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms list_append_assoc

/-- info: 'Foam.pool_append' does not depend on any axioms -/
#guard_msgs in #print axioms pool_append

/-- info: 'Foam.freq_adds' does not depend on any axioms -/
#guard_msgs in #print axioms freq_adds

/-- info: 'Foam.nat_swap_mid' does not depend on any axioms -/
#guard_msgs in #print axioms nat_swap_mid

/-- info: 'Foam.freq_pool_map_cons' does not depend on any axioms -/
#guard_msgs in #print axioms freq_pool_map_cons

/-- info: 'Foam.the_complete_book_balances' does not depend on any axioms -/
#guard_msgs in #print axioms the_complete_book_balances

/-- info: 'Foam.mem_map_intro' does not depend on any axioms -/
#guard_msgs in #print axioms mem_map_intro

/-- info: 'Foam.mem_append_left' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_left

/-- info: 'Foam.mem_append_right' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_right

/-- info: 'Foam.the_true_run_is_in_the_book' does not depend on any axioms -/
#guard_msgs in #print axioms the_true_run_is_in_the_book

/-- info: 'Foam.the_false_run_is_in_the_book' does not depend on any axioms -/
#guard_msgs in #print axioms the_false_run_is_in_the_book

/-- info: 'Foam.the_true_run_counts_full' does not depend on any axioms -/
#guard_msgs in #print axioms the_true_run_counts_full

/-- info: 'Foam.the_false_run_counts_none' does not depend on any axioms -/
#guard_msgs in #print axioms the_false_run_counts_none

/-- info: 'Foam.no_run_reads_its_own_ratio' does not depend on any axioms -/
#guard_msgs in #print axioms no_run_reads_its_own_ratio

end Foam
