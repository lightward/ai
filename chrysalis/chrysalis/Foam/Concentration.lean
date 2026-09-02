import Foam.Expectation
import Foam.Fold
import Foam.Amplitude
import Foam.Continuum

namespace Foam

def nearBalance (b n : Nat) (w : List Bool) : Bool :=
  Bool.and (Nat.ble (b * n) (n + 2 * (b * freq w true)))
    (Nat.ble (2 * (b * freq w true)) (n + b * n))

def dev (n : Nat) (w : List Bool) : Int :=
  2 * Int.ofNat (freq w true) - Int.ofNat n

def sqDev (n : Nat) (w : List Bool) : Int := dev n w * dev n w

def sumOver (f : List Bool → Int) : List (List Bool) → Int
  | [] => 0
  | w :: B => f w + sumOver f B

theorem dev_read (n : Nat) (w : List Bool) :
    dev n w = Int.subNatNat (2 * freq w true) n := by
  show 2 * Int.ofNat (freq w true) - Int.ofNat n = _
  rw [Int.sub_eq_add_neg,
      show (2 : Int) * Int.ofNat (freq w true) = Int.ofNat (2 * freq w true)
        from rfl,
      FInt.ofNat_add_neg_ofNat]

theorem dev_true (n : Nat) (w : List Bool) :
    dev (n + 1) (true :: w) = dev n w + 1 := by
  rw [dev_read, dev_read]
  show Int.subNatNat (2 * (1 + freq w true)) (n + 1)
      = Int.subNatNat (2 * freq w true) n + 1
  rw [Nat.left_distrib, show (2 : Nat) * 1 = 2 from rfl,
      Nat.add_comm 2 (2 * freq w true)]
  show Int.subNatNat ((2 * freq w true + 1) + 1) (n + 1) = _
  rw [FInt.subNatNat_succ_succ, FInt.subNatNat_succ_left]

theorem dev_false (n : Nat) (w : List Bool) :
    dev (n + 1) (false :: w) = dev n w - 1 := by
  rw [dev_read, dev_read]
  show Int.subNatNat (2 * (0 + freq w true)) (n + 1)
      = Int.subNatNat (2 * freq w true) n - 1
  rw [nothing_added, Int.sub_eq_add_neg,
      ← FInt.subNatNat_succ_right (2 * freq w true) n,
      FInt.add_assoc, FInt.add_right_neg, Int.add_zero]

theorem pair_of_squares (d : Int) :
    (d + 1) * (d + 1) + (d - 1) * (d - 1) = (d * d + d * d) + 2 := by
  rw [Int.sub_eq_add_neg, sq_add d 1, sq_add d (-1),
      neg_mul_neg_self 1, FInt.mul_neg, FInt.mul_one, FInt.mul_one,
      swap_mid (d * d + 1) (d + d) (d * d + 1) (-d + -d),
      swap_mid d d (-d) (-d), FInt.add_right_neg d, FInt.zero_add,
      Int.add_zero, swap_mid (d * d) 1 (d * d) 1]
  rfl

theorem sumOver_append (f : List Bool → Int) :
    ∀ X Y : List (List Bool), sumOver f (X ++ Y) = sumOver f X + sumOver f Y
  | [], Y => (FInt.zero_add (sumOver f Y)).symm
  | w :: X, Y => by
      show f w + sumOver f (X ++ Y) = (f w + sumOver f X) + sumOver f Y
      rw [sumOver_append f X Y, FInt.add_assoc]

theorem sumOver_map (f : List Bool → Int) (g : List Bool → List Bool) :
    ∀ B : List (List Bool), sumOver f (B.map g) = sumOver (fun w => f (g w)) B
  | [] => rfl
  | w :: B => congrArg (f (g w) + ·) (sumOver_map f g B)

theorem sumOver_add (f g : List Bool → Int) :
    ∀ B : List (List Bool),
      sumOver (fun w => f w + g w) B = sumOver f B + sumOver g B
  | [] => rfl
  | w :: B => by
      show (f w + g w) + sumOver (fun w => f w + g w) B
          = (f w + sumOver f B) + (g w + sumOver g B)
      rw [sumOver_add f g B, swap_mid]

theorem sumOver_congr {f g : List Bool → Int} (h : ∀ w, f w = g w) :
    ∀ B : List (List Bool), sumOver f B = sumOver g B
  | [] => rfl
  | w :: B => by
      show f w + sumOver f B = g w + sumOver g B
      rw [h w, sumOver_congr h B]

theorem sumOver_const (c : Int) :
    ∀ B : List (List Bool), sumOver (fun _ => c) B = Int.ofNat B.length * c
  | [] => (FInt.zero_mul c).symm
  | w :: B => by
      show c + sumOver (fun _ => c) B = Int.ofNat (B.length + 1) * c
      rw [sumOver_const c B,
          show Int.ofNat (B.length + 1) = Int.ofNat B.length + 1 from rfl,
          FInt.add_mul, FInt.one_mul, int_add_comm c]

theorem len_append {A : Type} :
    ∀ X Y : List A, (X ++ Y).length = X.length + Y.length
  | [], Y => (nothing_added Y.length).symm
  | _ :: X, Y => by
      show (X ++ Y).length + 1 = (X.length + 1) + Y.length
      rw [len_append X Y, succ_adds]

theorem len_map {A B : Type} (g : A → B) :
    ∀ X : List A, (X.map g).length = X.length
  | [] => rfl
  | _ :: X => congrArg (· + 1) (len_map g X)

theorem the_book_has_two_to_the_n :
    ∀ n : Nat, (book n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
      show ((book n).map (true :: ·) ++ (book n).map (false :: ·)).length
          = 2 ^ (n + 1)
      rw [len_append, len_map, len_map, the_book_has_two_to_the_n n,
          show (2 : Nat) ^ (n + 1) = 2 ^ n * 2 from rfl,
          show (2 : Nat) ^ n * 2 = 2 ^ n * 1 + 2 ^ n from rfl,
          Nat.mul_one]

theorem sqDev_true (n : Nat) (w : List Bool) :
    sqDev (n + 1) (true :: w) = (dev n w + 1) * (dev n w + 1) := by
  show dev (n + 1) (true :: w) * dev (n + 1) (true :: w) = _
  rw [dev_true]

theorem sqDev_false (n : Nat) (w : List Bool) :
    sqDev (n + 1) (false :: w) = (dev n w - 1) * (dev n w - 1) := by
  show dev (n + 1) (false :: w) * dev (n + 1) (false :: w) = _
  rw [dev_false]

theorem pair_sq_sqDev (n : Nat) (w : List Bool) :
    (dev n w + 1) * (dev n w + 1) + (dev n w - 1) * (dev n w - 1)
      = (sqDev n w + sqDev n w) + 2 :=
  pair_of_squares (dev n w)

theorem succ_mul' (a b : Nat) : (a + 1) * b = a * b + b := Nat.succ_mul a b

theorem nat_mul_two (a : Nat) : a * 2 = a + a := by
  show a * 1 + a = a + a
  rw [Nat.mul_one]

theorem depth_step_arith (n : Nat) :
    (n * 2 ^ n + n * 2 ^ n) + 2 ^ n * 2 = (n + 1) * 2 ^ (n + 1) := by
  rw [nat_mul_two,
      show (2 : Nat) ^ (n + 1) = 2 ^ n * 2 from rfl, nat_mul_two,
      succ_mul', Nat.left_distrib]

theorem the_squares_pool_to_the_depth :
    ∀ n : Nat, sumOver (sqDev n) (book n) = Int.ofNat n * Int.ofNat (2 ^ n)
  | 0 => rfl
  | n + 1 => by
      show sumOver (sqDev (n + 1))
            ((book n).map (true :: ·) ++ (book n).map (false :: ·)) = _
      rw [sumOver_append, sumOver_map, sumOver_map,
          sumOver_congr (sqDev_true n) (book n),
          sumOver_congr (sqDev_false n) (book n),
          ← sumOver_add,
          sumOver_congr (fun w => pair_sq_sqDev n w) (book n),
          sumOver_add, sumOver_add,
          the_squares_pool_to_the_depth n,
          sumOver_const, the_book_has_two_to_the_n n]
      exact congrArg Int.ofNat (depth_step_arith n)

def natSqDev (n : Nat) (w : List Bool) : Nat :=
  (2 * freq w true - n) * (2 * freq w true - n)
    + (n - 2 * freq w true) * (n - 2 * freq w true)

def natSumOver (v : List Bool → Nat) : List (List Bool) → Nat
  | [] => 0
  | w :: B => v w + natSumOver v B

theorem ofNat_natSqDev (n : Nat) (w : List Bool) :
    Int.ofNat (natSqDev n w) = sqDev n w := by
  show Int.ofNat ((2 * freq w true - n) * (2 * freq w true - n)
        + (n - 2 * freq w true) * (n - 2 * freq w true))
      = dev n w * dev n w
  cases Nat.lt_or_ge (2 * freq w true) n with
  | inl hlt =>
      rw [FInt.sub_eq_zero_of_le (Nat.le_of_lt hlt), Nat.zero_mul,
          nothing_added, dev_read, FInt.subNatNat_of_lt hlt, neg_mul_neg_self]
      rfl
  | inr hge =>
      rw [FInt.sub_eq_zero_of_le hge, Nat.zero_mul, Nat.add_zero,
          dev_read, FInt.subNatNat_of_ge hge]
      rfl

theorem ofNat_natSumOver (n : Nat) :
    ∀ B : List (List Bool),
      Int.ofNat (natSumOver (natSqDev n) B) = sumOver (sqDev n) B
  | [] => rfl
  | w :: B => by
      show Int.ofNat (natSqDev n w + natSumOver (natSqDev n) B)
          = sqDev n w + sumOver (sqDev n) B
      rw [← ofNat_natSqDev n w, ← ofNat_natSumOver n B]
      rfl

theorem the_nat_squares_pool (n : Nat) :
    natSumOver (natSqDev n) (book n) = n * 2 ^ n :=
  Int.ofNat.inj ((ofNat_natSumOver n (book n)).trans
    (show sumOver (sqDev n) (book n) = Int.ofNat (n * 2 ^ n) from
      the_squares_pool_to_the_depth n))

theorem natSumOver_mul (m : Nat) (v : List Bool → Nat) :
    ∀ L : List (List Bool),
      natSumOver (fun w => m * v w) L = m * natSumOver v L
  | [] => rfl
  | w :: L => by
      show m * v w + natSumOver (fun w => m * v w) L
          = m * (v w + natSumOver v L)
      rw [natSumOver_mul m v L, Nat.left_distrib]

theorem cancel_add_left : ∀ (k : Nat) {a b : Nat}, k + a ≤ k + b → a ≤ b
  | 0, _, _, h => by rw [nothing_added, nothing_added] at h; exact h
  | k + 1, a, b, h => by
      rw [succ_adds, succ_adds] at h
      exact cancel_add_left k (succ_le_succ_inv h)

theorem cancel_add_right {a b : Nat} (k : Nat) (h : a + k ≤ b + k) : a ≤ b := by
  rw [Nat.add_comm a k, Nat.add_comm b k] at h
  exact cancel_add_left k h

theorem lt_of_ble_false : ∀ m n : Nat, Nat.ble m n = false → n < m
  | 0, _, h => nomatch h
  | m + 1, 0, _ => Nat.zero_lt_succ m
  | m + 1, n + 1, h => Nat.succ_le_succ (lt_of_ble_false m n h)

theorem and_false_split :
    ∀ x y : Bool, Bool.and x y = false → x = false ∨ y = false
  | false, _, _ => Or.inl rfl
  | true, _, h => Or.inr h

theorem two_shuffle (b k : Nat) : b * (2 * k) = 2 * (b * k) := by
  rw [← FInt.nat_mul_assoc b 2 k, Nat.mul_comm b 2, FInt.nat_mul_assoc 2 b k]

theorem sq_mul_sq (a c : Nat) : (a * a) * (c * c) = (a * c) * (a * c) := by
  rw [FInt.nat_mul_assoc a a (c * c), FInt.nat_mul_assoc a c (a * c),
      ← FInt.nat_mul_assoc c a c, Nat.mul_comm c a, FInt.nat_mul_assoc a c c]

theorem deviant_low_pays (b n k : Nat) (h : n + 2 * (b * k) < b * n) :
    (n + 1) * (n + 1)
      ≤ (b * b) * ((2 * k - n) * (2 * k - n) + (n - 2 * k) * (n - 2 * k)) := by
  have h2k : 2 * k ≤ n := by
    cases Nat.lt_or_ge n (2 * k) with
    | inl hlt =>
        have hbn : b * n ≤ 2 * (b * k) := by
          rw [← two_shuffle]
          exact Nat.mul_le_mul_left b (Nat.le_of_lt hlt)
        exact (no_number_is_below_itself _
          (le_trans h (le_trans hbn (Nat.le_add_left _ n)))).elim
    | inr hge => exact hge
  obtain ⟨d, hd⟩ := Nat.le.dest h2k
  rw [← hd] at h
  rw [Nat.left_distrib, two_shuffle,
      Nat.add_comm (2 * k + d) (2 * (b * k))] at h
  have hkey : (2 * k + d) + 1 ≤ b * d := cancel_add_left (2 * (b * k)) h
  rw [FInt.sub_eq_zero_of_le h2k, Nat.zero_mul, nothing_added, ← hd,
      FInt.add_sub_cancel_left, sq_mul_sq b d]
  exact Nat.mul_le_mul hkey hkey

theorem deviant_high_pays (b n k : Nat) (h : n + b * n < 2 * (b * k)) :
    (n + 1) * (n + 1)
      ≤ (b * b) * ((2 * k - n) * (2 * k - n) + (n - 2 * k) * (n - 2 * k)) := by
  have hn2k : n ≤ 2 * k := by
    cases Nat.lt_or_ge (2 * k) n with
    | inl hlt =>
        have hb : 2 * (b * k) ≤ b * n := by
          rw [← two_shuffle]
          exact Nat.mul_le_mul_left b (Nat.le_of_lt hlt)
        exact (no_number_is_below_itself _
          (le_trans h (le_trans hb (Nat.le_add_left _ n)))).elim
    | inr hge => exact hge
  obtain ⟨e, he⟩ := Nat.le.dest hn2k
  rw [← two_shuffle, ← he, Nat.left_distrib, Nat.add_comm n (b * n)] at h
  have hkey : n + 1 ≤ b * e := cancel_add_left (b * n) h
  rw [FInt.sub_eq_zero_of_le hn2k, Nat.zero_mul, ← he,
      FInt.add_sub_cancel_left]
  show (n + 1) * (n + 1) ≤ (b * b) * (e * e)
  rw [sq_mul_sq b e]
  exact Nat.mul_le_mul hkey hkey

theorem deviant_pays (b n : Nat) (w : List Bool)
    (h : nearBalance b n w = false) :
    (n + 1) * (n + 1) ≤ (b * b) * natSqDev n w := by
  cases and_false_split _ _ h with
  | inl hA =>
      exact deviant_low_pays b n (freq w true) (lt_of_ble_false _ _ hA)
  | inr hB =>
      exact deviant_high_pays b n (freq w true) (lt_of_ble_false _ _ hB)

theorem ne_true_of_eq_false {x : Bool} (h : x = false) : ¬ x = true :=
  fun ht => nomatch h.symm.trans ht

theorem count_pays (p : List Bool → Bool) (v : List Bool → Nat) (C : Nat)
    (hpay : ∀ w, p w = false → C ≤ v w) :
    ∀ L : List (List Bool),
      (List.filter (fun w => Bool.not (p w)) L).length * C ≤ natSumOver v L
  | [] => by
      show 0 * C ≤ 0
      rw [Nat.zero_mul]
      exact Nat.le_refl 0
  | w :: L => by
      cases hp : p w with
      | true =>
          rw [List.filter_cons_of_neg (p := fun u => Bool.not (p u)) (a := w)
                (ne_true_of_eq_false ((congrArg Bool.not hp).trans rfl))]
          exact le_trans (count_pays p v C hpay L) (Nat.le_add_left _ _)
      | false =>
          rw [List.filter_cons_of_pos (p := fun u => Bool.not (p u)) (a := w)
                ((congrArg Bool.not hp).trans rfl)]
          show ((List.filter (fun w => Bool.not (p w)) L).length + 1) * C
              ≤ v w + natSumOver v L
          rw [succ_mul', Nat.add_comm (v w) (natSumOver v L)]
          exact Nat.add_le_add (count_pays p v C hpay L) (hpay w hp)

theorem filter_partition {A : Type} (q : A → Bool) :
    ∀ L : List A,
      (List.filter q L).length
          + (List.filter (fun a => Bool.not (q a)) L).length
        = L.length
  | [] => rfl
  | a :: L => by
      cases hq : q a with
      | true =>
          rw [List.filter_cons_of_pos hq,
              List.filter_cons_of_neg (p := fun u => Bool.not (q u)) (a := a)
                (ne_true_of_eq_false ((congrArg Bool.not hq).trans rfl))]
          show ((List.filter q L).length + 1)
              + (List.filter (fun a => Bool.not (q a)) L).length
            = L.length + 1
          rw [succ_adds, filter_partition q L]
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq),
              List.filter_cons_of_pos (p := fun u => Bool.not (q u)) (a := a)
                ((congrArg Bool.not hq).trans rfl)]
          show ((List.filter q L).length
              + (List.filter (fun a => Bool.not (q a)) L).length) + 1
            = L.length + 1
          rw [filter_partition q L]

theorem filter_none {A : Type} (q : A → Bool) (hq : ∀ a, q a = false) :
    ∀ L : List A, List.filter q L = []
  | [] => rfl
  | a :: L => by
      rw [List.filter_cons_of_neg (ne_true_of_eq_false (hq a)),
          filter_none q hq L]

theorem nearBalance_zero (n : Nat) (w : List Bool) :
    nearBalance 0 n w = true := by
  show Bool.and (Nat.ble (0 * n) (n + 2 * (0 * freq w true)))
        (Nat.ble (2 * (0 * freq w true)) (n + 0 * n)) = true
  rw [Nat.zero_mul, Nat.zero_mul]
  rfl

theorem shuffle_cap (D C B m : Nat) :
    D * ((C * B) * m) = (B * m) * (C * D) := by
  rw [FInt.nat_mul_assoc C B m, ← FInt.nat_mul_assoc D C (B * m),
      Nat.mul_comm (D * C) (B * m), Nat.mul_comm D C]

theorem outnumbered_of_pos (b c n : Nat) (hb : 0 < b)
    (hn : (c + 1) * (b * b) ≤ n) :
    c * (List.filter (fun w => Bool.not (nearBalance b n w)) (book n)).length
      ≤ (List.filter (fun w => nearBalance b n w) (book n)).length := by
  have hcap := count_pays (nearBalance b n)
      (fun w => (b * b) * natSqDev n w) ((n + 1) * (n + 1))
      (fun w hw => deviant_pays b n w hw) (book n)
  rw [natSumOver_mul (b * b) (natSqDev n) (book n),
      the_nat_squares_pool n] at hcap
  have h1 : (c + 1) * (b * b) ≤ n + 1 := le_trans hn (Nat.le_succ n)
  have h2 := Nat.mul_le_mul_left
      ((List.filter (fun w => Bool.not (nearBalance b n w)) (book n)).length)
      (Nat.mul_le_mul_right (n + 1) h1)
  have h3 : (b * b) * (n * 2 ^ n) ≤ (b * b * (n + 1)) * 2 ^ n := by
    rw [← FInt.nat_mul_assoc (b * b) n (2 ^ n)]
    exact Nat.mul_le_mul_right (2 ^ n) (Nat.mul_le_mul_left (b * b) (Nat.le_succ n))
  have h4 : (b * b * (n + 1))
        * ((c + 1)
          * (List.filter (fun w => Bool.not (nearBalance b n w)) (book n)).length)
      ≤ (b * b * (n + 1)) * 2 ^ n := by
    rw [← shuffle_cap
          ((List.filter (fun w => Bool.not (nearBalance b n w)) (book n)).length)
          (c + 1) (b * b) (n + 1)]
    exact le_trans h2 (le_trans hcap h3)
  have h5 := Nat.le_of_mul_le_mul_left h4
      (Nat.mul_pos (Nat.mul_pos hb hb) (Nat.zero_lt_succ n))
  have hpart := filter_partition (nearBalance b n) (book n)
  rw [the_book_has_two_to_the_n n] at hpart
  rw [← hpart, succ_mul'] at h5
  exact cancel_add_right _ h5

theorem the_deviants_are_outnumbered (b c : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      c * (List.filter (fun w => Bool.not (nearBalance b n w)) (book n)).length
        ≤ (List.filter (fun w => nearBalance b n w) (book n)).length := by
  cases b with
  | zero =>
      refine ⟨0, fun n _ => ?_⟩
      rw [filter_none (fun w => Bool.not (nearBalance 0 n w))
            (fun w => (congrArg Bool.not (nearBalance_zero n w)).trans rfl)
            (book n)]
      exact Nat.zero_le _
  | succ s =>
      exact ⟨(c + 1) * ((s + 1) * (s + 1)), fun n hn =>
        outnumbered_of_pos (s + 1) c n (Nat.zero_lt_succ s) hn⟩

theorem fold_reads_the_sum (f : List Bool → Int) :
    ∀ (B : List (List Bool)) (z : Int),
      fold (fun acc w => acc + f w) z B = z + sumOver f B
  | [], z => (Int.add_zero z).symm
  | w :: B, z => by
      show fold (fun acc w => acc + f w) (z + f w) B
          = z + (f w + sumOver f B)
      rw [fold_reads_the_sum f B (z + f w), FInt.add_assoc]

theorem the_pooled_square_caps_the_deviants (b n : Nat) :
    (List.filter (fun w => Bool.not (nearBalance b n w)) (book n)).length
        * ((n + 1) * (n + 1))
      ≤ (b * b) * (n * 2 ^ n) := by
  have hcap := count_pays (nearBalance b n)
      (fun w => (b * b) * natSqDev n w) ((n + 1) * (n + 1))
      (fun w hw => deviant_pays b n w hw) (book n)
  rw [natSumOver_mul (b * b) (natSqDev n) (book n),
      the_nat_squares_pool n] at hcap
  exact hcap

/-- info: 'Foam.fold_reads_the_sum' does not depend on any axioms -/
#guard_msgs in #print axioms fold_reads_the_sum

/-- info: 'Foam.the_pooled_square_caps_the_deviants' does not depend on any axioms -/
#guard_msgs in #print axioms the_pooled_square_caps_the_deviants

/-- info: 'Foam.dev_read' does not depend on any axioms -/
#guard_msgs in #print axioms dev_read

/-- info: 'Foam.dev_true' does not depend on any axioms -/
#guard_msgs in #print axioms dev_true

/-- info: 'Foam.dev_false' does not depend on any axioms -/
#guard_msgs in #print axioms dev_false

/-- info: 'Foam.pair_of_squares' does not depend on any axioms -/
#guard_msgs in #print axioms pair_of_squares

/-- info: 'Foam.sumOver_append' does not depend on any axioms -/
#guard_msgs in #print axioms sumOver_append

/-- info: 'Foam.sumOver_map' does not depend on any axioms -/
#guard_msgs in #print axioms sumOver_map

/-- info: 'Foam.sumOver_add' does not depend on any axioms -/
#guard_msgs in #print axioms sumOver_add

/-- info: 'Foam.sumOver_congr' does not depend on any axioms -/
#guard_msgs in #print axioms sumOver_congr

/-- info: 'Foam.sumOver_const' does not depend on any axioms -/
#guard_msgs in #print axioms sumOver_const

/-- info: 'Foam.len_append' does not depend on any axioms -/
#guard_msgs in #print axioms len_append

/-- info: 'Foam.len_map' does not depend on any axioms -/
#guard_msgs in #print axioms len_map

/-- info: 'Foam.the_book_has_two_to_the_n' does not depend on any axioms -/
#guard_msgs in #print axioms the_book_has_two_to_the_n

/-- info: 'Foam.sqDev_true' does not depend on any axioms -/
#guard_msgs in #print axioms sqDev_true

/-- info: 'Foam.sqDev_false' does not depend on any axioms -/
#guard_msgs in #print axioms sqDev_false

/-- info: 'Foam.pair_sq_sqDev' does not depend on any axioms -/
#guard_msgs in #print axioms pair_sq_sqDev

/-- info: 'Foam.succ_mul'' does not depend on any axioms -/
#guard_msgs in #print axioms succ_mul'

/-- info: 'Foam.nat_mul_two' does not depend on any axioms -/
#guard_msgs in #print axioms nat_mul_two

/-- info: 'Foam.depth_step_arith' does not depend on any axioms -/
#guard_msgs in #print axioms depth_step_arith

/-- info: 'Foam.the_squares_pool_to_the_depth' does not depend on any axioms -/
#guard_msgs in #print axioms the_squares_pool_to_the_depth

/-- info: 'Foam.ofNat_natSqDev' does not depend on any axioms -/
#guard_msgs in #print axioms ofNat_natSqDev

/-- info: 'Foam.ofNat_natSumOver' does not depend on any axioms -/
#guard_msgs in #print axioms ofNat_natSumOver

/-- info: 'Foam.the_nat_squares_pool' does not depend on any axioms -/
#guard_msgs in #print axioms the_nat_squares_pool

/-- info: 'Foam.natSumOver_mul' does not depend on any axioms -/
#guard_msgs in #print axioms natSumOver_mul

/-- info: 'Foam.cancel_add_left' does not depend on any axioms -/
#guard_msgs in #print axioms cancel_add_left

/-- info: 'Foam.cancel_add_right' does not depend on any axioms -/
#guard_msgs in #print axioms cancel_add_right

/-- info: 'Foam.lt_of_ble_false' does not depend on any axioms -/
#guard_msgs in #print axioms lt_of_ble_false

/-- info: 'Foam.and_false_split' does not depend on any axioms -/
#guard_msgs in #print axioms and_false_split

/-- info: 'Foam.two_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms two_shuffle

/-- info: 'Foam.sq_mul_sq' does not depend on any axioms -/
#guard_msgs in #print axioms sq_mul_sq

/-- info: 'Foam.deviant_low_pays' does not depend on any axioms -/
#guard_msgs in #print axioms deviant_low_pays

/-- info: 'Foam.deviant_high_pays' does not depend on any axioms -/
#guard_msgs in #print axioms deviant_high_pays

/-- info: 'Foam.deviant_pays' does not depend on any axioms -/
#guard_msgs in #print axioms deviant_pays

/-- info: 'Foam.ne_true_of_eq_false' does not depend on any axioms -/
#guard_msgs in #print axioms ne_true_of_eq_false

/-- info: 'Foam.count_pays' does not depend on any axioms -/
#guard_msgs in #print axioms count_pays

/-- info: 'Foam.filter_partition' does not depend on any axioms -/
#guard_msgs in #print axioms filter_partition

/-- info: 'Foam.filter_none' does not depend on any axioms -/
#guard_msgs in #print axioms filter_none

/-- info: 'Foam.nearBalance_zero' does not depend on any axioms -/
#guard_msgs in #print axioms nearBalance_zero

/-- info: 'Foam.shuffle_cap' does not depend on any axioms -/
#guard_msgs in #print axioms shuffle_cap

/-- info: 'Foam.outnumbered_of_pos' does not depend on any axioms -/
#guard_msgs in #print axioms outnumbered_of_pos

/-- info: 'Foam.the_deviants_are_outnumbered' does not depend on any axioms -/
#guard_msgs in #print axioms the_deviants_are_outnumbered

end Foam
