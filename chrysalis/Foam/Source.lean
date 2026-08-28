import Foam.Marks

namespace Foam

def weightOf (t f : Nat) (w : List Bool) : Nat :=
  t ^ freq w true * f ^ freq w false

def nearLean (t f b n : Nat) (w : List Bool) : Bool :=
  Bool.and (Nat.ble (b * (t * n)) (n + b * ((t + f) * freq w true)))
    (Nat.ble (b * ((t + f) * freq w true)) (n + b * (t * n)))

def tilt (t f n : Nat) (w : List Bool) : Int :=
  Int.ofNat ((t + f) * freq w true) - Int.ofNat (t * n)

def tiltTerm (t f n : Nat) (w : List Bool) : Int :=
  Int.ofNat (weightOf t f w) * (tilt t f n w * tilt t f n w)

def natSqTilt (t f n : Nat) (w : List Bool) : Nat :=
  ((t + f) * freq w true - t * n) * ((t + f) * freq w true - t * n)
    + (t * n - (t + f) * freq w true) * (t * n - (t + f) * freq w true)

theorem weight_true (t f : Nat) (w : List Bool) :
    weightOf t f (true :: w) = t * weightOf t f w := by
  show t ^ (1 + freq w true) * f ^ (0 + freq w false)
      = t * (t ^ freq w true * f ^ freq w false)
  rw [nothing_added, Nat.add_comm 1 (freq w true)]
  show t ^ freq w true * t * f ^ freq w false
      = t * (t ^ freq w true * f ^ freq w false)
  rw [Nat.mul_comm (t ^ freq w true) t, FInt.nat_mul_assoc]

theorem weight_false (t f : Nat) (w : List Bool) :
    weightOf t f (false :: w) = f * weightOf t f w := by
  show t ^ (0 + freq w true) * f ^ (1 + freq w false)
      = f * (t ^ freq w true * f ^ freq w false)
  rw [nothing_added, Nat.add_comm 1 (freq w false)]
  show t ^ freq w true * (f ^ freq w false * f)
      = f * (t ^ freq w true * f ^ freq w false)
  rw [← FInt.nat_mul_assoc,
      Nat.mul_comm (t ^ freq w true * f ^ freq w false) f]

theorem lean_shift (a t f : Nat) : (t + f) + a = (a + f) + t := by
  rw [Nat.add_comm (t + f) a, Nat.add_comm t f, adding_associates a f t]

theorem tilt_read (t f n : Nat) (w : List Bool) :
    tilt t f n w = Int.subNatNat ((t + f) * freq w true) (t * n) := by
  show Int.ofNat ((t + f) * freq w true) - Int.ofNat (t * n) = _
  rw [Int.sub_eq_add_neg, FInt.ofNat_add_neg_ofNat]

theorem tilt_true (t f n : Nat) (w : List Bool) :
    tilt t f (n + 1) (true :: w) = tilt t f n w + Int.ofNat f := by
  rw [tilt_read, tilt_read]
  show Int.subNatNat ((t + f) * (1 + freq w true)) (t * (n + 1))
      = Int.subNatNat ((t + f) * freq w true) (t * n) + Int.ofNat f
  rw [Nat.left_distrib (t + f) 1 (freq w true), Nat.mul_one,
      show t * (n + 1) = t * n + t from rfl,
      lean_shift ((t + f) * freq w true) t f,
      FInt.subNatNat_add_add ((t + f) * freq w true + f) (t * n) t,
      ← FInt.subNatNat_add_ofNat ((t + f) * freq w true) (t * n) f]

theorem subNatNat_sub_ofNat (m n k : Nat) :
    Int.subNatNat m n - Int.ofNat k = Int.subNatNat m (n + k) := by
  cases k with
  | zero =>
      show Int.subNatNat m n - 0 = Int.subNatNat m (n + 0)
      rw [FInt.sub_zero]
      rfl
  | succ s =>
      rw [Int.sub_eq_add_neg]
      show Int.subNatNat m n + Int.negSucc s = Int.subNatNat m (n + (s + 1))
      rw [FInt.subNatNat_add_negSucc]

theorem tilt_false (t f n : Nat) (w : List Bool) :
    tilt t f (n + 1) (false :: w) = tilt t f n w - Int.ofNat t := by
  rw [tilt_read, tilt_read]
  show Int.subNatNat ((t + f) * (0 + freq w true)) (t * (n + 1))
      = Int.subNatNat ((t + f) * freq w true) (t * n) - Int.ofNat t
  rw [nothing_added (freq w true),
      show t * (n + 1) = t * n + t from rfl,
      subNatNat_sub_ofNat]

theorem pair_cancel (x : Int) : (x + x) + (-x + -x) = 0 := by
  rw [swap_mid x x (-x) (-x), FInt.add_right_neg x]
  rfl

theorem pair_of_tilted_squares (T F D : Int) :
    T * ((D + F) * (D + F)) + F * ((D - T) * (D - T))
      = (T + F) * (D * D) + (T * F) * (T + F) := by
  have hx : T * (D * F) = F * (D * T) := by
    rw [FInt.mulComm D F, ← FInt.mul_assoc T F D, FInt.mulComm T F,
        FInt.mul_assoc F T D, FInt.mulComm T D]
  rw [Int.sub_eq_add_neg, sq_add D F, sq_add D (-T), neg_mul_neg_self T,
      FInt.mul_neg D T,
      FInt.mul_add T (D * D + F * F) (D * F + D * F),
      FInt.mul_add F (D * D + T * T) (-(D * T) + -(D * T)),
      swap_mid (T * (D * D + F * F)) (T * (D * F + D * F))
        (F * (D * D + T * T)) (F * (-(D * T) + -(D * T))),
      FInt.mul_add T (D * F) (D * F),
      FInt.mul_add F (-(D * T)) (-(D * T)),
      FInt.mul_neg F (D * T),
      hx,
      pair_cancel (F * (D * T)),
      Int.add_zero,
      FInt.mul_add T (D * D) (F * F),
      FInt.mul_add F (D * D) (T * T),
      swap_mid (T * (D * D)) (T * (F * F)) (F * (D * D)) (F * (T * T)),
      ← FInt.add_mul T F (D * D),
      ← FInt.mul_assoc T F F,
      ← FInt.mul_assoc F T T,
      FInt.mulComm F T,
      ← FInt.mul_add (T * F) F T,
      int_add_comm F T]

theorem tiltTerm_true (t f n : Nat) (w : List Bool) :
    tiltTerm t f (n + 1) (true :: w)
      = Int.ofNat t * (Int.ofNat (weightOf t f w)
          * ((tilt t f n w + Int.ofNat f) * (tilt t f n w + Int.ofNat f))) := by
  show Int.ofNat (weightOf t f (true :: w))
      * (tilt t f (n + 1) (true :: w) * tilt t f (n + 1) (true :: w)) = _
  rw [weight_true, tilt_true, ← FInt.ofNat_mul_ofNat t (weightOf t f w),
      FInt.mul_assoc]

theorem tiltTerm_false (t f n : Nat) (w : List Bool) :
    tiltTerm t f (n + 1) (false :: w)
      = Int.ofNat f * (Int.ofNat (weightOf t f w)
          * ((tilt t f n w - Int.ofNat t) * (tilt t f n w - Int.ofNat t))) := by
  show Int.ofNat (weightOf t f (false :: w))
      * (tilt t f (n + 1) (false :: w) * tilt t f (n + 1) (false :: w)) = _
  rw [weight_false, tilt_false, ← FInt.ofNat_mul_ofNat f (weightOf t f w),
      FInt.mul_assoc]

theorem tilt_step_combines (t f n : Nat) (w : List Bool) :
    Int.ofNat t * (Int.ofNat (weightOf t f w)
        * ((tilt t f n w + Int.ofNat f) * (tilt t f n w + Int.ofNat f)))
      + Int.ofNat f * (Int.ofNat (weightOf t f w)
          * ((tilt t f n w - Int.ofNat t) * (tilt t f n w - Int.ofNat t)))
      = Int.ofNat (t + f) * tiltTerm t f n w
        + Int.ofNat (t * f * (t + f)) * Int.ofNat (weightOf t f w) := by
  have hswap : ∀ c x y : Int, c * (x * y) = x * (c * y) := fun c x y => by
    rw [← FInt.mul_assoc c x y, FInt.mulComm c x, FInt.mul_assoc x c y]
  rw [hswap (Int.ofNat t) (Int.ofNat (weightOf t f w))
        ((tilt t f n w + Int.ofNat f) * (tilt t f n w + Int.ofNat f)),
      hswap (Int.ofNat f) (Int.ofNat (weightOf t f w))
        ((tilt t f n w - Int.ofNat t) * (tilt t f n w - Int.ofNat t)),
      ← FInt.mul_add (Int.ofNat (weightOf t f w)),
      pair_of_tilted_squares (Int.ofNat t) (Int.ofNat f) (tilt t f n w),
      FInt.mul_add (Int.ofNat (weightOf t f w)),
      hswap (Int.ofNat (weightOf t f w)) (Int.ofNat t + Int.ofNat f)
        (tilt t f n w * tilt t f n w),
      FInt.mulComm (Int.ofNat (weightOf t f w))
        ((Int.ofNat t * Int.ofNat f) * (Int.ofNat t + Int.ofNat f))]
  rfl

theorem natSumOver_append (v : List Bool → Nat) :
    ∀ X Y : List (List Bool),
      natSumOver v (X ++ Y) = natSumOver v X + natSumOver v Y
  | [], _ => (nothing_added _).symm
  | w :: X, Y => by
      show v w + natSumOver v (X ++ Y)
          = (v w + natSumOver v X) + natSumOver v Y
      rw [natSumOver_append v X Y, adding_associates]

theorem natSumOver_congr {v u : List Bool → Nat} (h : ∀ w, v w = u w) :
    ∀ B : List (List Bool), natSumOver v B = natSumOver u B
  | [] => rfl
  | w :: B => by
      show v w + natSumOver v B = u w + natSumOver u B
      rw [h w, natSumOver_congr h B]

theorem natSumOver_ofNat (v : List Bool → Nat) :
    ∀ B : List (List Bool),
      Int.ofNat (natSumOver v B) = sumOver (fun w => Int.ofNat (v w)) B
  | [] => rfl
  | w :: B => by
      show Int.ofNat (v w + natSumOver v B)
          = Int.ofNat (v w) + sumOver (fun w => Int.ofNat (v w)) B
      rw [← natSumOver_ofNat v B]
      rfl

theorem sumOver_smul (c : Int) (v : List Bool → Int) :
    ∀ B : List (List Bool),
      sumOver (fun w => c * v w) B = c * sumOver v B
  | [] => (FInt.mul_zero c).symm
  | w :: B => by
      show c * v w + sumOver (fun w => c * v w) B = c * (v w + sumOver v B)
      rw [sumOver_smul c v B, FInt.mul_add]

theorem the_weighted_book_sums_whole (t f : Nat) :
    ∀ n : Nat, natSumOver (weightOf t f) (book n) = (t + f) ^ n
  | 0 => by
      show weightOf t f [] + 0 = (t + f) ^ 0
      rfl
  | n + 1 => by
      show natSumOver (weightOf t f)
            ((book n).map (true :: ·) ++ (book n).map (false :: ·))
          = (t + f) ^ (n + 1)
      rw [natSumOver_append,
          natSumOver_map (weightOf t f) (true :: ·) (book n),
          natSumOver_map (weightOf t f) (false :: ·) (book n),
          natSumOver_congr (weight_true t f) (book n),
          natSumOver_congr (weight_false t f) (book n),
          natSumOver_mul t (weightOf t f) (book n),
          natSumOver_mul f (weightOf t f) (book n),
          the_weighted_book_sums_whole t f n,
          Nat.mul_comm t ((t + f) ^ n), Nat.mul_comm f ((t + f) ^ n),
          ← Nat.left_distrib ((t + f) ^ n) t f]
      rfl

theorem tilt_depth_arith (t f n P : Nat) :
    (t + f) * ((n * (t * f)) * P) + (t * f * (t + f)) * P
      = ((n + 1) * (t * f)) * (P * (t + f)) := by
  rw [← FInt.nat_mul_assoc (t + f) (n * (t * f)) P,
      Nat.mul_comm (t + f) (n * (t * f)),
      FInt.nat_mul_assoc (n * (t * f)) (t + f) P,
      FInt.nat_mul_assoc (t * f) (t + f) P,
      Nat.mul_comm (n * (t * f)) ((t + f) * P),
      Nat.mul_comm (t * f) ((t + f) * P),
      ← Nat.left_distrib ((t + f) * P) (n * (t * f)) (t * f),
      ← succ_mul' n (t * f),
      Nat.mul_comm ((t + f) * P) ((n + 1) * (t * f)),
      Nat.mul_comm (t + f) P]

theorem the_tilts_pool_to_the_depth (t f : Nat) :
    ∀ n : Nat, sumOver (tiltTerm t f n) (book n)
      = Int.ofNat ((n * (t * f)) * (t + f) ^ n)
  | 0 => by
      rw [Nat.zero_mul (t * f), Nat.zero_mul ((t + f) ^ 0)]
      rfl
  | n + 1 => by
      show sumOver (tiltTerm t f (n + 1))
            ((book n).map (true :: ·) ++ (book n).map (false :: ·))
          = Int.ofNat (((n + 1) * (t * f)) * (t + f) ^ (n + 1))
      rw [sumOver_append,
          sumOver_map (tiltTerm t f (n + 1)) (true :: ·) (book n),
          sumOver_map (tiltTerm t f (n + 1)) (false :: ·) (book n),
          sumOver_congr (tiltTerm_true t f n) (book n),
          sumOver_congr (tiltTerm_false t f n) (book n),
          ← sumOver_add,
          sumOver_congr (tilt_step_combines t f n) (book n),
          sumOver_add,
          sumOver_smul (Int.ofNat (t + f)) (tiltTerm t f n) (book n),
          sumOver_smul (Int.ofNat (t * f * (t + f)))
            (fun w => Int.ofNat (weightOf t f w)) (book n),
          the_tilts_pool_to_the_depth t f n,
          ← natSumOver_ofNat (weightOf t f) (book n),
          the_weighted_book_sums_whole t f n,
          FInt.ofNat_mul_ofNat (t + f) ((n * (t * f)) * (t + f) ^ n),
          FInt.ofNat_mul_ofNat (t * f * (t + f)) ((t + f) ^ n)]
      exact congrArg Int.ofNat (tilt_depth_arith t f n ((t + f) ^ n))

theorem ofNat_natSqTilt (t f n : Nat) (w : List Bool) :
    Int.ofNat (natSqTilt t f n w) = tilt t f n w * tilt t f n w := by
  show Int.ofNat
        (((t + f) * freq w true - t * n) * ((t + f) * freq w true - t * n)
          + (t * n - (t + f) * freq w true) * (t * n - (t + f) * freq w true))
      = tilt t f n w * tilt t f n w
  cases Nat.lt_or_ge ((t + f) * freq w true) (t * n) with
  | inl hlt =>
      rw [FInt.sub_eq_zero_of_le (Nat.le_of_lt hlt), Nat.zero_mul,
          nothing_added, tilt_read, FInt.subNatNat_of_lt hlt,
          neg_mul_neg_self]
      rfl
  | inr hge =>
      rw [FInt.sub_eq_zero_of_le hge, Nat.zero_mul, Nat.add_zero,
          tilt_read, FInt.subNatNat_of_ge hge]
      rfl

theorem ofNat_weight_natSqTilt (t f n : Nat) (w : List Bool) :
    Int.ofNat (weightOf t f w * natSqTilt t f n w) = tiltTerm t f n w := by
  rw [← FInt.ofNat_mul_ofNat, ofNat_natSqTilt]
  rfl

theorem the_nat_tilts_pool (t f n : Nat) :
    natSumOver (fun w => weightOf t f w * natSqTilt t f n w) (book n)
      = (n * (t * f)) * (t + f) ^ n :=
  Int.ofNat.inj (by
    rw [natSumOver_ofNat (fun w => weightOf t f w * natSqTilt t f n w)
          (book n),
        sumOver_congr (ofNat_weight_natSqTilt t f n) (book n)]
    exact the_tilts_pool_to_the_depth t f n)

theorem tilted_low_pays (b n A B : Nat) (h : n + b * A < b * B) :
    (n + 1) * (n + 1)
      ≤ (b * b) * ((A - B) * (A - B) + (B - A) * (B - A)) := by
  have hAB : A ≤ B := by
    cases Nat.lt_or_ge A B with
    | inl hlt => exact Nat.le_of_lt hlt
    | inr hge =>
        have hb : b * B ≤ b * A := Nat.mul_le_mul_left b hge
        exact (no_number_is_below_itself (n + b * A)
          (le_trans h (le_trans hb (Nat.le_add_left (b * A) n)))).elim
  obtain ⟨d, hd⟩ := Nat.le.dest hAB
  rw [← hd, Nat.left_distrib b A d, Nat.add_comm n (b * A)] at h
  have hkey : n + 1 ≤ b * d := cancel_add_left (b * A) h
  rw [FInt.sub_eq_zero_of_le hAB, Nat.zero_mul, nothing_added, ← hd,
      FInt.add_sub_cancel_left, sq_mul_sq b d]
  exact Nat.mul_le_mul hkey hkey

theorem tilted_high_pays (b n A B : Nat) (h : n + b * B < b * A) :
    (n + 1) * (n + 1)
      ≤ (b * b) * ((A - B) * (A - B) + (B - A) * (B - A)) := by
  have hBA : B ≤ A := by
    cases Nat.lt_or_ge B A with
    | inl hlt => exact Nat.le_of_lt hlt
    | inr hge =>
        have hb : b * A ≤ b * B := Nat.mul_le_mul_left b hge
        exact (no_number_is_below_itself (n + b * B)
          (le_trans h (le_trans hb (Nat.le_add_left (b * B) n)))).elim
  obtain ⟨d, hd⟩ := Nat.le.dest hBA
  rw [← hd, Nat.left_distrib b B d, Nat.add_comm n (b * B)] at h
  have hkey : n + 1 ≤ b * d := cancel_add_left (b * B) h
  rw [FInt.sub_eq_zero_of_le hBA, Nat.zero_mul, ← hd,
      FInt.add_sub_cancel_left]
  show (n + 1) * (n + 1) ≤ (b * b) * (d * d)
  rw [sq_mul_sq b d]
  exact Nat.mul_le_mul hkey hkey

theorem tilted_pays (t f b n : Nat) (w : List Bool)
    (h : nearLean t f b n w = false) :
    (n + 1) * (n + 1) ≤ (b * b) * natSqTilt t f n w := by
  cases and_false_split _ _ h with
  | inl hA =>
      exact tilted_low_pays b n ((t + f) * freq w true) (t * n)
        (lt_of_ble_false _ _ hA)
  | inr hB =>
      exact tilted_high_pays b n ((t + f) * freq w true) (t * n)
        (lt_of_ble_false _ _ hB)

theorem weighted_count_pays (p : List Bool → Bool) (u v : List Bool → Nat)
    (C : Nat) (hpay : ∀ w, p w = false → C ≤ v w) :
    ∀ L : List (List Bool),
      natSumOver u (List.filter (fun w => Bool.not (p w)) L) * C
        ≤ natSumOver (fun w => u w * v w) L
  | [] => by
      show 0 * C ≤ 0
      rw [Nat.zero_mul]
      exact Nat.le_refl 0
  | w :: L => by
      cases hp : p w with
      | true =>
          rw [List.filter_cons_of_neg (p := fun x => Bool.not (p x)) (a := w)
                (ne_true_of_eq_false ((congrArg Bool.not hp).trans rfl))]
          exact le_trans (weighted_count_pays p u v C hpay L)
            (Nat.le_add_left _ _)
      | false =>
          rw [List.filter_cons_of_pos (p := fun x => Bool.not (p x)) (a := w)
                ((congrArg Bool.not hp).trans rfl)]
          show (u w + natSumOver u (List.filter (fun x => Bool.not (p x)) L))
                * C
              ≤ u w * v w + natSumOver (fun x => u x * v x) L
          rw [Nat.mul_comm
                (u w + natSumOver u (List.filter (fun x => Bool.not (p x)) L))
                C,
              Nat.left_distrib C (u w)
                (natSumOver u (List.filter (fun x => Bool.not (p x)) L))]
          exact Nat.add_le_add
            (by rw [Nat.mul_comm C (u w)]
                exact Nat.mul_le_mul_left (u w) (hpay w hp))
            (by rw [Nat.mul_comm C
                      (natSumOver u
                        (List.filter (fun x => Bool.not (p x)) L))]
                exact weighted_count_pays p u v C hpay L)

theorem natSumOver_partition (q : List Bool → Bool) (u : List Bool → Nat) :
    ∀ L : List (List Bool),
      natSumOver u (List.filter q L)
          + natSumOver u (List.filter (fun a => Bool.not (q a)) L)
        = natSumOver u L
  | [] => rfl
  | w :: L => by
      cases hq : q w with
      | true =>
          rw [List.filter_cons_of_pos (l := L) hq,
              List.filter_cons_of_neg (p := fun a => Bool.not (q a)) (a := w)
                (ne_true_of_eq_false ((congrArg Bool.not hq).trans rfl))]
          show (u w + natSumOver u (List.filter q L))
              + natSumOver u (List.filter (fun a => Bool.not (q a)) L)
            = u w + natSumOver u L
          rw [← adding_associates, natSumOver_partition q u L]
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq),
              List.filter_cons_of_pos (p := fun a => Bool.not (q a)) (a := w)
                ((congrArg Bool.not hq).trans rfl)]
          show natSumOver u (List.filter q L)
              + (u w + natSumOver u (List.filter (fun a => Bool.not (q a)) L))
            = u w + natSumOver u L
          rw [adding_associates,
              Nat.add_comm (natSumOver u (List.filter q L)) (u w),
              ← adding_associates, natSumOver_partition q u L]

theorem cap_shuffle (q r a m P : Nat) :
    q * (r * ((m * a) * P)) = (q * (r * a)) * (m * P) := by
  rw [FInt.nat_mul_assoc m a P,
      ← FInt.nat_mul_assoc r m (a * P),
      Nat.mul_comm r m,
      FInt.nat_mul_assoc m r (a * P),
      ← FInt.nat_mul_assoc r a P,
      FInt.nat_mul_assoc q (r * a) (m * P),
      ← FInt.nat_mul_assoc (r * a) m P,
      Nat.mul_comm (r * a) m,
      FInt.nat_mul_assoc m (r * a) P]

theorem the_deviants_are_outweighed (t f b c : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      c * natSumOver (weightOf t f)
            (List.filter (fun w => Bool.not (nearLean t f b n w)) (book n))
        ≤ natSumOver (weightOf t f)
            (List.filter (fun w => nearLean t f b n w) (book n)) := by
  refine ⟨(c + 1) * ((b * b) * (t * f)), fun n hn => ?_⟩
  have hcap := weighted_count_pays (nearLean t f b n) (weightOf t f)
      (fun w => (b * b) * natSqTilt t f n w) ((n + 1) * (n + 1))
      (fun w hw => tilted_pays t f b n w hw) (book n)
  have hpt : ∀ w, weightOf t f w * ((b * b) * natSqTilt t f n w)
      = (b * b) * (weightOf t f w * natSqTilt t f n w) := fun w => by
    rw [← FInt.nat_mul_assoc (weightOf t f w) (b * b) (natSqTilt t f n w),
        Nat.mul_comm (weightOf t f w) (b * b),
        FInt.nat_mul_assoc (b * b) (weightOf t f w) (natSqTilt t f n w)]
  rw [natSumOver_congr hpt (book n),
      natSumOver_mul (b * b)
        (fun w => weightOf t f w * natSqTilt t f n w) (book n),
      the_nat_tilts_pool t f n] at hcap
  have h2 := Nat.mul_le_mul_left (c + 1) hcap
  rw [cap_shuffle (c + 1) (b * b) (t * f) n ((t + f) ^ n)] at h2
  have h4 : n * (n * (t + f) ^ n) ≤ ((n + 1) * (n + 1)) * (t + f) ^ n := by
    rw [← FInt.nat_mul_assoc n n ((t + f) ^ n)]
    exact Nat.mul_le_mul_right ((t + f) ^ n)
      (Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n))
  have h5 := le_trans h2
    (le_trans (Nat.mul_le_mul_right (n * (t + f) ^ n) hn) h4)
  rw [← FInt.nat_mul_assoc (c + 1)
        (natSumOver (weightOf t f)
          (List.filter (fun w => Bool.not (nearLean t f b n w)) (book n)))
        ((n + 1) * (n + 1)),
      Nat.mul_comm
        ((c + 1) * natSumOver (weightOf t f)
          (List.filter (fun w => Bool.not (nearLean t f b n w)) (book n)))
        ((n + 1) * (n + 1))] at h5
  have h6 := Nat.le_of_mul_le_mul_left h5
    (Nat.mul_pos (Nat.zero_lt_succ n) (Nat.zero_lt_succ n))
  have hpart := natSumOver_partition (fun w => nearLean t f b n w)
    (weightOf t f) (book n)
  rw [the_weighted_book_sums_whole t f n] at hpart
  rw [succ_mul', ← hpart] at h6
  exact cancel_add_right _ h6

/-- info: 'Foam.weight_true' does not depend on any axioms -/
#guard_msgs in #print axioms weight_true

/-- info: 'Foam.weight_false' does not depend on any axioms -/
#guard_msgs in #print axioms weight_false

/-- info: 'Foam.lean_shift' does not depend on any axioms -/
#guard_msgs in #print axioms lean_shift

/-- info: 'Foam.tilt_read' does not depend on any axioms -/
#guard_msgs in #print axioms tilt_read

/-- info: 'Foam.tilt_true' does not depend on any axioms -/
#guard_msgs in #print axioms tilt_true

/-- info: 'Foam.subNatNat_sub_ofNat' does not depend on any axioms -/
#guard_msgs in #print axioms subNatNat_sub_ofNat

/-- info: 'Foam.tilt_false' does not depend on any axioms -/
#guard_msgs in #print axioms tilt_false

/-- info: 'Foam.pair_cancel' does not depend on any axioms -/
#guard_msgs in #print axioms pair_cancel

/-- info: 'Foam.pair_of_tilted_squares' does not depend on any axioms -/
#guard_msgs in #print axioms pair_of_tilted_squares

/-- info: 'Foam.tiltTerm_true' does not depend on any axioms -/
#guard_msgs in #print axioms tiltTerm_true

/-- info: 'Foam.tiltTerm_false' does not depend on any axioms -/
#guard_msgs in #print axioms tiltTerm_false

/-- info: 'Foam.tilt_step_combines' does not depend on any axioms -/
#guard_msgs in #print axioms tilt_step_combines

/-- info: 'Foam.natSumOver_append' does not depend on any axioms -/
#guard_msgs in #print axioms natSumOver_append

/-- info: 'Foam.natSumOver_congr' does not depend on any axioms -/
#guard_msgs in #print axioms natSumOver_congr

/-- info: 'Foam.natSumOver_ofNat' does not depend on any axioms -/
#guard_msgs in #print axioms natSumOver_ofNat

/-- info: 'Foam.sumOver_smul' does not depend on any axioms -/
#guard_msgs in #print axioms sumOver_smul

/-- info: 'Foam.the_weighted_book_sums_whole' does not depend on any axioms -/
#guard_msgs in #print axioms the_weighted_book_sums_whole

/-- info: 'Foam.tilt_depth_arith' does not depend on any axioms -/
#guard_msgs in #print axioms tilt_depth_arith

/-- info: 'Foam.the_tilts_pool_to_the_depth' does not depend on any axioms -/
#guard_msgs in #print axioms the_tilts_pool_to_the_depth

/-- info: 'Foam.ofNat_natSqTilt' does not depend on any axioms -/
#guard_msgs in #print axioms ofNat_natSqTilt

/-- info: 'Foam.ofNat_weight_natSqTilt' does not depend on any axioms -/
#guard_msgs in #print axioms ofNat_weight_natSqTilt

/-- info: 'Foam.the_nat_tilts_pool' does not depend on any axioms -/
#guard_msgs in #print axioms the_nat_tilts_pool

/-- info: 'Foam.tilted_low_pays' does not depend on any axioms -/
#guard_msgs in #print axioms tilted_low_pays

/-- info: 'Foam.tilted_high_pays' does not depend on any axioms -/
#guard_msgs in #print axioms tilted_high_pays

/-- info: 'Foam.tilted_pays' does not depend on any axioms -/
#guard_msgs in #print axioms tilted_pays

/-- info: 'Foam.weighted_count_pays' does not depend on any axioms -/
#guard_msgs in #print axioms weighted_count_pays

/-- info: 'Foam.natSumOver_partition' does not depend on any axioms -/
#guard_msgs in #print axioms natSumOver_partition

/-- info: 'Foam.cap_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms cap_shuffle

/-- info: 'Foam.the_deviants_are_outweighed' does not depend on any axioms -/
#guard_msgs in #print axioms the_deviants_are_outweighed

end Foam
