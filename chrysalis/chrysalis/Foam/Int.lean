namespace Foam.FInt

theorem add_sub_cancel (m n : Nat) : (m + n) - n = m := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, Nat.succ_sub_succ]; exact ih
theorem add_sub_cancel_left (m n : Nat) : (m + n) - m = n := by
  rw [Nat.add_comm]; exact add_sub_cancel n m
theorem sub_eq_zero_of_le {m n : Nat} (h : m ≤ n) : m - n = 0 := by
  induction h with
  | refl => exact Nat.sub_self m
  | step _ ih => rw [Nat.sub_succ, ih]; rfl
theorem subNatNat_of_ge {m n : Nat} (h : n ≤ m) : Int.subNatNat m n = Int.ofNat (m - n) := by
  show (match n - m with | 0 => Int.ofNat (m - n) | Nat.succ k => Int.negSucc k) = Int.ofNat (m - n)
  rw [sub_eq_zero_of_le h]
theorem subNatNat_add_succ (m d : Nat) : Int.subNatNat m (m + d + 1) = Int.negSucc d := by
  show (match (m+d+1) - m with | 0 => Int.ofNat (m - (m+d+1)) | Nat.succ k => Int.negSucc k) = Int.negSucc d
  have h : (m + d + 1) - m = d + 1 := by rw [Nat.add_assoc m d 1, add_sub_cancel_left]
  rw [h]
theorem subNatNat_succ_succ (m n : Nat) :
    Int.subNatNat (m+1) (n+1) = Int.subNatNat m n := by
  show (match (n+1) - (m+1) with | 0 => Int.ofNat ((m+1) - (n+1)) | Nat.succ c => Int.negSucc c)
     = (match n - m with | 0 => Int.ofNat (m - n) | Nat.succ c => Int.negSucc c)
  rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
theorem subNatNat_succ_right (a j : Nat) :
    Int.subNatNat a (j+1) + 1 = Int.subNatNat a j := by
  rcases Nat.lt_or_ge j a with hlt | hge
  · rw [subNatNat_of_ge hlt, subNatNat_of_ge (Nat.le_of_lt hlt)]
    obtain ⟨d, rfl⟩ := Nat.le.dest hlt
    have e1 : j + 1 + d - (j+1) = d := add_sub_cancel_left (j+1) d
    have e2 : j + 1 + d - j = d + 1 := by
      rw [Nat.add_assoc j 1 d, add_sub_cancel_left, Nat.add_comm 1 d]
    rw [e1, e2]; rfl
  · obtain ⟨d, rfl⟩ := Nat.le.dest hge
    rcases d with _ | d'
    · rw [Nat.add_zero]
      show Int.subNatNat a (a+1) + 1 = Int.subNatNat a a
      rw [subNatNat_add_succ a 0, subNatNat_of_ge (Nat.le_refl a), Nat.sub_self]; rfl
    · show Int.subNatNat a (a + (d'+1) + 1) + 1 = Int.subNatNat a (a + (d'+1))
      rw [subNatNat_add_succ a (d'+1),
          show a + (d'+1) = a + d' + 1 from (Nat.add_assoc a d' 1).symm, subNatNat_add_succ a d']
      rfl
theorem ofNat_succ_add (a : Nat) (s : Int) :
    Int.ofNat (a+1) + s = (Int.ofNat a + s) + 1 := by
  cases s with
  | ofNat j =>
    show Int.ofNat ((a+1)+j) = Int.ofNat (a+j) + 1
    rw [show (a+1)+j = (a+j)+1 from by rw [Nat.add_right_comm a 1 j]]; rfl
  | negSucc j =>
    show Int.subNatNat (a+1) (j+1) = Int.subNatNat a (j+1) + 1
    rw [subNatNat_succ_succ a j, subNatNat_succ_right a j]
theorem zero_add (a : Int) : 0 + a = a := by
  cases a with
  | ofNat n => show Int.ofNat (0 + n) = Int.ofNat n; rw [Nat.zero_add]
  | negSucc n => rfl
theorem subNatNat_succ_left (m k : Nat) :
    Int.subNatNat (m+1) k = Int.subNatNat m k + 1 := by
  rcases Nat.lt_or_ge k (m+1) with hlt | hge
  · have hkm : k ≤ m := Nat.le_of_lt_succ hlt
    rw [subNatNat_of_ge (Nat.le_of_lt hlt), subNatNat_of_ge hkm]
    obtain ⟨d, rfl⟩ := Nat.le.dest hkm
    rw [add_sub_cancel_left,
        show (k+d+1) - k = d+1 from by rw [Nat.add_assoc k d 1, add_sub_cancel_left]]
    rfl
  · obtain ⟨e, rfl⟩ := Nat.le.dest hge
    rcases e with _ | e'
    · rw [Nat.add_zero, subNatNat_of_ge (Nat.le_refl _), Nat.sub_self]
      rw [show Int.subNatNat m (m+1) = Int.negSucc 0 from by
            have := subNatNat_add_succ m 0; rw [Nat.add_zero] at this; exact this]
      rfl
    · rw [show (m+1)+(e'+1) = (m+1)+e'+1 from (Nat.add_assoc (m+1) e' 1).symm,
          subNatNat_add_succ (m+1) e']
      rw [show m+1+e'+1 = m+(e'+1)+1 from by rw [Nat.add_right_comm m 1 e', Nat.add_assoc m e' 1],
          subNatNat_add_succ m (e'+1)]
      rfl
theorem subNatNat_add (m n k : Nat) :
    Int.subNatNat (m + n) k = Int.ofNat m + Int.subNatNat n k := by
  induction m with
  | zero => rw [Nat.zero_add, show Int.ofNat 0 = (0:Int) from rfl, zero_add]
  | succ a ih =>
    rw [Nat.succ_add, subNatNat_succ_left (a+n) k, ih]
    exact (ofNat_succ_add a (Int.subNatNat n k)).symm
theorem add_sub_add_left (k m n : Nat) : (k + m) - (k + n) = m - n := by
  induction k with
  | zero => rw [Nat.zero_add, Nat.zero_add]
  | succ d ih =>
    rw [show d+1+m = (d+m)+1 from by rw [Nat.add_right_comm d 1 m],
        show d+1+n = (d+n)+1 from by rw [Nat.add_right_comm d 1 n],
        Nat.succ_sub_succ]; exact ih
theorem add_sub_add_right (m k n : Nat) : (m + k) - (n + k) = m - n := by
  rw [Nat.add_comm m k, Nat.add_comm n k]; exact add_sub_add_left k m n
theorem subNatNat_add_add (m n k : Nat) :
    Int.subNatNat (m + k) (n + k) = Int.subNatNat m n := by
  show (match (n+k) - (m+k) with | 0 => Int.ofNat ((m+k) - (n+k)) | Nat.succ c => Int.negSucc c)
     = (match n - m with | 0 => Int.ofNat (m - n) | Nat.succ c => Int.negSucc c)
  rw [add_sub_add_right n k m, add_sub_add_right m k n]
theorem addComm (a b : Int) : a + b = b + a := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => show Int.ofNat (m + n) = Int.ofNat (n + m); rw [Nat.add_comm]
    | negSucc n => rfl
  | negSucc m => cases b with
    | ofNat n => rfl
    | negSucc n => show Int.negSucc (m + n).succ = Int.negSucc (n + m).succ; rw [Nat.add_comm]
theorem subNatNat_add_ofNat (m n k : Nat) :
    Int.subNatNat m n + Int.ofNat k = Int.subNatNat (m + k) n := by
  rw [Nat.add_comm m k, subNatNat_add k m n, addComm]
theorem subNatNat_add_negSucc (m n k : Nat) :
    Int.subNatNat m n + Int.negSucc k = Int.subNatNat m (n + (k+1)) := by
  rcases Nat.lt_or_ge n m with hlt | hge
  · rw [subNatNat_of_ge (Nat.le_of_lt hlt)]
    show Int.subNatNat (m-n) (k+1) = Int.subNatNat m (n+(k+1))
    obtain ⟨d, rfl⟩ := Nat.le.dest (Nat.le_of_lt hlt)
    rw [add_sub_cancel_left,
        show n+d = d+n from Nat.add_comm n d, show n+(k+1) = (k+1)+n from Nat.add_comm n (k+1),
        subNatNat_add_add d (k+1) n]
  · obtain ⟨d, rfl⟩ := Nat.le.dest hge
    rcases d with _ | d'
    · rw [Nat.add_zero, subNatNat_of_ge (Nat.le_refl m), Nat.sub_self]
      show Int.negSucc k = Int.subNatNat m (m + (k+1))
      rw [show m+(k+1) = m+k+1 from (Nat.add_assoc m k 1).symm, subNatNat_add_succ m k]
    · rw [show m+(d'+1) = m+d'+1 from (Nat.add_assoc m d' 1).symm, subNatNat_add_succ m d']
      show Int.negSucc (d' + k).succ = Int.subNatNat m (m + (d'+1) + (k+1))
      rw [show m+(d'+1)+(k+1) = m + ((d'+k+1)+1) from by
            rw [Nat.add_assoc m (d'+1) (k+1)]
            apply congrArg (m + ·)
            rw [Nat.add_assoc d' 1 (k+1), Nat.add_comm 1 (k+1), ← Nat.add_assoc d' (k+1) 1,
                Nat.add_assoc d' k 1],
          show m + ((d'+k+1)+1) = m + (d'+k+1) + 1 from (Nat.add_assoc m (d'+k+1) 1).symm,
          subNatNat_add_succ m (d'+k+1)]
theorem add_assoc (a b c : Int) : a + b + c = a + (b + c) := by
  cases a with
  | ofNat p => cases b with
    | ofNat q => cases c with
      | ofNat r => show Int.ofNat (p+q+r) = Int.ofNat (p+(q+r)); rw [Nat.add_assoc]
      | negSucc r => show Int.subNatNat (p+q) (r+1) = Int.ofNat p + Int.subNatNat q (r+1); rw [subNatNat_add]
    | negSucc q => cases c with
      | ofNat r =>
        show Int.subNatNat p (q+1) + Int.ofNat r = Int.ofNat p + Int.subNatNat r (q+1)
        rw [subNatNat_add_ofNat p (q+1) r, subNatNat_add p r (q+1)]
      | negSucc r =>
        show Int.subNatNat p (q+1) + Int.negSucc r = Int.ofNat p + Int.negSucc (q + r).succ
        rw [subNatNat_add_negSucc p (q+1) r]
        show Int.subNatNat p (q+1+(r+1)) = Int.subNatNat p ((q+r).succ + 1)
        rw [Nat.add_right_comm q 1 (r+1)]; show Int.subNatNat p (q+(r+1)+1) = Int.subNatNat p ((q+r)+1+1)
        rw [← Nat.add_assoc q r 1]
  | negSucc p => cases b with
    | ofNat q => cases c with
      | ofNat r =>
        show Int.subNatNat q (p+1) + Int.ofNat r = Int.subNatNat (q+r) (p+1)
        rw [subNatNat_add_ofNat q (p+1) r]
      | negSucc r =>
        show Int.subNatNat q (p+1) + Int.negSucc r = Int.negSucc p + Int.subNatNat q (r+1)
        rw [subNatNat_add_negSucc q (p+1) r,
            addComm (Int.negSucc p) (Int.subNatNat q (r+1)), subNatNat_add_negSucc q (r+1) p]
        show Int.subNatNat q (p+1+(r+1)) = Int.subNatNat q (r+1+(p+1))
        rw [Nat.add_comm (p+1) (r+1)]
    | negSucc q => cases c with
      | ofNat r =>
        show Int.subNatNat r ((p+q).succ+1) = Int.negSucc p + Int.subNatNat r (q+1)
        rw [addComm (Int.negSucc p) (Int.subNatNat r (q+1)), subNatNat_add_negSucc r (q+1) p]
        show Int.subNatNat r ((p+q).succ+1) = Int.subNatNat r (q+1+(p+1))
        rw [Nat.add_right_comm q 1 (p+1)]; show Int.subNatNat r ((p+q)+1+1) = Int.subNatNat r (q+(p+1)+1)
        rw [← Nat.add_assoc q p 1, Nat.add_comm q p]
      | negSucc r =>
        show Int.negSucc ((p+q).succ + r).succ = Int.negSucc (p + (q+r).succ).succ
        rw [show (p+q).succ + r = p + (q+r).succ from by rw [Nat.succ_add, Nat.add_succ, Nat.add_assoc]]
theorem add_right_neg (a : Int) : a + (-a) = 0 := by
  cases a with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ k =>
      show Int.subNatNat (k+1) (k+1) = 0
      rw [subNatNat_of_ge (Nat.le_refl _), Nat.sub_self]; rfl
  | negSucc n =>
    show Int.subNatNat (n+1) (n+1) = 0
    rw [subNatNat_of_ge (Nat.le_refl _), Nat.sub_self]; rfl
theorem add_left_neg (a : Int) : (-a) + a = 0 := by
  rw [addComm]; exact add_right_neg a
theorem neg_eq_of_add_eq_zero {a b : Int} (h : a + b = 0) : -a = b := by
  rw [← Int.add_zero (-a), ← h, ← add_assoc, add_left_neg, zero_add]
theorem neg_add (a b : Int) : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  rw [add_assoc, addComm (-a) (-b), ← add_assoc b (-b) (-a), add_right_neg, zero_add, add_right_neg]
theorem subNatNat_of_lt {m n : Nat} (h : m < n) : Int.subNatNat m n = -(Int.ofNat (n - m)) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  rw [show Int.subNatNat m (m+1+d) = Int.negSucc d from by
        rw [show m+1+d = m+d+1 from by rw [Nat.add_right_comm m 1 d]]; exact subNatNat_add_succ m d]
  rw [show (m+1+d) - m = d+1 from by
        rw [Nat.add_right_comm m 1 d, Nat.add_assoc m d 1, add_sub_cancel_left]]
  rfl
theorem mulComm (a b : Int) : a * b = b * a := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => show Int.ofNat (m * n) = Int.ofNat (n * m); rw [Nat.mul_comm]
    | negSucc n => show Int.negOfNat (m * n.succ) = Int.negOfNat (n.succ * m); rw [Nat.mul_comm]
  | negSucc m => cases b with
    | ofNat n => show Int.negOfNat (m.succ * n) = Int.negOfNat (n * m.succ); rw [Nat.mul_comm]
    | negSucc n => show Int.ofNat (m.succ * n.succ) = Int.ofNat (n.succ * m.succ); rw [Nat.mul_comm]
theorem zero_mul (a : Int) : 0 * a = 0 := by
  cases a with
  | ofNat n => show Int.ofNat (0 * n) = Int.ofNat 0; rw [Nat.zero_mul]
  | negSucc n => show Int.negOfNat (0 * n.succ) = (0:Int); rw [Nat.zero_mul]; rfl
theorem mul_zero (a : Int) : a * 0 = 0 := by rw [mulComm]; exact zero_mul a
theorem mul_one (a : Int) : a * 1 = a := by
  cases a with
  | ofNat n => show Int.ofNat (n * 1) = Int.ofNat n; rw [Nat.mul_one]
  | negSucc n => show Int.negOfNat (n.succ * 1) = Int.negSucc n; rw [Nat.mul_one]; rfl
theorem one_mul (a : Int) : 1 * a = a := by rw [mulComm]; exact mul_one a
theorem neg_mul (a b : Int) : (-a) * b = -(a * b) := by
  cases a with
  | ofNat m =>
    cases m with
    | zero => show (0:Int) * b = -((0:Int) * b); rw [zero_mul]; rfl
    | succ k =>
      cases b with
      | ofNat n => show Int.negOfNat ((k+1) * n) = -(Int.ofNat ((k+1)*n)); rw [Int.negOfNat_eq]
      | negSucc n => show Int.ofNat ((k+1) * n.succ) = -(Int.negOfNat ((k+1) * n.succ)); rw [Int.negOfNat_eq, Int.neg_neg]
  | negSucc m =>
    cases b with
    | ofNat n => show Int.ofNat (m.succ * n) = -(Int.negOfNat (m.succ * n)); rw [Int.negOfNat_eq, Int.neg_neg]
    | negSucc n => show Int.negOfNat (m.succ * n.succ) = -(Int.ofNat (m.succ * n.succ)); rw [Int.negOfNat_eq]
theorem mul_neg (a b : Int) : a * (-b) = -(a * b) := by rw [mulComm a (-b), neg_mul, mulComm]
theorem nat_mul_sub (c m n : Nat) (h : n ≤ m) : c * (m - n) = c * m - c * n := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  rw [add_sub_cancel_left n d, Nat.left_distrib c n d, add_sub_cancel_left (c*n) (c*d)]
theorem ofNat_mul_subNatNat (c m n : Nat) :
    Int.ofNat c * Int.subNatNat m n = Int.subNatNat (c*m) (c*n) := by
  cases c with
  | zero => rw [show Int.ofNat 0 = (0:Int) from rfl, zero_mul, Nat.zero_mul, Nat.zero_mul]; rfl
  | succ c' =>
    rcases Nat.lt_or_ge n m with hlt | hge
    · rw [subNatNat_of_ge (Nat.le_of_lt hlt),
          subNatNat_of_ge (Nat.mul_le_mul_left (c'+1) (Nat.le_of_lt hlt))]
      show Int.ofNat ((c'+1) * (m - n)) = Int.ofNat ((c'+1)*m - (c'+1)*n)
      rw [nat_mul_sub (c'+1) m n (Nat.le_of_lt hlt)]
    · rcases Nat.eq_or_lt_of_le hge with heq | hlt
      · rw [← heq, subNatNat_of_ge (Nat.le_refl m), Nat.sub_self,
            subNatNat_of_ge (Nat.le_refl ((c'+1)*m)), Nat.sub_self]; rfl
      · have hmul : (c'+1)*m < (c'+1)*n := Nat.mul_lt_mul_of_pos_left hlt (Nat.succ_pos c')
        rw [subNatNat_of_lt hlt, subNatNat_of_lt hmul, mul_neg]
        show -(Int.ofNat ((c'+1) * (n - m))) = -(Int.ofNat ((c'+1)*n - (c'+1)*m))
        rw [nat_mul_sub (c'+1) n m (Nat.le_of_lt hlt)]
theorem ofNat_mul_ofNat (p q : Nat) : Int.ofNat p * Int.ofNat q = Int.ofNat (p*q) := rfl
theorem ofNat_mul_negSucc (p q : Nat) : Int.ofNat p * Int.negSucc q = -(Int.ofNat (p*(q+1))) := by
  rw [show Int.negSucc q = -(Int.ofNat (q+1)) from rfl, mul_neg]; rfl
theorem ofNat_add_neg_ofNat (a b : Nat) : Int.ofNat a + -(Int.ofNat b) = Int.subNatNat a b := by
  cases b with
  | zero => show Int.ofNat a + 0 = Int.subNatNat a 0; rw [Int.add_zero, subNatNat_of_ge (Nat.zero_le a), Nat.sub_zero]
  | succ k => show Int.ofNat a + Int.negSucc k = Int.subNatNat a (k+1); rfl
theorem neg_ofNat_add_ofNat (a b : Nat) : -(Int.ofNat a) + Int.ofNat b = Int.subNatNat b a := by
  rw [addComm, ofNat_add_neg_ofNat]
theorem neg_ofNat_add_neg_ofNat (a b : Nat) :
    -(Int.ofNat a) + -(Int.ofNat b) = -(Int.ofNat (a + b)) := by
  rw [← neg_add]; rfl
theorem ofNat_mul_add (p : Nat) (b c : Int) :
    Int.ofNat p * (b + c) = Int.ofNat p * b + Int.ofNat p * c := by
  cases b with
  | ofNat q => cases c with
    | ofNat r =>
      show Int.ofNat (p*(q+r)) = Int.ofNat (p*q) + Int.ofNat (p*r)
      rw [Nat.left_distrib]; rfl
    | negSucc r =>
      show Int.ofNat p * Int.subNatNat q (r+1) = Int.ofNat (p*q) + Int.ofNat p * Int.negSucc r
      rw [ofNat_mul_subNatNat p q (r+1), ofNat_mul_negSucc p r, ofNat_add_neg_ofNat]
  | negSucc q => cases c with
    | ofNat r =>
      show Int.ofNat p * Int.subNatNat r (q+1) = Int.ofNat p * Int.negSucc q + Int.ofNat (p*r)
      rw [ofNat_mul_subNatNat p r (q+1), ofNat_mul_negSucc p q,
          addComm (-(Int.ofNat (p*(q+1)))) (Int.ofNat (p*r)), ofNat_add_neg_ofNat]
    | negSucc r =>
      show Int.ofNat p * Int.negSucc (q + r).succ = Int.ofNat p * Int.negSucc q + Int.ofNat p * Int.negSucc r
      rw [ofNat_mul_negSucc p (q+r+1), ofNat_mul_negSucc p q, ofNat_mul_negSucc p r,
          neg_ofNat_add_neg_ofNat]
      show -(Int.ofNat (p * ((q+r)+1+1))) = -(Int.ofNat (p*(q+1) + p*(r+1)))
      rw [← Nat.left_distrib p (q+1) (r+1)]
      show -(Int.ofNat (p * ((q+r)+1+1))) = -(Int.ofNat (p*((q+1)+(r+1))))
      rw [show (q+1)+(r+1) = (q+r)+1+1 from by
            rw [← Nat.add_assoc (q+1) r 1, Nat.add_right_comm q 1 r]]
theorem mul_add (a b c : Int) : a * (b + c) = a * b + a * c := by
  cases a with
  | ofNat p => exact ofNat_mul_add p b c
  | negSucc p =>
    show (-(Int.ofNat (p+1))) * (b + c) = (-(Int.ofNat (p+1))) * b + (-(Int.ofNat (p+1))) * c
    rw [neg_mul, neg_mul, neg_mul, ofNat_mul_add (p+1) b c, neg_add]
theorem add_mul (a b c : Int) : (a + b) * c = a * c + b * c := by
  rw [mulComm (a+b) c, mul_add, mulComm c a, mulComm c b]
theorem nat_mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ d ih => rw [Nat.mul_succ, Nat.mul_succ, Nat.left_distrib, ih]
theorem mul_assoc (a b c : Int) : a * b * c = a * (b * c) := by
  cases a with
  | ofNat p => cases b with
    | ofNat q => cases c with
      | ofNat r => show Int.ofNat (p*q*r) = Int.ofNat (p*(q*r)); rw [nat_mul_assoc]
      | negSucc r =>
        show Int.ofNat (p*q) * Int.negSucc r = Int.ofNat p * (Int.ofNat q * Int.negSucc r)
        rw [ofNat_mul_negSucc (p*q) r, ofNat_mul_negSucc q r, mul_neg, ofNat_mul_ofNat]
        show -(Int.ofNat (p*q*(r+1))) = -(Int.ofNat (p*(q*(r+1)))); rw [nat_mul_assoc]
    | negSucc q => cases c with
      | ofNat r =>
        show Int.ofNat p * Int.negSucc q * Int.ofNat r = Int.ofNat p * (Int.negSucc q * Int.ofNat r)
        rw [ofNat_mul_negSucc p q, mulComm (Int.negSucc q) (Int.ofNat r), ofNat_mul_negSucc r q,
            neg_mul, mul_neg, ofNat_mul_ofNat]
        show -(Int.ofNat (p*(q+1)*r)) = -(Int.ofNat (p*(r*(q+1)))); rw [nat_mul_assoc, Nat.mul_comm r (q+1)]
      | negSucc r =>
        show Int.ofNat p * Int.negSucc q * Int.negSucc r = Int.ofNat p * (Int.negSucc q * Int.negSucc r)
        rw [ofNat_mul_negSucc p q, neg_mul]
        show -(Int.ofNat (p*(q+1)) * Int.negSucc r) = Int.ofNat p * (Int.negSucc q * Int.negSucc r)
        rw [ofNat_mul_negSucc (p*(q+1)) r]
        show -(-(Int.ofNat (p*(q+1)*(r+1)))) = Int.ofNat p * (Int.negSucc q * Int.negSucc r)
        rw [Int.neg_neg]
        show Int.ofNat (p*(q+1)*(r+1)) = Int.ofNat p * Int.ofNat ((q+1)*(r+1))
        rw [ofNat_mul_ofNat, nat_mul_assoc]
  | negSucc p =>
    show (-(Int.ofNat (p+1))) * b * c = (-(Int.ofNat (p+1))) * (b * c)
    rw [neg_mul, neg_mul, neg_mul]
    apply congrArg Neg.neg
    cases b with
    | ofNat q => cases c with
      | ofNat r => show Int.ofNat ((p+1)*q*r) = Int.ofNat ((p+1)*(q*r)); rw [nat_mul_assoc]
      | negSucc r =>
        show Int.ofNat ((p+1)*q) * Int.negSucc r = Int.ofNat (p+1) * (Int.ofNat q * Int.negSucc r)
        rw [ofNat_mul_negSucc ((p+1)*q) r, ofNat_mul_negSucc q r, mul_neg, ofNat_mul_ofNat]
        show -(Int.ofNat ((p+1)*q*(r+1))) = -(Int.ofNat ((p+1)*(q*(r+1)))); rw [nat_mul_assoc]
    | negSucc q => cases c with
      | ofNat r =>
        show Int.ofNat (p+1) * Int.negSucc q * Int.ofNat r = Int.ofNat (p+1) * (Int.negSucc q * Int.ofNat r)
        rw [ofNat_mul_negSucc (p+1) q, mulComm (Int.negSucc q) (Int.ofNat r), ofNat_mul_negSucc r q,
            neg_mul, mul_neg, ofNat_mul_ofNat]
        show -(Int.ofNat ((p+1)*(q+1)*r)) = -(Int.ofNat ((p+1)*(r*(q+1)))); rw [nat_mul_assoc, Nat.mul_comm r (q+1)]
      | negSucc r =>
        show Int.ofNat (p+1) * Int.negSucc q * Int.negSucc r = Int.ofNat (p+1) * (Int.negSucc q * Int.negSucc r)
        rw [ofNat_mul_negSucc (p+1) q, neg_mul, ofNat_mul_negSucc ((p+1)*(q+1)) r, Int.neg_neg]
        show Int.ofNat ((p+1)*(q+1)*(r+1)) = Int.ofNat (p+1) * Int.ofNat ((q+1)*(r+1))
        rw [ofNat_mul_ofNat, nat_mul_assoc]
theorem mul_neg_one (a : Int) : a * (-1) = -a := by rw [mul_neg, mul_one]

theorem sub_zero (a : Int) : a - 0 = a := by
  rw [Int.sub_eq_add_neg]; show a + (-0) = a; rw [show (-0:Int) = 0 from rfl, Int.add_zero]
theorem sub_add_cancel (a b : Int) : a - b + b = a := by
  rw [Int.sub_eq_add_neg, add_assoc, add_left_neg, Int.add_zero]
theorem add_sub_cancel_right (a b : Int) : a + b - b = a := by
  rw [Int.sub_eq_add_neg, add_assoc, add_right_neg, Int.add_zero]
theorem neg_sub (a b : Int) : -(a - b) = b - a := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, neg_add, Int.neg_neg, addComm]
theorem mul_sub (a b c : Int) : a * (b - c) = a * b - a * c := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, mul_add, mul_neg]
theorem sub_mul (a b c : Int) : (a - b) * c = a * c - b * c := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, add_mul, neg_mul]
theorem sub_sub (a b c : Int) : a - b - c = a - (b + c) := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg, add_assoc, neg_add]

theorem two_mul (a : Int) : 2 * a = a + a := by
  rw [show (2:Int) = 1 + 1 from rfl, add_mul, one_mul]
theorem mul_eq_zero {a b : Int} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    cases a with
    | ofNat m => cases m with
      | zero => exact Or.inl rfl
      | succ k => cases b with
        | ofNat n => cases n with
          | zero => exact Or.inr rfl
          | succ j => exact absurd h (by
              show Int.ofNat ((k+1)*(j+1)) ≠ 0
              rw [show (k+1)*(j+1) = k*(j+1)+(j+1) from Nat.succ_mul k (j+1)]
              intro hc; exact Nat.noConfusion (Int.ofNat.inj hc))
        | negSucc n => exact absurd h (by
            show Int.negOfNat ((k+1)*(n+1)) ≠ 0
            rw [show (k+1)*(n+1) = k*(n+1)+(n+1) from Nat.succ_mul k (n+1)]
            intro hc; exact Int.noConfusion hc)
    | negSucc m => cases b with
      | ofNat n => cases n with
        | zero => exact Or.inr rfl
        | succ j => exact absurd h (by
            show Int.negOfNat ((m+1)*(j+1)) ≠ 0
            rw [show (m+1)*(j+1) = m*(j+1)+(j+1) from Nat.succ_mul m (j+1)]
            intro hc; exact Int.noConfusion hc)
      | negSucc n => exact absurd h (by
          show Int.ofNat ((m+1)*(n+1)) ≠ 0
          rw [show (m+1)*(n+1) = m*(n+1)+(n+1) from Nat.succ_mul m (n+1)]
          intro hc; exact Nat.noConfusion (Int.ofNat.inj hc))
  · intro h; cases h with
    | inl ha => rw [ha, zero_mul]
    | inr hb => rw [hb, mul_zero]

/-- info: 'Foam.FInt.add_sub_cancel' does not depend on any axioms -/
#guard_msgs in #print axioms add_sub_cancel

/-- info: 'Foam.FInt.add_sub_cancel_left' does not depend on any axioms -/
#guard_msgs in #print axioms add_sub_cancel_left

/-- info: 'Foam.FInt.sub_eq_zero_of_le' does not depend on any axioms -/
#guard_msgs in #print axioms sub_eq_zero_of_le

/-- info: 'Foam.FInt.subNatNat_of_ge' does not depend on any axioms -/
#guard_msgs in #print axioms subNatNat_of_ge

/-- info: 'Foam.FInt.subNatNat_add_succ' does not depend on any axioms -/
#guard_msgs in #print axioms subNatNat_add_succ

/-- info: 'Foam.FInt.subNatNat_succ_succ' does not depend on any axioms -/
#guard_msgs in #print axioms subNatNat_succ_succ

/-- info: 'Foam.FInt.subNatNat_succ_right' does not depend on any axioms -/
#guard_msgs in #print axioms subNatNat_succ_right

/-- info: 'Foam.FInt.ofNat_succ_add' does not depend on any axioms -/
#guard_msgs in #print axioms ofNat_succ_add

/-- info: 'Foam.FInt.zero_add' does not depend on any axioms -/
#guard_msgs in #print axioms zero_add

/-- info: 'Foam.FInt.subNatNat_succ_left' does not depend on any axioms -/
#guard_msgs in #print axioms subNatNat_succ_left

/-- info: 'Foam.FInt.subNatNat_add' does not depend on any axioms -/
#guard_msgs in #print axioms subNatNat_add

/-- info: 'Foam.FInt.add_sub_add_left' does not depend on any axioms -/
#guard_msgs in #print axioms add_sub_add_left

/-- info: 'Foam.FInt.add_sub_add_right' does not depend on any axioms -/
#guard_msgs in #print axioms add_sub_add_right

/-- info: 'Foam.FInt.subNatNat_add_add' does not depend on any axioms -/
#guard_msgs in #print axioms subNatNat_add_add

/-- info: 'Foam.FInt.addComm' does not depend on any axioms -/
#guard_msgs in #print axioms addComm

/-- info: 'Foam.FInt.subNatNat_add_ofNat' does not depend on any axioms -/
#guard_msgs in #print axioms subNatNat_add_ofNat

/-- info: 'Foam.FInt.subNatNat_add_negSucc' does not depend on any axioms -/
#guard_msgs in #print axioms subNatNat_add_negSucc

/-- info: 'Foam.FInt.add_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms add_assoc

/-- info: 'Foam.FInt.add_right_neg' does not depend on any axioms -/
#guard_msgs in #print axioms add_right_neg

/-- info: 'Foam.FInt.add_left_neg' does not depend on any axioms -/
#guard_msgs in #print axioms add_left_neg

/-- info: 'Foam.FInt.neg_eq_of_add_eq_zero' does not depend on any axioms -/
#guard_msgs in #print axioms neg_eq_of_add_eq_zero

/-- info: 'Foam.FInt.neg_add' does not depend on any axioms -/
#guard_msgs in #print axioms neg_add

/-- info: 'Foam.FInt.subNatNat_of_lt' does not depend on any axioms -/
#guard_msgs in #print axioms subNatNat_of_lt

/-- info: 'Foam.FInt.mulComm' does not depend on any axioms -/
#guard_msgs in #print axioms mulComm

/-- info: 'Foam.FInt.zero_mul' does not depend on any axioms -/
#guard_msgs in #print axioms zero_mul

/-- info: 'Foam.FInt.mul_zero' does not depend on any axioms -/
#guard_msgs in #print axioms mul_zero

/-- info: 'Foam.FInt.mul_one' does not depend on any axioms -/
#guard_msgs in #print axioms mul_one

/-- info: 'Foam.FInt.one_mul' does not depend on any axioms -/
#guard_msgs in #print axioms one_mul

/-- info: 'Foam.FInt.neg_mul' does not depend on any axioms -/
#guard_msgs in #print axioms neg_mul

/-- info: 'Foam.FInt.mul_neg' does not depend on any axioms -/
#guard_msgs in #print axioms mul_neg

/-- info: 'Foam.FInt.nat_mul_sub' does not depend on any axioms -/
#guard_msgs in #print axioms nat_mul_sub

/-- info: 'Foam.FInt.ofNat_mul_subNatNat' does not depend on any axioms -/
#guard_msgs in #print axioms ofNat_mul_subNatNat

/-- info: 'Foam.FInt.ofNat_mul_ofNat' does not depend on any axioms -/
#guard_msgs in #print axioms ofNat_mul_ofNat

/-- info: 'Foam.FInt.ofNat_mul_negSucc' does not depend on any axioms -/
#guard_msgs in #print axioms ofNat_mul_negSucc

/-- info: 'Foam.FInt.ofNat_add_neg_ofNat' does not depend on any axioms -/
#guard_msgs in #print axioms ofNat_add_neg_ofNat

/-- info: 'Foam.FInt.neg_ofNat_add_ofNat' does not depend on any axioms -/
#guard_msgs in #print axioms neg_ofNat_add_ofNat

/-- info: 'Foam.FInt.neg_ofNat_add_neg_ofNat' does not depend on any axioms -/
#guard_msgs in #print axioms neg_ofNat_add_neg_ofNat

/-- info: 'Foam.FInt.ofNat_mul_add' does not depend on any axioms -/
#guard_msgs in #print axioms ofNat_mul_add

/-- info: 'Foam.FInt.mul_add' does not depend on any axioms -/
#guard_msgs in #print axioms mul_add

/-- info: 'Foam.FInt.add_mul' does not depend on any axioms -/
#guard_msgs in #print axioms add_mul

/-- info: 'Foam.FInt.nat_mul_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms nat_mul_assoc

/-- info: 'Foam.FInt.mul_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms mul_assoc

/-- info: 'Foam.FInt.mul_neg_one' does not depend on any axioms -/
#guard_msgs in #print axioms mul_neg_one

/-- info: 'Foam.FInt.sub_zero' does not depend on any axioms -/
#guard_msgs in #print axioms sub_zero

/-- info: 'Foam.FInt.sub_add_cancel' does not depend on any axioms -/
#guard_msgs in #print axioms sub_add_cancel

/-- info: 'Foam.FInt.add_sub_cancel_right' does not depend on any axioms -/
#guard_msgs in #print axioms add_sub_cancel_right

/-- info: 'Foam.FInt.neg_sub' does not depend on any axioms -/
#guard_msgs in #print axioms neg_sub

/-- info: 'Foam.FInt.mul_sub' does not depend on any axioms -/
#guard_msgs in #print axioms mul_sub

/-- info: 'Foam.FInt.sub_mul' does not depend on any axioms -/
#guard_msgs in #print axioms sub_mul

/-- info: 'Foam.FInt.sub_sub' does not depend on any axioms -/
#guard_msgs in #print axioms sub_sub

/-- info: 'Foam.FInt.two_mul' does not depend on any axioms -/
#guard_msgs in #print axioms two_mul

/-- info: 'Foam.FInt.mul_eq_zero' does not depend on any axioms -/
#guard_msgs in #print axioms mul_eq_zero

end Foam.FInt
