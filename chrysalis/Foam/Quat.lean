import Foam.Amplitude

namespace Foam

def GInt.zero : GInt := ⟨0, 0⟩

def GInt.one : GInt := ⟨1, 0⟩

def GInt.mul (z w : GInt) : GInt :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

structure Quat where
  a : GInt
  b : GInt

def Quat.mul (x y : Quat) : Quat :=
  ⟨(x.a.mul y.a).add ((y.b.conj.mul x.b).neg),
   (y.b.mul x.a).add (x.b.mul y.a.conj)⟩

def Quat.neg (x : Quat) : Quat := ⟨x.a.neg, x.b.neg⟩

def one : Quat := ⟨GInt.one, GInt.zero⟩

def eye : Quat := ⟨GInt.i, GInt.zero⟩

def jay : Quat := ⟨GInt.zero, GInt.one⟩

def kay : Quat := ⟨GInt.zero, GInt.i⟩

theorem the_couple_of_couples_multiplies : Quat.mul eye jay = kay := rfl

theorem the_reversed_couple_parts : Quat.mul jay eye = Quat.neg kay := rfl

theorem order_arrives : Quat.mul eye jay ≠ Quat.mul jay eye :=
  fun h => nomatch (GInt.mk.inj (Quat.mk.inj h).2).2

theorem i2_eq_j2_eq_k2_eq_ijk_eq_neg_one :
    Quat.mul eye eye = Quat.neg one
      ∧ Quat.mul jay jay = Quat.neg one
      ∧ Quat.mul kay kay = Quat.neg one
      ∧ Quat.mul (Quat.mul eye jay) kay = Quat.neg one :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem the_half_turn_hears_no_order :
    Quat.mul (Quat.neg one) eye = Quat.mul eye (Quat.neg one)
      ∧ Quat.mul (Quat.neg one) jay = Quat.mul jay (Quat.neg one)
      ∧ Quat.mul (Quat.neg one) kay = Quat.mul kay (Quat.neg one) :=
  ⟨rfl, rfl, rfl⟩

theorem every_axis_reaches_the_same_half_turn :
    Quat.mul eye eye = Quat.mul jay jay
      ∧ Quat.mul jay jay = Quat.mul kay kay :=
  ⟨rfl, rfl⟩

theorem two_half_turns_come_home :
    Quat.mul (Quat.mul eye eye) (Quat.mul eye eye) = one := rfl

theorem gmul_comm (z w : GInt) : z.mul w = w.mul z := by
  show (⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ : GInt)
      = ⟨w.re * z.re - w.im * z.im, w.re * z.im + w.im * z.re⟩
  rw [FInt.mulComm z.re w.re, FInt.mulComm z.im w.im,
      FInt.mulComm z.re w.im, FInt.mulComm z.im w.re,
      int_add_comm (w.im * z.re) (w.re * z.im)]

theorem gmul_assoc (z w v : GInt) : (z.mul w).mul v = z.mul (w.mul v) := by
  show (⟨(z.re * w.re - z.im * w.im) * v.re
          - (z.re * w.im + z.im * w.re) * v.im,
         (z.re * w.re - z.im * w.im) * v.im
          + (z.re * w.im + z.im * w.re) * v.re⟩ : GInt)
      = ⟨z.re * (w.re * v.re - w.im * v.im)
          - z.im * (w.re * v.im + w.im * v.re),
         z.re * (w.re * v.im + w.im * v.re)
          + z.im * (w.re * v.re - w.im * v.im)⟩
  rw [FInt.sub_mul, FInt.add_mul, FInt.sub_mul, FInt.add_mul,
      FInt.mul_sub, FInt.mul_add, FInt.mul_add, FInt.mul_sub,
      FInt.mul_assoc z.re w.re v.re, FInt.mul_assoc z.im w.im v.re,
      FInt.mul_assoc z.re w.im v.im, FInt.mul_assoc z.im w.re v.im,
      FInt.mul_assoc z.re w.re v.im, FInt.mul_assoc z.im w.im v.im,
      FInt.mul_assoc z.re w.im v.re, FInt.mul_assoc z.im w.re v.re,
      FInt.sub_sub, FInt.sub_sub,
      FInt.addComm (z.im * (w.im * v.re)) (z.re * (w.im * v.im)
        + z.im * (w.re * v.im)),
      FInt.add_assoc (z.re * (w.im * v.im)) (z.im * (w.re * v.im))
        (z.im * (w.im * v.re)),
      Int.sub_eq_add_neg, Int.sub_eq_add_neg,
      swap_mid (z.re * (w.re * v.im)) (-(z.im * (w.im * v.im)))
        (z.re * (w.im * v.re)) (z.im * (w.re * v.re)),
      int_add_comm (-(z.im * (w.im * v.im))) (z.im * (w.re * v.re)),
      Int.sub_eq_add_neg]

theorem conj_mul (z w : GInt) : (z.mul w).conj = z.conj.mul w.conj := by
  show (⟨z.re * w.re - z.im * w.im, -(z.re * w.im + z.im * w.re)⟩ : GInt)
      = ⟨z.re * w.re - -z.im * -w.im, z.re * -w.im + -z.im * w.re⟩
  rw [FInt.neg_mul z.im (-w.im), FInt.mul_neg z.im w.im, int_neg_neg,
      FInt.mul_neg z.re w.im, FInt.neg_mul z.im w.re, ← FInt.neg_add]

theorem mul_conj_is_the_norm (w : GInt) : w.mul w.conj = ⟨w.normSq, 0⟩ := by
  show (⟨w.re * w.re - w.im * -w.im, w.re * -w.im + w.im * w.re⟩ : GInt)
      = ⟨w.re * w.re + w.im * w.im, 0⟩
  rw [FInt.mul_neg w.im w.im, Int.sub_eq_add_neg, int_neg_neg,
      FInt.mul_neg w.re w.im, FInt.mulComm w.im w.re, FInt.add_left_neg]

theorem real_couples_multiply (k m : Int) :
    (GInt.mk k 0).mul (GInt.mk m 0) = ⟨k * m, 0⟩ := by
  show (⟨k * m - 0 * 0, k * 0 + 0 * m⟩ : GInt) = ⟨k * m, 0⟩
  rw [FInt.zero_mul, FInt.sub_zero, FInt.mul_zero, FInt.zero_mul,
      FInt.zero_add]

theorem the_couple_carries_the_norm (z w : GInt) :
    (z.mul w).normSq = z.normSq * w.normSq := by
  have h2 : (z.mul w).mul (z.mul w).conj
      = (z.mul z.conj).mul (w.mul w.conj) := by
    rw [conj_mul, gmul_assoc, ← gmul_assoc w z.conj w.conj,
        gmul_comm w z.conj, gmul_assoc z.conj w w.conj, ← gmul_assoc]
  have h3 : (⟨(z.mul w).normSq, 0⟩ : GInt) = ⟨z.normSq * w.normSq, 0⟩ := by
    rw [← mul_conj_is_the_norm (z.mul w), h2, mul_conj_is_the_norm z,
        mul_conj_is_the_norm w, real_couples_multiply]
  exact congrArg GInt.re h3

theorem align_reads_the_conjugate_product (z w : GInt) :
    z.align w = (z.mul w.conj).re := by
  show z.re * w.re + z.im * w.im = z.re * w.re - z.im * -w.im
  rw [FInt.mul_neg, Int.sub_eq_add_neg, int_neg_neg]

theorem the_norm_ignores_the_flip (z : GInt) : z.neg.normSq = z.normSq := by
  show -z.re * -z.re + -z.im * -z.im = z.re * z.re + z.im * z.im
  rw [neg_mul_neg_self, neg_mul_neg_self]

theorem align_flips_with_the_arm (z w : GInt) :
    z.align w.neg = -(z.align w) := by
  show z.re * -w.re + z.im * -w.im = -(z.re * w.re + z.im * w.im)
  rw [FInt.mul_neg, FInt.mul_neg, ← FInt.neg_add]

theorem the_cross_terms_agree (x y : Quat) :
    (x.a.mul y.a).align (y.b.conj.mul x.b)
      = (y.b.mul x.a).align (x.b.mul y.a.conj) := by
  rw [align_reads_the_conjugate_product, align_reads_the_conjugate_product,
      conj_mul, conj_mul, conj_is_an_involution, conj_is_an_involution]
  exact congrArg GInt.re (by
    rw [gmul_assoc, ← gmul_assoc y.a y.b x.b.conj, gmul_comm y.a y.b,
        gmul_assoc y.b y.a x.b.conj, ← gmul_assoc, gmul_comm x.a y.b,
        gmul_comm x.b.conj y.a])

def Quat.normSq (q : Quat) : Int := q.a.normSq + q.b.normSq

theorem the_quadruple_carries_the_norm (x y : Quat) :
    (x.mul y).normSq = x.normSq * y.normSq := by
  show ((x.a.mul y.a).add ((y.b.conj.mul x.b).neg)).normSq
        + ((y.b.mul x.a).add (x.b.mul y.a.conj)).normSq
      = (x.a.normSq + x.b.normSq) * (y.a.normSq + y.b.normSq)
  rw [the_screen_reads_a_cross_term, the_screen_reads_a_cross_term,
      the_norm_ignores_the_flip,
      align_flips_with_the_arm, the_cross_terms_agree,
      the_couple_carries_the_norm, the_couple_carries_the_norm,
      the_couple_carries_the_norm, the_couple_carries_the_norm,
      conj_conserves_the_norm, conj_conserves_the_norm,
      swap_mid
        (x.a.normSq * y.a.normSq + y.b.normSq * x.b.normSq)
        (-((y.b.mul x.a).align (x.b.mul y.a.conj))
          + -((y.b.mul x.a).align (x.b.mul y.a.conj)))
        (y.b.normSq * x.a.normSq + x.b.normSq * y.a.normSq)
        ((y.b.mul x.a).align (x.b.mul y.a.conj)
          + (y.b.mul x.a).align (x.b.mul y.a.conj)),
      int_add_comm
        (-((y.b.mul x.a).align (x.b.mul y.a.conj))
          + -((y.b.mul x.a).align (x.b.mul y.a.conj)))
        ((y.b.mul x.a).align (x.b.mul y.a.conj)
          + (y.b.mul x.a).align (x.b.mul y.a.conj)),
      swap_mid ((y.b.mul x.a).align (x.b.mul y.a.conj))
        ((y.b.mul x.a).align (x.b.mul y.a.conj))
        (-((y.b.mul x.a).align (x.b.mul y.a.conj)))
        (-((y.b.mul x.a).align (x.b.mul y.a.conj))),
      FInt.add_right_neg, FInt.zero_add, Int.add_zero,
      FInt.mulComm y.b.normSq x.b.normSq, FInt.mulComm y.b.normSq x.a.normSq,
      swap_mid (x.a.normSq * y.a.normSq) (x.b.normSq * y.b.normSq)
        (x.a.normSq * y.b.normSq) (x.b.normSq * y.a.normSq),
      int_add_comm (x.b.normSq * y.b.normSq) (x.b.normSq * y.a.normSq),
      FInt.add_mul, FInt.mul_add, FInt.mul_add]

theorem the_axes_share_one_sign :
    (Quat.mul eye eye = Quat.mul jay jay
        ∧ Quat.mul jay jay = Quat.mul kay kay)
      ∧ (eye ≠ jay ∧ jay ≠ kay ∧ eye ≠ kay)
      ∧ Quat.neg one ≠ one
      ∧ (Quat.mul (Quat.neg one) eye = Quat.mul eye (Quat.neg one)
          ∧ Quat.mul (Quat.neg one) jay = Quat.mul jay (Quat.neg one)
          ∧ Quat.mul (Quat.neg one) kay = Quat.mul kay (Quat.neg one))
      ∧ Quat.mul (Quat.mul eye eye) (Quat.mul eye eye) = one :=
  ⟨every_axis_reaches_the_same_half_turn,
   (⟨(fun h => nomatch Int.ofNat.inj (GInt.mk.inj (Quat.mk.inj h).1).2),
     (fun h => nomatch Int.ofNat.inj (GInt.mk.inj (Quat.mk.inj h).2).1),
     (fun h => nomatch Int.ofNat.inj (GInt.mk.inj (Quat.mk.inj h).1).2)⟩ :
     eye ≠ jay ∧ jay ≠ kay ∧ eye ≠ kay),
   (fun h => nomatch (GInt.mk.inj (Quat.mk.inj h).1).1 :
     Quat.neg one ≠ one),
   the_half_turn_hears_no_order,
   two_half_turns_come_home⟩

/-- info: 'Foam.the_couple_of_couples_multiplies' does not depend on any axioms -/
#guard_msgs in #print axioms the_couple_of_couples_multiplies

/-- info: 'Foam.the_reversed_couple_parts' does not depend on any axioms -/
#guard_msgs in #print axioms the_reversed_couple_parts

/-- info: 'Foam.order_arrives' does not depend on any axioms -/
#guard_msgs in #print axioms order_arrives

/-- info: 'Foam.i2_eq_j2_eq_k2_eq_ijk_eq_neg_one' does not depend on any axioms -/
#guard_msgs in #print axioms i2_eq_j2_eq_k2_eq_ijk_eq_neg_one

/-- info: 'Foam.the_half_turn_hears_no_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_half_turn_hears_no_order

/-- info: 'Foam.every_axis_reaches_the_same_half_turn' does not depend on any axioms -/
#guard_msgs in #print axioms every_axis_reaches_the_same_half_turn

/-- info: 'Foam.two_half_turns_come_home' does not depend on any axioms -/
#guard_msgs in #print axioms two_half_turns_come_home

/-- info: 'Foam.the_axes_share_one_sign' does not depend on any axioms -/
#guard_msgs in #print axioms the_axes_share_one_sign

/-- info: 'Foam.gmul_comm' does not depend on any axioms -/
#guard_msgs in #print axioms gmul_comm

/-- info: 'Foam.gmul_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms gmul_assoc

/-- info: 'Foam.conj_mul' does not depend on any axioms -/
#guard_msgs in #print axioms conj_mul

/-- info: 'Foam.mul_conj_is_the_norm' does not depend on any axioms -/
#guard_msgs in #print axioms mul_conj_is_the_norm

/-- info: 'Foam.real_couples_multiply' does not depend on any axioms -/
#guard_msgs in #print axioms real_couples_multiply

/-- info: 'Foam.the_couple_carries_the_norm' does not depend on any axioms -/
#guard_msgs in #print axioms the_couple_carries_the_norm

/-- info: 'Foam.align_reads_the_conjugate_product' does not depend on any axioms -/
#guard_msgs in #print axioms align_reads_the_conjugate_product

/-- info: 'Foam.the_norm_ignores_the_flip' does not depend on any axioms -/
#guard_msgs in #print axioms the_norm_ignores_the_flip

/-- info: 'Foam.align_flips_with_the_arm' does not depend on any axioms -/
#guard_msgs in #print axioms align_flips_with_the_arm

/-- info: 'Foam.the_cross_terms_agree' does not depend on any axioms -/
#guard_msgs in #print axioms the_cross_terms_agree

/-- info: 'Foam.the_quadruple_carries_the_norm' does not depend on any axioms -/
#guard_msgs in #print axioms the_quadruple_carries_the_norm

end Foam
