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

end Foam
