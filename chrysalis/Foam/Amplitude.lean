import Foam.Int

namespace Foam

structure GInt where
  re : Int
  im : Int

def GInt.neg (z : GInt) : GInt := ⟨-z.re, -z.im⟩

def GInt.conj (z : GInt) : GInt := ⟨z.re, -z.im⟩

def GInt.rot (z : GInt) : GInt := ⟨-z.im, z.re⟩

def GInt.normSq (z : GInt) : Int := z.re * z.re + z.im * z.im

def GInt.i : GInt := ⟨0, 1⟩

theorem int_neg_neg : ∀ a : Int, -(-a) = a
  | .ofNat 0 => rfl
  | .ofNat (_ + 1) => rfl
  | .negSucc _ => rfl

theorem neg_mul_neg_self : ∀ a : Int, (-a) * (-a) = a * a
  | .ofNat 0 => rfl
  | .ofNat (_ + 1) => rfl
  | .negSucc _ => rfl

theorem int_add_comm : ∀ a b : Int, a + b = b + a
  | .ofNat m, .ofNat n => congrArg Int.ofNat (Nat.add_comm m n)
  | .ofNat _, .negSucc _ => rfl
  | .negSucc _, .ofNat _ => rfl
  | .negSucc m, .negSucc n =>
      congrArg Int.negSucc (congrArg Nat.succ (Nat.add_comm m n))

theorem conj_is_an_involution (z : GInt) : z.conj.conj = z := by
  show (⟨z.re, -(-z.im)⟩ : GInt) = z
  rw [int_neg_neg]

theorem the_wheel_comes_home (z : GInt) :
    z.rot.rot.rot.rot = z := by
  show (⟨-(-z.re), -(-z.im)⟩ : GInt) = z
  rw [int_neg_neg, int_neg_neg]

theorem rot_conserves_the_norm (z : GInt) :
    z.rot.normSq = z.normSq := by
  show (-z.im) * (-z.im) + z.re * z.re = z.re * z.re + z.im * z.im
  rw [neg_mul_neg_self]
  exact int_add_comm _ _

theorem conj_conserves_the_norm (z : GInt) :
    z.conj.normSq = z.normSq := by
  show z.re * z.re + (-z.im) * (-z.im) = z.re * z.re + z.im * z.im
  rw [neg_mul_neg_self]

theorem the_two_kinds_anticommute (z : GInt) :
    z.conj.rot = (z.rot.conj).neg := by
  show (⟨-(-z.im), z.re⟩ : GInt) = ⟨-(-z.im), -(-z.re)⟩
  rw [int_neg_neg z.re]

theorem the_kinds_are_two : GInt.i.rot ≠ GInt.i.conj :=
  fun h => nomatch (GInt.mk.inj h).1

theorem two_kinds_conserve_the_norm (z : GInt) :
    z.rot.normSq = z.normSq
      ∧ z.conj.normSq = z.normSq
      ∧ z.conj.rot = (z.rot.conj).neg
      ∧ GInt.i.rot ≠ GInt.i.conj :=
  ⟨rot_conserves_the_norm z, conj_conserves_the_norm z,
   the_two_kinds_anticommute z, the_kinds_are_two⟩

def GInt.add (z w : GInt) : GInt := ⟨z.re + w.re, z.im + w.im⟩

def GInt.align (z w : GInt) : Int := z.re * w.re + z.im * w.im

theorem swap_mid (p q r s : Int) : (p + q) + (r + s) = (p + r) + (q + s) := by
  rw [FInt.add_assoc, ← FInt.add_assoc q r s, int_add_comm q r,
      FInt.add_assoc r q s, ← FInt.add_assoc]

theorem swap_qs (p q r s : Int) : (p + q) + (r + s) = (p + s) + (r + q) := by
  rw [swap_mid, int_add_comm q s, swap_mid]

theorem sq_add (a c : Int) :
    (a + c) * (a + c) = (a * a + c * c) + (a * c + a * c) := by
  rw [FInt.add_mul, FInt.mul_add, FInt.mul_add, FInt.mulComm c a, swap_qs]

theorem six_shuffle (A B C D x y : Int) :
    ((A + C) + (x + x)) + ((B + D) + (y + y))
      = ((A + B) + (C + D)) + ((x + y) + (x + y)) := by
  rw [swap_mid (A + C) (x + x) (B + D) (y + y), swap_mid A C B D,
      swap_mid x x y y]

theorem the_screen_reads_a_cross_term (z w : GInt) :
    (z.add w).normSq = (z.normSq + w.normSq) + (z.align w + z.align w) := by
  show ((z.re + w.re) * (z.re + w.re)) + ((z.im + w.im) * (z.im + w.im))
      = ((z.re * z.re + z.im * z.im) + (w.re * w.re + w.im * w.im))
        + ((z.re * w.re + z.im * w.im) + (z.re * w.re + z.im * w.im))
  rw [sq_add, sq_add]
  exact six_shuffle (z.re * z.re) (z.im * z.im) (w.re * w.re) (w.im * w.im)
    (z.re * w.re) (z.im * w.im)

theorem cancel_eight (p q r s : Int) :
    (((p + q) + (-r + s)) + (-p + -q)) + (r + -s) = 0 := by
  rw [FInt.add_assoc ((p + q) + (-r + s)) (-p + -q) (r + -s),
      swap_mid (p + q) (-r + s) (-p + -q) (r + -s),
      swap_mid p q (-p) (-q), FInt.add_right_neg p, FInt.add_right_neg q,
      swap_mid (-r) s r (-s), FInt.add_left_neg r, FInt.add_right_neg s]
  rfl

theorem the_four_phases_read_nothing (z w : GInt) :
    ((z.align w + z.align w.rot) + z.align w.rot.rot)
        + z.align w.rot.rot.rot = 0 := by
  show (((z.re * w.re + z.im * w.im)
          + (z.re * -w.im + z.im * w.re))
        + (z.re * -w.re + z.im * -w.im))
      + (z.re * -(-w.im) + z.im * -w.re) = 0
  rw [int_neg_neg, FInt.mul_neg, FInt.mul_neg, FInt.mul_neg, FInt.mul_neg]
  exact cancel_eight (z.re * w.re) (z.im * w.im) (z.re * w.im) (z.im * w.re)

/-- info: 'Foam.int_neg_neg' does not depend on any axioms -/
#guard_msgs in #print axioms int_neg_neg

/-- info: 'Foam.neg_mul_neg_self' does not depend on any axioms -/
#guard_msgs in #print axioms neg_mul_neg_self

/-- info: 'Foam.int_add_comm' does not depend on any axioms -/
#guard_msgs in #print axioms int_add_comm

/-- info: 'Foam.conj_is_an_involution' does not depend on any axioms -/
#guard_msgs in #print axioms conj_is_an_involution

/-- info: 'Foam.the_wheel_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_comes_home

/-- info: 'Foam.rot_conserves_the_norm' does not depend on any axioms -/
#guard_msgs in #print axioms rot_conserves_the_norm

/-- info: 'Foam.conj_conserves_the_norm' does not depend on any axioms -/
#guard_msgs in #print axioms conj_conserves_the_norm

/-- info: 'Foam.the_two_kinds_anticommute' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_kinds_anticommute

/-- info: 'Foam.the_kinds_are_two' does not depend on any axioms -/
#guard_msgs in #print axioms the_kinds_are_two

/-- info: 'Foam.two_kinds_conserve_the_norm' does not depend on any axioms -/
#guard_msgs in #print axioms two_kinds_conserve_the_norm

end Foam
