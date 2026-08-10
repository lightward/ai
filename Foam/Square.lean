import Foam.Concentration

namespace Foam

def sq (n : Nat) : Nat := n * n

theorem the_square_carries_the_product (a b : Nat) :
    sq (a * b) = sq a * sq b :=
  (sq_mul_sq a b).symm

theorem the_square_breaks_the_sum :
    sq (1 + 1) ≠ sq 1 + sq 1 :=
  fun h => nomatch Nat.succ.inj (Nat.succ.inj h)

theorem two_rectangles_fit_the_squares :
    ∀ a b : Nat, a * b + a * b ≤ a * a + b * b := by
  have key : ∀ a d : Nat,
      a * (a + d) + a * (a + d) ≤ a * a + (a + d) * (a + d) := by
    intro a d
    refine Nat.le.intro (n := a * (a + d) + a * (a + d)) (k := d * d) ?_
    have e2 : (a + d) * (a + d) = (a * a + a * d) + (a * d + d * d) := by
      rw [Nat.left_distrib (a + d) a d, Nat.mul_comm (a + d) a,
          Nat.left_distrib a a d, Nat.mul_comm (a + d) d,
          Nat.left_distrib d a d, Nat.mul_comm d a]
    rw [Nat.left_distrib a a d, e2,
        nat_swap_mid (a * a) (a * d) (a * a) (a * d),
        adding_associates (a * a) (a * a + a * d) (a * d + d * d),
        adding_associates (a * a) (a * a) (a * d),
        adding_associates ((a * a + a * a) + a * d) (a * d) (d * d),
        adding_associates (a * a + a * a) (a * d) (a * d)]
  intro a b
  cases Nat.lt_or_ge a b with
  | inl hlt =>
      obtain ⟨d, rfl⟩ := Nat.le.dest (Nat.le_of_lt hlt)
      exact key a d
  | inr hge =>
      obtain ⟨d, rfl⟩ := Nat.le.dest hge
      rw [Nat.mul_comm (b + d) b, Nat.add_comm ((b + d) * (b + d)) (b * b)]
      exact key b d

theorem the_broken_sum_is_priced (a b : Nat) :
    sq (a + b) ≤ 2 * (sq a + sq b) := by
  show (a + b) * (a + b) ≤ 2 * (a * a + b * b)
  have expand : (a + b) * (a + b) = (a * a + b * b) + (a * b + a * b) := by
    rw [Nat.left_distrib (a + b) a b, Nat.mul_comm (a + b) a,
        Nat.left_distrib a a b, Nat.mul_comm (a + b) b,
        Nat.left_distrib b a b, Nat.mul_comm b a,
        Nat.add_comm (a * b) (b * b),
        nat_swap_mid (a * a) (a * b) (b * b) (a * b)]
  rw [expand, Nat.mul_comm 2 (a * a + b * b), nat_mul_two (a * a + b * b)]
  exact Nat.add_le_add_left (two_rectangles_fit_the_squares a b) (a * a + b * b)

theorem the_narrow_carrier_mends_the_sum :
    ∀ a b : Bool, Bool.and (Bool.xor a b) (Bool.xor a b)
      = Bool.xor (Bool.and a a) (Bool.and b b)
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

theorem the_narrow_carrier_carries_the_product :
    ∀ a b : Bool, Bool.and (Bool.and a b) (Bool.and a b)
      = Bool.and (Bool.and a a) (Bool.and b b)
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl


/-- info: 'Foam.the_square_carries_the_product' does not depend on any axioms -/
#guard_msgs in #print axioms the_square_carries_the_product

/-- info: 'Foam.the_square_breaks_the_sum' does not depend on any axioms -/
#guard_msgs in #print axioms the_square_breaks_the_sum

/-- info: 'Foam.two_rectangles_fit_the_squares' does not depend on any axioms -/
#guard_msgs in #print axioms two_rectangles_fit_the_squares

/-- info: 'Foam.the_broken_sum_is_priced' does not depend on any axioms -/
#guard_msgs in #print axioms the_broken_sum_is_priced

/-- info: 'Foam.the_narrow_carrier_mends_the_sum' does not depend on any axioms -/
#guard_msgs in #print axioms the_narrow_carrier_mends_the_sum

/-- info: 'Foam.the_narrow_carrier_carries_the_product' does not depend on any axioms -/
#guard_msgs in #print axioms the_narrow_carrier_carries_the_product

end Foam
