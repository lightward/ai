import Foam.Continuum

namespace Foam

def normSq3 (v : Int × Int × Int) : Int :=
  v.1 * v.1 + v.2.1 * v.2.1 + v.2.2 * v.2.2

theorem int_sq_is_nat_sq : ∀ a : Int, ∃ n : Nat, a * a = Int.ofNat (n * n)
  | .ofNat m => ⟨m, rfl⟩
  | .negSucc m => ⟨m + 1, rfl⟩

theorem fifteen_is_not_three_squares :
    ∀ x y z : Nat, x * x + y * y + z * z ≠ 15 := by
  have key : ∀ x : Nat, x < 4 → ∀ y : Nat, y < 4 → ∀ z : Nat, z < 4 →
      x * x + y * y + z * z ≠ 15 := by decide
  have hb : ∀ w v : Nat, w * w + v = 15 → w < 4 := by
    intro w v hwv
    cases Nat.lt_or_ge w 4 with
    | inl hlt => exact hlt
    | inr hge =>
        exact absurd (le_trans (Nat.mul_le_mul hge hge) (Nat.le.intro hwv))
          (no_number_is_below_itself 15)
  intro x y z h
  have e : (x * x + y * y) + z * z = y * y + (x * x + z * z) := by
    rw [Nat.add_comm (x * x) (y * y), Nat.add_assoc]
  exact key
    x (hb x (y * y + z * z)
        ((Nat.add_assoc (x * x) (y * y) (z * z)).symm.trans h))
    y (hb y (x * x + z * z) (e.symm.trans h))
    z (hb z (x * x + y * y)
        ((Nat.add_comm (x * x + y * y) (z * z)).symm.trans h))
    h

theorem no_int_triple_squares_to_fifteen (a b c : Int) :
    a * a + b * b + c * c ≠ 15 := by
  intro h
  obtain ⟨x, hx⟩ := int_sq_is_nat_sq a
  obtain ⟨y, hy⟩ := int_sq_is_nat_sq b
  obtain ⟨z, hz⟩ := int_sq_is_nat_sq c
  rw [hx, hy, hz] at h
  have h' : Int.ofNat ((x * x + y * y) + z * z) = Int.ofNat 15 := h
  exact fifteen_is_not_three_squares x y z (Int.ofNat.inj h')

theorem no_triple_carries_the_norm :
    ¬ ∃ mul : (Int × Int × Int) → (Int × Int × Int) → (Int × Int × Int),
      ∀ x y, normSq3 (mul x y) = normSq3 x * normSq3 y :=
  fun he =>
    he.elim (fun mul hmul =>
      no_int_triple_squares_to_fifteen
        (mul (1, 1, 1) (0, 1, 2)).1
        (mul (1, 1, 1) (0, 1, 2)).2.1
        (mul (1, 1, 1) (0, 1, 2)).2.2
        (hmul (1, 1, 1) (0, 1, 2)))

/-- info: 'Foam.int_sq_is_nat_sq' does not depend on any axioms -/
#guard_msgs in #print axioms int_sq_is_nat_sq

/-- info: 'Foam.fifteen_is_not_three_squares' does not depend on any axioms -/
#guard_msgs in #print axioms fifteen_is_not_three_squares

/-- info: 'Foam.no_int_triple_squares_to_fifteen' does not depend on any axioms -/
#guard_msgs in #print axioms no_int_triple_squares_to_fifteen

/-- info: 'Foam.no_triple_carries_the_norm' does not depend on any axioms -/
#guard_msgs in #print axioms no_triple_carries_the_norm

end Foam
