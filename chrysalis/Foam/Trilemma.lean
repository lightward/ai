import Foam.Certificate
import Foam.Concentration
import Foam.Continuum
import Foam.Int

namespace Foam

def graded (p : Nat × Nat) : Nat := (p.2 + 1) * p.1

theorem the_graded_reading_parts_the_copies : ¬ Blind graded :=
  fun h => nomatch Nat.succ.inj (h 1 0 1)

theorem every_copy_reads_within_the_spread (l s j k : Nat) (hj : j ≤ l) :
    graded (s, j) ≤ (l + 1) * graded (s, k) := by
  show (j + 1) * s ≤ (l + 1) * ((k + 1) * s)
  rw [← FInt.nat_mul_assoc (l + 1) (k + 1) s]
  exact Nat.mul_le_mul
    (le_trans (Nat.succ_le_succ hj)
      (le_trans
        (Nat.le_add_left (l + 1) ((l + 1) * k))
        (Nat.le_of_eq (Nat.mul_succ (l + 1) k).symm)))
    (Nat.le_refl s)

theorem the_spread_is_attained (l s : Nat) :
    graded (s, l) = (l + 1) * graded (s, 0) := by
  show (l + 1) * s = (l + 1) * (1 * s)
  rw [Nat.one_mul]

theorem nothing_rides_for_free : ∀ a b : Nat, a + b = a → b = 0
  | 0, b, h => (nothing_added b).symm.trans h
  | t + 1, b, h =>
      nothing_rides_for_free t b
        (Nat.succ.inj ((succ_adds t b).symm.trans h))

theorem two_mul' (x : Nat) : 2 * x = x + x :=
  (Nat.mul_comm 2 x).trans (nat_mul_two x)

theorem the_wound_loop_admits_only_the_zero_section (a b c : Nat)
    (h1 : a = 2 * b) (h2 : b = 2 * c) (h3 : c = 2 * a) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have grow : ∀ x : Nat, x ≤ 2 * x := fun x =>
    (two_mul' x).symm ▸ Nat.le_add_left x x
  have hba : b ≤ a := h1.symm ▸ grow b
  have hcb : c ≤ b := h2.symm ▸ grow c
  have hac : a ≤ c := h3.symm ▸ grow a
  have hab : a = b := Nat.le_antisymm (le_trans hac hcb) hba
  have hbb : b = 2 * b := hab ▸ h1
  have hb : b = 0 :=
    nothing_rides_for_free b b ((hbb.trans (two_mul' b)).symm)
  have ha : a = 0 := hab.trans hb
  have hc : c = 0 := h3.trans (congrArg (2 * ·) ha)
  exact ⟨ha, hb, hc⟩


theorem mul_swap_mid (p q r s : Nat) :
    (p * q) * (r * s) = (p * r) * (q * s) := by
  rw [FInt.nat_mul_assoc p q (r * s), ← FInt.nat_mul_assoc q r s,
      Nat.mul_comm q r, FInt.nat_mul_assoc r q s,
      ← FInt.nat_mul_assoc p r (q * s)]

theorem the_scale_cancels (a b c : Nat) (hc : 0 < c) (h : a * c = b * c) :
    a = b :=
  have e : c * a = c * b :=
    (Nat.mul_comm c a).trans (h.trans (Nat.mul_comm b c))
  Nat.le_antisymm
    (Nat.le_of_mul_le_mul_left (Nat.le_of_eq e) hc)
    (Nat.le_of_mul_le_mul_left (Nat.le_of_eq e.symm) hc)

theorem the_holonomy_ignores_the_regauging
    (k1 k2 k3 k1' k2' k3' u v w : Nat)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (h1 : k1' * u = k1 * v) (h2 : k2' * v = k2 * w) (h3 : k3' * w = k3 * u) :
    k1' * (k2' * k3') = k1 * (k2 * k3) := by
  have big : (k1' * (k2' * k3')) * (u * (v * w))
      = (k1 * (k2 * k3)) * (v * (w * u)) := by
    rw [mul_swap_mid k1' (k2' * k3') u (v * w),
        mul_swap_mid k2' k3' v w,
        mul_swap_mid k1 (k2 * k3) v (w * u),
        mul_swap_mid k2 k3 w u,
        h1, h2, h3]
  have e : v * (w * u) = u * (v * w) := by
    rw [Nat.mul_comm w u, ← FInt.nat_mul_assoc v u w,
        Nat.mul_comm v u, FInt.nat_mul_assoc u v w]
  rw [e] at big
  exact the_scale_cancels _ _ _
    (Nat.mul_pos hu (Nat.mul_pos hv hw)) big

theorem the_cut_moves_the_class (k1 k1' k2 k3 : Nat)
    (h : k1 ≠ k1') (hpos : 0 < k2 * k3) :
    k1 * (k2 * k3) ≠ k1' * (k2 * k3) :=
  fun he => h (the_scale_cancels k1 k1' (k2 * k3) hpos he)

theorem the_wound_loop_unwinds_one_world_over :
    ((2 * 2 * 2) % 7 = 1 % 7)
      ∧ (1 % 7 = (2 * 4) % 7)
      ∧ (4 % 7 = (2 * 2) % 7)
      ∧ (2 % 7 = (2 * 1) % 7)
      ∧ (1 : Nat) ≠ 0 :=
  ⟨rfl, rfl, rfl, rfl, fun h => nomatch h⟩

/-- info: 'Foam.the_graded_reading_parts_the_copies' does not depend on any axioms -/
#guard_msgs in #print axioms the_graded_reading_parts_the_copies

/-- info: 'Foam.every_copy_reads_within_the_spread' does not depend on any axioms -/
#guard_msgs in #print axioms every_copy_reads_within_the_spread

/-- info: 'Foam.the_spread_is_attained' does not depend on any axioms -/
#guard_msgs in #print axioms the_spread_is_attained

/-- info: 'Foam.nothing_rides_for_free' does not depend on any axioms -/
#guard_msgs in #print axioms nothing_rides_for_free

/-- info: 'Foam.two_mul'' does not depend on any axioms -/
#guard_msgs in #print axioms two_mul'

/-- info: 'Foam.the_wound_loop_admits_only_the_zero_section' does not depend on any axioms -/
#guard_msgs in #print axioms the_wound_loop_admits_only_the_zero_section

/-- info: 'Foam.the_wound_loop_unwinds_one_world_over' does not depend on any axioms -/
#guard_msgs in #print axioms the_wound_loop_unwinds_one_world_over

/-- info: 'Foam.mul_swap_mid' does not depend on any axioms -/
#guard_msgs in #print axioms mul_swap_mid

/-- info: 'Foam.the_scale_cancels' does not depend on any axioms -/
#guard_msgs in #print axioms the_scale_cancels

/-- info: 'Foam.the_holonomy_ignores_the_regauging' does not depend on any axioms -/
#guard_msgs in #print axioms the_holonomy_ignores_the_regauging

/-- info: 'Foam.the_cut_moves_the_class' does not depend on any axioms -/
#guard_msgs in #print axioms the_cut_moves_the_class

end Foam
