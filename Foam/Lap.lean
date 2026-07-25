import Foam.Amplitude
import Foam.Ledger

namespace Foam

def lapAround (z : GInt) : List GInt := [z.rot, z.rot.rot, z.rot.rot.rot]

def lapAgainst (z : GInt) : List GInt := [z.rot.rot.rot, z.rot.rot, z.rot]

theorem the_two_laps_permute (z : GInt) :
    (lapAround z).Perm (lapAgainst z) :=
  (List.Perm.cons z.rot
      (List.Perm.swap z.rot.rot.rot z.rot.rot [])).trans
    ((List.Perm.swap z.rot.rot.rot z.rot [z.rot.rot]).trans
      (List.Perm.cons z.rot.rot.rot (List.Perm.swap z.rot.rot z.rot [])))

theorem the_laps_part_at_the_witness :
    lapAround GInt.i ≠ lapAgainst GInt.i :=
  fun h => nomatch (GInt.mk.inj (List.cons.inj h).1).1

theorem the_lap_conserves_the_charge (z : GInt) :
    ∀ w, w ∈ lapAround z → w.normSq = z.normSq := by
  intro w hw
  cases hw with
  | head => exact rot_conserves_the_norm z
  | tail _ hw' =>
      cases hw' with
      | head =>
          exact (rot_conserves_the_norm z.rot).trans
            (rot_conserves_the_norm z)
      | tail _ hw'' =>
          cases hw'' with
          | head =>
              exact ((rot_conserves_the_norm z.rot.rot).trans
                (rot_conserves_the_norm z.rot)).trans
                (rot_conserves_the_norm z)
          | tail _ hw''' => exact nomatch hw'''

theorem the_lap_direction_is_the_remainder (z : GInt) :
    lapAgainst z = (lapAround z).reverse
      ∧ (lapAround z).Perm (lapAgainst z)
      ∧ lapAround GInt.i ≠ lapAgainst GInt.i
      ∧ z.rot.rot.rot.rot = z :=
  ⟨rfl, the_two_laps_permute z, the_laps_part_at_the_witness,
   the_wheel_comes_home z⟩

theorem the_opposite_turns_cancel (z w : GInt) :
    z.align w.rot + z.align w.rot.rot.rot = 0 := by
  show (z.re * -w.im + z.im * w.re)
      + (z.re * -(-w.im) + z.im * -w.re) = 0
  rw [int_neg_neg, FInt.mul_neg z.re w.im, FInt.mul_neg z.im w.re,
      swap_mid (-(z.re * w.im)) (z.im * w.re) (z.re * w.im)
        (-(z.im * w.re)),
      FInt.add_left_neg (z.re * w.im), FInt.add_right_neg (z.im * w.re)]
  rfl

theorem the_facing_pair_cancels (z w : GInt) :
    z.align w + z.align w.rot.rot = 0 := by
  show (z.re * w.re + z.im * w.im)
      + (z.re * -w.re + z.im * -w.im) = 0
  rw [FInt.mul_neg z.re w.re, FInt.mul_neg z.im w.im,
      swap_mid (z.re * w.re) (z.im * w.im) (-(z.re * w.re))
        (-(z.im * w.im)),
      FInt.add_right_neg (z.re * w.re), FInt.add_right_neg (z.im * w.im)]
  rfl

theorem cancellation_not_absence :
    (∀ z w : GInt, z.align w.rot + z.align w.rot.rot.rot = 0)
      ∧ (∀ z w : GInt, z.align w + z.align w.rot.rot = 0)
      ∧ GInt.align ⟨1, 1⟩ (GInt.rot ⟨1, 0⟩) ≠ 0 :=
  ⟨the_opposite_turns_cancel, the_facing_pair_cancels,
   fun h => nomatch Int.ofNat.inj h⟩

/-- info: 'Foam.the_two_laps_permute' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_laps_permute

/-- info: 'Foam.the_laps_part_at_the_witness' does not depend on any axioms -/
#guard_msgs in #print axioms the_laps_part_at_the_witness

/-- info: 'Foam.the_lap_conserves_the_charge' does not depend on any axioms -/
#guard_msgs in #print axioms the_lap_conserves_the_charge

/-- info: 'Foam.the_lap_direction_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_lap_direction_is_the_remainder

/-- info: 'Foam.the_opposite_turns_cancel' does not depend on any axioms -/
#guard_msgs in #print axioms the_opposite_turns_cancel

/-- info: 'Foam.the_facing_pair_cancels' does not depend on any axioms -/
#guard_msgs in #print axioms the_facing_pair_cancels

/-- info: 'Foam.cancellation_not_absence' does not depend on any axioms -/
#guard_msgs in #print axioms cancellation_not_absence

end Foam
