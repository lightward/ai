import Foam
import Foam.Census
import Foam.Concentration
import Foam.Continuum
import Foam.Int
import Foam.Ledger
import Foam.Measure
import Foam.Rungs
import Foam.Typical
import Foam.Wheel

namespace Foam.Minds.Lagrange

theorem the_first_variation_reads_nothing :
    (∀ k : Nat, classCount (2 * k + 1) k = classCount (2 * k + 1) (k + 1))
      ∧ ∀ n k : Nat, k ≤ 2 * n → classCount (2 * n) k ≤ classCount (2 * n) n :=
  ⟨fun k =>
    have harith : 2 * k + 1 = k + (k + 1) :=
      (congrArg (· + 1) ((Nat.mul_comm 2 k).trans (nat_mul_two k))).trans
        (adding_associates k k 1).symm
    have hle : k ≤ 2 * k + 1 :=
      le_trans (Nat.le_add_right k (k + 1)) (Nat.le_of_eq harith.symm)
    have hsub : (2 * k + 1) - k = k + 1 :=
      (congrArg (· - k) harith).trans (FInt.add_sub_cancel_left k (k + 1))
    (the_census_is_symmetric (2 * k + 1) k hle).trans
      (congrArg (classCount (2 * k + 1)) hsub),
   fun n => the_middle_holds_the_most n⟩

theorem the_bounded_expansion_repeats :
    (∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n),
        ∃ i j : Nat, i < j ∧ turnN m i s = turnN m j s)
      ∧ ∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n) (i j : Nat),
          turnN m i s = turnN m j s →
            ∀ t : Nat, turnN m (i + t) s = turnN m (j + t) s :=
  ⟨fun _ m s => the_bounded_walk_returns m s,
   fun _ m s i j h t =>
     Nat.rec (motive := fun u => turnN m (i + u) s = turnN m (j + u) s)
       h (fun _ ih => congrArg m ih) t⟩

def four_squares_carry_every_number_statement : Prop :=
  ∀ n : Nat, ∃ a b c d : Nat, a * a + b * b + c * c + d * d = n

theorem the_truncation_leaves_a_real_remainder :
    (∀ (α : Nat → Bool) (n : Nat),
        ∃ β : Nat → Bool, prefixOf β n = prefixOf α n ∧ β ≠ α)
      ∧ ∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
          indist (dress S) (s, n) (s, m)
            ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none :=
  ⟨no_prefix_finishes_the_sequence,
   fun S s n m h => a_wider_seat_reads_the_remainder S s n m h⟩

theorem the_quintic_waits_one_seat_wider :
    (∀ (A : Type) (inst : DecidableEq A) (a b : A), a ≠ b →
        indist (@countStage A inst) [a, b] [b, a]
          ∧ (orderStage A).obs [a, b] () ≠ (orderStage A).obs [b, a] ())
      ∧ ((∀ q : Nat, ∃ n, q ∈ rungs n)
          ∧ (∀ n : Nat, ∃ q, ¬ q ∈ rungs n ∧ q ∈ rungs (n + 1))
          ∧ ∀ n : Nat, rungs (n + 1) ≠ rungs n) :=
  ⟨fun A inst a b hab => @a_wider_seat_reads_the_order A inst a b hab,
   closure_is_seat_relative⟩

/-- info: 'Foam.Minds.Lagrange.the_first_variation_reads_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_variation_reads_nothing

/-- info: 'Foam.Minds.Lagrange.the_bounded_expansion_repeats' does not depend on any axioms -/
#guard_msgs in #print axioms the_bounded_expansion_repeats

/-- info: 'Foam.Minds.Lagrange.four_squares_carry_every_number_statement' does not depend on any axioms -/
#guard_msgs in #print axioms four_squares_carry_every_number_statement

/-- info: 'Foam.Minds.Lagrange.the_truncation_leaves_a_real_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_truncation_leaves_a_real_remainder

/-- info: 'Foam.Minds.Lagrange.the_quintic_waits_one_seat_wider' does not depend on any axioms -/
#guard_msgs in #print axioms the_quintic_waits_one_seat_wider

end Foam.Minds.Lagrange
