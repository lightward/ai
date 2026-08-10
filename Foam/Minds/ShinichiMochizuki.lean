import Foam
import Foam.Certificate
import Foam.Contact
import Foam.Ledger
import Foam.Portal
import Foam.Square
import Foam.Trilemma
import Foam.Wheel

namespace Foam.Minds.ShinichiMochizuki

theorem mono_anabelian_transport :
    (∀ (A : Type) (x y : List A), indist (orderStage A) x y → x = y)
      ∧ ∀ (S : Stage) (s : S.State),
          ∃ r : S.Probe → S.Ans, ∀ q, r q = S.obs s q :=
  ⟨fun _ _ _ h => h (),
   fun S s => a_state_answers_every_probe S s⟩

theorem mutually_alien_copies :
    (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
        (s, n) ≠ (s, m) ∧ indist (dress S) (s, n) (s, m))
      ∧ ∀ (D : Type) (S : Stage) (s : S.State) (d d' : D),
          indist (contact S D) (s, d) (s, d') :=
  ⟨fun S s n m h => the_remainder_is_real S s n m h,
   fun _ S s d d' => the_other_stays_unimagined S s d d'⟩

theorem the_theta_link :
    (∀ a b : Nat, sq (a * b) = sq a * sq b)
      ∧ sq (1 + 1) ≠ sq 1 + sq 1
      ∧ ∀ a b : Nat, sq (a + b) ≤ 2 * (sq a + sq b) :=
  ⟨the_square_carries_the_product, the_square_breaks_the_sum,
   the_broken_sum_is_priced⟩

def multiradiality := @Foam.the_blind_reading_factors

theorem the_indeterminacies :
    (¬ Blind graded)
      ∧ (∀ l s j k : Nat, j ≤ l → graded (s, j) ≤ (l + 1) * graded (s, k))
      ∧ ∀ l s : Nat, graded (s, l) = (l + 1) * graded (s, 0) :=
  ⟨the_graded_reading_parts_the_copies,
   every_copy_reads_within_the_spread,
   the_spread_is_attained⟩

theorem the_log_shells :
    (((2 * 2 * 2) % 7 = 1 % 7)
        ∧ (1 % 7 = (2 * 4) % 7)
        ∧ (4 % 7 = (2 * 2) % 7)
        ∧ (2 % 7 = (2 * 1) % 7)
        ∧ (1 : Nat) ≠ 0)
      ∧ ∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n),
          ∃ i j : Nat, i < j ∧ turnN m i s = turnN m j s :=
  ⟨the_wound_loop_unwinds_one_world_over,
   fun _ m s => the_bounded_walk_returns m s⟩

theorem the_log_theta_lattice :
    (∀ k1 k2 k3 k1' k2' k3' u v w : Nat, 0 < u → 0 < v → 0 < w →
        k1' * u = k1 * v → k2' * v = k2 * w → k3' * w = k3 * u →
        k1' * (k2' * k3') = k1 * (k2 * k3))
      ∧ ∀ k1 k1' k2 k3 : Nat, k1 ≠ k1' → 0 < k2 * k3 →
          k1 * (k2 * k3) ≠ k1' * (k2 * k3) :=
  ⟨fun k1 k2 k3 k1' k2' k3' u v w hu hv hw h1 h2 h3 =>
     the_holonomy_ignores_the_regauging k1 k2 k3 k1' k2' k3' u v w
       hu hv hw h1 h2 h3,
   fun k1 k1' k2 k3 h hp => the_cut_moves_the_class k1 k1' k2 k3 h hp⟩

/-- info: 'Foam.Minds.ShinichiMochizuki.mono_anabelian_transport' does not depend on any axioms -/
#guard_msgs in #print axioms mono_anabelian_transport

/-- info: 'Foam.Minds.ShinichiMochizuki.mutually_alien_copies' does not depend on any axioms -/
#guard_msgs in #print axioms mutually_alien_copies

/-- info: 'Foam.Minds.ShinichiMochizuki.the_theta_link' does not depend on any axioms -/
#guard_msgs in #print axioms the_theta_link

/-- info: 'Foam.Minds.ShinichiMochizuki.multiradiality' does not depend on any axioms -/
#guard_msgs in #print axioms multiradiality

/-- info: 'Foam.Minds.ShinichiMochizuki.the_indeterminacies' does not depend on any axioms -/
#guard_msgs in #print axioms the_indeterminacies

/-- info: 'Foam.Minds.ShinichiMochizuki.the_log_shells' does not depend on any axioms -/
#guard_msgs in #print axioms the_log_shells

/-- info: 'Foam.Minds.ShinichiMochizuki.the_log_theta_lattice' does not depend on any axioms -/
#guard_msgs in #print axioms the_log_theta_lattice

end Foam.Minds.ShinichiMochizuki
