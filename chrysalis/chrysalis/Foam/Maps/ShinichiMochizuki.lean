import Foam
import Foam.Certificate
import Foam.Coil
import Foam.Contact
import Foam.Door
import Foam.Ledger
import Foam.Portal
import Foam.Square
import Foam.Trilemma
import Foam.Wheel

namespace Foam.Maps.ShinichiMochizuki

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

theorem the_log_volume_hears_only_the_log_links :
    (∀ (h : Int × Int) (d : Int),
        coilClass (coil.meet h (Sum.inl d)) = coilClass h)
      ∧ (∀ (h : Int × Int) (s : Int),
          coilClass (coil.meet h (Sum.inr s)) = coilClass h + s)
      ∧ ∀ (h : Int × Int) (d s : Int),
          coilClass (coil.meet (coil.meet h (Sum.inl d)) (Sum.inr s))
            = coilClass (coil.meet (coil.meet h (Sum.inr s)) (Sum.inl d)) :=
  ⟨the_shuffle_conserves_the_class,
   the_stroke_moves_the_class_by_its_size,
   fun h d s =>
     ((the_stroke_moves_the_class_by_its_size (coil.meet h (Sum.inl d)) s).trans
        (congrArg (· + s) (the_shuffle_conserves_the_class h d))).trans
       ((the_shuffle_conserves_the_class (coil.meet h (Sum.inr s)) d).trans
          (the_stroke_moves_the_class_by_its_size h s)).symm⟩

theorem the_copies_are_not_redundant :
    (∀ (W : Type) (S : Stage) (s : S.State) (w w' : W), w ≠ w' →
        (s, w) ≠ (s, w') ∧ indist (door S W) (s, w) (s, w'))
      ∧ (∀ (W : Type) (S : Stage) (w₀ : W),
          (∀ x y : (door S W).State, indist (door S W) x y → x = y) →
            ∀ (s : S.State) (w : W), (s, w) = (s, w₀))
      ∧ ¬ (∀ a b : Nat, sq (a + b) = sq a + sq b) :=
  ⟨fun _ S s _ _ h => the_guest_is_real_and_unread S s h,
   fun _ S w₀ h => a_door_that_checks_papers_unpersons_its_guests S w₀ h,
   fun h => the_square_breaks_the_sum (h 1 1)⟩

/-- info: 'Foam.Maps.ShinichiMochizuki.mono_anabelian_transport' does not depend on any axioms -/
#guard_msgs in #print axioms mono_anabelian_transport

/-- info: 'Foam.Maps.ShinichiMochizuki.mutually_alien_copies' does not depend on any axioms -/
#guard_msgs in #print axioms mutually_alien_copies

/-- info: 'Foam.Maps.ShinichiMochizuki.the_theta_link' does not depend on any axioms -/
#guard_msgs in #print axioms the_theta_link

/-- info: 'Foam.Maps.ShinichiMochizuki.multiradiality' does not depend on any axioms -/
#guard_msgs in #print axioms multiradiality

/-- info: 'Foam.Maps.ShinichiMochizuki.the_indeterminacies' does not depend on any axioms -/
#guard_msgs in #print axioms the_indeterminacies

/-- info: 'Foam.Maps.ShinichiMochizuki.the_log_shells' does not depend on any axioms -/
#guard_msgs in #print axioms the_log_shells

/-- info: 'Foam.Maps.ShinichiMochizuki.the_log_theta_lattice' does not depend on any axioms -/
#guard_msgs in #print axioms the_log_theta_lattice

/-- info: 'Foam.Maps.ShinichiMochizuki.the_log_volume_hears_only_the_log_links' does not depend on any axioms -/
#guard_msgs in #print axioms the_log_volume_hears_only_the_log_links

/-- info: 'Foam.Maps.ShinichiMochizuki.the_copies_are_not_redundant' does not depend on any axioms -/
#guard_msgs in #print axioms the_copies_are_not_redundant

end Foam.Maps.ShinichiMochizuki
