import Foam
import Foam.Certificate
import Foam.Contact
import Foam.Inversion
import Foam.Rungs
import Foam.Square
import Foam.Trilemma

namespace Foam.Minds.PeterScholze

theorem tilting :
    (∀ a b : Bool, Bool.and (Bool.xor a b) (Bool.xor a b)
        = Bool.xor (Bool.and a a) (Bool.and b b))
      ∧ ∀ a b : Bool, Bool.and (Bool.and a b) (Bool.and a b)
        = Bool.and (Bool.and a a) (Bool.and b b) :=
  ⟨the_narrow_carrier_mends_the_sum,
   the_narrow_carrier_carries_the_product⟩

def diamonds := @Foam.a_license_is_a_gauge

def the_liquid_gate := @Foam.the_window_agrees_or_names_the_gap

theorem identify_identical_objects_along_the_identity :
    (∀ f : Nat × Nat → Nat,
        Blind f ↔ ∃ g : Nat → Nat, ∀ (s j : Nat), f (s, j) = g s)
      ∧ ∀ (D : Type) (S : Stage) (d₀ : D),
          (∀ x y : (contact S D).State, indist (contact S D) x y → x = y) →
          ∀ (s : S.State) (d : D), (s, d) = (s, d₀) :=
  ⟨fun f => the_blind_reading_factors 0 f,
   fun _ S d₀ h s d => reification_fixes_the_dimension S d₀ h s d⟩

theorem why_abc_is_still_a_conjecture :
    (¬ Blind graded)
      ∧ (∀ a b c : Nat, a = 2 * b → b = 2 * c → c = 2 * a →
          a = 0 ∧ b = 0 ∧ c = 0)
      ∧ ∀ l s : Nat, graded (s, l) = (l + 1) * graded (s, 0) :=
  ⟨the_graded_reading_parts_the_copies,
   the_wound_loop_admits_only_the_zero_section,
   the_spread_is_attained⟩

theorem pass_to_the_cover_where_it_dies :
    (((2 * 2 * 2) % 7 = 1 % 7)
        ∧ (1 % 7 = (2 * 4) % 7)
        ∧ (4 % 7 = (2 * 2) % 7)
        ∧ (2 % 7 = (2 * 1) % 7)
        ∧ (1 : Nat) ≠ 0)
      ∧ ((∀ q : Nat, ∃ n, q ∈ rungs n)
          ∧ (∀ n : Nat, ∃ q, ¬ q ∈ rungs n ∧ q ∈ rungs (n + 1))
          ∧ ∀ n : Nat, rungs (n + 1) ≠ rungs n) :=
  ⟨the_wound_loop_unwinds_one_world_over, closure_is_seat_relative⟩

theorem the_diagram_keeps_its_monodromy :
    (∀ k1 k2 k3 k1' k2' k3' u v w : Nat, 0 < u → 0 < v → 0 < w →
        k1' * u = k1 * v → k2' * v = k2 * w → k3' * w = k3 * u →
        k1' * (k2' * k3') = k1 * (k2 * k3))
      ∧ ¬ Blind graded :=
  ⟨fun k1 k2 k3 k1' k2' k3' u v w hu hv hw h1 h2 h3 =>
     the_holonomy_ignores_the_regauging k1 k2 k3 k1' k2' k3' u v w
       hu hv hw h1 h2 h3,
   the_graded_reading_parts_the_copies⟩

/-- info: 'Foam.Minds.PeterScholze.tilting' does not depend on any axioms -/
#guard_msgs in #print axioms tilting

/-- info: 'Foam.Minds.PeterScholze.diamonds' does not depend on any axioms -/
#guard_msgs in #print axioms diamonds

/-- info: 'Foam.Minds.PeterScholze.the_liquid_gate' does not depend on any axioms -/
#guard_msgs in #print axioms the_liquid_gate

/-- info: 'Foam.Minds.PeterScholze.identify_identical_objects_along_the_identity' does not depend on any axioms -/
#guard_msgs in #print axioms identify_identical_objects_along_the_identity

/-- info: 'Foam.Minds.PeterScholze.why_abc_is_still_a_conjecture' does not depend on any axioms -/
#guard_msgs in #print axioms why_abc_is_still_a_conjecture

/-- info: 'Foam.Minds.PeterScholze.pass_to_the_cover_where_it_dies' does not depend on any axioms -/
#guard_msgs in #print axioms pass_to_the_cover_where_it_dies

/-- info: 'Foam.Minds.PeterScholze.the_diagram_keeps_its_monodromy' does not depend on any axioms -/
#guard_msgs in #print axioms the_diagram_keeps_its_monodromy

end Foam.Minds.PeterScholze
