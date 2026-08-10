import Foam
import Foam.Certificate
import Foam.Contact
import Foam.Inversion
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

end Foam.Minds.PeterScholze
