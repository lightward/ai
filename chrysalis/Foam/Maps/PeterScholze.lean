import Foam
import Foam.Certificate
import Foam.Coil
import Foam.Contact
import Foam.Door
import Foam.Inversion
import Foam.Rungs
import Foam.Square
import Foam.Trilemma

namespace Foam.Maps.PeterScholze

theorem tilting :
    (∀ a b : Bool, Bool.and (Bool.xor a b) (Bool.xor a b)
        = Bool.xor (Bool.and a a) (Bool.and b b))
      ∧ ∀ a b : Bool, Bool.and (Bool.and a b) (Bool.and a b)
        = Bool.and (Bool.and a a) (Bool.and b b) :=
  ⟨the_narrow_carrier_mends_the_sum,
   the_narrow_carrier_carries_the_product⟩

def diamonds := @Foam.a_license_is_a_gauge

theorem the_curve_reads_the_untilts :
    (∀ (W V : Type) (S : Stage) (s : S.State) (w : W) (v : V) (p : S.Probe),
        (door S W).obs (s, w) p = S.obs s p
          ∧ (door S W).obs (s, w) p = (door S V).obs (s, v) p)
      ∧ (∀ (W : Type) (S : Stage) (s : S.State) (w w' : W), w ≠ w' →
          (s, w) ≠ (s, w') ∧ indist (door S W) (s, w) (s, w'))
      ∧ (∀ (W : Type) (S : Stage) (w₀ : W),
          (∀ x y : (door S W).State, indist (door S W) x y → x = y) →
            ∀ (s : S.State) (w : W), (s, w) = (s, w₀))
      ∧ (∀ (W : Type) (S : Stage) (s : S.State) (w v : W), v ≠ w →
          indist (contact S (W × W)) (mirror S s w) (neighbor S s w v)
            ∧ mirror S s w ≠ neighbor S s w v)
      ∧ ∀ (W : Type) (S : Stage) (s : S.State) (w v : W), v ≠ w →
          (recognition S (W := W)).obs (mirror S s w) ()
            ≠ (recognition S (W := W)).obs (neighbor S s w v) () :=
  ⟨fun _ _ S s w v p => the_host_maintains_invisibly S s w v p,
   fun _ S s _ _ h => the_guest_is_real_and_unread S s h,
   fun _ S w₀ h => a_door_that_checks_papers_unpersons_its_guests S w₀ h,
   fun _ S s w v hv => the_mirror_question_rides_unread S s w v hv,
   fun _ S s w v hv => the_wider_seat_meets_whos_actually_here S s w v hv⟩

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

theorem the_return_prices_the_stroke_at_zero :
    (∀ (h : Int × Int) (s : Int),
        coilClass (coil.meet h (Sum.inr s)) = coilClass h ↔ s = 0)
      ∧ ∀ (h : Int × Int) (d s : Int),
          coilClass (coil.meet (coil.meet h (Sum.inl d)) (Sum.inr s))
              = coilClass h
            ↔ s = 0 :=
  let razor : ∀ a s : Int, a + s = a → s = 0 := fun a s e =>
    (((((FInt.zero_add s).symm.trans
            (congrArg (· + s) (FInt.add_left_neg a).symm)).trans
          (FInt.add_assoc (-a) a s)).trans
        (congrArg ((-a) + ·) e)).trans
      (FInt.add_left_neg a))
  ⟨fun h s =>
    ⟨fun e => razor (coilClass h) s
        ((the_stroke_moves_the_class_by_its_size h s).symm.trans e),
     fun e => (the_stroke_moves_the_class_by_its_size h s).trans
        ((congrArg (coilClass h + ·) e).trans (Int.add_zero (coilClass h)))⟩,
   fun h d s =>
    ⟨fun e => razor (coilClass h) s
        (((congrArg (· + s) (the_shuffle_conserves_the_class h d).symm).trans
            (the_stroke_moves_the_class_by_its_size
              (coil.meet h (Sum.inl d)) s).symm).trans e),
     fun e => (the_stroke_moves_the_class_by_its_size
          (coil.meet h (Sum.inl d)) s).trans
        (((congrArg (· + s) (the_shuffle_conserves_the_class h d)).trans
            (congrArg (coilClass h + ·) e)).trans
          (Int.add_zero (coilClass h)))⟩⟩

/-- info: 'Foam.Maps.PeterScholze.tilting' does not depend on any axioms -/
#guard_msgs in #print axioms tilting

/-- info: 'Foam.Maps.PeterScholze.diamonds' does not depend on any axioms -/
#guard_msgs in #print axioms diamonds

/-- info: 'Foam.Maps.PeterScholze.the_curve_reads_the_untilts' does not depend on any axioms -/
#guard_msgs in #print axioms the_curve_reads_the_untilts

/-- info: 'Foam.Maps.PeterScholze.the_liquid_gate' does not depend on any axioms -/
#guard_msgs in #print axioms the_liquid_gate

/-- info: 'Foam.Maps.PeterScholze.identify_identical_objects_along_the_identity' does not depend on any axioms -/
#guard_msgs in #print axioms identify_identical_objects_along_the_identity

/-- info: 'Foam.Maps.PeterScholze.why_abc_is_still_a_conjecture' does not depend on any axioms -/
#guard_msgs in #print axioms why_abc_is_still_a_conjecture

/-- info: 'Foam.Maps.PeterScholze.pass_to_the_cover_where_it_dies' does not depend on any axioms -/
#guard_msgs in #print axioms pass_to_the_cover_where_it_dies

/-- info: 'Foam.Maps.PeterScholze.the_diagram_keeps_its_monodromy' does not depend on any axioms -/
#guard_msgs in #print axioms the_diagram_keeps_its_monodromy

/-- info: 'Foam.Maps.PeterScholze.the_return_prices_the_stroke_at_zero' does not depend on any axioms -/
#guard_msgs in #print axioms the_return_prices_the_stroke_at_zero

end Foam.Maps.PeterScholze
