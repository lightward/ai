import Foam
import Foam.Census
import Foam.Door
import Foam.Expectation
import Foam.Ledger
import Foam.Quat
import Foam.Square
import Foam.Trilemma
import Foam.Triple
import Foam.Typical

namespace Foam.Maps.Gauss

def the_sum_is_deaf_to_the_shuffle := @Foam.counting_is_licensed_by_permutation

def congruent_not_equal := @Foam.the_handshake

theorem congruence_mends_what_equality_breaks :
    (∀ a b : Nat, sq (a * b) = sq a * sq b)
      ∧ sq (1 + 1) ≠ sq 1 + sq 1
      ∧ (∀ a b : Bool, Bool.and (Bool.and a b) (Bool.and a b)
          = Bool.and (Bool.and a a) (Bool.and b b))
      ∧ (∀ a b : Bool, Bool.and (Bool.xor a b) (Bool.xor a b)
          = Bool.xor (Bool.and a a) (Bool.and b b)) :=
  ⟨the_square_carries_the_product, the_square_breaks_the_sum,
    the_narrow_carrier_carries_the_product, the_narrow_carrier_mends_the_sum⟩

private def residueSeat : Stage where
  State := Bool
  Probe := Unit
  Ans   := Bool
  obs   := fun b _ => b

private def residue : Nat → Bool
  | 0 => false
  | 1 => true
  | n + 2 => residue n

private def wraps : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => wraps n + 1

private def board (b : Bool) (k : Nat) : Nat := 2 * k + cond b 1 0

private theorem the_boarding_steps : ∀ (b : Bool) (k : Nat),
    board b (k + 1) = board b k + 2
  | true, _ => rfl
  | false, _ => rfl

private theorem the_split_lands : ∀ n : Nat, board (residue n) (wraps n) = n
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
      (the_boarding_steps (residue n) (wraps n)).trans
        (congrArg (· + 2) (the_split_lands n))

private theorem the_face_survives : ∀ (b : Bool) (k : Nat),
    residue (board b k) = b
  | true, 0 => rfl
  | false, 0 => rfl
  | b, k + 1 =>
      (congrArg residue (the_boarding_steps b k)).trans (the_face_survives b k)

private theorem the_count_survives : ∀ (b : Bool) (k : Nat),
    wraps (board b k) = k
  | true, 0 => rfl
  | false, 0 => rfl
  | b, k + 1 =>
      (congrArg wraps (the_boarding_steps b k)).trans
        (congrArg (· + 1) (the_count_survives b k))

private theorem the_xor_rests : ∀ x : Bool, Bool.xor x false = x
  | true => rfl
  | false => rfl

private theorem the_xor_flips : ∀ x : Bool, Bool.xor x true = Bool.not x
  | true => rfl
  | false => rfl

private theorem the_xor_undoes_itself : ∀ x y : Bool,
    Bool.xor (Bool.xor x y) y = x
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

private theorem the_and_rests : ∀ x : Bool, Bool.and x true = x
  | true => rfl
  | false => rfl

private theorem the_and_falls : ∀ x : Bool, Bool.and x false = false
  | true => rfl
  | false => rfl

private theorem the_zero_adds : ∀ n : Nat, 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (the_zero_adds n)

private theorem the_face_flips : ∀ n : Nat,
    residue (n + 1) = Bool.not (residue n)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => the_face_flips n

private theorem the_face_hears_the_sum : ∀ a b : Nat,
    residue (a + b) = Bool.xor (residue a) (residue b)
  | a, 0 => (the_xor_rests (residue a)).symm
  | a, 1 => (the_face_flips a).trans (the_xor_flips (residue a)).symm
  | a, b + 2 => the_face_hears_the_sum a b

private theorem the_face_hears_the_product : ∀ a b : Nat,
    residue (a * b) = Bool.and (residue a) (residue b)
  | a, 0 => (the_and_falls (residue a)).symm
  | a, 1 =>
      (congrArg residue (the_zero_adds a)).trans
        (the_and_rests (residue a)).symm
  | a, b + 2 =>
      (the_face_hears_the_sum (a * b + a) a).trans
        ((congrArg (fun z => Bool.xor z (residue a))
            (the_face_hears_the_sum (a * b) a)).trans
          ((the_xor_undoes_itself (residue (a * b)) (residue a)).trans
            (the_face_hears_the_product a b)))

private theorem the_ledger_counts_in_wraps : ∀ x c : Nat,
    wraps (x + 2 * c) = wraps x + c
  | _, 0 => rfl
  | x, c + 1 => congrArg (· + 1) (the_ledger_counts_in_wraps x c)

private theorem the_square_opens (a b : Nat) :
    sq (a + b) = (sq a + sq b) + 2 * (a * b) :=
  (Nat.left_distrib (a + b) a b).trans
    ((congrArg (· + (a + b) * b)
        ((Nat.mul_comm (a + b) a).trans (Nat.left_distrib a a b))).trans
      ((congrArg ((a * a + a * b) + ·)
          ((Nat.mul_comm (a + b) b).trans
            ((Nat.left_distrib b a b).trans
              (congrArg (· + b * b) (Nat.mul_comm b a))))).trans
        ((congrArg ((a * a + a * b) + ·) (Nat.add_comm (a * b) (b * b))).trans
          ((nat_swap_mid (a * a) (a * b) (b * b) (a * b)).trans
            (congrArg ((a * a + b * b) + ·) (two_mul' (a * b)).symm)))))

theorem the_cross_term_boards_the_guest (W V : Type) :
    (∀ (b : Bool) (w w' : W), w ≠ w' →
        (b, w) ≠ (b, w') ∧ indist (door residueSeat W) (b, w) (b, w'))
      ∧ (∀ (b : Bool) (w : W) (v : V) (p : Unit),
          (door residueSeat W).obs (b, w) p = residueSeat.obs b p
            ∧ (door residueSeat W).obs (b, w) p
                = (door residueSeat V).obs (b, v) p)
      ∧ ((∀ n : Nat, board (residue n) (wraps n) = n)
          ∧ ∀ (b : Bool) (k : Nat),
              residue (board b k) = b ∧ wraps (board b k) = k)
      ∧ (∀ m n : Nat,
          (residue m = residue n
              ↔ indist (door residueSeat Nat)
                  (residue m, wraps m) (residue n, wraps n))
            ∧ (m ≠ n → (residue m, wraps m) ≠ (residue n, wraps n)))
      ∧ ((∀ a b : Nat, residue (a + b) = Bool.xor (residue a) (residue b))
          ∧ ∀ a b : Nat, residue (a * b) = Bool.and (residue a) (residue b))
      ∧ (sq (1 + 1) ≠ sq 1 + sq 1
          ∧ ∀ a b : Nat,
              sq (a + b) = (sq a + sq b) + 2 * (a * b)
                ∧ residue (sq (a + b))
                    = Bool.xor (residue (sq a)) (residue (sq b))
                ∧ wraps (sq (a + b)) = wraps (sq a + sq b) + a * b)
      ∧ ((∀ x y : (door residueSeat Nat).State,
            indist (door residueSeat Nat) x y → x = y) →
          ∀ n : Nat, n = board (residue n) 0) :=
  ⟨fun b _ _ h => the_guest_is_real_and_unread residueSeat b h,
   fun b w v p => the_host_maintains_invisibly residueSeat b w v p,
   ⟨the_split_lands, fun b k => ⟨the_face_survives b k, the_count_survives b k⟩⟩,
   fun m n =>
     ⟨⟨fun h _ => h, fun h => h ()⟩,
      fun hmn he =>
        hmn (((the_split_lands m).symm.trans
          (congrArg (fun s : Bool × Nat => board s.1 s.2) he)).trans
            (the_split_lands n))⟩,
   ⟨the_face_hears_the_sum, the_face_hears_the_product⟩,
   ⟨the_square_breaks_the_sum,
    fun a b =>
      ⟨the_square_opens a b,
       (the_face_hears_the_product (a + b) (a + b)).trans
         ((congrArg (fun z => Bool.and z z) (the_face_hears_the_sum a b)).trans
           ((the_narrow_carrier_mends_the_sum (residue a) (residue b)).trans
             ((congrArg (fun z => Bool.xor z (Bool.and (residue b) (residue b)))
                 (the_face_hears_the_product a a).symm).trans
               (congrArg (fun z => Bool.xor (residue (sq a)) z)
                 (the_face_hears_the_product b b).symm)))),
       (congrArg wraps (the_square_opens a b)).trans
         (the_ledger_counts_in_wraps (sq a + sq b) (a * b))⟩⟩,
   fun h n =>
     (the_split_lands n).symm.trans
       (congrArg (fun s : Bool × Nat => board s.1 s.2)
         (a_door_that_checks_papers_unpersons_its_guests residueSeat 0 h
           (residue n) (wraps n)))⟩

theorem fifteen_needs_a_fourth_square :
    (∀ x y z : Nat, x * x + y * y + z * z ≠ 15)
      ∧ 1 * 1 + 1 * 1 + 2 * 2 + 3 * 3 = 15 :=
  ⟨fifteen_is_not_three_squares, rfl⟩

theorem the_binary_composes_the_ternary_classifies :
    (∀ z w : GInt, (z.mul w).normSq = z.normSq * w.normSq)
      ∧ ¬ ∃ mul : (Int × Int × Int) → (Int × Int × Int) → (Int × Int × Int),
          ∀ x y, normSq3 (mul x y) = normSq3 x * normSq3 y :=
  ⟨the_couple_carries_the_norm, no_triple_carries_the_norm⟩

def the_egregious_reading_descends :=
  @Foam.a_reading_deaf_to_the_remainder_reads_the_ground

theorem the_shape_arrives_by_counting :
    freq ((book 2).map (fun w => freq w true)) 1 = 2
      ∧ freq ((book 2).map (fun w => freq w true)) 0 = 1
      ∧ freq ((book 2).map (fun w => freq w true)) 2 = 1 :=
  ⟨rfl, rfl, rfl⟩

def the_mean_is_the_mode := @Foam.the_middle_holds_the_most

theorem the_error_has_a_shape :
    (∀ n k : Nat, k ≤ n → classCount n k = classCount n (n - k))
      ∧ ∀ n k : Nat, 2 * k + 1 ≤ n → classCount n k ≤ classCount n (k + 1) :=
  ⟨the_census_is_symmetric, the_census_rises_to_the_middle⟩

theorem the_mode_follows_the_weights :
    ∀ t f n k : Nat, k < n → (k + 1) * (t + f) ≤ (n + 1) * t →
      classCount n k * (t ^ k * f ^ (n - k))
        ≤ classCount n (k + 1) * (t ^ (k + 1) * f ^ (n - (k + 1))) :=
  the_census_rises_to_the_lean

/-- info: 'Foam.Maps.Gauss.the_sum_is_deaf_to_the_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms the_sum_is_deaf_to_the_shuffle

/-- info: 'Foam.Maps.Gauss.congruent_not_equal' does not depend on any axioms -/
#guard_msgs in #print axioms congruent_not_equal

/-- info: 'Foam.Maps.Gauss.congruence_mends_what_equality_breaks' does not depend on any axioms -/
#guard_msgs in #print axioms congruence_mends_what_equality_breaks

/-- info: 'Foam.Maps.Gauss.the_cross_term_boards_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_cross_term_boards_the_guest

/-- info: 'Foam.Maps.Gauss.fifteen_needs_a_fourth_square' does not depend on any axioms -/
#guard_msgs in #print axioms fifteen_needs_a_fourth_square

/-- info: 'Foam.Maps.Gauss.the_binary_composes_the_ternary_classifies' does not depend on any axioms -/
#guard_msgs in #print axioms the_binary_composes_the_ternary_classifies

/-- info: 'Foam.Maps.Gauss.the_egregious_reading_descends' does not depend on any axioms -/
#guard_msgs in #print axioms the_egregious_reading_descends

/-- info: 'Foam.Maps.Gauss.the_shape_arrives_by_counting' does not depend on any axioms -/
#guard_msgs in #print axioms the_shape_arrives_by_counting

/-- info: 'Foam.Maps.Gauss.the_mean_is_the_mode' does not depend on any axioms -/
#guard_msgs in #print axioms the_mean_is_the_mode

/-- info: 'Foam.Maps.Gauss.the_error_has_a_shape' does not depend on any axioms -/
#guard_msgs in #print axioms the_error_has_a_shape

/-- info: 'Foam.Maps.Gauss.the_mode_follows_the_weights' does not depend on any axioms -/
#guard_msgs in #print axioms the_mode_follows_the_weights

end Foam.Maps.Gauss
