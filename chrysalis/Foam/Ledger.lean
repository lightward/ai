import Foam

namespace Foam

def freq {A : Type} [DecidableEq A] : List A → A → Nat
  | [], _ => 0
  | x :: l, s => (if x = s then 1 else 0) + freq l s

abbrev countStage (A : Type) [DecidableEq A] : Stage where
  State := List A
  Probe := A
  Ans   := Nat
  obs   := freq

abbrev orderStage (A : Type) : Stage where
  State := List A
  Probe := Unit
  Ans   := List A
  obs   := fun l _ => l

def swapTop {A : Type} : List A → List A
  | [] => []
  | [a] => [a]
  | a :: b :: t => b :: a :: t

theorem freq_perm {A : Type} [DecidableEq A] {xs ys : List A}
    (h : xs.Perm ys) (s : A) : freq xs s = freq ys s := by
  induction h with
  | nil => rfl
  | cons x _ ih => exact congrArg ((if x = s then 1 else 0) + ·) ih
  | swap x y l => exact Nat.add_left_comm _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem counting_is_licensed_by_permutation (A : Type) [DecidableEq A] :
    Licensed (countStage A) List.Perm :=
  fun _ _ h p => freq_perm h p

theorem swapTop_perm {A : Type} : ∀ l : List A, (swapTop l).Perm l
  | [] => List.Perm.nil
  | [a] => List.Perm.cons a List.Perm.nil
  | a :: b :: t => List.Perm.swap a b t

theorem the_shuffle_is_unheard {A : Type} [DecidableEq A] :
    ∀ (ps s : List A),
      transcriptWith (countStage A) swapTop s ps = transcript (countStage A) s ps :=
  a_license_is_a_gauge (countStage A) List.Perm
    (counting_is_licensed_by_permutation A) swapTop swapTop_perm

theorem the_order_is_the_remainder {A : Type} [DecidableEq A]
    (a b : A) (hab : a ≠ b) :
    indist (countStage A) [a, b] [b, a] ∧ [a, b] ≠ [b, a] :=
  ⟨fun p => freq_perm (List.Perm.swap b a []) p,
   fun h => hab (congrArg (fun l => l.headD a) h)⟩

theorem a_wider_seat_reads_the_order {A : Type} [DecidableEq A]
    (a b : A) (hab : a ≠ b) :
    indist (countStage A) [a, b] [b, a]
      ∧ (orderStage A).obs [a, b] () ≠ (orderStage A).obs [b, a] () :=
  ⟨(the_order_is_the_remainder a b hab).1,
   fun h => hab (congrArg (fun l => l.headD a) h)⟩

theorem the_first_handshake_is_counting {A : Type} [DecidableEq A]
    (a b : A) (hab : a ≠ b) :
    (∀ (ps s : List A),
      transcriptWith (countStage A) swapTop s ps = transcript (countStage A) s ps)
      ∧ indist (countStage A) [a, b] [b, a]
      ∧ [a, b] ≠ [b, a]
      ∧ (orderStage A).obs [a, b] () ≠ (orderStage A).obs [b, a] () :=
  ⟨the_shuffle_is_unheard,
   (the_order_is_the_remainder a b hab).1,
   (the_order_is_the_remainder a b hab).2,
   (a_wider_seat_reads_the_order a b hab).2⟩

/-- info: 'Foam.freq_perm' does not depend on any axioms -/
#guard_msgs in #print axioms freq_perm

/-- info: 'Foam.counting_is_licensed_by_permutation' does not depend on any axioms -/
#guard_msgs in #print axioms counting_is_licensed_by_permutation

/-- info: 'Foam.swapTop_perm' does not depend on any axioms -/
#guard_msgs in #print axioms swapTop_perm

/-- info: 'Foam.the_shuffle_is_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms the_shuffle_is_unheard

/-- info: 'Foam.the_order_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_order_is_the_remainder

/-- info: 'Foam.a_wider_seat_reads_the_order' does not depend on any axioms -/
#guard_msgs in #print axioms a_wider_seat_reads_the_order

/-- info: 'Foam.the_first_handshake_is_counting' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_handshake_is_counting

end Foam
