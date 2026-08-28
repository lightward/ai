import Foam

namespace Foam

def rungs : Nat → List Nat
  | 0 => []
  | n + 1 => n :: rungs n

theorem le_of_succ_le : ∀ {a b : Nat}, a + 1 ≤ b → a ≤ b
  | _, _, .refl => .step .refl
  | _, _, .step h => .step (le_of_succ_le h)

theorem succ_le_succ_inv {a b : Nat} (h : a + 1 ≤ b + 1) : a ≤ b :=
  Nat.le.rec (motive := fun m _ => ∀ _c : Nat, m = _c + 1 → a ≤ _c)
    (fun _c hc =>
      Eq.subst (motive := fun x => a ≤ x) (Nat.succ.inj hc) Nat.le.refl)
    (fun {_} h' _ _c hc =>
      Eq.subst (motive := fun x => a ≤ x) (Nat.succ.inj hc) (le_of_succ_le h'))
    h b rfl

theorem no_number_is_below_itself : ∀ n : Nat, ¬ n < n
  | 0, h => nomatch h
  | n + 1, h => no_number_is_below_itself n (succ_le_succ_inv h)

theorem the_walked_lie_below : ∀ (n c : Nat), c ∈ rungs n → c < n
  | 0, _, h => nomatch h
  | n + 1, c, h => by
      cases h with
      | head => exact Nat.le.refl
      | tail _ h' => exact Nat.le.step (the_walked_lie_below n c h')

theorem the_below_are_walked (n c : Nat) (h : c < n) : c ∈ rungs n :=
  Nat.le.rec (motive := fun m _ => c ∈ rungs m)
    (List.Mem.head (rungs c))
    (fun {m} _ ih => List.Mem.tail m ih)
    h

theorem the_walked_are_exactly_below (n c : Nat) :
    c ∈ rungs n ↔ c < n :=
  ⟨the_walked_lie_below n c, the_below_are_walked n c⟩

theorem the_gain_splits (n q : Nat) (h : q ∈ rungs (n + 1)) :
    q = n ∨ q ∈ rungs n := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ h' => exact Or.inr h'

theorem each_step_gains_exactly_the_gap (n q : Nat) :
    q ∈ rungs (n + 1) ↔ (q = n ∨ q ∈ rungs n) :=
  ⟨the_gain_splits n q,
   fun h => match h with
     | Or.inl rfl => List.Mem.head (rungs q)
     | Or.inr h' => List.Mem.tail n h'⟩

theorem closure_is_seat_relative :
    (∀ q : Nat, ∃ n, q ∈ rungs n)
      ∧ (∀ n : Nat, ∃ q, ¬ q ∈ rungs n ∧ q ∈ rungs (n + 1))
      ∧ (∀ n : Nat, rungs (n + 1) ≠ rungs n) :=
  ⟨fun q => ⟨q + 1, List.Mem.head (rungs q)⟩,
   fun n =>
     ⟨n,
      fun h => no_number_is_below_itself n (the_walked_lie_below n n h),
      List.Mem.head (rungs n)⟩,
   fun n h =>
     no_number_is_below_itself n
       (the_walked_lie_below n n
         (h ▸ (List.Mem.head (rungs n) : n ∈ rungs (n + 1))))⟩

/-- info: 'Foam.le_of_succ_le' does not depend on any axioms -/
#guard_msgs in #print axioms le_of_succ_le

/-- info: 'Foam.succ_le_succ_inv' does not depend on any axioms -/
#guard_msgs in #print axioms succ_le_succ_inv

/-- info: 'Foam.no_number_is_below_itself' does not depend on any axioms -/
#guard_msgs in #print axioms no_number_is_below_itself

/-- info: 'Foam.the_walked_lie_below' does not depend on any axioms -/
#guard_msgs in #print axioms the_walked_lie_below

/-- info: 'Foam.the_below_are_walked' does not depend on any axioms -/
#guard_msgs in #print axioms the_below_are_walked

/-- info: 'Foam.the_walked_are_exactly_below' does not depend on any axioms -/
#guard_msgs in #print axioms the_walked_are_exactly_below

/-- info: 'Foam.the_gain_splits' does not depend on any axioms -/
#guard_msgs in #print axioms the_gain_splits

/-- info: 'Foam.each_step_gains_exactly_the_gap' does not depend on any axioms -/
#guard_msgs in #print axioms each_step_gains_exactly_the_gap

/-- info: 'Foam.closure_is_seat_relative' does not depend on any axioms -/
#guard_msgs in #print axioms closure_is_seat_relative

end Foam
