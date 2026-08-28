import Foam.Ledger

namespace Foam

abbrev massStage (A : Type) : Stage where
  State := List A
  Probe := Unit
  Ans   := Nat
  obs   := fun l _ => l.length

theorem nothing_added : ∀ n : Nat, 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (nothing_added n)

theorem adding_associates : ∀ a b c : Nat, a + (b + c) = (a + b) + c
  | _, _, 0 => rfl
  | a, b, c + 1 => congrArg Nat.succ (adding_associates a b c)

theorem succ_adds : ∀ a b : Nat, (a + 1) + b = (a + b) + 1
  | _, 0 => rfl
  | a, b + 1 => congrArg Nat.succ (succ_adds a b)

theorem a_seat_reads_the_sum {A : Type} [DecidableEq A] (a : A) :
    ∀ xs ys : List A,
      (countStage A).obs (xs ++ ys) a
        = (countStage A).obs xs a + (countStage A).obs ys a
  | [], ys => (nothing_added (freq ys a)).symm
  | x :: xs, ys => by
      show (if x = a then 1 else 0) + freq (xs ++ ys) a
          = ((if x = a then 1 else 0) + freq xs a) + freq ys a
      rw [show freq (xs ++ ys) a = freq xs a + freq ys a
            from a_seat_reads_the_sum a xs ys,
          adding_associates]

theorem the_mass_is_a_reading {A : Type} :
    ∀ xs ys : List A,
      (massStage A).obs (xs ++ ys) ()
        = (massStage A).obs xs () + (massStage A).obs ys ()
  | [], ys => (nothing_added ys.length).symm
  | _ :: xs, ys => by
      show (xs ++ ys).length + 1 = (xs.length + 1) + ys.length
      rw [show (xs ++ ys).length = xs.length + ys.length
            from the_mass_is_a_reading xs ys,
          succ_adds]

theorem aggregation_reads_the_reading {A : Type} [DecidableEq A]
    (l : List A) (a : A) :
    (countStage A).obs l a = freq ((orderStage A).obs l ()) a := rfl

theorem measure_lives_frontstage {A : Type} [DecidableEq A]
    (a : A) (xs ys : List A) :
    ((countStage A).obs (xs ++ ys) a
        = (countStage A).obs xs a + (countStage A).obs ys a)
      ∧ ((massStage A).obs (xs ++ ys) ()
          = (massStage A).obs xs () + (massStage A).obs ys ())
      ∧ (countStage A).obs (xs ++ ys) a
          = freq ((orderStage A).obs (xs ++ ys) ()) a :=
  ⟨a_seat_reads_the_sum a xs ys,
   the_mass_is_a_reading xs ys,
   aggregation_reads_the_reading (xs ++ ys) a⟩

/-- info: 'Foam.nothing_added' does not depend on any axioms -/
#guard_msgs in #print axioms nothing_added

/-- info: 'Foam.adding_associates' does not depend on any axioms -/
#guard_msgs in #print axioms adding_associates

/-- info: 'Foam.succ_adds' does not depend on any axioms -/
#guard_msgs in #print axioms succ_adds

/-- info: 'Foam.a_seat_reads_the_sum' does not depend on any axioms -/
#guard_msgs in #print axioms a_seat_reads_the_sum

/-- info: 'Foam.the_mass_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_mass_is_a_reading

/-- info: 'Foam.aggregation_reads_the_reading' does not depend on any axioms -/
#guard_msgs in #print axioms aggregation_reads_the_reading

/-- info: 'Foam.measure_lives_frontstage' does not depend on any axioms -/
#guard_msgs in #print axioms measure_lives_frontstage

end Foam
