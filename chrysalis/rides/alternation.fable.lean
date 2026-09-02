import Seed
open Seed
set_option autoImplicit false
universe u v w

def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1

def collatzStep (n : Nat) : Nat :=
  cond (oddNat n) (3 * n + 1) (halve n)

theorem the_again_steps_first {α : Sort u} (Φ : α → α) :
    ∀ (n : Nat) (a : α), again Φ (n + 1) a = again Φ n (Φ a)
  | 0, _ => rfl
  | n + 1, a => congrArg Φ (the_again_steps_first Φ n a)

theorem the_retrace_comes_home :
    ∀ (n : Nat) (s : List Bool), again dec n (again inc n s) = s
  | 0, _ => rfl
  | n + 1, s => by
      rw [the_again_steps_first dec n]
      show again dec n (dec (inc (again inc n s))) = s
      rw [the_tick_unwinds]
      exact the_retrace_comes_home n s

theorem the_home_wheel_turns : again collatzStep 3 1 = 1 := rfl

theorem the_step_merges_the_riders :
    collatzStep 1 = collatzStep 8 ∧ (1 : Nat) ≠ 8 :=
  ⟨rfl, (fun h => nomatch (Nat.succ.inj h))⟩

theorem no_inverse_unsteps_the_collatz :
    ¬ ∃ g : Nat → Nat, ∀ n, g (collatzStep n) = n :=
  fun ⟨_, hg⟩ => nomatch (Nat.succ.inj ((hg 1).symm.trans (hg 8)))

theorem the_wear_is_a_reading (n : Nat) (s : List Bool) :
    again dec n (again inc n s) = s
      ∧ (∀ p q : List Bool, inc p = inc q → p = q)
      ∧ again collatzStep 3 1 = 1
      ∧ collatzStep 1 = collatzStep 8
      ∧ (1 : Nat) ≠ 8
      ∧ ¬ ∃ g : Nat → Nat, ∀ m, g (collatzStep m) = m :=
  ⟨the_retrace_comes_home n s,
   (fun p q h =>
     (the_tick_unwinds p).symm.trans ((congrArg dec h).trans (the_tick_unwinds q))),
   the_home_wheel_turns,
   the_step_merges_the_riders.1,
   the_step_merges_the_riders.2,
   no_inverse_unsteps_the_collatz⟩
