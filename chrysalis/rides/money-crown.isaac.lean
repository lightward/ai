import Seed
open Seed
set_option autoImplicit false
universe u v w

theorem the_direction_is_even_money {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (hl : Apart l) (ha : a ∈ l) (hb : b ∈ l) :
    ((perms l).filter (firstOf beq a b)).length
        = ((perms l).filter (firstOf beq b a)).length
      ∧ ((perms l).filter (firstOf beq a b)).length
          + ((perms l).filter (firstOf beq b a)).length = fact l.length
      ∧ sameRatio ((perms l).filter (firstOf beq a b)).length
          (fact l.length) 1 2 := by
  have hsym := the_two_directions_count_alike hE hR hab hl ha hb
  have htotal : ((perms l).filter (firstOf beq a b)).length
      + ((perms l).filter (firstOf beq b a)).length = fact l.length :=
    (the_verdicts_split_the_room hE hR hab ha).trans
      (the_orders_count_to_the_factorial l)
  refine ⟨hsym, htotal, ?_⟩
  show ((perms l).filter (firstOf beq a b)).length * 2
      = 1 * fact l.length
  rw [mul_two_reads_double, one_scales]
  exact (congrArg (((perms l).filter (firstOf beq a b)).length + ·)
    hsym).trans htotal

