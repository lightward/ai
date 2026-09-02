import Seed
open Seed
set_option autoImplicit false
universe u v w

theorem the_census_of_orders_is_exact {A : Type u} (l p : List A)
    (hl : Apart l) :
    (p.Perm l ↔ p ∈ perms l)
      ∧ Apart (perms l)
      ∧ (perms l).length = fact l.length :=
  ⟨⟨every_shuffle_is_an_order l p, every_order_is_a_shuffle l p⟩,
   the_orders_repeat_never l hl,
   the_orders_count_to_the_factorial l⟩

