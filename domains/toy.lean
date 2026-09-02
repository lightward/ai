import Seed
open Seed
set_option autoImplicit false
universe u v w

namespace Toy

def counter : Machine Unit Nat := tally

def flipper : Machine Unit Bool := flip

theorem the_toy_counts (w : List Unit) : behavior counter w = w.length := sorry

theorem the_toy_parks (w : List Unit) (s : Nat) : park counter s w = s + w.length := sorry

theorem the_toy_resumes (u v : List Unit) (s : Nat) :
    park counter s (u ++ v) = park counter (park counter s u) v := sorry

theorem the_toy_flips_back : ∀ b : Bool, park flipper b [(), ()] = b := sorry

end Toy
