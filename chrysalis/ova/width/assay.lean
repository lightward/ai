import Seed
open Seed
set_option autoImplicit false

#guard [true, false].all (fun x => [true, false].all (fun y => [true, false].all
  (fun z => (x == y) || (y == z) || (x == z))))
#guard census 3 == 2
#guard census 4 == 5
#guard (walkIn (fun a b : Nat => a + b)
  ((pairFace (appFace Unit Nat) (appFace Unit Nat) (fun n : Nat => fun _ => n)
    (fun n : Nat => fun _ => n + n)).obs (7 : Nat) (atTheDoor () ())) == 21)
