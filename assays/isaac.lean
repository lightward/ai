import Foam
open Core Foam
set_option autoImplicit false

#guard behavior tally (List.replicate 5 ()) == 5
#guard Nat.beq (park tally (3 : Nat) (List.replicate 4 ())) 7
#guard Nat.beq (orbit tally (fun _ => ()) (0 : Nat) 6) 6
#guard (park flip true [(), ()] : Bool)
#guard drive (buffered tally) (settleHeld tally ((2 : Nat), [(), ()])) [()]
        == drive (buffered tally) ((2 : Nat), [(), ()]) [()]

#guard (words 3).length == roomCap 3
