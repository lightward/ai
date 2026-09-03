import Face
open Room Face
set_option autoImplicit false

#guard behavior tally (List.replicate 4 ()) == 4
#guard drive (buffered tally) (settleHeld tally ((2 : Nat), [(), ()])) [()]
        == drive (buffered tally) ((2 : Nat), [(), ()]) [()]
