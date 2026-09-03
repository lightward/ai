import Face
open Room Face
set_option autoImplicit false

#guard enrolled Nat.beq (intake Nat.beq ([], []) [(7, [7]), (7, [7]), (7, [7])]).1 7 == false
#guard enrolled Nat.beq (intake Nat.beq ([], []) [(8, [9]), (9, [8]), (8, [9]), (9, [8])]).1 8 == false
#guard enrolled Nat.beq (intake Nat.beq ([], []) [(8, [9]), (9, [8]), (8, [9]), (9, [8])]).1 9 == false
#guard lacking Nat.beq [1, 2] [1, 2, 9] == 1
#guard backed Nat.beq (9 :: [1, 2]) [1, 2, 9]
#guard enrolled Nat.beq (welcome Nat.beq (welcome Nat.beq ([1, 2], []) (9, [])) (8, [1, 2, 9])).1 8
#guard behavior tally (List.replicate 4 ()) == 4
#guard drive (buffered tally) (settleHeld tally ((2 : Nat), [(), ()])) [()]
        == drive (buffered tally) ((2 : Nat), [(), ()]) [()]
