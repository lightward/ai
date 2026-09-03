import Foam
open Core Foam
set_option autoImplicit false

#guard peek (liftFrom tally (3 : Nat)) == 3
#guard feed (liftFrom tally (0 : Nat)) () [(), ()] == 3
#guard (liftFrom flip true [(), ()] : Bool)
#guard liftFrom tally (0 : Nat) [(), (), (), ()] == behavior tally [(), (), (), ()]
