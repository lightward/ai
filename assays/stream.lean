import Foam
open Foam
set_option autoImplicit false

#guard streamOf tally 5 == 5
#guard toSheet (streamOf tally) [(), (), ()] == 3
#guard toStream (liftFrom tally (0 : Nat)) 4 == 4
#guard streamOf flip 2 == streamOf flip 0
