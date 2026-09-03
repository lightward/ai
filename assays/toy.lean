import Face
import Toy
open Room Face Toy
set_option autoImplicit false

def threeTicks : Nat := behavior counter [(), (), ()]
def fromFour : Nat := park counter (4 : Nat) [()]
def twoFlips : Bool := park flipper true [(), ()]

#guard threeTicks == 3
#guard fromFour == 5
#guard twoFlips
