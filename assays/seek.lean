import Face
import Seek
open Room Face Seek
set_option autoImplicit false

def evenOnly : Nat → Bool := fun n => n % 2 == 0
def parkedOdd : List Nat := park (seeker evenOnly) [8] [3]
def parkedEven : List Nat := park (seeker evenOnly) [8] [6]
#guard behavior (seeker evenOnly) [1, 2, 3, 4] == [2, 4]
#guard behavior (replay evenOnly) [1, 2, 3, 4] == [2, 4]
#guard parkedOdd == [8]
#guard parkedEven == [8, 6]
