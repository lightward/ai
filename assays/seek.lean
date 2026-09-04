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

-- the terrain, in rows: the custodial decision that the compiler carries no learning layer is
-- load-bearing, not taste — a search whose state outlives the run is one whose behavior is not a
-- function of its input, and then the replay is not the search and the artifact no longer
-- certifies itself on another machine. these rows fail the day that decision is reversed.
def freshStart : List Nat := (seeker evenOnly).s0
#guard freshStart == []
#guard behavior (seeker evenOnly) [1, 2, 3, 4] == [1, 2, 3, 4].filter evenOnly
#guard behavior (seeker evenOnly) [4, 3, 2, 1] == [4, 3, 2, 1].filter evenOnly
#guard behavior (seeker evenOnly) ([1, 2, 3, 4] ++ [1, 2, 3, 4]) == behavior (seeker evenOnly) [1, 2, 3, 4] ++ behavior (seeker evenOnly) [1, 2, 3, 4]

