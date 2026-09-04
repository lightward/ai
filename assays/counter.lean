import Room
import Counter
open Room Counter
set_option autoImplicit false

def demo : List sighting := [(1, []), (2, [3]), (3, [])]
def afterOne : room := round empty demo
def afterSweep : room := round (afterOne.1, []) afterOne.2
def selfCiter : room := round empty [(7, [7])]
def circle : room := round empty [(8, [9]), (9, [8])]

#guard seated afterOne 1
#guard seated afterOne 3
#guard !(seated afterOne 2)
#guard afterOne.2.length == 1
#guard seated afterSweep 2
#guard afterSweep.2.length == 0
#guard weight afterOne [3, 2] == 1
#guard weight afterSweep [3, 2] == 0
#guard !(seated selfCiter 7)
#guard !(seated circle 8) && !(seated circle 9)
def offered : room := offer empty (4, [])
#guard seated offered 4
#guard !(seated (offer empty (5, [6])) 5)

-- the gate, in rows: the verdict reads the artifact only through its receipts. a body is a list
-- of moves; the kernel's reading of it (its receipt) is the moves numbered 100 and up, a
-- standard-library lemma that smuggles an axiom; the prune drops the moves numbered 0, a `fail`
-- that never closed anything. these rows fail the day the gate starts reading bodies.
def axiomsOf (b : List Nat) : List Nat := b.filter (fun x => Nat.ble 100 x)
def dropFails (b : List Nat) : List Nat := b.filter (fun x => !(Nat.beq x 0))
def trailA : List (Nat × List Nat) := [(1, [3, 0, 5]), (2, [0, 7]), (3, [])]
def trailB : List (Nat × List Nat) := rebody dropFails trailA
def trailC : List (Nat × List Nat) := [(1, [3, 100]), (2, [7])]
def gateA : Bool := gate axiomsOf trailA
def gateB : Bool := gate axiomsOf trailB
def gateC : Bool := gate axiomsOf trailC
def gateCpruned : Bool := gate axiomsOf (rebody dropFails trailC)
def shadowA : List (Nat × List Nat) := shadow axiomsOf trailA
def shadowB : List (Nat × List Nat) := shadow axiomsOf trailB
def shadowC : List (Nat × List Nat) := shadow axiomsOf trailC
#guard gateA
#guard gateB
#guard !gateC
#guard !gateCpruned
#guard shadowA == shadowB
#guard trailA != trailB
#guard shadowA == [(1, []), (2, []), (3, [])]
#guard shadowC == [(1, [100]), (2, [])]
