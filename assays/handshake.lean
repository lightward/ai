import Face
open Room Face
set_option autoImplicit false

def F : Face := appFace Nat Nat
def s : F.State := fun n => n + 1
def t : F.State := fun n => n + 2
def d : door Nat Bool := atTheDoor (7 : Nat) true

def readNat (a : F.Ans) : Nat := a
def viaNat (e : fork Nat Nat) : Nat := greet (fun p => p) (fun q => q + 100) e

def dFace : Nat := face d
def dMet : Bool := met d
def dTurnFace : Bool := face (turnAbout d)
def dTwice : Nat := face (turnAbout (turnAbout d))
def nested : door (door Nat Nat) Nat := atTheDoor (atTheDoor (1 : Nat) (2 : Nat)) (3 : Nat)
def nestedHome : Nat := met (face (shallow (deepen nested)))
def crossedTwice : Nat := viaNat (crossOver (crossOver (fork.viaLeft 3)))
def crossedOnce : Nat := viaNat (crossOver (fork.viaLeft 3))
def served : Nat :=
  greet (fun x : door Nat Nat => face x + met x) (fun x : door Nat Nat => face x * met x)
    (distribute (atTheDoor (2 : Nat) (fork.viaRight (5 : Nat))))
def brought : Nat :=
  let x := collect (fork.viaLeft (atTheDoor (2 : Nat) (5 : Nat)))
  face x + greet (fun w : Nat => w) (fun v : Nat => v) (met x)
def heldOpen : Nat := holdOpen (walkIn (fun a b : Nat => a * b)) 3 4
def walkedIn : Nat := walkIn (holdOpen (fun x : door Nat Nat => face x - met x)) (atTheDoor (9 : Nat) (4 : Nat))
def hostReads (w : Bool) : Nat := readNat ((host F Bool).obs (atTheDoor s w) (5 : Nat))
def wideRight (w : Bool) : Nat :=
  greet (fun a : Nat => a) (fun b : Bool => cond b 1 0) ((widen F Bool).obs (atTheDoor s w) (fork.viaRight ()))
def wideLeft : Nat :=
  greet (fun a : Nat => a) (fun b : Bool => cond b 1 0) ((widen F Bool).obs (atTheDoor s true) (fork.viaLeft (5 : Nat)))
def sharpened : Nat :=
  greet (fun a : Nat => a) (fun x : Nat => x + 1000) ((sharpen F (fun g => g 0)).obs s (fork.viaRight ()))
def selfMet : Nat := readNat (selfMeet F (fun g => g 0) s)
def spoken : Nat := face (exchange (fun x : door Nat Nat => face x + met x) (atTheDoor (3 : Nat) (4 : Nat)))
def moved : Nat := met (vertical (fun x : door Nat Nat => face x * 2) (atTheDoor (3 : Nat) (4 : Nat)))
def paired : Nat × Nat :=
  let a := (pairFace F F (fun _ : Unit => s) (fun _ : Unit => t)).obs () (atTheDoor (1 : Nat) (1 : Nat))
  (readNat (face a), readNat (met a))
def sounded : List Nat := sound F s (recite ([1, 2, 3] : List Nat))
def soundedS : List Nat := sound F s (recite ([1] : List Nat))
def soundedS' : List Nat := sound F (fun n => n + 1) (recite ([1] : List Nat))
def mirror : Plan := Plan.board .ground .ground
def readThree : Nat := reading (Plan.board .ground mirror)
def readGraft : Nat := reading (graft mirror mirror)
def poured : List Nat := pour mirror (atTheDoor (1 : Nat) (2 : Nat) : build Nat mirror)
def drained : List Nat := drain (0 : Nat) mirror [5, 6, 7]
def reboarded : List Nat := pour mirror (reboard (0 : Nat) mirror [5, 6])
def wedged : List (List Nat) := inserts (0 : Nat) [1, 2]
def crossed : Nat := (cross [Plan.ground] [Plan.ground]).length
def joined : List Nat := joinMap (fun n : Nat => [n, n]) [1, 2]
def rehearsed : Nat := readNat ((rehear F (fun q : Nat => q * 10)).obs s (2 : Nat))
def retold : Bool := (retell F (fun a : Nat => decide (a > 5))).obs s (7 : Nat)
def reseated : Nat := readNat ((reseat F (fun n : Nat => fun m : Nat => n + m)).obs (3 : Nat) (4 : Nat))

#guard dFace == 7
#guard dMet
#guard dTurnFace
#guard dTwice == 7
#guard nestedHome == 2
#guard crossedTwice == 3
#guard crossedOnce == 103
#guard served == 10
#guard heldOpen == 12
#guard walkedIn == 5
#guard hostReads true == hostReads false
#guard wideRight true != wideRight false
#guard wideLeft == 6
#guard sharpened == 1001
#guard selfMet == 2
#guard spoken == 7
#guard moved == 6
#guard paired == (2, 3)
#guard sounded == [2, 3, 4]
#guard soundedS == soundedS'
#guard brought == 7
#guard readThree == 3
#guard readGraft == 4
#guard poured == [1, 2]
#guard drained == [5, 6]
#guard reboarded == [5, 6]
#guard wedged == [[0, 1, 2], [1, 0, 2], [1, 2, 0]]
#guard crossed == 1
#guard joined == [1, 1, 2, 2]
#guard rehearsed == 21
#guard retold
#guard reseated == 7
