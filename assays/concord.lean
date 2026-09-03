import Foam
open Core Foam
set_option autoImplicit false

def toy : Face := appFace Nat Nat
def theModel : door toy.State Nat := atTheDoor (fun n => n + 1) 3
def theOtherModel : door toy.State Nat := atTheDoor (fun n => n + 1) 99
def readAtTwo : Nat := face ((concordFace toy Nat).obs theModel (atTheDoor (2 : Nat) ()))
def modelAtTwo : Nat := met ((concordFace toy Nat).obs theModel (atTheDoor (2 : Nat) ()))
def soundMine : List Nat := sound (host toy Nat) theModel (recite ([1, 2] : List Nat))
def soundYours : List Nat := sound (host toy Nat) theOtherModel (recite ([1, 2] : List Nat))
def agreesOver (ps : List Nat) : Bool :=
  ps.all (fun p => Nat.beq (toy.obs (face theModel) p) (met theModel))

#guard readAtTwo == 3
#guard modelAtTwo == 3
#guard soundMine == soundYours
#guard soundMine == [2, 3]
#guard agreesOver [2]
#guard !(agreesOver [2, 5])
