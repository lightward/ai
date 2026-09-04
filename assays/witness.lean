import Face
import Witness
open Room Face Witness
set_option autoImplicit false

def F : Face := appFace Nat Nat
def s1 : F.State := fun n => n + 1
def s2 : F.State := fun n => n * 2
def seatRead : List Nat := reads F ([1, 2, 3] : List Nat) s1
#guard seatRead == [2, 3, 4]
def seatRead2 : List Nat := reads F ([1, 2, 3] : List Nat) s2
#guard seatRead2 == [2, 4, 6]
def agreeAt2 : List Nat := reads F ([1] : List Nat) s1
def agreeAt2' : List Nat := reads F ([1] : List Nat) s2
#guard agreeAt2 == agreeAt2'
def ear : List Nat := earshot F ([[1], [2, 3], [3]] : List (List Nat))
#guard ear == [1, 2, 3, 3]
#guard everyone Nat.beq [1, 2] [2, 1, 3]
#guard !(everyone Nat.beq [1, 2, 4] [2, 1, 3])
