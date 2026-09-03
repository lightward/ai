import Face
open Room Face
set_option autoImplicit false

#guard census 1 == 1
#guard census 2 == 1
#guard census 3 == 2
#guard census 4 == 5
#guard census 5 == 14
#guard fold (fun a b : Nat => a + b) 1 (Plan.board .ground (Plan.board .ground .ground)) == 3
#guard (allPlans 2).length == 5
#guard (allPlans 3).length == 26
def regrounded : List Nat :=
  pour (Plan.board .ground .ground)
    (reground (· + 1) (Plan.board .ground .ground) (atTheDoor (1 : Nat) (2 : Nat)))
#guard regrounded == [2, 3]
#guard (reboardAux (0 : Nat) (Plan.board .ground .ground) [5, 6, 7]).2 == [7]
