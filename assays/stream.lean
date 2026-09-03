import Face
open Room Face
set_option autoImplicit false

#guard streamOf tally 5 == 5
#guard toSheet (streamOf tally) [(), (), ()] == 3
#guard toStream (liftFrom tally (0 : Nat)) 4 == 4
#guard streamOf flip 2 == streamOf flip 0
#guard behavior (selfSteered tally (fun _ => ())) [(), (), ()] == 3
#guard (selfWord tally (fun _ => ()) (0 : Nat) 2).length == 2
#guard behavior restingCounter [(), ()] == true
#guard behavior hollowShell [()] == behavior restingCounter [()]
#guard behavior paceOne [(), (), ()] == true
#guard behavior (retune (fun (_ : Bool) => ()) tally) [true, false] == 2
#guard behavior (revoice (· + 1) tally) [()] == 2
#guard behavior (ledger Nat) [1, 2, 3] == [1, 2, 3]
#guard behavior (replayer tally) [(), ()] == 2
def gapRead : Nat := (airGap Unit Nat).obs tally [(), ()]
#guard gapRead == 2
