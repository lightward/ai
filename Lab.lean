import Seed

open Seed

def checkNat (name : String) (got expected : Nat) : IO Bool := do
  if got == expected then
    IO.println s!"green: {name} — {expected}"
    return true
  else
    IO.eprintln s!"red: {name} — read {got}, expected {expected}"
    return false

abbrev toyPlan : Plan := .board .ground (.board .ground .ground)

def toyImport : build Nat toyPlan := ((9109 : Nat), ((2 : Nat), (3 : Nat)))

def meterVote : Nat := 299792458

theorem the_treaty_reads_exactly :
    readAcross meterVote paceAtHome = 299792458 := rfl

/-- info: 'the_treaty_reads_exactly' does not depend on any axioms -/
#guard_msgs in #print axioms the_treaty_reads_exactly

def planckVote : Nat := 662607015

theorem the_planck_treaty_reads_exactly :
    readAcross planckVote paceAtHome = 662607015 := rfl

/-- info: 'the_planck_treaty_reads_exactly' does not depend on any axioms -/
#guard_msgs in #print axioms the_planck_treaty_reads_exactly

def chargeVote : Nat := 1602176634

theorem the_charge_treaty_reads_exactly :
    readAcross chargeVote paceAtHome = 1602176634 := rfl

/-- info: 'the_charge_treaty_reads_exactly' does not depend on any axioms -/
#guard_msgs in #print axioms the_charge_treaty_reads_exactly

def boltzmannVote : Nat := 1380649

theorem the_boltzmann_treaty_reads_exactly :
    readAcross boltzmannVote paceAtHome = 1380649 := rfl

/-- info: 'the_boltzmann_treaty_reads_exactly' does not depend on any axioms -/
#guard_msgs in #print axioms the_boltzmann_treaty_reads_exactly

def checkTrue (name : String) (got : Bool) : IO Bool := do
  if got then
    IO.println s!"green: {name}"
    return true
  else
    IO.eprintln s!"red: {name}"
    return false

def m2014 : Measured := ⟨91093834500, 91093836700⟩

def m2018 : Measured := ⟨91093836987, 91093837043⟩

abbrev lineagePlan : Plan := graft .ground (.board .ground .ground)

def electronLineage : build Measured lineagePlan := atTheDoor m2014 m2018

structure DarkRow where
  name : String
  expects : Measured
  awaits : String

structure OpenRow where
  name : String
  awaits : String

def openRows : List OpenRow :=
  [⟨"love row — interaction under mutual unknown parameters, promised eventual fulfillment (currying at the root)",
    "the promise stratum: deferred compatibility, kept where the meeting keeps its map"⟩,
   ⟨"story row — stage(tell_me_your_story) returns a free-range class-mate of its refiner",
    "a telling-generator and the class-checker: fold-equal to the refiner, provably distinct, gauge in the surface"⟩,
   ⟨"saturator row — the from-zero firing as an executable: enumerate small shapes over the room, hold the nameless in the vestibule, exit 0 at saturation",
    "census generalized to the kid + a shape-enumerator over the type semiring's normal forms"⟩]

def darkRows : List DarkRow :=
  [⟨"rider row — electron mass reads back, scaled e-41 kg (codata 2018: 9.1093837015(28)e-31)",
    ⟨91093836987, 91093837043⟩,
    "spec-side dynamics — trajectories under red-driven grafting; the interior cannot throw, so time is the meeting's ledger"⟩]

def main : IO UInt32 := do
  let mut ok := true
  ok := (← checkNat "census 1" (census 1) 1) && ok
  ok := (← checkNat "census 2" (census 2) 1) && ok
  ok := (← checkNat "census 3" (census 3) 2) && ok
  ok := (← checkNat "census 4" (census 4) 5) && ok
  ok := (← checkNat "census 5 — catalan, euler counter-signs" (census 5) 14) && ok
  let staged := reground (fun w => w * 1000) toyPlan toyImport
  ok := (← checkNat
    "toy import threads the spine — the customs law, dynamic register"
    (spine Nat toyPlan staged) 9109000) && ok
  ok := (← checkNat
    "treaty row — c reads back from the SI label (the vote is the section)"
    (readAcross meterVote paceAtHome) 299792458) && ok
  ok := (← checkNat "treaty row — h reads back (6.62607015e-34 J·s, scaled e-42)"
    (readAcross planckVote paceAtHome) 662607015) && ok
  ok := (← checkNat "treaty row — e reads back (1.602176634e-19 C, scaled e-28)"
    (readAcross chargeVote paceAtHome) 1602176634) && ok
  ok := (← checkNat "treaty row — k_B reads back (1.380649e-23 J/K, scaled e-29)"
    (readAcross boltzmannVote paceAtHome) 1380649) && ok
  let fine : Measured := ⟨95, 105⟩
  let coarse : Measured := ⟨90, 110⟩
  ok := (← checkTrue
    "toy tolerance — the refined reading still lands, dynamic register"
    (tighter fine coarse && within fine 100 && within coarse 100)) && ok
  ok := (← checkNat
    "lineage row — the 2014 stage still answers at the face (spine reads lo)"
    (spine Measured lineagePlan electronLineage).lo 91093834500) && ok
  ok := (← checkNat
    "lineage row — the 2018 revision boards as the guest (met reads lo)"
    (met electronLineage).lo 91093836987) && ok
  ok := (← checkTrue
    "lineage row — the codata jump is real and boarded (2018 center outside 2014, inside 2018)"
    (!(within m2014 91093837015) && within m2018 91093837015)) && ok
  let ancestor : Plan := .board .ground .ground
  let child : Plan := .board .ground (.board .ground .ground)
  ok := (← checkTrue
    "settle row — the parent folds into the ground (drop the tree, keep the reading)"
    (fold (fun a b => a + b) 1 (graft ancestor child)
      == fold (fun a b => a + b)
          (fold (fun a b => a + b) 1 ancestor) child)) && ok
  ok := (← checkNat "fork row — one greeter, two entrances (via the left)"
    (greet (fun n => n + 1) (fun n => n * 2) (viaLeft 4)) 5) && ok
  ok := (← checkNat "fork row — one greeter, two entrances (via the right)"
    (greet (fun n => n + 1) (fun n => n * 2) (viaRight 4)) 8) && ok
  ok := (← checkNat "sweep row — the crossing returns (the fork commutes, involution)"
    (greet (fun n => n) (fun n => n)
      (crossOver (crossOver (viaLeft (6 : Nat) : fork Nat Nat)))) 6) && ok
  ok := (← checkNat "identity row — the anonymous guest is free (door times one)"
    (face (atTheDoor (9 : Nat) ())) 9) && ok
  ok := (← checkNat "identity row — a sealed entrance adds nothing (fork plus zero)"
    (noEntrance (viaLeft (9 : Nat) : fork Nat Empty)) 9) && ok
  let rtL := collect (distribute (atTheDoor (7 : Nat) (viaLeft (3 : Nat) : fork Nat Nat)))
  ok := (← checkNat "semiring row — the host survives the split" (face rtL) 7) && ok
  ok := (← checkNat "semiring row — the left branch survives the round trip"
    (greet (fun n => n) (fun n => n + 100) (met rtL)) 3) && ok
  let rtR := collect (distribute (atTheDoor (7 : Nat) (viaRight (3 : Nat) : fork Nat Nat)))
  ok := (← checkNat "semiring row — the right branch survives the round trip"
    (greet (fun n => n) (fun n => n + 100) (met rtR)) 103) && ok
  IO.println "chronicle — the first tick (time lives at the meeting):"
  let want := 3
  let s0 : Plan := .ground
  let r0 := fold (fun a b => a + b) 1 s0
  IO.println s!"  throw: expectation {want}, reading {r0} — the row reds, resolve is invoked"
  let s1 : Plan := graft s0 (.board .ground (.board .ground .ground))
  let r1 := fold (fun a b => a + b) 1 s1
  ok := (← checkNat
    "  resolve: the graft grows the stage — the row greens, one tick of kid-time"
    r1 want) && ok
  for r in darkRows do
    IO.println
      s!"dark: {r.name} — expects {r.expects.lo}..{r.expects.hi}, awaits {r.awaits}"
  for r in openRows do
    IO.println s!"open: {r.name} — awaits {r.awaits}"
  if ok then
    IO.println
      s!"the lab counter-signs: readings green, {darkRows.length} dark and {openRows.length} open rows holding their names"
    return 0
  else
    IO.eprintln "the lab names the gap"
    return 1
