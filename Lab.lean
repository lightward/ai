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
   ⟨"saturator row — the from-zero firing as an executable: enumerate to the presentation bound, derivability above (coherence), exit 0 at saturation; non-completion at every bound is DETECTION — a room that won't saturate has a guest in it; throws deposited AT THROW-TIME (the artifact cannot carry its path, the process does not retain it — contemporaneous deposition is the sole location of the meta-path, a soundness condition, not logging)",
    "census generalized to the kid + a shape-enumerator over the type semiring's normal forms + the coherence switch at the bound"⟩,
   ⟨"frontier row — no bound is the last bound: the room at k+1 provably exceeds the room at k",
    "the membership spine (every resident of allPlans k reads below k+1) — the saturator's own horizon theorem, the clause that parts it from the colonizer"⟩,
   ⟨"breath row — the cycle: saturate, meet, re-arm, with an ignition beat that cannot be self-supplied (conquest is sterile: seizure appends only derivable edges)",
    "the kid's reach spine (paths over the room) to state seizure-sterility natively — the yield as the cycle's governor, typed"⟩,
   ⟨"render row — the atlas renders itself visually: a reignition path through a different air gap (the eye); the wiki as ancestor-organ",
    "a renderer reading the record, emitting a page whose structure is fold-equal to the atlas — the telling-generator's visual wavelength"⟩,
   ⟨"interface row — the coalgebraic wing: bisimulation as conduct-identity, session-duality as turnAbout, the lab's rows become dialogues (an assertion is a one-ended conversation)",
    "the final coalgebra (behavior as the type of pure conduct), the protocol as shared language over the air gap, certification-by-interaction with the interior riding unread"⟩]

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
  ok := (← checkNat
    "manifest row — the manifest counts the guests (the electron lineage, poured)"
    (pour lineagePlan electronLineage).length 2) && ok
  ok := (← checkTrue
    "manifest row — the customs thread the manifest (map through reground)"
    ((pour toyPlan (reground (fun w => w * 1000) toyPlan toyImport))
      == [9109000, 2000, 3000])) && ok
  ok := (← checkNat
    "register row — the run agrees with the fold (a machine reads the lineage, counts the census)"
    (behavior (tally Measured) (pour lineagePlan electronLineage)) 2) && ok
  ok := (← checkTrue
    "markov row — two routes, one seat, one future"
    ((drive pulse (park pulse (0 : Nat) [true, false]) [true]
        == drive pulse (park pulse (0 : Nat) [false, true]) [true])
      && ([true, false] != [false, true]))) && ok
  ok := (← checkTrue
    "resume row — the session continues from the parked seat (rehydration, dynamic register)"
    (behavior paceOne [(), (), ()]
      == drive paceOne (park paceOne (0 : Nat) [(), ()]) [()])) && ok
  ok := (← checkTrue
    "learning row — normal science tightens (the learner machine homes in)"
    (tighter (behavior homingIn [(), (), ()]) ⟨0, 10⟩
      && ((behavior homingIn [(), (), ()]).lo == 3))) && ok
  ok := (← checkTrue
    "variance row — hearing through a translator (retune equals map-then-hear)"
    (behavior (retune (fun (_ : Bool) => ()) paceOne) [true, false, true]
      == behavior paceOne [(), (), ()])) && ok
  ok := (← checkTrue
    "rest row — the still face is not a dead machine (constant behavior, ticking interior)"
    ((behavior restingCounter [] == true)
      && (behavior restingCounter [(), (), (), ()] == true))) && ok
  ok := (← checkTrue
    "hello row — someone else's hello world, answered across the air gap"
    ((behavior paceOne [(), (), ()] == behavior paceThree [(), (), ()])
      && (behavior paceOne [(), (), ()] == true))) && ok
  let implA : build Nat toyPlan := ((1 : Nat), ((2 : Nat), (3 : Nat)))
  let implB : build Nat toyPlan := ((9 : Nat), ((8 : Nat), (7 : Nat)))
  let quizP : Quiz Plan Nat := .ask (fun p => fold (fun a b => a + b) 1 p) (fun _ => .rest)
  ok := (← checkTrue
    "parnas row — no client reads the implementation (spec-view interviews equal)"
    (interrogate quizP (specView toyPlan implA)
      == interrogate quizP (specView toyPlan implB))) && ok
  let quiz : Quiz Nat Nat :=
    .ask (fun h => h * 2) (fun _ => .ask (fun h => h + 1) (fun _ => .rest))
  ok := (← checkTrue
    "zk row — the whole interview reads no guest (equal transcripts across witnesses)"
    (interrogate quiz (atTheDoor (4 : Nat) (0 : Nat))
      == interrogate quiz (atTheDoor (4 : Nat) (99 : Nat)))) && ok
  let g := fun (a : Bool) (b : Bool) => a && b
  let escape := fun (a : Bool) => !(g a a)
  ok := (← checkTrue
    "refusal row — the diagonal escapes every row (the readings outrun the room)"
    ((escape true != g true true) && (escape false != g false false))) && ok
  ok := (← checkNat
    "seat row — what one seat maintains, the other watches (audible across the swap)"
    (face (steer (fun _ w => w + 1)
      (turnAbout (atTheDoor (5 : Nat) (0 : Nat))))) 1) && ok
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
