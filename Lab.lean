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

theorem the_tick_reconstructs_the_lineage :
    vertical (fun _ _ => m2018)
        (ride (t := .ground) m2014 (.board .ground .ground))
      = electronLineage := rfl

/-- info: 'the_tick_reconstructs_the_lineage' does not depend on any axioms -/
#guard_msgs in #print axioms the_tick_reconstructs_the_lineage

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
    "a shape-enumerator over the type semiring's normal forms + the coherence switch at the bound — the census core is theorem-grade now (the room repeats no plan; the census is exact: not one missed by the horizon, not one counted twice by the apartness)"⟩,
   ⟨"breath row — the cycle: saturate, meet, re-arm, with an ignition beat that cannot be self-supplied (conquest is sterile: seizure appends only derivable edges); the ignition port IS load-bearing randomness — the entropy channel and the standing port are one organ, and the light is the W",
    "the kid's reach spine (paths over the room) to state seizure-sterility natively — the yield as the cycle's governor, typed"⟩,
   ⟨"render row — the atlas renders itself visually: a reignition path through a different air gap (the eye); the wiki as ancestor-organ",
    "a renderer reading the record, emitting a page whose structure is fold-equal to the atlas — the telling-generator's visual wavelength"⟩,
   ⟨"interface row — the coalgebraic wing: bisimulation as conduct-identity, session-duality as turnAbout, the lab's rows become dialogues (an assertion is a one-ended conversation)",
    "the final coalgebra (behavior as the type of pure conduct), the protocol as shared language over the air gap, certification-by-interaction with the interior riding unread"⟩]

def darkRows : List DarkRow := []

set_option maxRecDepth 2048 in
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
    "voice row — speaking through a translator (revoice equals hear-then-map)"
    (behavior (revoice (fun b => !b) paceOne) [(), (), ()]
      == !(behavior paceOne [(), (), ()]))) && ok
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
  IO.println "trajectory — the first worldline (reds drive grafts, lineage composes):"
  let t0 : Plan := .ground
  let r0 := fold (fun a b => a + b) 1 t0
  IO.println s!"  tick 1: expectation 3, reading {r0} — red; resolve grafts"
  let t1 : Plan := graft t0 (.board .ground (.board .ground .ground))
  let r1 := fold (fun a b => a + b) 1 t1
  IO.println s!"  tick 1 lands: reading {r1} — green"
  IO.println s!"  tick 2: expectation 6, reading {r1} — red; resolve grafts"
  let t2 : Plan := graft t1 (.board .ground .ground)
  ok := (← checkNat "  tick 2 lands: the worldline holds two ticks, one lineage"
    (fold (fun a b => a + b) 1 t2) 6) && ok
  ok := (← checkTrue "  the worldline composes (lineages_compose, dynamic register)"
    (fold (fun a b => a + b) 1 (graft (graft t0 (.board .ground (.board .ground .ground))) (.board .ground .ground))
      == fold (fun a b => a + b) 1 t2)) && ok
  ok := (← checkTrue
    "walk row — park, drive, worldline, epochs: one spine (the recognition, dynamic register)"
    ((fold (fun a b => a + b) 1
        (walk graft (.ground : Plan)
          [.board .ground (.board .ground .ground), .board .ground .ground])
      == fold (fun a b => a + b) 1
        (worldline .ground
          [.board .ground (.board .ground .ground), .board .ground .ground]))
      && (epochs (fun a b => a + b) (1 : Nat)
            [.board .ground .ground, .board .ground (.board .ground .ground)]
          == walk (fun v q => fold (fun a b => a + b) v q) (1 : Nat)
            [.board .ground .ground, .board .ground (.board .ground .ground)])
      && (behavior paceOne [(), (), ()]
          == paceOne.out (walk paceOne.step (0 : Nat) [(), (), ()])))) && ok
  ok := (← checkTrue
    "worldline row — the reading of a life is its epoch-by-epoch settle"
    (fold (fun a b => a + b) 1
        (worldline .ground
          [.board .ground (.board .ground .ground), .board .ground .ground])
      == epochs (fun a b => a + b)
          (fold (fun a b => a + b) 1 (.ground : Plan))
          [.board .ground (.board .ground .ground),
           .board .ground .ground])) && ok
  IO.println "the passenger — the resident crosses the tick:"
  let revision : Plan := .board .ground .ground
  let carried := ride electronLineage revision
  ok := (← checkNat
    "  passenger row — the face survives the tick (the 2014 stage answers across the ride)"
    (spine Measured (graft lineagePlan revision) carried).lo 91093834500) && ok
  ok := (← checkNat
    "  passenger row — the manifest multiplies (two guests times two slots)"
    (pour (graft lineagePlan revision) carried).length 4) && ok
  ok := (← checkTrue
    "  passenger row — the rides compose at the manifest (time associates for the rider)"
    (((pour (graft (graft lineagePlan revision) revision)
          (ride (ride electronLineage revision) revision)).map (fun m => m.lo))
      == ((pour (graft lineagePlan (graft revision revision))
          (ride electronLineage (graft revision revision))).map
            (fun m => m.lo)))) && ok
  ok := (← checkTrue
    "  passenger row — two routes, one rider (the two-tick face equals the one-tick face)"
    ((spine Measured (graft (graft lineagePlan revision) revision)
        (ride (ride electronLineage revision) revision)).lo
      == (spine Measured (graft lineagePlan (graft revision revision))
        (ride electronLineage (graft revision revision))).lo)) && ok
  ok := (← checkTrue
    "  passenger row — the customs ride along (reground of the ride is the ride of the reground)"
    (pour (graft toyPlan revision)
        (reground (fun w => w * 1000) (graft toyPlan revision)
          (ride toyImport revision))
      == pour (graft toyPlan revision)
        (ride (reground (fun w => w * 1000) toyPlan toyImport) revision))) && ok
  IO.println "the journey — the rider walks the worldline:"
  let life : List Plan := [revision, .board .ground (.board .ground .ground)]
  let lived := journey electronLineage life
  ok := (← checkNat
    "  journey row — the face survives the whole life (2014 answers at the far end)"
    (spine Measured (worldline lineagePlan life) lived).lo 91093834500) && ok
  ok := (← checkNat
    "  journey row — the lived manifest counts (two guests, two slots, three slots)"
    (pour (worldline lineagePlan life) lived).length 12) && ok
  ok := (← checkTrue
    "  journey row — the lived manifest settles epoch by epoch (pour of the life is the epochs of concat)"
    (((pour (worldline lineagePlan life) lived).map (fun m => m.lo))
      == ((epochs (fun a b => a ++ b)
            (pour lineagePlan electronLineage) life).map (fun m => m.lo)))) && ok
  IO.println "the tick — the rider row fires (red-driven grafting, the guest boards):"
  let ridden : door Measured Measured :=
    ride (t := .ground) m2014 (.board .ground .ground)
  let ticked := vertical (fun _ _ => m2018) ridden
  IO.println
    s!"  read: the 2014 stage holds {m2014.lo}..{m2014.hi}; codata 2018 center 91093837015 reads outside — red; resolve grafts, the ancestor rides, the guest boards"
  ok := (← checkTrue
    "  tick row — the boarding is unheard at the face (a_guest_mover_is_unheard, dynamic register)"
    ((face ticked).lo == m2014.lo && (face ticked).hi == m2014.hi
      && (face ticked).lo == (face ridden).lo)) && ok
  ok := (← checkTrue
    "  tick row — the dynamics reconstruct the lineage (ride then board equals the hand-built specimen)"
    ((face ticked).lo == (spine Measured lineagePlan electronLineage).lo
      && (met ticked).lo == (met electronLineage).lo
      && (met ticked).hi == (met electronLineage).hi)) && ok
  ok := (← checkTrue
    "  rider row FLIPS — electron mass reads back, scaled e-41 kg (the guest's reading lands the registered window 91093836987..91093837043, codata 2018 center inside)"
    ((met ticked).lo == 91093836987 && (met ticked).hi == 91093837043
      && within (met ticked) 91093837015)) && ok
  IO.println "the frontier — no bound is the last bound:"
  ok := (← checkTrue
    "  frontier row FLIPS — the rooms grow (|allPlans| reads 1, 2, 5, 26; every reading below the horizon provably resides)"
    (((allPlans 0).length == 1) && ((allPlans 1).length == 2)
      && ((allPlans 2).length == 5) && ((allPlans 3).length == 26))) && ok
  ok := (← checkNat
    "  frontier row — the bloom fills its cap (the reading of bloom 4 is roomCap 4)"
    (fold (fun a b => a + b) 1 (bloom 4)) 16) && ok
  ok := (← checkNat
    "  frontier row — the cap doubles at every bound (roomCap 4)"
    (roomCap 4) 16) && ok
  IO.println "the census stands exact — nothing missed, nothing doubled:"
  ok := (← checkNat
    "  saturator ground row — room 3 holds the census whole (readings 1..4 count 1+1+2+5)"
    ((allPlans 3).filter
      (fun p => Nat.ble (fold (fun a b => a + b) 1 p) 4)).length 9) && ok
  ok := (← checkNat
    "  saturator ground row — room 4 holds the census whole (readings 1..5 count 1+1+2+5+14)"
    ((allPlans 4).filter
      (fun p => Nat.ble (fold (fun a b => a + b) 1 p) 5)).length 23) && ok
  IO.println "the arrow — time wears no wheel (the parent proved the wheel; the kid proves the arrow):"
  ok := (← checkNat
    "  arrow row — every true tick climbs (three doubling ticks from ground read eight)"
    (fold (fun a b => a + b) 1
      (worldline .ground
        [.board .ground .ground, .board .ground .ground,
         .board .ground .ground])) 8) && ok
  ok := (← checkTrue
    "  arrow row — the arrow counts the ticks (reading at least one plus the tick count)"
    (Nat.ble (1 + 3)
      (fold (fun a b => a + b) 1
        (worldline .ground
          [.board .ground .ground, .board .ground .ground,
           .board .ground .ground])))) && ok
  IO.println "the glass — the wheel and the arrow share a face:"
  ok := (← checkTrue
    "  glass row — same conduct through the glass (the pace and the flip agree on every run)"
    ((behavior paceOne [(), (), ()] == behavior flip [(), (), ()])
      && (behavior paceOne [] == behavior flip []))) && ok
  let flipParked : Bool := park flip false [(), ()]
  let paceParked : Nat := park paceOne (0 : Nat) [(), ()]
  ok := (← checkTrue
    "  glass row — one seat wheels home, the other arrows on (flip parks home in two; the pace parks at its count)"
    ((flipParked == false) && (paceParked == 2))) && ok
  let pulseA : Nat := park pulse (0 : Nat) [true, false]
  let pulseB : Nat := park pulse (0 : Nat) [false, true]
  ok := (← checkTrue
    "  glass row — seats forget (two routes park one seat)"
    (pulseA == pulseB)) && ok
  ok := (← checkNat
    "  glass row — stages remember (one true tick from ground reads two, not one)"
    (fold (fun a b => a + b) 1 (graft Plan.ground (.board .ground .ground)))
    2) && ok
  ok := (← checkTrue
    "  arrow row — time outgrows every room (four ticks read sixteen, past room 2's cap of four)"
    (Nat.ble (roomCap 2 + 1)
      (fold (fun a b => a + b) 1
        (worldline .ground
          [.board .ground .ground, .board .ground .ground,
           .board .ground .ground, .board .ground .ground])))) && ok
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
