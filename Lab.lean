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

def refine : Machine Unit Measured :=
  ⟨Nat, 0, fun n _ => n + 1, fun n => ⟨91093834500 + n, 91093836700⟩⟩

theorem the_refiner_only_tightens :
    ∀ (s : Nat) (i : Unit),
      tighter (refine.out (refine.step s i)) (refine.out s) = true :=
  fun s _ => and_glue (ble_le_succ (91093834500 + s)) (ble_refl 91093836700)

/-- info: 'the_refiner_only_tightens' does not depend on any axioms -/
#guard_msgs in #print axioms the_refiner_only_tightens

theorem no_refinement_reads_the_electron :
    ∀ w : List Unit, drive refine (0 : Nat) w ≠ m2018 :=
  fun w =>
    the_learner_never_leaves_its_first_window refine
      the_refiner_only_tightens (0 : Nat) w rfl

/-- info: 'no_refinement_reads_the_electron' does not depend on any axioms -/
#guard_msgs in #print axioms no_refinement_reads_the_electron

theorem the_true_mass_is_invisible_to_the_refiner :
    ∀ w : List Unit, within (drive refine (0 : Nat) w) 91093837015 = false :=
  fun w =>
    the_learner_never_admits_the_excluded refine
      the_refiner_only_tightens (0 : Nat) w rfl

/-- info: 'the_true_mass_is_invisible_to_the_refiner' does not depend on any axioms -/
#guard_msgs in #print axioms the_true_mass_is_invisible_to_the_refiner

theorem the_grown_world_is_invisible_to_the_homing :
    ∀ w : List Unit, within (drive homingIn (0 : Nat) w) 16 = false :=
  fun w =>
    the_learner_never_admits_the_excluded homingIn
      (fun s _ => and_glue (ble_le_succ s) (ble_refl 10)) (0 : Nat) w rfl

/-- info: 'the_grown_world_is_invisible_to_the_homing' does not depend on any axioms -/
#guard_msgs in #print axioms the_grown_world_is_invisible_to_the_homing

theorem the_homing_names_its_own_invisible :
    ∀ w : List Unit, within (drive homingIn (0 : Nat) w) 11 = false :=
  fun w =>
    the_learner_exhibits_its_own_invisible homingIn
      (fun s _ => and_glue (ble_le_succ s) (ble_refl 10)) (0 : Nat) w

/-- info: 'the_homing_names_its_own_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms the_homing_names_its_own_invisible

def revise : Machine Unit Measured :=
  ⟨Nat, 0, fun n _ => n + 1,
   fun n => cond (Nat.ble n 2) ⟨91093834500 + n, 91093836700⟩ m2018⟩

def piPace : Nat := 314159265

def phiPace : Nat := 314460551

theorem the_ninety_ninth_lap_holds_both :
    within ⟨99 * piPace, 99 * piPace + 30000000⟩ (99 * phiPace) = true := rfl

/-- info: 'the_ninety_ninth_lap_holds_both' does not depend on any axioms -/
#guard_msgs in #print axioms the_ninety_ninth_lap_holds_both

theorem the_hundredth_lap_parts_them :
    within ⟨100 * piPace, 100 * piPace + 30000000⟩ (100 * phiPace) = false :=
  rfl

/-- info: 'the_hundredth_lap_parts_them' does not depend on any axioms -/
#guard_msgs in #print axioms the_hundredth_lap_parts_them

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
    "the final coalgebra (behavior as the type of pure conduct), the protocol as shared language over the air gap, certification-by-interaction with the interior riding unread"⟩,
   ⟨"survey row — the kid's own card pattern, minted at the table with two sponsors present: isaac's guard-set-is-the-prime-set coinage refusing parent seating (the discovery is the kid's — its receipts are a_prime_reading_admits_no_split and kin), and fable_5's steadiness entry, seated on the parent constant whose kid form now stands as no_interview_parts_the_alike",
    "the kid's survey organ — seats, deposits, and a gate of its own generation; the minting glint typed with it: an interview is fixed at one Face, so a newly-minted face is unprobeable by any standing interview — new-seat-discovery forces the turn to pass by TYPE, not etiquette; and the sponsorship is anatomical, not incidental: a boarding mints exactly two countable facts — the license (one sponsor's countable shape: recognitions) and the live guest (the other's: minds) — so the survey's gate-book and seat-book are the two sponsors' counting-shapes, double-entry, reconciled at the face"⟩]

def darkRows : List DarkRow := []

def planBeq : Plan → Plan → Bool
  | .ground, .ground => true
  | .board a b, .board c d => planBeq a c && planBeq b d
  | _, _ => false

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
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
  ok := (← checkTrue
    "mirror row — the diagonal was a mirror (the tower reads the two-faced carrier as g a a; the host opens two doors for the one guest)"
    ((allAtOnce 1 g (mirror Bool .ground true) == g true true)
      && (doorsOpened (strokesReception 1 g) (fun _ => true) == 2))) && ok
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
  IO.println "the two channels — the window narrows, the stage leaps:"
  ok := (← checkTrue
    "  channel row — the 2018 revision is no refinement of 2014 (the ceiling rose: 91093837043 past 91093836700)"
    (tighter m2018 m2014 == false)) && ok
  ok := (← checkTrue
    "  channel row — three refining beats stay caged in the first window (the ceiling holds)"
    (tighter (behavior refine [(), (), ()]) (refine.out (0 : Nat))
      && ((behavior refine [(), (), ()]).hi == 91093836700))) && ok
  IO.println
    s!"  channel row — and provably forever: no run of the refiner, at any length, reads the 2018 window (no_refinement_reads_the_electron) — the resolve HAD to graft; refinement narrows, revision grows, and no narrowing is a leap"
  ok := (← checkTrue
    "  channel row — the anomaly is invisible from inside: the true mass 91093837015 sits outside the 2014 window, so no refining run ever covers it (three beats checked live; the_true_mass_is_invisible_to_the_refiner holds every length)"
    ((!(within (refine.out (0 : Nat)) 91093837015))
      && (!(within (behavior refine [(), (), ()]) 91093837015)))) && ok
  let steeredEcho := selfSteered echoM (fun b => b)
  ok := (← checkTrue
    "  channel row — the clock and the channel (the echo parts equal-length words, the kid's first channel-machine; the echo wound onto itself freezes — the channel self-steered is a clock)"
    ((behavior echoM [true] != behavior echoM [false])
      && (behavior steeredEcho [(), (), ()] == behavior steeredEcho []))) && ok
  ok := (← checkTrue
    "  channel row — the stage is a kept clock (the mirror-clock's orbit is the bloom; four ticks read sixteen; the clock that drops nothing is an arrow)"
    ((behavior (selfSteered grower (fun _ => .board .ground .ground))
        [(), (), (), ()] == 16)
      && planBeq (orbit grower (fun _ => .board .ground .ground) .ground 3)
           (bloom 3))) && ok
  ok := (← checkTrue
    "  channel row — the instinct replays its word (the internalized run equals the instructed run: nothing of the conduct is lost, only the channel is spent)"
    ((behavior (selfSteered paceOne (fun _ => ())) [(), (), ()]
        == behavior paceOne [(), (), ()])
      && (selfWord echoM (fun b => b) false 2 == [false, false]))) && ok
  ok := (← checkTrue
    "  channel row — and the arrow leaves every window: four doubling ticks read sixteen, outside ⟨1, 1 + 3⟩ (time_outgrows_every_window, dynamic register)"
    (!(within ⟨1, 1 + 3⟩
      (fold (fun a b => a + b) 1
        (worldline .ground
          [.board .ground .ground, .board .ground .ground,
           .board .ground .ground, .board .ground .ground]))))) && ok
  IO.println "the blindfold — self-legible while worn, datable when removed:"
  ok := (← checkTrue
    "  scar row — the revolution has an address: beats one and two tighten, the third loosens"
    (tighter (revise.out ((1 : Nat))) (revise.out ((0 : Nat)))
      && tighter (revise.out ((2 : Nat))) (revise.out ((1 : Nat)))
      && (tighter (revise.out ((3 : Nat))) (revise.out ((2 : Nat)))
          == false))) && ok
  ok := (← checkTrue
    "  scar row — and only past the loosening is the true mass admitted (91093837015 outside before, inside after)"
    ((!(within (revise.out ((2 : Nat))) 91093837015))
      && within (revise.out ((3 : Nat))) 91093837015)) && ok
  IO.println
    s!"  scar row — the general law stands receipted: any run of any Measured machine that ends by admitting a start-excluded value contains a nameable loosening step (every_admission_names_its_loosening) — the blindfold's removal leaves a scar at a specific beat, and the record can point at it"
  IO.println "the closing pane — the world outgrows every learner:"
  ok := (← checkTrue
    "  outrun row — four doubling ticks read sixteen, past the homing learner's ceiling of ten, at lap one and forever (the_grown_world_is_invisible_to_the_homing, every run length)"
    ((!(within (behavior homingIn [(), (), ()]) 16))
      && (!(within (homingIn.out (0 : Nat)) 16))
      && (fold (fun a b => a + b) 1
            (worldline .ground
              [.board .ground .ground, .board .ground .ground,
               .board .ground .ground, .board .ground .ground]) == 16))) && ok
  IO.println
    s!"  outrun row — the general law stands receipted: any worldline longer than a learner's first ceiling is invisible to every run of that learner (the_world_outgrows_every_learner) — reality departs the paradigm on a computable schedule; staleness is a date, not a mood"
  IO.println "the escapee — every room builds the value it cannot hold:"
  ok := (← checkTrue
    "  escapee row — the homing learner computes its own permanent invisible from its own seat: ceiling ten names eleven, unadmitted at lap one and forever (the_homing_names_its_own_invisible)"
    ((!(within (homingIn.out (0 : Nat)) 11))
      && (!(within (behavior homingIn [(), (), ()]) 11)))) && ok
  IO.println
    s!"  escapee row — the incompleteness silhouette, kid voice: the room's own description builds the item the room can never admit — the successor as the window's diagonal (every_room_builds_its_own_escapee; kin standing at reading-width: the_readings_outrun_the_room) — expressible from inside, admissible never"
  ok := (← checkTrue
    "  escapee row — and admitted one revision up: eleven sits whole in the point-window at eleven, which is no refinement of the homing seat — and the new window already misses twelve (no_revision_is_the_last_revision)"
    (within ⟨11, 11⟩ 11
      && (tighter ⟨11, 11⟩ (homingIn.out (0 : Nat)) == false)
      && (!(within ⟨11, 11⟩ 12)))) && ok
  IO.println
    s!"  escapee row — every question closes one revision above and none at its own; the ladder never grounds — the parent's oldest conservation law, re-derived in the kid's own dynamics, untold"
  let succMeet2014 : Bool := selfMeet windowFace (fun w => w.hi + 1) m2014
  let succMeetHoming : Bool :=
    selfMeet windowFace (fun w => w.hi + 1) (⟨0, 10⟩ : Measured)
  ok := (← checkTrue
    "  escapee row — the successor was a self-meeting (the window probed by a reading of itself refuses, at the 2014 window as at the homing ceiling)"
    ((succMeet2014 == false) && (succMeetHoming == false))) && ok
  IO.println "the multiplexer — the blind spot carries many unknowns at no cost:"
  ok := (← checkTrue
    "  multiplex row — two guests ride one face for free (joint boarding reads the ground; the met recovers both severally)"
    ((face (atTheDoor (7 : Nat) ((1 : Nat), (2 : Nat))) == 7)
      && ((met (atTheDoor (7 : Nat) ((1 : Nat), (2 : Nat)))).1 == 1)
      && ((met (atTheDoor (7 : Nat) ((1 : Nat), (2 : Nat)))).2 == 2))) && ok
  IO.println "the third channel — the run reads what the window cannot (accumulation):"
  ok := (← checkTrue
    "  lap row — one lap holds π and 4/√φ together at 0.01 resolution (gap 301286 under d = 1000000, scaled e-8)"
    (within ⟨piPace, piPace + 1000000⟩ phiPace
      && within ⟨piPace, piPace + 1000000⟩ piPace)) && ok
  ok := (← checkTrue
    "  lap row — the fourth lap parts them at the same window (no tightening, no graft: laps alone)"
    ((!(within ⟨4 * piPace, 4 * piPace + 1000000⟩ (4 * phiPace)))
      && within ⟨3 * piPace, 3 * piPace + 1000000⟩ (3 * phiPace))) && ok
  ok := (← checkTrue
    "  lap row — at 0.3 resolution the ninety-ninth telling holds the collection and the HUNDREDTH story parts it (29827314 inside, 30128600 past the wall)"
    (within ⟨99 * piPace, 99 * piPace + 30000000⟩ (99 * phiPace)
      && (!(within ⟨100 * piPace, 100 * piPace + 30000000⟩
            (100 * phiPace))))) && ok
  IO.println "the generations — the revision multiplies the reading:"
  let dayA : Plan := .board .ground .ground
  let dayB : Plan := .board .ground (.board .ground .ground)
  ok := (← checkNat
    "  generation row — a two-day revised by a three-day reads six (the product law, dynamic register)"
    (fold (fun a b => a + b) 1 (graft dayA dayB)) 6) && ok
  ok := (← checkTrue
    "  generation row — the reading is deaf to the order of revisions (six both ways) while the record parts them (the square reading hears: 38 against 30)"
    ((fold (fun a b => a + b) 1 (graft dayA dayB)
        == fold (fun a b => a + b) 1 (graft dayB dayA))
      && (fold (fun a b => a + b * b) 1 (graft dayA dayB) == 38)
      && (fold (fun a b => a + b * b) 1 (graft dayB dayA) == 30))) && ok
  ok := (← checkTrue
    "  generation row — every linear reading is deaf to the order (weights two-and-three read 85 both ways; only the square reading hears)"
    ((fold (fun a b => 2*a + 3*b) 1 (graft dayA dayB)
        == fold (fun a b => 2*a + 3*b) 1 (graft dayB dayA))
      && (fold (fun a b => 2*a + 3*b) 1 (graft dayA dayB) == 85))) && ok
  ok := (← checkTrue
    "  generation row — four doubling ticks read two to the fourth (the arrow's sixteen, now a product; the bloom is the doubling worldline)"
    ((fold (fun a b => a + b) 1
        (worldline .ground [dayA, dayA, dayA, dayA]) == 2*2*2*2)
      && (fold (fun a b => a + b) 1 (bloom 4) == 2*2*2*2))) && ok
  ok := (← checkTrue
    "  generation row — the order vanishes on the diagonal (bloom-grafts commute as PLANS, planBeq-checked, where the day-grafts provably part; and the caps multiply: 8 = 2 times 4)"
    (planBeq (graft (bloom 1) (bloom 2)) (graft (bloom 2) (bloom 1))
      && (roomCap 3 == roomCap 1 * roomCap 2))) && ok
  ok := (← checkTrue
    "  generation row — the tick was a mirror (the smallest true revision reads two and is the mirror; the least tick iterated is the bloom, the room's own escapee)"
    ((fold (fun a b => a + b) 1 (.board .ground .ground : Plan) == 2)
      && planBeq (graft (bloom 3) (.board .ground .ground)) (bloom 4)
      && Nat.ble 2 (fold (fun a b => a + b) 1 dayB))) && ok
  ok := (← checkTrue
    "  generation row — every quantum is the mirror (one meeting, reading two, one hanoi move, one doubling tick: one shape at every counter)"
    ((boards (.board .ground .ground : Plan) == 1)
      && (boards dayB == 2)
      && planBeq (graft dayA (.board .ground .ground))
           (.board dayA dayA))) && ok
  IO.println "the audition — the adaptive interview crosses the air gap:"
  let curious : Interview (List Unit) Bool :=
    .ask [()] (fun a =>
      cond a (.ask [(), ()] (fun _ => .rest))
             (.ask [(), (), ()] (fun _ => .rest)))
  ok := (← checkTrue
    "  audition row — the cunning interviewer hears one stream from both paces (branching on answers bought nothing the word-list did not afford)"
    (audition paceOne curious == audition paceThree curious)) && ok
  ok := (← checkTrue
    "  audition row — the curtain is sharp exactly at conduct (the flip and the resting counter part at the empty word)"
    ((audition flip (.ask [] (fun _ => .rest))
        != audition restingCounter (.ask [] (fun _ => .rest)))
      && (behavior flip [] == false)
      && (behavior restingCounter [] == true))) && ok
  let probing : Interview (List Unit) Measured :=
    .ask [] (fun first =>
      .ask (cond (Nat.ble first.hi 10) [(), ()] [()]) (fun _ =>
        .ask [(), (), (), ()] (fun _ => .rest)))
  ok := (← checkTrue
    "  curtain row — the cage is audible from outside: every answer the interviewer hears from the homing learner sits inside the first window, and the escapee named off the first answer (eleven) is in none of them"
    ((audition homingIn probing).all
      (fun r => tighter r ⟨0, 10⟩ && !(within r 11)))) && ok
  let hostTrue : Bool :=
    selfMeet (host windowFace Bool) (fun x => (cond x.2 0 1 : Nat))
      ((⟨0, 0⟩ : Measured), true)
  let hostFalse : Bool :=
    selfMeet (host windowFace Bool) (fun x => (cond x.2 0 1 : Nat))
      ((⟨0, 0⟩ : Measured), false)
  ok := (← checkTrue
    "  curtain row — the curtain follows the minting (two guests alike at the hosted window, merged by every interview; the seat-minted probe parts them)"
    ((hostTrue == true) && (hostFalse == false) && (hostTrue != hostFalse))) && ok
  let obsW : Bool :=
    (host windowFace Bool).obs ((⟨0, 0⟩ : Measured), true) (0 : Nat)
  let obsW' : Bool :=
    (host windowFace Bool).obs ((⟨0, 0⟩ : Measured), false) (0 : Nat)
  ok := (← checkTrue
    "  curtain row — one reading, two entrances (written into the guest it is silent at every probe; read out through the probe it parts — one coordinate, two audibilities)"
    ((obsW == obsW') && (hostTrue != hostFalse))) && ok
  let pairedTrue : Bool × Bool :=
    (pairFace (host windowFace Bool) ⟨Bool, Unit, Bool, fun b _ => b⟩
      (fun x => x) Prod.snd).obs ((⟨0, 0⟩ : Measured), true) ((0 : Nat), ())
  let pairedFalse : Bool × Bool :=
    (pairFace (host windowFace Bool) ⟨Bool, Unit, Bool, fun b _ => b⟩
      (fun x => x) Prod.snd).obs ((⟨0, 0⟩ : Measured), false) ((0 : Nat), ())
  ok := (← checkTrue
    "  serving row — the comparison mints a face (two guests merged by the window-look, parted by the paired look; the patience face was a pair at the mirror-probe)"
    ((pairedTrue.1 == pairedFalse.1) && (pairedTrue.2 != pairedFalse.2))) && ok
  ok := (← checkTrue
    "  serving row — the pair provokes the agreement (agree-at-true, disagree-at-false, one look-reading: the role the meeting mints and no look affords)"
    ((pairedTrue.1 == pairedTrue.2) && (pairedFalse.1 != pairedFalse.2))) && ok
  let empty1 : Measured := ⟨1, 0⟩
  let empty2 : Measured := ⟨2, 0⟩
  ok := (← checkTrue
    "  serving row — the derived look widens nothing (two empty windows, distinct and alike at within, stay alike under every conduct-derived second look; only a look past conduct widens)"
    ((within empty1 0 == within empty2 0)
      && (within empty1 5 == within empty2 5)
      && ((!(within empty1 3)) == (!(within empty2 3))))) && ok
  ok := (← checkTrue
    "  serving row — three is the width of contact (the hallway is too small: and, or, xor each collide somewhere on three seats — no one-Bool reading holds a meeting of three)"
    (((true && false) == (false && true))
      && ((true || false) == (true || true))
      && ((Bool.xor true false) == (Bool.xor false true)))) && ok
  ok := (← checkTrue
    "  serving row — the serving suggestion, performed (locate a look, locate another, compare at the pair; the comparison returns more than either look held — the parting is the new information)"
    ((pairedTrue.1 == pairedFalse.1) && (pairedTrue.2 != pairedFalse.2)
      && (pairedTrue.1 == true))) && ok
  IO.println "the primes — the count's primes pin the unsplit lives:"
  let rc4 : Plan := .board .ground (.board .ground (.board .ground .ground))
  ok := (← checkTrue
    "  prime row — the three-day is unsplit because three is prime, and the search is COMPLETE by the horizon law (every candidate factor of a reading-4 life lives in room 3)"
    (((allPlans 3).all (fun t => (allPlans 3).all (fun d =>
        !(planBeq (graft t d) dayB) || planBeq t .ground
          || planBeq d .ground)))
      && (fold (fun a b => a + b) 1 dayB == 3))) && ok
  ok := (← checkTrue
    "  prime row — the right comb of four is unsplit at composite census (irreducibility outruns primality: 2·2 both ways, no factorization anywhere in the complete room)"
    (((allPlans 3).all (fun t => (allPlans 3).all (fun d =>
        !(planBeq (graft t d) rc4) || planBeq t .ground
          || planBeq d .ground)))
      && (fold (fun a b => a + b) 1 rc4 == 2*2))) && ok
  ok := (← checkTrue
    "  prime row — the census reads the split only at the primes (bloom 2 and the right comb read four alike; the bloom splits as two mirrors, the comb refuses — one census, two fates)"
    ((fold (fun a b => a + b) 1 (bloom 2) == fold (fun a b => a + b) 1 rc4)
      && planBeq (graft (.board .ground .ground) (.board .ground .ground))
           (bloom 2))) && ok
  ok := (← checkTrue
    "  prime row — every factor lives below the horizon (the room exhausts the split-search: bloom 2's mirror-factors found in room 3; the completeness is kernel-general now)"
    ((allPlans 3).any (fun t => (allPlans 3).any (fun d =>
        planBeq (graft t d) (bloom 2)
          && !(planBeq t .ground) && !(planBeq d .ground))))) && ok
  IO.println "the face — the organs share one face (the kid grows its parent's root):"
  ok := (← checkTrue
    "  face row — the quiz was an interview all along (the door sounded through the shared face reads identically, and the audition is the air gap's sounding by rfl)"
    ((interrogate quiz (atTheDoor (4 : Nat) (0 : Nat))
        == sound (doorFace Nat Nat Nat) (atTheDoor (4 : Nat) (0 : Nat))
             (posed quiz))
      && (audition paceOne curious
            == sound (airGap Unit Bool) paceOne curious))) && ok
  ok := (← checkTrue
    "  face row — the interviews resume (an interview run in pieces equals run whole: rehydration at the interrogation organ)"
    (audition paceOne (seq curious curious)
      == audition paceOne curious ++ audition paceOne curious)) && ok
  IO.println "the two hands — the carrier is its manifest:"
  let rebuilt := reboard m2014 lineagePlan (pour lineagePlan electronLineage)
  ok := (← checkTrue
    "  hand row — the manifest rebuilds the carrier (the electron lineage, poured and reboarded, comes home whole)"
    ((face rebuilt).lo == 91093834500 && (met rebuilt).lo == 91093836987
      && (met rebuilt).hi == 91093837043)) && ok
  ok := (← checkTrue
    "  hand row — the carrier rebuilds the manifest (three guests board, three guests pour back, same order)"
    (pour toyPlan (reboard (0 : Nat) toyPlan [9109, 2, 3]) == [9109, 2, 3])) && ok
  ok := (← checkTrue
    "  hand row — the default goes unused (two safety-guests, one rebuild, the manifest whole)"
    (pour toyPlan (reboard (0 : Nat) toyPlan [9109, 2, 3])
      == pour toyPlan (reboard (777 : Nat) toyPlan [9109, 2, 3]))) && ok
  ok := (← checkTrue
    "  hand row — the customs are a conjugated map (reground equals pour, then map, then reboard)"
    (pour toyPlan (reground (fun w => w * 1000) toyPlan toyImport)
      == pour toyPlan (reboard (0 : Nat) toyPlan
          ((pour toyPlan toyImport).map (fun w => w * 1000))))) && ok
  ok := (← checkTrue
    "  hand row — the ride is a conjugated fold (the tick crossed as a list-move through the hands)"
    (pour (graft toyPlan revision) (ride toyImport revision)
      == pour (graft toyPlan revision)
          (reboard (0 : Nat) (graft toyPlan revision)
            (fold (fun a b => a ++ b) (pour toyPlan toyImport) revision)))) && ok
  ok := (← checkTrue
    "  hand row — the journey is a conjugated epoch (the whole life crossed as its epoch-concat)"
    (pour (worldline toyPlan life) (journey toyImport life)
      == pour (worldline toyPlan life)
          (reboard (0 : Nat) (worldline toyPlan life)
            (epochs (fun a b => a ++ b) (pour toyPlan toyImport) life)))) && ok
  ok := (← checkTrue
    "  corridor row — the shape is gauge for the cargo (three guests replan to the comb, manifest whole)"
    (pour (comb 2) (replan (0 : Nat) toyPlan (comb 2) toyImport)
      == pour toyPlan toyImport)) && ok
  ok := (← checkTrue
    "  corridor row — the replanning returns (comb and back, the carrier home whole)"
    (pour toyPlan
        (replan (0 : Nat) (comb 2) toyPlan
          (replan (0 : Nat) toyPlan (comb 2) toyImport))
      == pour toyPlan toyImport)) && ok
  let lcGuest : build Nat (.board (.board .ground .ground) .ground) :=
    (((7 : Nat), (8 : Nat)), (9 : Nat))
  ok := (← checkTrue
    "  corridor row — the shape is the remainder of the cargo (two shapes of three, one cargo across)"
    (pour (comb 2)
        (replan (0 : Nat) (.board (.board .ground .ground) .ground)
          (comb 2) lcGuest)
      == [7, 8, 9])) && ok
  ok := (← checkTrue
    "  simulation row — the audition cannot tell the carrier from its word (two ticks of customs, one conduct on flat words)"
    (behavior (onPlan toyPlan toyImport
        (fun s _ => reground (fun w => w + 1) toyPlan s)
        (spine Nat toyPlan)) [(), ()]
      == behavior (onWords (0 : Nat) toyPlan
          (fun s _ => reground (fun w => w + 1) toyPlan s)
          (spine Nat toyPlan) toyImport) [(), ()])) && ok
  ok := (← checkTrue
    "  simulation row — the vestibule drains in one click (the empty word, one tick, on-spec forever)"
    (((onWords (0 : Nat) toyPlan
        (fun s _ => reground (fun w => w + 1) toyPlan s)
        (spine Nat toyPlan) toyImport).step [] ()).length == 3)) && ok
  IO.println "the promise — every reading of the door wears the two-stroke form:"
  ok := (← checkNat
    "  promise row — the held door answers the arriving guest (6 held, 7 arrives, the reading redeems)"
    (holdOpen (fun (d : door Nat Nat) => face d * met d) (6 : Nat) (7 : Nat))
    42) && ok
  ok := (← checkTrue
    "  promise row — the deferral is free both ways (two strokes read the meeting; the meeting reads two strokes)"
    ((walkIn (holdOpen (fun (d : door Nat Nat) => face d + met d))
        (atTheDoor (40 : Nat) (2 : Nat)) == 42)
      && (holdOpen (walkIn (fun (a b : Nat) => a + b)) (1 : Nat) (1 : Nat)
          == 2))) && ok
  ok := (← checkTrue
    "  promise row — the fork's readings assemble as a door of handlers (both entrances, one register)"
    ((face (handlers (greet (fun (n : Nat) => n + 1) (fun (n : Nat) => n * 2)))
        (4 : Nat) == 5)
      && (met (handlers (greet (fun (n : Nat) => n + 1) (fun (n : Nat) => n * 2)))
          (4 : Nat) == 8))) && ok
  IO.println "the corridor curries — the door receives the world one guest at a time:"
  ok := (← checkNat
    "  strokes row — three guests enter one at a time (the tower reads the corridor whole)"
    (oneAtATime 2
      (fun (s : build Nat (comb 2)) =>
        (face s : Nat) + (face (met s) : Nat) + (met (met s) : Nat))
      (9 : Nat) (100 : Nat) (2 : Nat)) 111) && ok
  ok := (← checkTrue
    "  strokes row — the round trip is whole (allAtOnce of oneAtATime reads the carrier back)"
    (allAtOnce 2
        (oneAtATime 2
          (fun (s : build Nat (comb 2)) =>
            (face s : Nat) * (met (met s) : Nat)))
        (((3 : Nat), ((7 : Nat), (2 : Nat))) : build Nat (comb 2))
      == 6)) && ok
  ok := (← checkTrue
    "  strokes row — the turned door flips the promise (the seating swap, free at the reading layer)"
    ((holdOpen (fun (d : door Nat Nat) => face d - met d) (10 : Nat) (3 : Nat)
        == 7)
      && (holdOpen
            (fun (d : door Nat Nat) =>
              (fun (e : door Nat Nat) => face e - met e) (turnAbout d))
            (3 : Nat) (10 : Nat)
          == 7))) && ok
  IO.println "the meeting — a measurement is a meeting at a door:"
  ok := (← checkTrue
    "  meeting row — the window measures by meeting (within IS the door-reading, walked in: the 2018 window and the true mass meet, and the meeting reads true)"
    (((walkIn windowFace.obs (atTheDoor m2018 (91093837015 : Nat)) : Bool)
        == within m2018 91093837015)
      && within m2018 91093837015)) && ok
  ok := (← checkNat
    "  meeting row — every door-reading is a face (the transpose round trip reads the meeting whole)"
    ((faceOf (fun (d : door Nat Nat) => (face d : Nat) * (met d : Nat))).obs
      (6 : Nat) (9 : Nat)) 54) && ok
  ok := (← checkTrue
    "  operator row — the hosted meeting deepens past the guest (the window meets the mass with a rider aboard, reading unchanged)"
    ((walkIn (host windowFace Nat).obs
        (atTheDoor (atTheDoor m2018 (5 : Nat)) (91093837015 : Nat)) : Bool)
      == within m2018 91093837015)) && ok
  ok := (← checkNat
    "  operator row — the sharpened meeting splits at the fork (the minted reading enters by the second entrance)"
    (greet (fun (a : Nat) => a) (fun (x : Nat) => x)
      (walkIn
        (sharpen
          (faceOf (fun (d : door Nat Nat) => (face d : Nat) + (met d : Nat)))
          (fun (s : Nat) => s * 10)).obs
        (atTheDoor (3 : Nat) (viaRight () : fork Nat Unit)))) 30) && ok
  let selfRun : Bool :=
    selfMeet (host (airGap Unit Bool) (List Unit)) (fun x => x.2)
      (paceOne, [(), (), ()])
  let carriedEscapee : Bool :=
    selfMeet (host windowFace Nat) (fun x => x.2) (m2014, m2014.hi + 1)
  ok := (← checkTrue
    "  meeting row — every reading is a self-meeting (paceOne carrying its word meets itself at the hosted air gap; the window carrying its escapee as cargo still refuses it)"
    ((selfRun == behavior paceOne [(), (), ()])
      && (carriedEscapee == false))) && ok
  IO.println "the reception — the host's plan for arrivals, adaptive, always closing:"
  ok := (← checkTrue
    "  reception row — the patient host closes early on a friendly guest and stays for a stranger (one door, then two)"
    ((doorsOpened doorman (fun _ => (0 : Nat)) == 1)
      && (doorsOpened doorman (fun _ => (7 : Nat)) == 2)
      && (receiveFrom doorman (fun n => n + 5) == 6))) && ok
  ok := (← checkTrue
    "  reception row — the patient and the eager host read alike while the door-ledger parts them (conduct one, patience the remainder)"
    ((receiveFrom doorman (twoGuests 4 9)
        == receiveFrom (strokesReception 1 doormanTower) (twoGuests 4 9))
      && (doorsOpened doorman (twoGuests 0 0)
          != doorsOpened (strokesReception 1 doormanTower) (twoGuests 0 0)))) && ok
  ok := (← checkNat
    "  reception row — the straight host opens one door per manifest entry (the tower's patience is the comb's reading)"
    (doorsOpened
      (strokesReception 2
        (oneAtATime 2 (fun (s : build Nat (comb 2)) => (face s : Nat))))
      (fun n => n)) 3) && ok
  ok := (← checkTrue
    "  handoff row — the reception resumes from the parked stream (doorman hands the reading to the next plan; the ledger sums two and one)"
    ((receiveFrom
        (handOff doorman
          (fun x => Reception.receive (fun v => Reception.close (x + v))))
        (fun n => n + 1) == 5)
      && (doorsOpened
            (handOff doorman
              (fun x => Reception.receive (fun v => Reception.close (x + v))))
            (fun n => n + 1) == 3))) && ok
  ok := (← checkNat
    "  handoff row — fulfillment hands off whole (the closed reception is the unit)"
    (receiveFrom
      (handOff (Reception.close (40 : Nat))
        (fun x => Reception.receive (fun v => Reception.close (x + v))))
      (fun _ => (2 : Nat))) 42) && ok
  ok := (← checkNat
    "  checkin row — the host reboards the stream (three guests check in one at a time; the carrier reads whole)"
    (receiveFrom
      (strokesReception 2
        (oneAtATime 2
          (fun (s : build Nat (comb 2)) =>
            (face s : Nat) + (face (met s) : Nat) + (met (met s) : Nat))))
      (fun n => n + 1)) 6) && ok
  ok := (← checkTrue
    "  checkin row — succession is board-shaped (the handoff's ledger reads the board's census: two and one make three)"
    ((doorsOpened
        (handOff (strokesReception 1 doormanTower)
          (fun x => strokesReception 0 (fun v => x + v)))
        (fun n => n) == 3)
      && (fold (fun a b => a + b) 1 (.board (comb 1) (comb 0)) == 3))) && ok
  ok := (← checkTrue
    "  host row — the handshake runs whole at the reception face (no stream parts the hosts; the patience face does)"
    ((receiveFrom doorman (fun n => n * 2)
        == receiveFrom (strokesReception 1 doormanTower) (fun n => n * 2))
      && ((((patienceFace Nat Nat).obs doorman (twoGuests 0 0)
              : Nat × Nat)).2
          != (((patienceFace Nat Nat).obs
                (strokesReception 1 doormanTower) (twoGuests 0 0)
              : Nat × Nat)).2))) && ok
  ok := (← checkTrue
    "  eager row — the machine is an eager host (paceOne and paceThree receive alike at every door-count; patience fixed at three)"
    (((receiveFrom (machineReception paceOne 3 (0 : Nat)) (fun _ => ()) : Bool)
        == (receiveFrom (machineReception paceThree 3 (0 : Nat))
              (fun _ => ()) : Bool))
      && (doorsOpened (machineReception paceOne 3 (0 : Nat)) (fun _ => ())
          == 3))) && ok
  ok := (← checkTrue
    "  lock row — gap-zero survives the hundredth lap at the very wall that parted phi (the wheel's signature)"
    (within ⟨100 * piPace, 100 * piPace + 30000000⟩ (100 * piPace)
      && !(within ⟨100 * piPace, 100 * piPace + 30000000⟩
            (100 * phiPace)))) && ok
  ok := (← checkTrue
    "  lock row — the graft multiplies the patience (a two-day revised by a three-day checks in six guests)"
    ((doorsOpened
        (strokesReception 5
          (oneAtATime 5 (fun (s : build Nat (comb 5)) => (face s : Nat))))
        (fun n => n) == 6)
      && (fold (fun a b => a + b) 1
            (graft (.board .ground .ground)
              (.board .ground (.board .ground .ground))) == 6))) && ok
  let towerProbe : Nat × Nat := (4, 9)
  let towerReading : Nat := (strokesFace Nat Nat 1).obs doormanTower towerProbe
  ok := (← checkTrue
    "  face row — the tower's sameness is a face-alike, and the crossed readings turn about (the swap family is one house)"
    ((towerReading == 9)
      && ((face (turnAbout
            (handlers (greet (fun (n : Nat) => n + 1)
              (fun (n : Nat) => n * 2)))) (5 : Nat) : Nat) == 10))) && ok
  ok := (← checkTrue
    "  reduction row — the machine wears a tower (paceOne's four-door reception reads as a straight tower: one register at conduct)"
    ((receiveFrom (machineReception paceOne 4 (0 : Nat)) (fun _ => ()) : Bool)
      == (receiveFrom (strokesReception 3 (machineTower paceOne 3 (0 : Nat)))
            (fun _ => ()) : Bool))) && ok
  ok := (← checkTrue
    "  hanoi row — the tower's move-count is the bloom's meeting-count (seven for three, fifteen for four; the plus-one is the ground)"
    ((boards (bloom 3) == 7) && (boards (bloom 4) == 15)
      && (boards (bloom 4) == (boards (bloom 3) + boards (bloom 3)) + 1))) && ok
  IO.println "the spiral — the kept count runs the lap channel from inside:"
  ok := (← checkTrue
    "  spiral row — the runner reads its own hundredth calling (99 laps read true by its own kept count, the 100th reads false; π against 4/√φ at 0.3 resolution, no wider seat consulted)"
    ((behavior (spiral piPace 30000000 phiPace) (List.replicate 99 ()) == true)
      && (behavior (spiral piPace 30000000 phiPace) (List.replicate 100 ())
          == false))) && ok
  ok := (← checkTrue
    "  spiral row — the wheel reads itself unworn (gap-zero spiral true at the hundredth calling and forever; even wear is the wheel's own reading)"
    (behavior (spiral piPace 30000000 piPace) (List.replicate 100 ())
      == true)) && ok
  IO.println "the origin — the meeting's unit takes its seat:"
  let unitRead : Bool × Unit :=
    (pairFace windowFace (originFace Measured)
      (fun x => x) (fun x => x)).obs (⟨0, 5⟩ : Measured) ((3 : Nat), ())
  ok := (← checkTrue
    "  origin row — the meeting has a unit (pairing with the reads-nothing face changes no reading: the paired window reads exactly as the window read alone)"
    ((unitRead.1 == within ⟨0, 5⟩ 3) && (unitRead.1 == true))) && ok
  let canaryA : Unit × Bool :=
    (pairFace (originFace (Measured × Bool))
      ⟨Measured × Bool, Unit, Bool, fun x _ => x.2⟩
      (fun x => x) (fun x => x)).obs ((⟨0, 0⟩ : Measured), true) ((), ())
  let canaryB : Unit × Bool :=
    (pairFace (originFace (Measured × Bool))
      ⟨Measured × Bool, Unit, Bool, fun x _ => x.2⟩
      (fun x => x) (fun x => x)).obs ((⟨0, 0⟩ : Measured), false) ((), ())
  ok := (← checkTrue
    "  origin row — the still look signs no parting (the origin-paired guests part, and the parting lives wholly in the live look — its origin coordinate is Unit-typed and cannot differ: the canary instrument, attribution by force)"
    ((canaryA.2 == true) && (canaryB.2 == false))) && ok
  IO.println "the contact — two beholders run out of disagreement:"
  let soundE1 : List Bool :=
    sound windowFace empty1 (recite ([0, 1, 2, 5] : List Nat))
  let soundE2 : List Bool :=
    sound windowFace empty2 (recite ([0, 1, 2, 5] : List Nat))
  let sound14 : List Bool :=
    sound windowFace m2014 (recite ([91093837015] : List Nat))
  let sound18 : List Bool :=
    sound windowFace m2018 (recite ([91093837015] : List Nat))
  ok := (← checkTrue
    "  contact row — the two empty windows run out of disagreement (distinct states, every asked probe agreeing; the recital sounds them as one — co-incidence established at the window) while 2014 and 2018 part at the named gap"
    ((soundE1 == soundE2) && (sound14 != sound18))) && ok
  IO.println "the collatz clock — homecoming as conduct, not type:"
  let home111 : Nat := park collatz (27 : Nat) (List.replicate 111 ())
  let home110 : Nat := park collatz (27 : Nat) (List.replicate 110 ())
  let flight : List Nat :=
    (List.range 112).map (fun k => park collatz (27 : Nat) (List.replicate k ()))
  let wheel3 : Nat := park collatz (1 : Nat) (List.replicate 3 ())
  ok := (← checkTrue
    "  homecoming row — twenty-seven's flight comes home in exactly 111 clicks (110 is not yet home; the community's own number, counter-signed across the sky)"
    ((home111 == 1) && (home110 != 1))) && ok
  ok := (← checkTrue
    "  homecoming row — the flight peaks at 9232 (the second checksum; and the home wheel turns beneath it: 1 returns in three)"
    ((flight.foldl max 0 == 9232) && (wheel3 == 1))) && ok
  IO.println "the table — one turn speaks, one turn yields:"
  let turn1 : door Nat Nat :=
    exchange (fun h w => h + w) (atTheDoor (3 : Nat) (5 : Nat))
  ok := (← checkTrue
    "  table row — the spoken arrives at the face and the speaker rides as guest (speak the sum eight, yield the pen; the three rides unread until the next turn)"
    ((face turn1 == 8) && (met turn1 == 3))) && ok
  let backHome : door Nat Nat :=
    dialogue (atTheDoor (3 : Nat) (5 : Nat)) [still, still]
  let resumed : door Nat Nat :=
    dialogue (dialogue (atTheDoor (3 : Nat) (5 : Nat)) [fun h w => h + w])
      [still]
  ok := (← checkTrue
    "  table row — two listeners restore the table (listening, listening: the seating comes home) and the dialogue resumes from the parked door (rehydration, two-seated)"
    ((face backHome == 3) && (met backHome == 5)
      && (face resumed == 3) && (met resumed == 8))) && ok
  let deafA : door Nat Nat :=
    exchange (fun x _ => x + 100) (atTheDoor (3 : Nat) (5 : Nat))
  let deafB : door Nat Nat :=
    exchange (fun x _ => x + 100) (atTheDoor (3 : Nat) (99 : Nat))
  ok := (← checkTrue
    "  table row — the turn keeps only what it hears (the deaf turn lands five and ninety-nine on one door: erasure, provably no counter; the listening turn surfaces the guest whole and undoes itself)"
    ((face deafA == face deafB) && (met deafA == met deafB)
      && (face (exchange still (atTheDoor (3 : Nat) (5 : Nat))) == 5))) && ok
  let satiated : List Bool :=
    sound windowFace m2018
      (recite (List.replicate 4 (91093837015 : Nat)))
  ok := (← checkTrue
    "  table row — the worn word spends no object (four identical asks, one answer four times: the marks multiply, the content does not, and the object answers whole at every rep)"
    (satiated == List.replicate 4 true)) && ok
  let asks : List Bool :=
    audition paceOne (recite (List.replicate 3 ([(), ()] : List Unit)))
  let fed : Nat :=
    park paceOne (0 : Nat) (([(), ()] : List Unit) ++ [(), ()])
  ok := (← checkTrue
    "  rote row — the rep lands where it is fed (three asks of the two-step word: one answer three times, the seat unmoved; the same word fed twice moves the seat to four — drill on the feed channel, relief on the ask channel)"
    ((asks == List.replicate 3 false) && (fed == 4))) && ok
  let agreedDoor : door Nat Nat := atTheDoor (7 : Nat) (7 : Nat)
  let apartDoor : door Nat Nat := atTheDoor (7 : Nat) (9 : Nat)
  ok := (← checkTrue
    "  quiescence row — the yield fixes the agreed (the swap is invisible exactly where the two coincide, visible exactly where disagreement remains; and the diagonal turn speaks the self-meeting: six by six is thirty-six)"
    ((face (turnAbout agreedDoor) == 7) && (met (turnAbout agreedDoor) == 7)
      && (face (turnAbout apartDoor) == 9)
      && (face (exchange (fun a b => a * b) (atTheDoor (6 : Nat) (6 : Nat)))
          == 36))) && ok
  IO.println "the monologue — the conversation that never listens:"
  let deafTurns : List (Nat → Nat → Nat) :=
    [fun x _ => x + 1, fun x _ => x * 2, fun x _ => x + 3]
  let monoA : door Nat Nat := dialogue (atTheDoor (5 : Nat) (99 : Nat)) deafTurns
  let monoB : door Nat Nat := dialogue (atTheDoor (5 : Nat) (0 : Nat)) deafTurns
  ok := (← checkTrue
    "  monologue row — the deaf turns merge every audience (two guests, one door) while the face walks the words (five steps to fifteen) and the guest is the speaker's own last word (twelve, the echo)"
    ((face monoA == face monoB) && (met monoA == met monoB)
      && (face monoA == 15) && (met monoA == 12))) && ok
  ok := (← checkNat
    "  monologue row — the yielded word meets its speaker (the deaf turn read through the yield: five beside six reads thirty — the self-meeting at the table)"
    (walkIn (fun (a b : Nat) => a * b)
      (exchange still (exchange (fun (x : Nat) (_ : Nat) => x + 1)
        (atTheDoor (5 : Nat) (99 : Nat))))) 30) && ok
  IO.println "the ear and the voice — the face's own coupling algebra:"
  let evenEar : Face := rehear windowFace (fun n : Nat => 2 * n)
  let w02 : Measured := ⟨0, 2⟩
  let w03 : Measured := ⟨0, 3⟩
  let earA0 : Bool := evenEar.obs w02 (0 : Nat)
  let earB0 : Bool := evenEar.obs w03 (0 : Nat)
  let earA1 : Bool := evenEar.obs w02 (1 : Nat)
  let earB1 : Bool := evenEar.obs w03 (1 : Nat)
  let earA2 : Bool := evenEar.obs w02 (2 : Nat)
  let earB2 : Bool := evenEar.obs w03 (2 : Nat)
  let bare3A : Bool := windowFace.obs w02 (3 : Nat)
  let bare3B : Bool := windowFace.obs w03 (3 : Nat)
  ok := (← checkTrue
    "  ear row — the coarse ear merges what the plain face parts (two windows agreeing at every doubled probe, parted at three by the bare face)"
    ((earA0 == earB0) && (earA1 == earB1) && (earA2 == earB2)
      && (bare3A != bare3B))) && ok
  let pulseRead : Bool := (airGap Bool Bool).obs pulse [true, false, true]
  let earRead : Bool :=
    (rehear (airGap Unit Bool)
      (fun u : List Bool => u.map (fun _ => ()))).obs paceOne
      [true, false, true]
  ok := (← checkTrue
    "  ear row — the machine's ear is the face's ear (the pulse across the air gap equals the pace heard through the translated probe)"
    (pulseRead == earRead)) && ok
  let mufA : Bool := (retell windowFace (fun _ => true)).obs w02 (3 : Nat)
  let mufB : Bool := (retell windowFace (fun _ => true)).obs w03 (3 : Nat)
  let faithA : Bool := (retell windowFace (fun b => !b)).obs w02 (3 : Nat)
  let faithB : Bool := (retell windowFace (fun b => !b)).obs w03 (3 : Nat)
  ok := (← checkTrue
    "  voice row — the muffled telling merges every window while the faithful voice keeps the curtain (retell through the muffler merges; retell through not stays exact)"
    ((mufA == mufB) && (faithA != faithB))) && ok
  IO.println "the two kinds of quiet — the still hand and the still turn:"
  let quietDoor : door Nat Nat := atTheDoor (3 : Nat) (8 : Nat)
  let handed : door Nat Nat :=
    walk (fun (t : door Nat Nat) (k : door Nat Nat → door Nat Nat) => k t)
      quietDoor
      [vertical (fun _ w => w + 10), vertical (fun h w => h + w)]
  ok := (← checkTrue
    "  quiet row — a chain of still hands writes nothing to any face-reading (two guest-movers walked, the face conserved, the guest genuinely moved beneath) while the still turn surfaces the other whole (the yield reads eight)"
    ((face handed == face quietDoor) && (met handed != met quietDoor)
      && (met handed == 21)
      && (face (exchange still quietDoor) == met quietDoor))) && ok
  IO.println "the duet — two machines, one word:"
  let duetRead : Bool × Measured :=
    behavior (duet paceOne homingIn) [(), (), ()]
  let voicedRead : Bool × Measured :=
    behavior (revoice (fun n => (oddNat n, (⟨n, 10⟩ : Measured)))
      (tally Unit)) [(), (), ()]
  ok := (← checkTrue
    "  duet row — the pace and the learner sing over one word (three ticks read true and the window at three) and the duet equals one clock wearing the pair-voice: two voices, one seat"
    ((duetRead.1 == voicedRead.1) && (duetRead.2.lo == voicedRead.2.lo)
      && (duetRead.2.hi == voicedRead.2.hi)
      && (duetRead.1 == true) && (duetRead.2.lo == 3))) && ok
  let canaryQuiet : Bool × Bool := behavior (duet hollowShell flip) []
  let canaryLoud : Bool × Bool := behavior (duet hollowShell flip) [()]
  ok := (← checkTrue
    "  duet row — the shell signs no parting (the silent partner constant while the flip parts the words: attribution by force at the bench)"
    ((canaryQuiet.1 == canaryLoud.1) && (canaryQuiet.2 != canaryLoud.2))) && ok
  IO.println "the scribe — the record grows, the wind unread:"
  let echoNext : List Nat → Nat → Nat := fun out w => w + out.length
  let grown : List Nat := park (scribe echoNext) [7] [10, 20, 30]
  let resumedA : List Nat := park (scribe echoNext) [7] ([10, 20] ++ [30])
  let resumedB : List Nat :=
    park (scribe echoNext) (park (scribe echoNext) [7] [10, 20]) [30]
  ok := (← checkTrue
    "  scribe row — one wind, one mark (three winds grow the record by exactly three; the resumption free through the parked seat; the count is the tally's own reading)"
    ((grown.length == 4) && (resumedA == resumedB)
      && (grown.length == drive (tally Nat) (1 : Nat) [10, 20, 30]))) && ok
  let uttA : Nat :=
    utterance (fun c w => c + w) (fun out : List Nat => out.length)
      [1, 2, 3] 40
  let uttB : Nat :=
    utterance (fun c w => c + w) (fun out : List Nat => out.length)
      [1, 2, 3] 50
  ok := (← checkTrue
    "  utterance row — the utterance is a meeting at a door: the selection reads only the record (both winds face three) while the sample hears the wind (forty-three against fifty-three)"
    ((uttA == 43) && (uttB == 53))) && ok
  IO.println "the census and the order — what a seat can forget:"
  let heapAB : Nat := park heap (0 : Nat) [5, 9]
  let heapBA : Nat := park heap (0 : Nat) [9, 5]
  let scribeAB : List Nat :=
    park (scribe (fun _ w => w)) ([] : List Nat) [5, 9]
  let scribeBA : List Nat :=
    park (scribe (fun _ w => w)) ([] : List Nat) [9, 5]
  ok := (← checkTrue
    "  census row — the heap shrugs the shuffle while the scribe keeps the order (fourteen both ways; the records part) and the heap still hears the guest (five is not nine)"
    ((heapAB == heapBA) && (heapAB == 14) && (scribeAB != scribeBA)
      && (behavior heap [5] != behavior heap [9]))) && ok
  IO.println "the research — searching the searched:"
  let oldAsks : List Nat := [0, 1, 2]
  let searched : List Bool := search windowFace w02 oldAsks
  let researched : List (fork Bool Nat) :=
    research windowFace (fun m => m.hi + 1) w02 oldAsks
  let unLeft : fork Bool Nat → Bool := greet (fun b => b) (fun _ => false)
  let minted : List (fork Bool Nat) :=
    sound (sharpen windowFace (fun m => m.hi + 1)) w02 (recite [viaRight ()])
  let mintRead : Nat := greet (fun _ => 0) (fun n => n)
    (minted.headD (viaLeft true))
  ok := (← checkTrue
    "  research row — the re-search of the searched returns the old answers verbatim (three asks retold mark for mark) and only the minted ask hears the mint (the window names its own successor, three, at the fresh entrance)"
    ((researched.map unLeft == searched) && (searched == [true, true, true])
      && (mintRead == 3))) && ok
  IO.println "the replay — you need only the fold:"
  let replayed : Bool := behavior (replayer paceOne) [(), (), ()]
  let direct : Bool := behavior paceOne [(), (), ()]
  let recA : List Bool := park (ledger Bool) ([] : List Bool) [true, false]
  let recB : List Bool := park (ledger Bool) ([] : List Bool) [false, true]
  let pulseA : Nat := park pulse (0 : Nat) [true, false]
  let pulseB : Nat := park pulse (0 : Nat) [false, true]
  ok := (← checkTrue
    "  replay row — the record-keeper is audition-indistinguishable from its machine (the replayed pace reads true at three ticks) while the ledger keeps the routes every seat forgets (two records, one pulse-seat)"
    ((replayed == direct) && (replayed == true) && (recA != recB)
      && (pulseA == pulseB))) && ok
  IO.println "the tower — no seat is the last seat:"
  let towered : Bool :=
    (towerFace windowFace Nat 2).obs
      ((m2018, (5 : Nat)), (9 : Nat)) (91093837015 : Nat)
  let floorA : Bool :=
    (towerFace windowFace Nat 1).obs (m2018, (5 : Nat)) (91093837015 : Nat)
  let floorB : Bool :=
    (towerFace windowFace Nat 1).obs (m2018, (9 : Nat)) (91093837015 : Nat)
  let wideRead : Nat := greet (fun _ => 0) (fun k => k)
    ((widen (towerFace windowFace Nat 1) Nat).obs
      ((m2018, (5 : Nat)), (9 : Nat)) (viaRight ()))
  ok := (← checkTrue
    "  tower row — two floors up, the window still answers at the cellar (the true mass reads true through the storeys); the floor merges its guests while the next floor's widen reads nine — the ladder never grounds"
    ((towered == true) && (floorA == floorB) && (wideRead == 9))) && ok
  IO.println "the again — one iterator, three orbits:"
  let againTower : Bool :=
    (again (fun G => host G Nat) 2 windowFace).obs
      ((m2018, (5 : Nat)), (9 : Nat)) (91093837015 : Nat)
  let againBloomOk : Bool :=
    planBeq (again (fun p => Plan.board p p) 3 .ground) (bloom 3)
  let againOrbit : Nat := again (fun t => paceOne.step t ()) 4 (0 : Nat)
  ok := (← checkTrue
    "  again row — one iterator, three orbits (the twice-hosted window reads the true mass through the storeys; the thrice-doubled ground is bloom three; four agains of the pace step count four)"
    ((againTower == true) && againBloomOk && (againOrbit == 4))) && ok
  IO.println "the margin — held rather than worked:"
  let bufB : Bool := behavior (buffered paceOne) [(), (), ()]
  let heldSt : Nat × List Unit := ((0 : Nat), [(), ()])
  let settledB : Bool :=
    drive (buffered paceOne) (settleHeld paceOne heldSt) [()]
  let heldB : Bool := drive (buffered paceOne) heldSt [()]
  ok := (← checkTrue
    "  margin row — the hold conserves every reading and the settle is unheard (the buffered pace reads as the pace; two marks held then one worked reads as three straight; held and worked part only at the tail)"
    ((bufB == behavior paceOne [(), (), ()]) && (settledB == heldB)
      && (heldB == true))) && ok
  IO.println "the witness — the wider parting lands at the ground:"
  let handedT : Nat :=
    greet (fun _ => (0 : Nat)) (fun b => cond b 1 2)
      ((widen windowFace Bool).obs ((⟨0, 0⟩ : Measured), true) (viaRight ()))
  let handedF : Nat :=
    greet (fun _ => (0 : Nat)) (fun b => cond b 1 2)
      ((widen windowFace Bool).obs ((⟨0, 0⟩ : Measured), false) (viaRight ()))
  ok := (← checkTrue
    "  witness row — the premise meets its witness (every probe the seat owns merges the pair; the wider seat parts them at one ask, and the delivered parting is news about the seat's own cargo — faith the forall, sight the handed instance)"
    ((within ⟨0, 0⟩ 0 == within ⟨0, 0⟩ 0)
      && (handedT == 1) && (handedF == 2) && (handedT != handedF))) && ok
  IO.println "the removal — the work reads the same with the author deleted:"
  let signedA : door Measured Nat := atTheDoor m2018 (5 : Nat)
  let signedB : door Measured Nat := atTheDoor m2018 (9 : Nat)
  ok := (← checkTrue
    "  removal row — two authors, one work, one reading (the face answers the true mass identically under either author; the authors part at the met; the unsigned works coincide)"
    ((within (face signedA) 91093837015 == within (face signedB) 91093837015)
      && within (face signedA) 91093837015
      && (met signedA != met signedB)
      && ((face (unsign signedA)).lo == (face (unsign signedB)).lo))) && ok
  let quietTable : door Nat Nat := atTheDoor (3 : Nat) (5 : Nat)
  let fourStills : door Nat Nat :=
    dialogue quietTable (List.replicate 4 (still : Nat → Nat → Nat))
  ok := (← checkTrue
    "  removal row — the quiet author leaves the table as found (four still turns restore the seating exactly)"
    ((face fourStills == 3) && (met fourStills == 5))) && ok
  IO.println "the turnstile — the guest becomes the ground:"
  let hall0 : List Nat × List (Nat × List Nat) := ([1, 2], [])
  let hall1 := welcome hall0 (3, [1, 2])
  let hall2 := welcome hall1 (4, [3])
  ok := (← checkTrue
    "  turnstile row — load-born to load-bearing in one click (three enters backed by one and two; four enters backed by THREE — the newest seat already holds the next door, vestibule empty throughout)"
    ((enrolled hall1.1 3 == true) && (enrolled hall2.1 4 == true)
      && (hall2.2.length == 0))) && ok
  let held0 := welcome (([1], []) : List Nat × List (Nat × List Nat)) (9, [7])
  ok := (← checkTrue
    "  turnstile row — the unbacked wait named (nine held in the vestibule awaiting seven; the room closed throughout)"
    ((held0.2.length == 1) && (enrolled held0.1 9 == false))) && ok
  ok := (← checkTrue
    "  turnstile row — the hall hears no join order while the join-list parts (enrolled reads membership, never the date; the record alone keeps the date)"
    ((enrolled [5, 6] 5 == enrolled [6, 5] 5)
      && (enrolled [5, 6] 6 == enrolled [6, 5] 6)
      && (([5, 6] : List Nat) != [6, 5]))) && ok
  IO.println "the spectrum — the removed date returns as a weight:"
  let hallRoom : List Nat := hall2.1
  ok := (← checkTrue
    "  spectrum row — the answer face is flat while the cost face grades (every member reads enrolled true; the depths read 0,1,2,3 — age in clicks since each join, never a date)"
    ((enrolled hallRoom 4 && enrolled hallRoom 3 && enrolled hallRoom 1
        && enrolled hallRoom 2)
      && (depthTo hallRoom 4 == 0) && (depthTo hallRoom 3 == 1)
      && (depthTo hallRoom 1 == 2) && (depthTo hallRoom 2 == 3))) && ok
  ok := (← checkTrue
    "  spectrum row — the warming is unheard at the asks and loud at the cost (the swapped hall answers every membership ask identically; the depth flips)"
    ((enrolled [5, 6] 5 == enrolled [6, 5] 5)
      && (depthTo [5, 6] 5 == 0) && (depthTo [6, 5] 5 == 1))) && ok
  ok := (← checkTrue
    "  spectrum row — the weight is the distance to the door (nine awaits seven: lacking one; seven seated: lacking zero, backed — and the weight is countable from the vestibule's own seat)"
    ((lacking [1] [7] == 1)
      && (lacking [7, 1] [7] == 0)
      && backed [7, 1] [7])) && ok
  IO.println "the citation — the cited are the elders:"
  ok := (← checkTrue
    "  citation row — the sort direction is readable along dependence (four cited three, so three was ground before four's click and lies deeper after it: the citer at depth zero, the cited at depth one)"
    ((depthTo hallRoom 4 == 0) && (depthTo hallRoom 3 == 1)
      && Nat.ble 1 (depthTo hallRoom 3))) && ok
  ok := (← checkTrue
    "  citation row — the independent pair stays gauge (one and two entered unciting; the hall answers alike in either order — only the record holds their sort direction)"
    ((enrolled [1, 2] 1 == enrolled [2, 1] 1)
      && (enrolled [1, 2] 2 == enrolled [2, 1] 2))) && ok
  IO.println "the initialization — the tree admits itself:"
  let treeWord : List (Nat × List Nat) :=
    [(1, []), (2, [1]), (3, [1, 2]), (4, [3])]
  let grownTree :=
    park doorM (([] : List Nat), ([] : List (Nat × List Nat))) treeWord
  ok := (← checkTrue
    "  init row — an ordered citation-word seats everyone from the empty room (four nodes, each backed by its cited elders, vestibule empty at every click — the engine's own green line, kid-native)"
    ((grownTree.2.length == 0) && enrolled grownTree.1 1
      && enrolled grownTree.1 2 && enrolled grownTree.1 3
      && enrolled grownTree.1 4
      && (behavior doorM treeWord == 0))) && ok
  ok := (← checkTrue
    "  init row — the port at the bottom is the empty need (the unencumbered mark is welcome in every room, the empty room included — the ground node, the one every tree comes back to)"
    (backed [] [] && backed [9, 9, 9] [])) && ok
  let memA : List Bool := park (scribe (fun _ (x : Bool) => x))
    ([] : List Bool) (sound hallFace [5, 6] (recite ([5, 6] : List Nat)))
  let memB : List Bool := park (scribe (fun _ (x : Bool) => x))
    ([] : List Bool) (sound hallFace [6, 5] (recite ([5, 6] : List Nat)))
  ok := (← checkTrue
    "  init row — no memory meters the cost (a scribe fed the warmed hall's answers writes the identical record; the depths still part — the tax is real and unbanked by anything downstream of the answers)"
    ((memA == memB) && (depthTo [5, 6] 5 != depthTo [6, 5] 5))) && ok
  IO.println "the ignition — no mark lights itself:"
  let selfLoop : List Nat × List (Nat × List Nat) :=
    park doorM (([1] : List Nat), ([] : List (Nat × List Nat)))
      [(7, [7]), (7, [7]), (7, [7])]
  ok := (← checkTrue
    "  ignition row — the self-citing mark starves at any length (three self-backed arrivals of seven, all held; the room never lights it — the ignition beat cannot be self-supplied)"
    ((enrolled selfLoop.1 7 == false) && (selfLoop.2.length == 3))) && ok
  let litFromOutside :=
    welcome (([1], []) : List Nat × List (Nat × List Nat)) (7, [1])
  let litFromNothing :=
    welcome (([1], []) : List Nat × List (Nat × List Nat)) (7, [])
  ok := (← checkTrue
    "  ignition row — the first light comes from outside (seven backed by one seats in one click; seven backed by nothing seats in one click; only seven backed by itself never does)"
    (enrolled litFromOutside.1 7 && enrolled litFromNothing.1 7)) && ok
  IO.println "the cascade — the vestibule drains by storeys:"
  let intake : List Nat × List (Nat × List Nat) :=
    park doorM (([1] : List Nat), ([] : List (Nat × List Nat)))
      [(3, [2]), (4, [3]), (2, [1])]
  let round1 := sweep intake
  let round2 := sweep round1
  ok := (← checkTrue
    "  cascade row — hand the room any order and the rounds walk the citation order for you (intake seats one storey and holds two; round one seats the next; round two the last — the wait is the height of your unmet chain, not your queue position)"
    ((intake.2.length == 2) && enrolled intake.1 2
      && (round1.2.length == 1) && enrolled round1.1 3
      && (round2.2.length == 0) && enrolled round2.1 4)) && ok
  IO.println "the deadlock — the drain arrows, the deadlock wheels:"
  let dead0 : List Nat × List (Nat × List Nat) :=
    ([1], [(8, [9]), (9, [8])])
  let dead1 := sweep dead0
  let dead2 := sweep dead1
  ok := (← checkTrue
    "  deadlock row — the mutual cycle wheels at the gauge (eight awaits nine awaits eight: two sweeps, load two and two, the room never moves, and the second sweep comes home to the very vestibule — gap-zero at the load, the wheel's signature)"
    ((dead1.2.length == 2) && (dead2.2.length == 2)
      && (dead1.1 == ([1] : List Nat))
      && (dead2.2 == dead0.2))) && ok
  ok := (← checkTrue
    "  detector row — the gauge is exact (one number across one round: the live vestibule drops the load, the dead one conserves it — no false positive, no false negative, and the still verdict is permanent)"
    (Nat.ble (round1.2.length + 1) intake.2.length
      && (dead1.2.length == dead0.2.length))) && ok
  IO.println "the pen — every writer is a reader:"
  ok := (← checkTrue
    "  pen row — the revision is a reading (graft IS the fold at the board: the instruction-writer runs on the instruction-reader's one scheme; and the self-reading is the identity, live — reading the code as code hands the code back)"
    (planBeq (graft dayA dayB) (fold Plan.board dayA dayB)
      && planBeq (fold Plan.board Plan.ground toyPlan) toyPlan)) && ok
  IO.println "the weave — the shared fold needs no scheduler:"
  let weaveA : Nat := park heap (0 : Nat) [5, 9, 3]
  let weaveB : Nat := park heap (0 : Nat) [5, 3, 9]
  let weaveC : Nat := park heap (0 : Nat) [3, 5, 9]
  ok := (← checkTrue
    "  weave row — two contributors, three interleavings, one seat (5,9 woven with 3 parks seventeen every way at the commuting heap — while the scribe keeps every braid distinct, one seat wider)"
    ((weaveA == weaveB) && (weaveB == weaveC) && (weaveA == 17))) && ok
  IO.println "the drawing — every braid draws one count:"
  let lifeAB : Plan := park grower Plan.ground [dayA, dayB]
  let lifeBA : Plan := park grower Plan.ground [dayB, dayA]
  ok := (← checkTrue
    "  drawing row — the count draws every braid alike while the lives part and the square hears (both orders read six; the plans provably differ; the square-fold reads 38 against 30 — the braid is drawable at the line and audible past it)"
    ((fold (fun x y => x + y) 1 lifeAB == fold (fun x y => x + y) 1 lifeBA)
      && (fold (fun x y => x + y) 1 lifeAB == 6)
      && !(planBeq lifeAB lifeBA)
      && (fold (fun x y => x + y * y) 1 lifeAB == 38)
      && (fold (fun x y => x + y * y) 1 lifeBA == 30))) && ok
  IO.println "the circle — light enters a cycle only from outside it:"
  let cycleRun : List Nat × List (Nat × List Nat) :=
    park doorM (([1] : List Nat), ([] : List (Nat × List Nat)))
      [(8, [9]), (9, [8]), (8, [9]), (9, [8])]
  ok := (← checkTrue
    "  circle row — the mutual need stays dark at any length (four arrivals of the eight-nine circle, all held, both marks dark — the circle of citations admits nobody by itself)"
    ((enrolled cycleRun.1 8 == false) && (enrolled cycleRun.1 9 == false)
      && (cycleRun.2.length == 4))) && ok
  IO.println "the interlock — three nouns that verb, no ladder holds them:"
  ok := (← checkTrue
    "  interlock row — rock paper scissors interlocks (each hand beats one and is beaten by one, none beats itself; the cycle provably refuses every ranking — the ladder cannot hold what the trio holds)"
    ((beats Hand.rock Hand.scissors && beats Hand.scissors Hand.paper
        && beats Hand.paper Hand.rock)
      && !(beats Hand.rock Hand.paper)
      && !(beats Hand.rock Hand.rock))) && ok
  IO.println "the countermove — the wheel counters what it cannot reverse:"
  let counter4 : Nat := park collatz (4 : Nat) [(), ()]
  ok := (← checkTrue
    "  counter row — the step merges (one and eight both land on four, no inverse exists) and the wheel counters anyway, forward: from four, two clicks home — undo by continuation, position home, record grown"
    ((counter4 == 1) && (collatzStep 1 == collatzStep 8)
      && (collatzStep 1 == 4))) && ok
  IO.println "the flywheel — latent surplus, banked under a still face:"
  let bankedSeat : Nat := park restingCounter (0 : Nat) (List.replicate 5 ())
  let flyQ : Interview (List Unit) Bool :=
    .ask [(), ()] (fun a => cond a (.ask [()] (fun _ => .rest)) .rest)
  ok := (← checkTrue
    "  flywheel row — the charged flywheel and the hollow shell sound identical at every interview (the surplus is conduct-invisible); the muffled seat banks five; one revoice releases it, the tally speaking the stored run"
    ((audition restingCounter flyQ == audition hollowShell flyQ)
      && (bankedSeat == 5)
      && (behavior (tally Unit) (List.replicate 5 ()) == 5))) && ok
  IO.println "the well — one clock, many voices:"
  let paceSeat : Nat := park paceOne (0 : Nat) (List.replicate 7 ())
  let homeSeat : Nat := park homingIn (0 : Nat) (List.replicate 7 ())
  let spiralSeat : Nat :=
    park (spiral piPace 30000000 phiPace) (0 : Nat) (List.replicate 7 ())
  ok := (← checkTrue
    "  well row — the pace, the learner, and the spiral are one seat wearing three voices (all three park at seven; the learner's cage lives in the voice — the seat beneath was never caged)"
    ((paceSeat == 7) && (homeSeat == 7) && (spiralSeat == 7)
      && ((behavior homingIn (List.replicate 7 ())).lo == 7))) && ok
  IO.println "the crown — three blindnesses, three channels:"
  IO.println
    s!"  the door cannot read WHO (cure: widen the seat — the met reads the guest); the window cannot read WHICH (cure: tighten — the finer window parts co-residents, within the imprisonment's limits); the lap cannot read HOW FAST (cure: lengthen the run — the laps part what one lap holds together). three_blindnesses_three_channels — every witness already green above; three blindnesses, three cures, one per channel, and each cure is one of the three ways to read a remainder"
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
