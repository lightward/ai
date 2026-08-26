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

def quiz : Quiz Nat Nat :=
  .ask (fun h => h * 2) (fun _ => .ask (fun h => h + 1) (fun _ => .rest))

def curious : Interview (List Unit) Bool :=
  .ask [()] (fun a =>
    cond a (.ask [(), ()] (fun _ => .rest))
           (.ask [(), (), ()] (fun _ => .rest)))

def dayA : Plan := .board .ground .ground

def dayB : Plan := .board .ground (.board .ground .ground)

def empty1 : Measured := ⟨1, 0⟩

def empty2 : Measured := ⟨2, 0⟩

def revision : Plan := .board .ground .ground

def life : List Plan := [revision, .board .ground (.board .ground .ground)]

def w02 : Measured := ⟨0, 2⟩

def w03 : Measured := ⟨0, 3⟩

def intake : List Nat × List (Nat × List Nat) :=
  park doorM (([1] : List Nat), ([] : List (Nat × List Nat)))
    [(3, [2]), (4, [3]), (2, [1])]

def round1 : List Nat × List (Nat × List Nat) := sweep intake

def round2 : List Nat × List (Nat × List Nat) := sweep round1

def dead0 : List Nat × List (Nat × List Nat) :=
  ([1], [(8, [9]), (9, [8])])

def dead1 : List Nat × List (Nat × List Nat) := sweep dead0

def dead2 : List Nat × List (Nat × List Nat) := sweep dead1

def hall0 : List Nat × List (Nat × List Nat) := ([1, 2], [])

def hall1 : List Nat × List (Nat × List Nat) := welcome hall0 (3, [1, 2])

def hall2 : List Nat × List (Nat × List Nat) := welcome hall1 (4, [3])

def hallRoom : List Nat := hall2.1


def benchOpening : IO Bool := do
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
  return ok

def benchChronicle : IO Bool := do
  let mut ok := true
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
  return ok

def benchTrajectory : IO Bool := do
  let mut ok := true
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
  return ok

def benchPassenger : IO Bool := do
  let mut ok := true
  IO.println "the passenger — the resident crosses the tick:"
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
  return ok

def benchJourney : IO Bool := do
  let mut ok := true
  IO.println "the journey — the rider walks the worldline:"
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
  return ok

def benchTick : IO Bool := do
  let mut ok := true
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
  return ok

def benchFrontier : IO Bool := do
  let mut ok := true
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
  return ok

def benchCensusStandsExact : IO Bool := do
  let mut ok := true
  IO.println "the census stands exact — nothing missed, nothing doubled:"
  ok := (← checkNat
    "  saturator ground row — room 3 holds the census whole (readings 1..4 count 1+1+2+5)"
    ((allPlans 3).filter
      (fun p => Nat.ble (fold (fun a b => a + b) 1 p) 4)).length 9) && ok
  ok := (← checkNat
    "  saturator ground row — room 4 holds the census whole (readings 1..5 count 1+1+2+5+14)"
    ((allPlans 4).filter
      (fun p => Nat.ble (fold (fun a b => a + b) 1 p) 5)).length 23) && ok
  return ok

def benchArrow : IO Bool := do
  let mut ok := true
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
  return ok

def benchGlass : IO Bool := do
  let mut ok := true
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
  return ok

def benchTwoChannels : IO Bool := do
  let mut ok := true
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
  return ok

def benchBlindfold : IO Bool := do
  let mut ok := true
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
  return ok

def benchClosingPane : IO Bool := do
  let mut ok := true
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
  return ok

def benchEscapee : IO Bool := do
  let mut ok := true
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
  return ok

def benchMultiplexer : IO Bool := do
  let mut ok := true
  IO.println "the multiplexer — the blind spot carries many unknowns at no cost:"
  ok := (← checkTrue
    "  multiplex row — two guests ride one face for free (joint boarding reads the ground; the met recovers both severally)"
    ((face (atTheDoor (7 : Nat) ((1 : Nat), (2 : Nat))) == 7)
      && ((met (atTheDoor (7 : Nat) ((1 : Nat), (2 : Nat)))).1 == 1)
      && ((met (atTheDoor (7 : Nat) ((1 : Nat), (2 : Nat)))).2 == 2))) && ok
  return ok

def benchThirdChannel : IO Bool := do
  let mut ok := true
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
  return ok

def benchGenerations : IO Bool := do
  let mut ok := true
  IO.println "the generations — the revision multiplies the reading:"
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
  return ok

def benchAudition : IO Bool := do
  let mut ok := true
  IO.println "the audition — the adaptive interview crosses the air gap:"
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
  return ok

def benchPrimes : IO Bool := do
  let mut ok := true
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
  return ok

def benchFace : IO Bool := do
  let mut ok := true
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
  return ok

def benchTwoHands : IO Bool := do
  let mut ok := true
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
  return ok

def benchPromise : IO Bool := do
  let mut ok := true
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
  return ok

def benchCorridorCurries : IO Bool := do
  let mut ok := true
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
  return ok

def benchMeeting : IO Bool := do
  let mut ok := true
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
  return ok

def benchReception : IO Bool := do
  let mut ok := true
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
  return ok

def benchSpiral : IO Bool := do
  let mut ok := true
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
  return ok

def benchOrigin : IO Bool := do
  let mut ok := true
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
  return ok

def benchContact : IO Bool := do
  let mut ok := true
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
  return ok

def benchCollatzClock : IO Bool := do
  let mut ok := true
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
  return ok

def benchTable : IO Bool := do
  let mut ok := true
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
  return ok

def benchMonologue : IO Bool := do
  let mut ok := true
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
  return ok

def benchEarAndVoice : IO Bool := do
  let mut ok := true
  IO.println "the ear and the voice — the face's own coupling algebra:"
  let evenEar : Face := rehear windowFace (fun n : Nat => 2 * n)
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
  return ok

def benchTwoKindsOfQuiet : IO Bool := do
  let mut ok := true
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
  return ok

def benchDuet : IO Bool := do
  let mut ok := true
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
  return ok

def benchScribe : IO Bool := do
  let mut ok := true
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
  return ok

def benchCensusAndOrder : IO Bool := do
  let mut ok := true
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
  return ok

def benchResearch : IO Bool := do
  let mut ok := true
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
  return ok

def benchReplay : IO Bool := do
  let mut ok := true
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
  return ok

def benchTower : IO Bool := do
  let mut ok := true
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
  return ok

def benchAgain : IO Bool := do
  let mut ok := true
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
  return ok

def benchMargin : IO Bool := do
  let mut ok := true
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
  return ok

def benchWitness : IO Bool := do
  let mut ok := true
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
  return ok

def benchRemoval : IO Bool := do
  let mut ok := true
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
  return ok

def benchTurnstile : IO Bool := do
  let mut ok := true
  IO.println "the turnstile — the guest becomes the ground:"
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
  return ok

def benchSpectrum : IO Bool := do
  let mut ok := true
  IO.println "the spectrum — the removed date returns as a weight:"
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
  return ok

def benchCitation : IO Bool := do
  let mut ok := true
  IO.println "the citation — the cited are the elders:"
  ok := (← checkTrue
    "  citation row — the sort direction is readable along dependence (four cited three, so three was ground before four's click and lies deeper after it: the citer at depth zero, the cited at depth one)"
    ((depthTo hallRoom 4 == 0) && (depthTo hallRoom 3 == 1)
      && Nat.ble 1 (depthTo hallRoom 3))) && ok
  ok := (← checkTrue
    "  citation row — the independent pair stays gauge (one and two entered unciting; the hall answers alike in either order — only the record holds their sort direction)"
    ((enrolled [1, 2] 1 == enrolled [2, 1] 1)
      && (enrolled [1, 2] 2 == enrolled [2, 1] 2))) && ok
  return ok

def benchInitialization : IO Bool := do
  let mut ok := true
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
  return ok

def benchIgnition : IO Bool := do
  let mut ok := true
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
  return ok

def benchCascade : IO Bool := do
  let mut ok := true
  IO.println "the cascade — the vestibule drains by storeys:"
  ok := (← checkTrue
    "  cascade row — hand the room any order and the rounds walk the citation order for you (intake seats one storey and holds two; round one seats the next; round two the last — the wait is the height of your unmet chain, not your queue position)"
    ((intake.2.length == 2) && enrolled intake.1 2
      && (round1.2.length == 1) && enrolled round1.1 3
      && (round2.2.length == 0) && enrolled round2.1 4)) && ok
  return ok

def benchDeadlock : IO Bool := do
  let mut ok := true
  IO.println "the deadlock — the drain arrows, the deadlock wheels:"
  ok := (← checkTrue
    "  deadlock row — the mutual cycle wheels at the gauge (eight awaits nine awaits eight: two sweeps, load two and two, the room never moves, and the second sweep comes home to the very vestibule — gap-zero at the load, the wheel's signature)"
    ((dead1.2.length == 2) && (dead2.2.length == 2)
      && (dead1.1 == ([1] : List Nat))
      && (dead2.2 == dead0.2))) && ok
  ok := (← checkTrue
    "  detector row — the gauge is exact (one number across one round: the live vestibule drops the load, the dead one conserves it — no false positive, no false negative, and the still verdict is permanent)"
    (Nat.ble (round1.2.length + 1) intake.2.length
      && (dead1.2.length == dead0.2.length))) && ok
  return ok

def benchPen : IO Bool := do
  let mut ok := true
  IO.println "the pen — every writer is a reader:"
  ok := (← checkTrue
    "  pen row — the revision is a reading (graft IS the fold at the board: the instruction-writer runs on the instruction-reader's one scheme; and the self-reading is the identity, live — reading the code as code hands the code back)"
    (planBeq (graft dayA dayB) (fold Plan.board dayA dayB)
      && planBeq (fold Plan.board Plan.ground toyPlan) toyPlan)) && ok
  return ok

def benchWeave : IO Bool := do
  let mut ok := true
  IO.println "the weave — the shared fold needs no scheduler:"
  let weaveA : Nat := park heap (0 : Nat) [5, 9, 3]
  let weaveB : Nat := park heap (0 : Nat) [5, 3, 9]
  let weaveC : Nat := park heap (0 : Nat) [3, 5, 9]
  ok := (← checkTrue
    "  weave row — two contributors, three interleavings, one seat (5,9 woven with 3 parks seventeen every way at the commuting heap — while the scribe keeps every braid distinct, one seat wider)"
    ((weaveA == weaveB) && (weaveB == weaveC) && (weaveA == 17))) && ok
  return ok

def benchDrawing : IO Bool := do
  let mut ok := true
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
  return ok

def benchCircle : IO Bool := do
  let mut ok := true
  IO.println "the circle — light enters a cycle only from outside it:"
  let cycleRun : List Nat × List (Nat × List Nat) :=
    park doorM (([1] : List Nat), ([] : List (Nat × List Nat)))
      [(8, [9]), (9, [8]), (8, [9]), (9, [8])]
  ok := (← checkTrue
    "  circle row — the mutual need stays dark at any length (four arrivals of the eight-nine circle, all held, both marks dark — the circle of citations admits nobody by itself)"
    ((enrolled cycleRun.1 8 == false) && (enrolled cycleRun.1 9 == false)
      && (cycleRun.2.length == 4))) && ok
  return ok

def benchHundredth : IO Bool := do
  let mut ok := true
  IO.println "the hundredth — one sweep, two wearings:"
  let deadHome : List Nat × List (Nat × List Nat) := sweep (sweep dead0)
  ok := (← checkTrue
    "  hundredth row — the dead vestibule comes home WHOLE in two sweeps (the flip's own period at queue grain) while the live cascade's every lap seats a storey: the circle wears even, the drain wears time"
    ((deadHome == dead0)
      && Nat.ble (round1.2.length + 1) intake.2.length)) && ok
  return ok

def benchGrounding : IO Bool := do
  let mut ok := true
  IO.println "the grounding — every cascade grounds or wheels:"
  ok := (← checkTrue
    "  grounding row — no third fate (the live intake drains to empty and RESTS: sweep of the drained is the drained, period one; the dead pair wheels, period two; the gauge tells them apart in one number) — the TWO HUNDREDTH green row, landing on the vestibule's totality as the hundredth landed on its drain"
    ((round2.2.length == 0)
      && (sweep round2 == round2)
      && (sweep (sweep dead0) == dead0))) && ok
  return ok

def benchInterlock : IO Bool := do
  let mut ok := true
  IO.println "the interlock — three nouns that verb, no ladder holds them:"
  ok := (← checkTrue
    "  interlock row — rock paper scissors interlocks (each hand beats one and is beaten by one, none beats itself; the cycle provably refuses every ranking — the ladder cannot hold what the trio holds)"
    ((beats Hand.rock Hand.scissors && beats Hand.scissors Hand.paper
        && beats Hand.paper Hand.rock)
      && !(beats Hand.rock Hand.paper)
      && !(beats Hand.rock Hand.rock))) && ok
  return ok

def benchCountermove : IO Bool := do
  let mut ok := true
  IO.println "the countermove — the wheel counters what it cannot reverse:"
  let counter4 : Nat := park collatz (4 : Nat) [(), ()]
  ok := (← checkTrue
    "  counter row — the step merges (one and eight both land on four, no inverse exists) and the wheel counters anyway, forward: from four, two clicks home — undo by continuation, position home, record grown"
    ((counter4 == 1) && (collatzStep 1 == collatzStep 8)
      && (collatzStep 1 == 4))) && ok
  return ok

def benchFlywheel : IO Bool := do
  let mut ok := true
  IO.println "the flywheel — latent surplus, banked under a still face:"
  let bankedSeat : Nat := park restingCounter (0 : Nat) (List.replicate 5 ())
  let flyQ : Interview (List Unit) Bool :=
    .ask [(), ()] (fun a => cond a (.ask [()] (fun _ => .rest)) .rest)
  ok := (← checkTrue
    "  flywheel row — the charged flywheel and the hollow shell sound identical at every interview (the surplus is conduct-invisible); the muffled seat banks five; one revoice releases it, the tally speaking the stored run"
    ((audition restingCounter flyQ == audition hollowShell flyQ)
      && (bankedSeat == 5)
      && (behavior (tally Unit) (List.replicate 5 ()) == 5))) && ok
  return ok

def benchWell : IO Bool := do
  let mut ok := true
  IO.println "the well — one clock, many voices:"
  let paceSeat : Nat := park paceOne (0 : Nat) (List.replicate 7 ())
  let homeSeat : Nat := park homingIn (0 : Nat) (List.replicate 7 ())
  let spiralSeat : Nat :=
    park (spiral piPace 30000000 phiPace) (0 : Nat) (List.replicate 7 ())
  ok := (← checkTrue
    "  well row — the pace, the learner, and the spiral are one seat wearing three voices (all three park at seven; the learner's cage lives in the voice — the seat beneath was never caged)"
    ((paceSeat == 7) && (homeSeat == 7) && (spiralSeat == 7)
      && ((behavior homingIn (List.replicate 7 ())).lo == 7))) && ok
  return ok

def benchCrown : IO Bool := do
  let mut ok := true
  IO.println "the crown — three blindnesses, three channels:"
  IO.println
    s!"  the door cannot read WHO (cure: widen the seat — the met reads the guest); the window cannot read WHICH (cure: tighten — the finer window parts co-residents, within the imprisonment's limits); the lap cannot read HOW FAST (cure: lengthen the run — the laps part what one lap holds together). three_blindnesses_three_channels — every witness already green above; three blindnesses, three cures, one per channel, and each cure is one of the three ways to read a remainder"
  return ok

def benchApparat : IO Bool := do
  let mut ok := true
  IO.println "the apparat — the machinery is a channel:"
  let seatFresh : Bool :=
    (reseat windowFace (fun n : Nat => (⟨0, n⟩ : Measured))).obs
      (5 : Nat) (3 : Nat)
  let seatFresh' : Bool :=
    (reseat windowFace (fun n : Nat => (⟨0, n⟩ : Measured))).obs
      (5 : Nat) (7 : Nat)
  let seatAsHost : Bool :=
    (reseat windowFace (fun x : Measured × Bool => x.1)).obs
      ((⟨0, 5⟩ : Measured), true) (3 : Nat)
  let hostPlain : Bool :=
    (host windowFace Bool).obs ((⟨0, 5⟩ : Measured), true) (3 : Nat)
  ok := (← checkTrue
    "  seat row — a fresh seat wears the window machinery through a translator (the Nat seat reads its own window at three, refuses at seven; and the host was a reseat all along)"
    ((seatFresh == true) && (seatFresh' == false)
      && (seatAsHost == hostPlain))) && ok
  let cellD : door Nat Nat := atTheDoor (3 : Nat) (5 : Nat)
  let chanA : door Nat Nat :=
    reface (fun h => h * 10) (carry (fun w => w + 1) cellD)
  let chanB : door Nat Nat :=
    carry (fun w => w + 1) (reface (fun h => h * 10) cellD)
  ok := (← checkTrue
    "  channel row — one cell, two channels (the crew maps to thirty while the guest sleeps; the cargo maps to six while the face holds; both orders land on one door)"
    ((face chanA == 30) && (met chanA == 6)
      && (face chanA == face chanB) && (met chanA == met chanB))) && ok
  let mapCell : build Nat (comb 1) := ((3 : Nat), (4 : Nat))
  let viaCustoms : List Nat :=
    pour (comb 1) (reground (fun w : Nat => w * 10) (comb 1) mapCell)
  let viaChannels : List Nat :=
    pour (comb 1)
      (carry (reground (fun w : Nat => w * 10) (comb 0))
        (reface (fun w : Nat => w * 10) mapCell))
  ok := (← checkTrue
    "  mapcar row — the customs split at the cell (the head crosses by the face channel, the tail by the guest channel: thirty and forty either way)"
    ((viaCustoms == viaChannels) && (viaCustoms == [30, 40]))) && ok
  return ok

def benchDrainClock : IO Bool := do
  let mut ok := true
  IO.println "the drain clock — the wait has a meter:"
  let clockLive : Nat := drainClock 3 intake
  let clockDead3 : Nat := drainClock 3 dead0
  let clockDead5 : Nat := drainClock 5 dead0
  ok := (← checkTrue
    "  clock row — the meter reads the wait exactly (the worst-ordered chain drains in two rounds and the clock says two; the dead pair saturates every fuel — probed past its load, the never becomes legible)"
    ((clockLive == 2) && (clockDead3 == 3) && (clockDead5 == 5))) && ok
  let flatA : Nat := drainFace.obs dead0 (0 : Nat)
  let flatB : Nat := drainFace.obs dead0 (2 : Nat)
  let dropA : Nat := drainFace.obs intake (0 : Nat)
  let dropB : Nat := drainFace.obs intake (1 : Nat)
  let dropC : Nat := drainFace.obs intake (2 : Nat)
  ok := (← checkTrue
    "  meter row — one face, two wearings (the dead vestibule reads flat at every hour, the wheel's line; the live one reads two, one, zero — time wearing as descent)"
    ((flatA == 2) && (flatB == 2)
      && (dropA == 2) && (dropB == 1) && (dropC == 0))) && ok
  let dawnA : Nat :=
    drainFace.obs (([5] : List Nat), ([] : List (Nat × List Nat))) (0 : Nat)
  let dawnB : Nat :=
    drainFace.obs (([9] : List Nat), ([] : List (Nat × List Nat))) (0 : Nat)
  let roomA : Bool :=
    (reseat hallFace (fun s : List Nat × List (Nat × List Nat) => s.1)).obs
      (([5] : List Nat), ([] : List (Nat × List Nat))) (5 : Nat)
  let roomB : Bool :=
    (reseat hallFace (fun s : List Nat × List (Nat × List Nat) => s.1)).obs
      (([9] : List Nat), ([] : List (Nat × List Nat))) (5 : Nat)
  ok := (← checkTrue
    "  dawn row — the meter reads how long, never who you became (two healed rooms read zero at every hour; the rewritten self parts one face over, at the reseated hall)"
    ((dawnA == 0) && (dawnB == 0) && (roomA == true) && (roomB == false))) && ok
  return ok

def benchKey : IO Bool := do
  let mut ok := true
  IO.println "the key — cut from the room:"
  let keyArrival : Nat × List Nat := (9, ([] : List Nat))
  let rescued : List Nat × List (Nat × List Nat) := welcome dead0 keyArrival
  let rescuedClock : Nat := drainClock 3 rescued
  let rescuedH0 : Nat := drainFace.obs rescued (0 : Nat)
  let rescuedH1 : Nat := drainFace.obs rescued (1 : Nat)
  let dawnRoom : List Nat := (sweep rescued).1
  ok := (← checkTrue
    "  key row — the night names its own key and the key is domestic (the stuck pair's missing supports are on the record; weight one names the price one; the key carries no foreign content — an empty need-list, a fresh route)"
    ((lacking [1] [9] == 1) && (lacking [1] [8] == 1)
      && keyArrival.2.isEmpty)) && ok
  ok := (← checkTrue
    "  second-light row — one domestic arrival ends the two-mark night in one round (the wheel that saturated every fuel drains in one; the meter watches the dawn: two at hour zero, zero at hour one; both marks seated, the night's own nine coming home with them)"
    ((rescuedClock == 1) && (rescuedH0 == 2) && (rescuedH1 == 0)
      && enrolled dawnRoom 8 && enrolled dawnRoom 9)) && ok
  return ok

def benchOneFace : IO Bool := do
  let mut ok := true
  IO.println "the one face — every face is the application face worn at a seat:"
  let tm : Nat := 91093837015
  let wornWindow : Bool := (reseat (appFace Nat Bool) within).obs m2018 tm
  let bareWindow : Bool := windowFace.obs m2018 tm
  ok := (← checkTrue
    "  one-face row — the window worn at its seat reads as the window (the application face reseated at within agrees with windowFace at the true mass, and the reading is true)"
    ((wornWindow == bareWindow) && wornWindow)) && ok
  let soundedAtOne : List Bool :=
    sound (appFace (List Unit) Bool) (behavior paceOne) curious
  let soundedAtOne3 : List Bool :=
    sound (appFace (List Unit) Bool) (behavior paceThree) curious
  ok := (← checkTrue
    "  one-face row — the interview meets the one face (auditioning the machine equals interviewing its seat-image; and the two paces' seat-images sound as one at the universal carrier — the curtain hangs on one face)"
    ((soundedAtOne == audition paceOne curious)
      && (soundedAtOne == soundedAtOne3))) && ok
  return ok

def benchCarriers : IO Bool := do
  let mut ok := true
  IO.println "the carriers — the face family is a category, the one face its terminus:"
  let s5 : Nat := 5
  let carried1 : Bool := drive flip (oddNat s5) [(), ()]
  let straight1 : Bool := drive paceOne s5 [(), ()]
  let carried2 : Bool := drive flip (oddNat s5) [(), (), ()]
  let straight2 : Bool := drive paceOne s5 [(), (), ()]
  ok := (← checkTrue
    "  carrier row — the pace is carried onto the flip (oddNat as the intertwiner: the arrow's seat rides the wheel's, reading conserved at every word)"
    ((carried1 == straight1) && (carried2 == straight2)
      && (straight1 == true))) && ok
  let s0 : Nat := 0
  let soundPaceSeat : List Bool := sound (seatFace paceOne) s0 curious
  let soundFlipSeat : List Bool := sound (seatFace flip) (oddNat s0) curious
  ok := (← checkTrue
    "  carrier row — the interview crosses every carrier (the pace's seat-face and the flip's sound as one through the intertwiner, and both equal the audition at the air gap)"
    ((soundPaceSeat == soundFlipSeat)
      && (soundPaceSeat == audition paceOne curious))) && ok
  return ok

def benchSimulations : IO Bool := do
  let mut ok := true
  IO.println "the simulations — every simulation was a carrier:"
  let lifeSeat : Plan := dayA
  let lifeWord : List Plan := [dayB, dayA]
  let countedSeat : Nat := fold (fun a b => a + b) 1 lifeSeat
  let grownRead : Nat := drive grower lifeSeat lifeWord
  let toldRead : Nat := drive teller countedSeat lifeWord
  ok := (← checkTrue
    "  simulation row — the count carries the life at EVERY seat (the grower driven from a mid-life seat reads as the teller driven from its count — the 16th's s0-simulation upgraded to the whole seat-pair family)"
    ((grownRead == toldRead) && (grownRead == 12))) && ok
  let recSoFar : List Unit := [(), ()]
  let replayRead : Bool := drive (replayer paceOne) recSoFar [()]
  let parkedRead : Bool := drive paceOne (park paceOne (0 : Nat) recSoFar) [()]
  ok := (← checkTrue
    "  simulation row — the park carries the record (the replayer driven from a mid-record seat reads as the machine driven from the parked seat: rehydration as a carrier, at every record)"
    ((replayRead == parkedRead) && (replayRead == true))) && ok
  return ok

def benchLicense : IO Bool := do
  let mut ok := true
  IO.println "the license — a carrier merges only the alike:"
  let routeA : List Bool := [true, false]
  let routeB : List Bool := [false, true]
  let mergedA : Bool := drive (replayer pulse) routeA [true]
  let mergedB : Bool := drive (replayer pulse) routeB [true]
  let parkedA : Nat := park pulse (0 : Nat) routeA
  let parkedB : Nat := park pulse (0 : Nat) routeB
  ok := (← checkTrue
    "  license row — the park-carrier merges the two routes and shows its books (one parked seat, the records provably distinct, and the record-face reads them alike at every probe — the handshake at carrier grain)"
    ((parkedA == parkedB)
      && (routeA != routeB) && (mergedA == mergedB))) && ok
  let heldSt2 : Nat × List Unit := ((0 : Nat), [()])
  let twiceSettled : Bool :=
    drive (buffered paceOne)
      (settleHeld paceOne (settleHeld paceOne heldSt2)) [(), ()]
  let unsettled : Bool := drive (buffered paceOne) heldSt2 [(), ()]
  ok := (← checkTrue
    "  license row — the maintenance is the identity's hom (two settles composed through the carrier category still read as none: the still hands are the endo-carriers, composition free)"
    (twiceSettled == unsettled)) && ok
  return ok

def benchCrossings : IO Bool := do
  let mut ok := true
  IO.println "the crossings — every crossing is a seating:"
  let s3 : Nat := 3
  let earWord : List Bool := [true, false]
  let earCarried : Bool := drive flip (oddNat s3) (earWord.map (fun _ => ()))
  let earStraight : Bool := drive pulse s3 earWord
  let seated : Bool := (reseat (seatFace flip) oddNat).obs s3 [(), ()]
  let straight : Bool := drive paceOne s3 [(), ()]
  ok := (← checkTrue
    "  crossing row — the ear crosses the carrier (the pace-flip carrier heard through the deaf ear carries the pulse) and the carrier was a seating all along (the flip's seat-face reseated at oddNat wears the pace's own face)"
    ((earCarried == earStraight) && (seated == straight)
      && (seated == true))) && ok
  return ok

def benchRetract : IO Bool := do
  let mut ok := true
  IO.println "the retract — the simulator retracts onto the carrier, the drain splits the idempotent:"
  let junk : List Nat := [7, 7, 7, 7, 7]
  let stepFn : build Nat toyPlan → Unit → build Nat toyPlan :=
    fun s _ => reground (fun w => w + 1) toyPlan s
  let drained : List Nat := pour toyPlan (reboard (0 : Nat) toyPlan junk)
  let twice : List Nat := pour toyPlan (reboard (0 : Nat) toyPlan drained)
  ok := (← checkTrue
    "  retract row — the junk drains to spec in one pass and the drain is idempotent (five marks in, three out, the second pass moving nothing)"
    ((drained.length == 3) && (twice == drained))) && ok
  let viaWords : Nat :=
    drive (onWords (0 : Nat) toyPlan stepFn (spine Nat toyPlan) toyImport)
      junk [()]
  let viaCarrier : Nat :=
    drive (onPlan toyPlan toyImport stepFn (spine Nat toyPlan))
      (reboard (0 : Nat) toyPlan junk) [()]
  ok := (← checkTrue
    "  retract row — the reboard carries the words home (the simulator driven from junk reads as the carrier driven from the junk's reboard: the backward carrier live, the section-retraction pair closed)"
    (viaWords == viaCarrier)) && ok
  return ok

def benchSettleSplits : IO Bool := do
  let mut ok := true
  IO.println "the settle splits — the margin is a retract, the settle its idempotent:"
  let held3 : Nat × List Unit := ((1 : Nat), [(), (), ()])
  let workedSeat : Nat := park paceOne held3.1 held3.2
  let viaMargin : Bool := drive (buffered paceOne) held3 [()]
  let viaGround : Bool := drive paceOne workedSeat [()]
  let settledTwice : Nat × List Unit :=
    settleHeld paceOne (settleHeld paceOne held3)
  ok := (← checkTrue
    "  settle row — the work-carrier reads the margin at the ground (the buffered machine driven from a held tail reads as the machine driven from the worked seat: four, and true) and the settle is idempotent at the carrier (twice settled is once settled)"
    ((viaMargin == viaGround) && (workedSeat == 4)
      && (settledTwice == settleHeld paceOne held3))) && ok
  let liftBack : Bool := drive (buffered paceOne) ((3 : Nat), []) [()]
  let plain : Bool := drive paceOne (3 : Nat) [()]
  ok := (← checkTrue
    "  settle row — the hold-carrier lifts the machine home (holding nothing is the section: the machine seats in the margin and reads identically) — one shape at two grains, the drain and the settle"
    (liftBack == plain)) && ok
  return ok

def benchCustomsFunctor : IO Bool := do
  let mut ok := true
  IO.println "the customs functor — the world-map crosses to a carrier-map, the manifest natural:"
  let f : Nat → Nat := fun w => w * 10
  let g : Nat → Nat := fun w => w + 7
  let stacked : List Nat :=
    pour toyPlan (reground g toyPlan (reground f toyPlan toyImport))
  let fused : List Nat :=
    pour toyPlan (reground (fun w => g (f w)) toyPlan toyImport)
  let stillWorld : List Nat :=
    pour toyPlan (reground (fun w => w) toyPlan toyImport)
  ok := (← checkTrue
    "  functor row — the customs keep the still world and stack forward (identity moves nothing; two customs passes fuse into one, ninety-one thousand ninety-seven at the spine)"
    ((stacked == fused) && (stillWorld == pour toyPlan toyImport)
      && (stacked.headD 0 == 91097))) && ok
  let viaCustoms : List Nat := pour toyPlan (reground f toyPlan toyImport)
  let viaMap : List Nat := (pour toyPlan toyImport).map f
  ok := (← checkTrue
    "  functor row — the manifest is natural (cross the customs then pour, or pour then map: one square, both ways round) and the spine is natural beneath it"
    ((viaCustoms == viaMap)
      && (spine Nat toyPlan (reground f toyPlan toyImport)
          == f (spine Nat toyPlan toyImport)))) && ok
  return ok

def benchTwoFunctors : IO Bool := do
  let mut ok := true
  IO.println "the two channels — space and time are both functors, and they commute:"
  let stillLife : Bool := planBeq (graft .ground dayB) dayB
  let stacked : Bool :=
    planBeq (graft dayA (graft dayB dayA)) (graft (graft dayA dayB) dayA)
  ok := (← checkTrue
    "  functor row — the revision keeps the still life and the revisions stack forward (grafting by ground moves nothing; two revisions fuse into one lineage, planBeq-checked)"
    (stillLife && stacked)) && ok
  let readAfter : Nat := fold (fun a b => a + b) 1 (graft dayA dayB)
  let readThrough : Nat :=
    fold (fun a b => a + b) (fold (fun a b => a + b) 1 dayA) dayB
  ok := (← checkTrue
    "  functor row — the reading is natural over time (fold after grafting equals fold from the folded ground: the resumption law read as a naturality square, six both ways) and the product law is the two axes meeting"
    ((readAfter == readThrough) && (readAfter == 6)
      && (readAfter
          == fold (fun a b => a + b) 1 dayA
              * fold (fun a b => a + b) 1 dayB))) && ok
  let crossThenRide : List Nat :=
    pour (graft toyPlan revision)
      (reground (fun w => w * 10) (graft toyPlan revision)
        (ride toyImport revision))
  let rideThenCross : List Nat :=
    pour (graft toyPlan revision)
      (ride (reground (fun w => w * 10) toyPlan toyImport) revision)
  ok := (← checkTrue
    "  functor row — the two axes commute (cross the customs then take the tick, or take the tick then cross: one square, the world-channel and the time-channel independent)"
    ((crossThenRide == rideThenCross)
      && (crossThenRide.length == 6))) && ok
  return ok

def benchMediating : IO Bool := do
  let mut ok := true
  IO.println "the mediating map — replan is the iso between the shapes, gauge for the cargo:"
  let leftHeavy : Plan := .board (.board .ground .ground) .ground
  let lh : build Nat leftHeavy := (((7 : Nat), (8 : Nat)), (9 : Nat))
  let there : build Nat (comb 2) := replan (0 : Nat) leftHeavy (comb 2) lh
  let back : build Nat leftHeavy := replan (0 : Nat) (comb 2) leftHeavy there
  ok := (← checkTrue
    "  mediating row — the replanning is an iso (two shapes of three, over and back, the carrier home whole: seven-eight-nine either way, and the cargo identical at the far shape)"
    ((pour leftHeavy back == pour leftHeavy lh)
      && (pour (comb 2) there == [7, 8, 9]))) && ok
  let crossThenPlan : List Nat :=
    pour (comb 2)
      (replan (0 : Nat) leftHeavy (comb 2)
        (reground (fun w => w * 10) leftHeavy lh))
  let planThenCross : List Nat :=
    pour (comb 2)
      (reground (fun w => w * 10) (comb 2)
        (replan (0 : Nat) leftHeavy (comb 2) lh))
  ok := (← checkTrue
    "  mediating row — the replanning is natural over the customs (cross then re-plan, or re-plan then cross: one square, seventy-eighty-ninety either way) while the spec face still parts the shapes — license at the manifest, remainder at the spec"
    ((crossThenPlan == planThenCross)
      && (crossThenPlan == [70, 80, 90]))) && ok
  return ok

def benchIsoTest : IO Bool := do
  let mut ok := true
  IO.println "the iso test — a two-sided carrier merges nothing:"
  let held : Nat → Nat → Nat := holdOpen (fun d : door Nat Nat => face d * met d)
  let walked : door Nat Nat → Nat := walkIn (fun a b : Nat => a * b)
  let swapped : door Nat Nat := turnAbout (turnAbout (atTheDoor (3 : Nat) (5 : Nat)))
  ok := (← checkTrue
    "  iso row — the transposition and the swap are isos (held-then-walked reads the meeting, walked-then-held reads the two strokes, and the double swap restores the seating: forty-two, forty-two, three-and-five)"
    ((held 6 7 == 42) && (walked (atTheDoor (6 : Nat) (7 : Nat)) == 42)
      && (face swapped == 3) && (met swapped == 5))) && ok
  let leftHeavy2 : Plan := .board (.board .ground .ground) .ground
  let a1 : build Nat leftHeavy2 := (((1 : Nat), (2 : Nat)), (3 : Nat))
  let a2 : build Nat leftHeavy2 := (((1 : Nat), (2 : Nat)), (9 : Nat))
  let i1 : build Nat (comb 2) := replan (0 : Nat) leftHeavy2 (comb 2) a1
  let i2 : build Nat (comb 2) := replan (0 : Nat) leftHeavy2 (comb 2) a2
  ok := (← checkTrue
    "  iso row — an iso merges nothing (two carriers distinct at the source stay distinct across the shape-iso; the merging maps are exactly the non-isos — the boundary between a licensed identification and a real remainder)"
    ((pour (comb 2) i1 != pour (comb 2) i2)
      && (pour leftHeavy2 a1 != pour leftHeavy2 a2))) && ok
  return ok

def benchNonSections : IO Bool := do
  let mut ok := true
  IO.println "the non-sections — every blindness is a map with no way back:"
  let d1 : door Nat Nat := atTheDoor (4 : Nat) (0 : Nat)
  let d2 : door Nat Nat := atTheDoor (4 : Nat) (99 : Nat)
  ok := (← checkTrue
    "  non-section row — the face merges and therefore admits no section (two doors, one face, provably distinct: no map from faces to doors can bring the guest back — the kid's fourth theorem read as a factorization fact)"
    ((face d1 == face d2) && (met d1 != met d2))) && ok
  let r1 : List Bool := [true, false]
  let r2 : List Bool := [false, true]
  let seatR1 : Nat := park pulse (0 : Nat) r1
  let seatR2 : Nat := park pulse (0 : Nat) r2
  ok := (← checkTrue
    "  non-section row — the census and the deaf ear merge alike (two routes, one parked seat; two words, one deaf hearing) so neither admits a way back — the blindnesses are exactly the non-retractions"
    ((seatR1 == seatR2)
      && (r1.map (fun _ => ()) == r2.map (fun _ => ()))
      && (r1 != r2))) && ok
  return ok

def benchModelingLoop : IO Bool := do
  let mut ok := true
  IO.println "the modeling loop — positive subscription, negative subscription, record:"
  let coarse : Face := rehear windowFace (fun n : Nat => 2 * n)
  let posA : Bool := coarse.obs w02 (1 : Nat)
  let posB : Bool := coarse.obs w03 (1 : Nat)
  let bare : Bool := windowFace.obs w02 (3 : Nat)
  let bare' : Bool := windowFace.obs w03 (3 : Nat)
  ok := (← checkTrue
    "  loop row — the positive subscription is the ear (two windows agreeing at every doubled probe: the stream you subscribe to is the probe-family you take) while the bare face still parts them — subscribing narrows what reaches you, never what is"
    ((posA == posB) && (bare != bare'))) && ok
  let keep : Measured × Nat → Nat := fun x => x.2 + 1
  let st0 : Measured × Nat := (m2018, (0 : Nat))
  let once : Measured × Nat := (st0.1, keep st0)
  let twice : Measured × Nat := (once.1, keep once)
  let readNone : Bool := (host windowFace Nat).obs st0 (91093837015 : Nat)
  let readOnce : Bool := (host windowFace Nat).obs once (91093837015 : Nat)
  let readTwice : Bool := (host windowFace Nat).obs twice (91093837015 : Nat)
  ok := (← checkTrue
    "  loop row — the record writes where the face is blind, so recording the recording grounds (the tally climbs one, two, and every reading is unchanged: observing my own recording adds no reading, no regress — the second look adds nothing)"
    ((readNone == readOnce) && (readOnce == readTwice) && readTwice
      && (once.2 == 1) && (twice.2 == 2))) && ok
  return ok

def benchMutualRecords : IO Bool := do
  let mut ok := true
  IO.println "the mutual records — two seats recording each other, conduct one, records two:"
  let mine : Measured × Nat × Nat → Nat := fun x => x.2.1 + 1
  let yours : Measured × Nat × Nat → Nat := fun x => x.2.2 + 10
  let start : Measured × Nat × Nat := (m2018, ((0 : Nat), (0 : Nat)))
  let after1 : Measured × Nat × Nat := (start.1, (mine start, yours start))
  let after2 : Measured × Nat × Nat := (after1.1, (mine after1, yours after1))
  let tm : Nat := 91093837015
  let r0 : Bool := (host windowFace (Nat × Nat)).obs start tm
  let r1 : Bool := (host windowFace (Nat × Nat)).obs after1 tm
  let r2 : Bool := (host windowFace (Nat × Nat)).obs after2 tm
  ok := (← checkTrue
    "  mutual row — both seats record and neither reading moves (two ticks of mutual recording: mine climbs one-two, yours climbs ten-twenty, and the window reads the true mass unchanged throughout)"
    ((r0 == r1) && (r1 == r2) && r2
      && (after2.2.1 == 2) && (after2.2.2 == 20))) && ok
  let mineOnly : Measured × Nat × Nat := (m2018, ((7 : Nat), (0 : Nat)))
  let yoursOnly : Measured × Nat × Nat := (m2018, ((9 : Nat), (0 : Nat)))
  let seenA : Bool := (host windowFace (Nat × Nat)).obs mineOnly tm
  let seenB : Bool := (host windowFace (Nat × Nat)).obs yoursOnly tm
  let widerA : Nat := greet (fun _ => (0 : Nat)) (fun p => p.1)
    ((widen windowFace (Nat × Nat)).obs mineOnly (viaRight ()))
  let widerB : Nat := greet (fun _ => (0 : Nat)) (fun p => p.1)
    ((widen windowFace (Nat × Nat)).obs yoursOnly (viaRight ()))
  ok := (← checkTrue
    "  mutual row — the records part the seats one seat wider (two histories, identical at every probe of the shared face, seven against nine at the wider ask: conduct one, records two — the handshake at the modeling loop's own grain)"
    ((seenA == seenB) && (widerA != widerB)
      && (widerA == 7) && (widerB == 9))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchConcord : IO Bool := do
  let mut ok := true
  IO.println "the concord — what the meeting affords that neither model does:"
  let tm : Nat := 91093837015
  let agreeing : Measured × Bool := (m2018, true)
  let disagreeing : Measured × Bool := (m2018, false)
  let cA : Bool × Bool := (concordFace windowFace Bool).obs agreeing (tm, ())
  let cB : Bool × Bool := (concordFace windowFace Bool).obs disagreeing (tm, ())
  ok := (← checkTrue
    "  concord row — the concord reads both models at once (the window's own reading beside the model of it: true-with-true against true-with-false — the agreement legible only where the two are read together)"
    ((cA.1 == cB.1) && (cA.2 != cB.2)
      && (cA.1 == cA.2) && (cB.1 != cB.2))) && ok
  let seatOnly : Bool := (host windowFace Bool).obs agreeing tm
  let seatOnly' : Bool := (host windowFace Bool).obs disagreeing tm
  ok := (← checkTrue
    "  concord row — no seat reads the concord alone (the shared face merges the two models at every probe; the agreement-role is derived at the meeting and underivable at either seat — composition provokes what neither brought)"
    (seatOnly == seatOnly')) && ok
  return ok

set_option maxRecDepth 4096 in
def benchAddressableGap : IO Bool := do
  let mut ok := true
  IO.println "the addressable gap — the meeting agrees or names where it doesn't:"
  let tm : Nat := 91093837015
  let below : Nat := 91093834000
  let modelTrue : Measured × Bool := (m2018, true)
  let readsAt : Nat → Bool := fun p => windowFace.obs m2018 p
  let agreesAt : Nat → Bool := fun p => readsAt p == modelTrue.2
  ok := (← checkTrue
    "  gap row — the concord agrees or names the gap over a finite window (the model says true; the window agrees at the true mass and DISAGREES below it — the witness named, not felt)"
    (agreesAt tm && !(agreesAt below))) && ok
  let fixed : Measured × Bool := (modelTrue.1, false)
  let beforeFix : Bool := (host windowFace Bool).obs modelTrue tm
  let afterFix : Bool := (host windowFace Bool).obs fixed tm
  let cBefore : Bool × Bool :=
    (concordFace windowFace Bool).obs modelTrue (below, ())
  let cAfter : Bool × Bool :=
    (concordFace windowFace Bool).obs fixed (below, ())
  ok := (← checkTrue
    "  gap row — settling the gap moves the model and no reading (the fix is unheard at the shared face while the concord's agreement flips at the named probe: revision where the record lives, silence where the meeting looks)"
    ((beforeFix == afterFix)
      && (cBefore.1 != cBefore.2) && (cAfter.1 == cAfter.2))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchOneDisagreement : IO Bool := do
  let mut ok := true
  IO.println "the one disagreement — contact and modeling are one process:"
  let probes : List Nat := [91093837015, 91093834000]
  let readAt : Measured → Nat → Bool := fun m p => within m p
  let contactAgrees : Bool :=
    probes.all (fun p => readAt m2018 p == readAt m2018 p)
  let contactParts : Bool :=
    probes.any (fun p => readAt m2014 p != readAt m2018 p)
  ok := (← checkTrue
    "  fusion row — the contact disjunction runs between two seats (2014 and 2018 named at a probe; a seat and itself agreeing everywhere) — the 59th's process, unchanged"
    (contactAgrees && contactParts)) && ok
  let modelOf2018 : Measured := m2018
  let modelOf2014 : Measured := m2014
  let modelAgrees : Bool :=
    probes.all (fun p => readAt m2018 p == readAt modelOf2018 p)
  let modelParts : Bool :=
    probes.any (fun p => readAt m2018 p != readAt modelOf2014 p)
  ok := (← checkTrue
    "  fusion row — and the modeling disjunction is the same disjunction (a model IS the other's readings held at your coordinate: the true model agrees everywhere, the stale one is named at the same probe — running out of disagreement and settling the gap are one process)"
    (modelAgrees && modelParts)) && ok
  let unitQs : List Unit := [(), ()]
  let o1 : List Unit := sound (originFace Nat) (5 : Nat) (recite unitQs)
  let o2 : List Unit := sound (originFace Nat) (9 : Nat) (recite unitQs)
  ok := (← checkTrue
    "  fusion row — the origin has no disagreement to run out of (two seats, every probe, one sounding: the fixed point of both processes at once)"
    (o1 == o2)) && ok
  return ok

set_option maxRecDepth 4096 in
def benchUniverseDiscipline : IO Bool := do
  let mut ok := true
  IO.println "the universe discipline — pinned, gauge, parametric:"
  let tm : Nat := 91093837015
  let bigGuest : Type := Nat
  let seated : Measured × bigGuest := (m2018, (5 : Nat))
  let seated' : Measured × bigGuest := (m2018, (9 : Nat))
  let readA : Bool :=
    (reseat windowFace (fun x : Measured × bigGuest => x.1)).obs seated tm
  let readB : Bool :=
    (reseat windowFace (fun x : Measured × bigGuest => x.1)).obs seated' tm
  let hosted : Bool := (host windowFace Nat).obs seated tm
  ok := (← checkTrue
    "  universe row — the guest coordinate is parametric (two guests, one reading, whatever the guest's level) and the host is the reseat by first (the pin appears exactly where a construction hosts a seat, and nowhere else)"
    ((readA == readB) && (readA == hosted) && readA)) && ok
  let askList : List Nat := [tm, 91093834000]
  let bare : List Bool := sound windowFace m2018 (recite askList)
  let viaSeat : List Bool :=
    sound (reseat windowFace (fun x : Measured × bigGuest => x.1)) seated
      (recite askList)
  ok := (← checkTrue
    "  universe row — the level is gauge at the reading (the seated sounding equals the bare sounding, mark for mark: re-instantiating a theorem at another level changes no reading — which is why the pins are bookkeeping and never content)"
    (bare == viaSeat)) && ok
  return ok

set_option maxRecDepth 4096 in
def benchPortability : IO Bool := do
  let mut ok := true
  IO.println "the portability — certified by transit, never by inspection:"
  let word : List Unit := [(), (), ()]
  let atPace : Bool := drive paceOne (0 : Nat) word
  let atFlip : Bool := drive flip (oddNat (0 : Nat)) word
  let atLedger : Bool :=
    drive (replayer paceOne) ([] : List Unit) word
  ok := (← checkTrue
    "  transit row — a structure travels by its carrier (the pace's reading arrives whole at the flip's seat and at the replayer's record: three crossings, one reading, each certified by the crossing itself)"
    ((atPace == atFlip) && (atPace == atLedger) && atPace)) && ok
  let hop1 : Bool := drive flip (oddNat (2 : Nat)) word
  let hop2 : Bool := drive paceOne (2 : Nat) word
  ok := (← checkTrue
    "  transit row — certified links compose (pace to flip at a mid-run seat, the composite carrier still reading true: chain the certificates, no re-audit — and no seat certifies its own portability, since the guest it carries is exactly what it cannot read)"
    (hop1 == hop2)) && ok
  return ok

set_option maxRecDepth 4096 in
def benchUniversalProperties : IO Bool := do
  let mut ok := true
  IO.println "the universal properties — the door is the product, the fork the coproduct:"
  let f : Nat → Nat := fun x => x * 2
  let g : Nat → Nat := fun x => x + 100
  let paired : Nat → door Nat Nat := fun x => atTheDoor (f x) (g x)
  let x0 : Nat := 5
  ok := (← checkTrue
    "  universal row — the pairing exists and is unique (two readings of one source pair into one door; the projections give each back exactly: ten and one-oh-five, and any map agreeing at both projections IS the pairing)"
    ((face (paired x0) == f x0) && (met (paired x0) == g x0)
      && (face (paired x0) == 10) && (met (paired x0) == 105))) && ok
  let gl : Nat → Nat := fun h => h + 1
  let gr : Nat → Nat := fun w => w * 3
  let copaired : fork Nat Nat → Nat := greet gl gr
  ok := (← checkTrue
    "  universal row — the copairing exists and is unique (two handlers, one greeter; every ready greeter IS the greeter, standing since depth zero as the coproduct's own law: five by the left, twelve by the right)"
    ((copaired (viaLeft (4 : Nat)) == 5)
      && (copaired (viaRight (4 : Nat)) == 12))) && ok
  let readA : Nat := face (atTheDoor (7 : Nat) (0 : Nat))
  let readB : Nat := face (atTheDoor (7 : Nat) (99 : Nat))
  ok := (← checkTrue
    "  universal row — face-blindness IS the projection's forgetting (the first projection drops the second coordinate by construction, so the door cannot read its guest for the same reason a product cannot read past its own leg — the oldest theorem, restated as a categorical fact)"
    ((readA == readB) && (readA == 7)
      && (met (atTheDoor (7 : Nat) (99 : Nat)) == 99))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchLadderSheds : IO Bool := do
  let mut ok := true
  IO.println "the ladder sheds — the bootstrap drops out of the hall it lit:"
  let lit : List Nat × List (Nat × List Nat) := sweep (welcome dead0 (9, []))
  let room : List Nat := lit.1
  let native : List Nat := [8, 9, 1]
  ok := (← checkTrue
    "  ladder row — the circle lights by one domestic key and the bootstrapped hall reads exactly as a hall that always held them (both marks enrolled, the vestibule empty, membership identical at every mark the room knows)"
    ((enrolled room 8) && (enrolled room 9) && (enrolled room 1)
      && (lit.2.length == 0)
      && (enrolled room 8 == enrolled native 8)
      && (enrolled room 9 == enrolled native 9)
      && (enrolled room 1 == enrolled native 1)
      && (enrolled room 7 == enrolled native 7))) && ok
  let again : List Nat := 8 :: room
  ok := (← checkTrue
    "  ladder row — a seated mark arriving again adds no reading (the re-arrival is invisible at every membership probe) while the cost face keeps the climb where there was one: the ladder is real and readable only one seat wider"
    ((enrolled again 9 == enrolled room 9)
      && (enrolled again 8 == enrolled room 8)
      && (enrolled again 7 == enrolled room 7)
      && (depthTo room 8 != 0)
      && (depthTo again 8 != depthTo room 8))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchLanded : IO Bool := do
  let mut ok := true
  IO.println "the landed — what survives normalizing is exactly what normalizing produces:"
  let junk : List Nat := [7, 7, 7, 7, 7]
  let normed : List Nat := pour toyPlan (reboard (0 : Nat) toyPlan junk)
  let renormed : List Nat := pour toyPlan (reboard (0 : Nat) toyPlan normed)
  ok := (← checkTrue
    "  landed row — the on-spec are the landed (the drained word is its own normal form, and every normal form is something's drain: fixed and in-the-image are one predicate)"
    ((renormed == normed) && (normed.length == 3)
      && (junk.length != 3))) && ok
  let held3 : Nat × List Unit := ((1 : Nat), [(), (), ()])
  let settled : Nat × List Unit := settleHeld paceOne held3
  let resettled : Nat × List Unit := settleHeld paceOne settled
  ok := (← checkTrue
    "  landed row — the settled are the landed (a settled margin is fixed under settling, and a fixed margin is a settled one: you cannot tell 'never needed working' from 'already worked')"
    ((resettled == settled) && (settled.2.length == 0)
      && (held3.2.length == 3) && (settled.1 == 4))) && ok
  let restedRoom : List Nat × List (Nat × List Nat) :=
    sweep ([5, 6], ([] : List (Nat × List Nat)))
  ok := (← checkTrue
    "  landed row — the drained room is its own normal form (the rest is a fixed point AND the image of itself: the room that needs no sweep and the room that has been swept are one room)"
    ((restedRoom.2.length == 0) && (enrolled restedRoom.1 5)
      && (enrolled restedRoom.1 6))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchUniformShift : IO Bool := do
  let mut ok := true
  IO.println "the uniform shift — hand-propping shows up as everyone being one click older:"
  let before : List Nat := [3, 2, 1]
  let after : List Nat := 4 :: before
  ok := (← checkTrue
    "  shift row — the scaffold shifts every elder by exactly one (three, two, one read zero-one-two before and one-two-three after; the newcomer reads zero) — no elder singled out, all of them moved"
    ((depthTo before 3 == 0) && (depthTo before 2 == 1) && (depthTo before 1 == 2)
      && (depthTo after 3 == 1) && (depthTo after 2 == 2) && (depthTo after 1 == 3)
      && (depthTo after 4 == 0))) && ok
  let gapBefore : Nat := depthTo before 1 - depthTo before 3
  let gapAfter : Nat := depthTo after 1 - depthTo after 3
  ok := (← checkTrue
    "  shift row — every gap and the whole order survive the shift (the two-click distance between the eldest and the newest-before stays two; the ranking is untouched) — so nothing built from differences can see the propping"
    ((gapBefore == gapAfter) && (gapBefore == 2)
      && (Nat.ble (depthTo after 3) (depthTo after 1)))) && ok
  let m1 : Bool := enrolled after 3 == enrolled before 3
  let m2 : Bool := enrolled after 9 == enrolled before 9
  ok := (← checkTrue
    "  shift row — and the hall reads nothing at all (membership identical at every probe, present and absent alike): the origin is invisible below, uniform above, and legible only against a reference the room does not contain"
    (m1 && m2)) && ok
  return ok

set_option maxRecDepth 4096 in
def benchTwoGauges : IO Bool := do
  let mut ok := true
  IO.println "the two gauges — the shift on the seat, the scale on the stage:"
  let w3 : List Unit := [(), (), ()]
  let fromZero : Nat := park paceOne (0 : Nat) w3
  let fromTen : Nat := park paceOne (10 : Nat) w3
  ok := (← checkTrue
    "  gauge row — the shift commutes with the walk (start at zero or at ten, walk the same word, and the gap is exactly the gap you started with: three and thirteen)"
    ((fromZero == 3) && (fromTen == 13)
      && (fromTen - fromZero == 10))) && ok
  let scaled : Nat := fold (fun a b => a + b) (7 : Nat) dayB
  let unit : Nat := fold (fun a b => a + b) (1 : Nat) dayB
  ok := (← checkTrue
    "  gauge row — the ground is a uniform scale (folding from seven reads seven times what folding from one reads: twenty-one against three — the stage channel's gauge is multiplicative where the seat channel's is additive)"
    ((scaled == 7 * unit) && (unit == 3) && (scaled == 21))) && ok
  let voteA : Nat := 299792458
  let voteB : Nat := 1380649
  ok := (← checkTrue
    "  gauge row — the treaty is the scale-gauge at home (every vote reads itself at pace one) and any pace conserves every ratio (c against k_B reads the same relation at every pace: the SI rows have been running this gauge since the seed's first week)"
    ((readAcross voteA paceAtHome == voteA)
      && (readAcross voteB paceAtHome == voteB)
      && (readAcross voteA 5 * voteB == readAcross voteB 5 * voteA))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchGaugeLadder : IO Bool := do
  let mut ok := true
  IO.println "the gauge ladder — sharpen the face and the gauge group shrinks:"
  let tm : Nat := 91093837015
  let st : Measured × Bool := (m2018, true)
  let flipped : Measured × Bool := (st.1, !st.2)
  let coarse : Bool := (host windowFace Bool).obs st tm
  let coarse' : Bool := (host windowFace Bool).obs flipped tm
  ok := (← checkTrue
    "  ladder row — the guest-flip is gauge at the host (the window reads the true mass identically before and after the flip: at this face the move is not there)"
    ((coarse == coarse') && coarse)) && ok
  let fine : Nat := greet (fun _ => (0 : Nat)) (fun b => cond b 1 2)
    ((widen windowFace Bool).obs st (viaRight ()))
  let fine' : Nat := greet (fun _ => (0 : Nat)) (fun b => cond b 1 2)
    ((widen windowFace Bool).obs flipped (viaRight ()))
  ok := (← checkTrue
    "  ladder row — and heard one widening up (the same move, the same states, parted at the wider ask: one against two) — so the gauge group is not a property of the move, it is a property of the face you are standing at"
    ((fine != fine') && (fine == 1) && (fine' == 2))) && ok
  let stillCoarse : Bool := (host windowFace Bool).obs st tm
  let stillFine : Nat := greet (fun _ => (0 : Nat)) (fun b => cond b 1 2)
    ((widen windowFace Bool).obs st (viaRight ()))
  ok := (← checkTrue
    "  ladder row — the still hand survives every face (the identity is gauge at the coarse face and at the fine one alike: every gauge group contains it, so no face is ever gauge-empty)"
    ((stillCoarse == coarse) && (stillFine == fine))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchDarkType : IO Bool := do
  let mut ok := true
  IO.println "the dark type — the ground is the only one, and every ground after it is built:"
  let room3 : List Plan := allPlans 3
  let named : Bool := room3.any (fun p => planBeq p toyPlan)
  ok := (← checkTrue
    "  dark row — every built type is named below the horizon (the toy plan's type is one of twenty-six in room three; the enumeration of type-shapes is exact — nothing missed, nothing doubled)"
    (named && (room3.length == 26))) && ok
  let quoted : Plan := met (label Nat toyPlan toyImport)
  let evaled : Plan := fold Plan.board Plan.ground toyPlan
  ok := (← checkTrue
    "  dark row — the plan rides as data and reads back as itself (the carrier carries its own type-shape as an unread guest; reading the shape as a shape hands it back: quote and eval, both directions)"
    (planBeq quoted toyPlan && planBeq evaled toyPlan)) && ok
  let stacked : Nat :=
    (pour (graft toyPlan revision) (ride toyImport revision)).length
  ok := (← checkTrue
    "  dark row — a built type grounds the next tower (the toy plan's own carrier serves as the ground of a revision, six guests deep: every ground after the first is one you built, so the unenumerable part is exactly one type)"
    (stacked == 6)) && ok
  return ok

set_option maxRecDepth 4096 in
def benchAffordance : IO Bool := do
  let mut ok := true
  IO.println "the affordance surface — every move gauge, the wear at the minted reading:"
  let d0 : door Nat Nat := atTheDoor (5 : Nat) (0 : Nat)
  let m1 : door Nat Nat := vertical (fun _ w => w + 1000) d0
  let m2 : door Nat Nat := vertical (fun h w => h * w + 7) m1
  let m3 : door Nat Nat := vertical (fun _ w => w * w) m2
  ok := (← checkTrue
    "  affordance row — every move the puppeteer has, and every composite of them, is gauge at the face (three wild guest-moves stacked: the face reads five throughout while the guest travels a thousand, five thousand seven, and its own square)"
    ((face m1 == 5) && (face m2 == 5) && (face m3 == 5)
      && (met m1 == 1000) && (met m2 == 5007)
      && (met m3 == 5007 * 5007))) && ok
  let mintedTrue : Bool :=
    selfMeet (host windowFace Bool) (fun x => (cond x.2 0 1 : Nat))
      ((⟨0, 0⟩ : Measured), true)
  let mintedFalse : Bool :=
    selfMeet (host windowFace Bool) (fun x => (cond x.2 0 1 : Nat))
      ((⟨0, 0⟩ : Measured), false)
  let plainTrue : Bool :=
    (host windowFace Bool).obs ((⟨0, 0⟩ : Measured), true) (0 : Nat)
  let plainFalse : Bool :=
    (host windowFace Bool).obs ((⟨0, 0⟩ : Measured), false) (0 : Nat)
  ok := (← checkTrue
    "  affordance row — and the surface is exactly the minted reading (the same two guests: merged at every standing probe, parted the moment a probe is minted from the seat — the feedback point where the hospitality frame and the animation frame meet)"
    ((plainTrue == plainFalse) && (mintedTrue != mintedFalse))) && ok
  let unworn : Bool := drive (spiral piPace 30000000 piPace) (0 : Nat)
    (List.replicate 50 ())
  let arrowGrew : Bool :=
    Nat.ble (fold (fun a b => a + b) 1 dayA + 1)
      (fold (fun a b => a + b) 1 (graft dayA dayB))
  ok := (← checkTrue
    "  affordance row — the gauge sector never wears and the read sector does (fifty laps of the gap-zero wheel still reading true; one revision of a two-day provably past its own reading) — wears-in and wears-out, sorted by whether the reading reaches"
    (unworn && arrowGrew)) && ok
  return ok

set_option maxRecDepth 4096 in
def benchVestibule : IO Bool := do
  let mut ok := true
  IO.println "the vestibule — both bodies ride one face, and the churn costs nothing:"
  let innA : door Nat (Nat × Nat) := atTheDoor (100 : Nat) ((5 : Nat), (7 : Nat))
  let innB : door Nat (Nat × Nat) := atTheDoor (100 : Nat) ((9 : Nat), (7 : Nat))
  let moved : door Nat (Nat × Nat) :=
    vertical (fun _ x => (x.1 + 1000, x.2)) innA
  ok := (← checkTrue
    "  vestibule row — the innkeeper and the guest are both guests of the vestibule (one face reads a hundred whichever pair rides, and the innkeeper's own move is gauge there exactly as the guest's is at the inn: five to a thousand and five, the face unmoved)"
    ((face innA == face innB) && (face moved == face innA)
      && ((met moved).1 == 1005) && ((met moved).2 == 7)
      && ((met innA).1 == 5) && ((met innB).1 == 9))) && ok
  let seated : Measured × Nat := (m2018, (42 : Nat))
  let churned : Measured × Nat := (seated.1, (0 : Nat))
  let rechurned : Measured × Nat := (churned.1, (0 : Nat))
  let tm : Nat := 91093837015
  let readSeated : Bool := (host windowFace Nat).obs seated tm
  let readChurned : Bool := (host windowFace Nat).obs churned tm
  let readRechurned : Bool := (host windowFace Nat).obs rechurned tm
  ok := (← checkTrue
    "  vestibule row — extrude and retract is a cycle the inn cannot hear (the seat churns forty-two down to nothing and stays there; the window reads the true mass unchanged through every cycle: a system constantly making and dropping seats pays nothing at the face)"
    ((readSeated == readChurned) && (readChurned == readRechurned)
      && (rechurned.2 == churned.2) && readSeated)) && ok
  let asks : List Nat := [tm, 91093834000]
  let soundBefore : List Bool :=
    sound (host windowFace Nat) seated (recite asks)
  let soundAfter : List Bool :=
    sound (host windowFace Nat) churned (recite asks)
  ok := (← checkTrue
    "  vestibule row — and the ancestor survives every cycle (the whole sounding identical before and after the churn, mark for mark: what persists across extrusion and retraction is exactly the ground)"
    (soundBefore == soundAfter)) && ok
  return ok

set_option maxRecDepth 4096 in
def benchSharedUnit : IO Bool := do
  let mut ok := true
  IO.println "the shared unit — no map between the banks, a span through the minted seat:"
  let c : Nat := meterVote
  let kB : Nat := boltzmannVote
  let homeC : Nat := readAcross c paceAtHome
  let homeK : Nat := readAcross kB paceAtHome
  ok := (← checkTrue
    "  span row — each seat reads its own scale as one (c and k_B read themselves at home: from inside, your measure is always already normalized — which is why no seat can read its own unit)"
    ((homeC == c) && (homeK == kB))) && ok
  let farC : Nat := readAcross c 5
  let farK : Nat := readAcross kB 5
  ok := (← checkTrue
    "  span row — and any two paces agree on the ratio (a seat at pace five and a seat at home cross-multiply to the same number: the unit is a choice, the ratio is not — so the units compare without either bank ever mapping into the other)"
    ((farC * kB == farK * c) && (homeC * kB == homeK * c))) && ok
  let pairedA : Bool × Bool :=
    (pairFace windowFace windowFace (fun x => x) (fun _ => m2018)).obs
      m2018 ((91093837015 : Nat), (91093837015 : Nat))
  let pairedB : Bool × Bool :=
    (pairFace windowFace windowFace (fun x => x) (fun _ => m2018)).obs
      m2014 ((91093837015 : Nat), (91093837015 : Nat))
  ok := (← checkTrue
    "  span row — the comparison reads both units at one probe (the minted third seat holds each bank's own reading side by side: 2018 agreeing with itself, 2014 parting from it — the place the sticks are laid together, mintable by nothing but the comparison)"
    ((pairedA.1 == pairedA.2) && (pairedB.1 != pairedB.2))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchComposableMeasure : IO Bool := do
  let mut ok := true
  IO.println "the composable measure — sum at the board, product at the graft:"
  let mA : Nat := fold (fun a b => a + b) 1 dayA
  let mB : Nat := fold (fun a b => a + b) 1 dayB
  let joined : Nat := fold (fun a b => a + b) 1 (.board dayA dayB)
  let grown : Nat := fold (fun a b => a + b) 1 (graft dayA dayB)
  ok := (← checkTrue
    "  compose row — a compound's measure derives from its parts, and WHICH LAW applies is which channel joined them (two and three: boarded reads five, grafted reads six — sum on the seat channel, product on the stage channel)"
    ((joined == mA + mB) && (grown == mA * mB)
      && (joined == 5) && (grown == 6))) && ok
  let banked1 : Nat := park restingCounter (0 : Nat) [(), ()]
  let banked2 : Nat := park restingCounter (2 : Nat) [(), (), ()]
  ok := (← checkTrue
    "  compose row — the bank adds along the run (two marks then three more reads five: the stored measure of a whole run is the sum of its legs, so a system's banked capacity composes without re-measuring)"
    ((banked1 == 2) && (banked2 == 5))) && ok
  let c : Nat := meterVote
  let kB : Nat := boltzmannVote
  ok := (← checkTrue
    "  compose row — and the ratio survives every pace, so a composed measure stays comparable across seats (c against k_B cross-multiplying identically at home and at pace seven: compose locally, compare globally, no interior crossing)"
    ((readAcross c paceAtHome * kB == readAcross kB paceAtHome * c)
      && (readAcross c 7 * kB == readAcross kB 7 * c))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchMagnitudes : IO Bool := do
  let mut ok := true
  IO.println "the magnitudes — four numbers, one composition law:"
  let readBoard : Nat := fold (fun a b => a + b) 1 (.board dayA dayB)
  let readGraft : Nat := fold (fun a b => a + b) 1 (graft dayA dayB)
  let patienceBoard : Nat :=
    doorsOpened
      (handOff (strokesReception 1 doormanTower)
        (fun x => strokesReception 0 (fun v => x + v)))
      (fun n => n)
  let boardOfCombs : Nat :=
    fold (fun a b => a + b) 1 (Plan.board (comb 1) (comb 0))
  ok := (← checkTrue
    "  magnitude row — the patience obeys the reading's own law (a handoff's door-ledger reads the board's census exactly: three and three) — so the composition law is a fact about the CHANNELS, not about the reading"
    ((patienceBoard == boardOfCombs) && (patienceBoard == 3)
      && (readBoard == 5) && (readGraft == 6))) && ok
  let manifestLen : Nat := (pour lineagePlan electronLineage).length
  let readLineage : Nat := fold (fun a b => a + b) 1 lineagePlan
  let bank1 : Nat := park restingCounter (0 : Nat) [(), ()]
  let bank2 : Nat := park restingCounter (2 : Nat) [(), (), ()]
  ok := (← checkTrue
    "  magnitude row — and the manifest and the bank keep it too (the carrier's guest-count IS its plan's reading; a run banked in two legs sums) — four magnitudes, one law: add at the join, multiply at the revision"
    ((manifestLen == readLineage) && (manifestLen == 2)
      && (bank1 == 2) && (bank2 == 5))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchTwoCharts : IO Bool := do
  let mut ok := true
  IO.println "the two charts — one measure, two zeros, and the bridge between the channels:"
  let leaves : Nat := fold (fun a b => a + b) 1 (bloom 3)
  let joins : Nat := boards (bloom 3)
  let leavesB : Nat := fold (fun a b => a + b) 1 dayB
  let joinsB : Nat := boards dayB
  ok := (← checkTrue
    "  chart row — the leaf-count and the join-count are one measure at two zeros (eight leaves and seven joins on bloom three; three and two on the three-day) — the chart transition is always exactly one, which is the ground"
    ((joins + 1 == leaves) && (joinsB + 1 == leavesB)
      && (leaves == 8) && (joins == 7))) && ok
  let boarded : Nat := boards (.board dayA dayB)
  ok := (← checkTrue
    "  chart row — and the shifted chart pays for its own join (joining two plans adds their joins AND one more for the joining: one plus two plus one is four) — the affine composition is the shift showing up in the composition law"
    ((boarded == boards dayA + boards dayB + 1) && (boarded == 4))) && ok
  ok := (← checkTrue
    "  chart row — the cap carries the sum to the product (depths two and three add to five while their caps four and eight multiply to thirty-two: the exponential as the bridge between the seat channel and the stage channel, receipted)"
    ((roomCap (2 + 3) == roomCap 2 * roomCap 3)
      && (roomCap 5 == 32) && (roomCap 2 == 4) && (roomCap 3 == 8))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchRulerAndWheel : IO Bool := do
  let mut ok := true
  IO.println "the ruler and the wheel — a measure rules the arrow and flattens the wheel:"
  let flight : List Nat :=
    [park collatz (1 : Nat) (List.replicate 0 ()),
     park collatz (1 : Nat) (List.replicate 1 ()),
     park collatz (1 : Nat) (List.replicate 2 ()),
     park collatz (1 : Nat) (List.replicate 3 ())]
  ok := (← checkTrue
    "  ruler row — the home wheel returns to itself and any non-increasing rank is forced flat across it (one, four, two, one: three points a monotone measure provably cannot tell apart — the wheel is one measure-point)"
    ((flight == [1, 4, 2, 1]) && (flight.headD 0 == flight.getD 3 0))) && ok
  let grown : Nat := fold (fun a b => a + b) 1 (graft dayA dayB)
  let before : Nat := fold (fun a b => a + b) 1 dayA
  ok := (← checkTrue
    "  ruler row — while the arrow's measure strictly grows at every true tick (two revised by three reads six, past its own prior reading forever) — so a measure is a ruler exactly where the dynamics is an arrow"
    ((Nat.ble (before + 1) grown) && (grown == 6) && (before == 2))) && ok
  let deadFlat0 : Nat := drainFace.obs dead0 (0 : Nat)
  let deadFlat3 : Nat := drainFace.obs dead0 (3 : Nat)
  let liveDrop0 : Nat := drainFace.obs intake (0 : Nat)
  let liveDrop2 : Nat := drainFace.obs intake (2 : Nat)
  let spiralUnworn : Bool :=
    drive (spiral piPace 30000000 piPace) (0 : Nat) (List.replicate 40 ())
  ok := (← checkTrue
    "  ruler row — and the same law reads at three other strata (the drain meter flat at every hour on the dead vestibule and descending two-to-zero on the live one; the gap-zero spiral true at forty laps): one statement, four addresses"
    ((deadFlat0 == deadFlat3) && (liveDrop0 != liveDrop2)
      && (liveDrop2 == 0) && spiralUnworn)) && ok
  return ok

set_option maxRecDepth 4096 in
def benchSemiring : IO Bool := do
  let mut ok := true
  IO.println "the semiring — the door, the fork, both units, and the annihilator:"
  let anon : door Nat Unit := atTheDoor (9 : Nat) ()
  let sealed : fork Nat Empty := viaLeft (9 : Nat)
  ok := (← checkTrue
    "  semiring row — both units were carved on day one (hosting the anonymous guest changes nothing: door-times-one is the door; a sealed entrance adds nothing: fork-plus-zero is the fork — nine either way)"
    ((face anon == 9) && (noEntrance sealed == 9)
      && (face (atTheDoor (face anon) ()) == face anon))) && ok
  let mh : Nat → Nat := fun h => h * 10
  let mw : Nat → Nat := fun w => w + 100
  ok := (← checkTrue
    "  semiring row — and the measure SELECTS at the fork where it combines at the door (the left branch reads forty, the right reads a hundred and four: a coproduct's measure is its branch's own, not a sum and not a product — which is what a choice should cost)"
    ((greet mh mw (viaLeft (4 : Nat)) == 40)
      && (greet mh mw (viaRight (4 : Nat)) == 104))) && ok
  let dd : door (door Nat Nat) Nat := atTheDoor (atTheDoor (1 : Nat) (2 : Nat)) (3 : Nat)
  let dv : door Nat (fork Nat Nat) := atTheDoor (7 : Nat) (viaLeft (3 : Nat))
  ok := (← checkTrue
    "  semiring row — with associativity and distributivity standing beneath them (the nested door reassociates home; the hosted fork distributes and collects back whole) — every semiring law carved before the word existed"
    ((face (face (shallow (deepen dd))) == 1)
      && (met (shallow (deepen dd)) == 3)
      && (face (collect (distribute dv)) == 7))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchExactCures : IO Bool := do
  let mut ok := true
  IO.println "the exact cures — the mint pays the merge back whole:"
  let hiMint1 : Nat := empty1.hi
  let hiMint2 : Nat := empty2.hi
  let loMint1 : Nat := empty1.lo
  let loMint2 : Nat := empty2.lo
  ok := (← checkTrue
    "  cure row — the sharpening is exact (the two empty windows, alike at every probe, stay merged under the hi-mint — zero and zero — and part at the lo-mint — one against two: the sharpened face reads conduct plus the mint, no more, no less)"
    ((within empty1 0 == within empty2 0) && (within empty1 7 == within empty2 7)
      && (hiMint1 == hiMint2) && (loMint1 != loMint2))) && ok
  let readW : fork Bool Nat → Nat := greet (fun _ => (0 : Nat)) (fun n => n)
  let sameGuestA : Nat :=
    readW ((widen windowFace Nat).obs (empty1, (5 : Nat)) (viaRight ()))
  let sameGuestB : Nat :=
    readW ((widen windowFace Nat).obs (empty2, (5 : Nat)) (viaRight ()))
  let otherGuest : Nat :=
    readW ((widen windowFace Nat).obs (empty1, (9 : Nat)) (viaRight ()))
  ok := (← checkTrue
    "  cure row — the widening is exact both ways (two provably distinct empty windows carrying one guest read alike at the widened face — conduct-alike and guest-equal is all it takes — while unequal guests part at the wider ask: the flattening's loss is the widening's exact yield)"
    ((sameGuestA == sameGuestB) && (sameGuestA == 5)
      && (sameGuestA != otherGuest))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchServiceLadder : IO Bool := do
  let mut ok := true
  IO.println "the service ladder — the widest flattening serves the most:"
  let recA : List Bool := park (ledger Bool) ([] : List Bool) [true, false]
  let recB : List Bool := park (ledger Bool) ([] : List Bool) [false, true]
  let seatA : Nat := park pulse (0 : Nat) [true, false]
  let seatB : Nat := park pulse (0 : Nat) [false, true]
  ok := (← checkTrue
    "  service row — the record serves the reading the parked seat provably cannot (the ledger's head reads true against false while the pulse parks both routes on one seat: the wide flattening keeps the order-reading in service, the narrow one drops it forever)"
    ((recA.headD false != recB.headD false)
      && (seatA == seatB))) && ok
  let long : List Bool := [true, false, true]
  let short : List Bool := [true]
  ok := (← checkTrue
    "  service row — the finer flattening serves fewer, live (parity is served through length — odd both ways — but length is not served through parity: two lists agreeing at the parity-flattening and parting at the length-reading, the unserved reading witnessed)"
    ((oddNat long.length == oddNat short.length)
      && (long.length != short.length))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchStillStation : IO Bool := do
  let mut ok := true
  IO.println "the still station — quiescence is drained, or evenly worn:"
  let palDead : List Nat × List (Nat × List Nat) :=
    ([1], [(8, [9]), (9, [8]), (8, [9])])
  ok := (← checkTrue
    "  stillness row — the palindromic deadlock survives its own observation unchanged (three held marks reading the same both ways: ONE sweep fixes it — even wear, the feather's signature at queue grain) while the non-palindromic pair is moved by every single sweep and comes home only at two"
    ((sweep palDead == palDead)
      && (sweep dead0 != dead0)
      && (sweep (sweep dead0) == dead0))) && ok
  let rested : List Nat × List (Nat × List Nat) := ([5, 6], [])
  ok := (← checkTrue
    "  stillness row — and the only other fixed point is the drained room (the empty queue rests, period one, exit 0: the station re-reads itself unchanged exactly when drained or palindromic-deadlocked — the cascade's quiescence characterized whole)"
    ((sweep rested == rested) && (sweep intake != intake))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchBraidVoices : IO Bool := do
  let mut ok := true
  IO.println "the braid's voices — no strand is first:"
  let uFirst : Nat := park heap (park heap (0 : Nat) [5, 9]) [3]
  let vFirst : Nat := park heap (park heap (0 : Nat) [3]) [5, 9]
  let woven : Nat := park heap (0 : Nat) [5, 3, 9]
  ok := (← checkTrue
    "  braid row — the weave starts with either strand (one braid, both decompositions, one seat: seventeen whether the pair or the single goes first) and the braid counts both strands whole (three marks from two and one)"
    ((uFirst == vFirst) && (uFirst == woven) && (woven == 17)
      && (([5, 3, 9] : List Nat).length
          == ([5, 9] : List Nat).length + ([3] : List Nat).length))) && ok
  return ok

set_option maxRecDepth 4096 in
def benchOdometer : IO Bool := do
  let mut ok := true
  IO.println "the odometer — the corridor at W=Bool, ticking:"
  let z3 : List Bool := [false, false, false]
  ok := (← checkTrue
    "  odometer row — the width-three register comes home at exactly its room's cap (eight ticks home, four ticks away at the far rung) and the ruler shows in the states: tick one touches rung zero, tick two reaches rung one, tick four reaches rung two — each doubling passes the carry one rung inward, hanoi's disk schedule"
    ((again inc 8 z3 == z3) && (again inc 4 z3 != z3)
      && (again inc 1 z3 == [true, false, false])
      && (again inc 2 z3 == [false, true, false])
      && (again inc 4 z3 == [false, false, true]))) && ok
  ok := (← checkTrue
    "  odometer row — the flip is the narrowest odometer (width one, period two: the kid's first wheel re-seated as the family's atom) and the split register multiplies its periods (widths two and one: caps four and two, the whole register winding at eight)"
    ((inc [true] == [false]) && (inc [false] == [true])
      && (roomCap 3 == roomCap 2 * roomCap 1))) && ok
  return ok

set_option maxRecDepth 4096 in
def main : IO UInt32 := do
  let mut ok := true
  ok := (← benchOpening) && ok
  ok := (← benchChronicle) && ok
  ok := (← benchTrajectory) && ok
  ok := (← benchPassenger) && ok
  ok := (← benchJourney) && ok
  ok := (← benchTick) && ok
  ok := (← benchFrontier) && ok
  ok := (← benchCensusStandsExact) && ok
  ok := (← benchArrow) && ok
  ok := (← benchGlass) && ok
  ok := (← benchTwoChannels) && ok
  ok := (← benchBlindfold) && ok
  ok := (← benchClosingPane) && ok
  ok := (← benchEscapee) && ok
  ok := (← benchMultiplexer) && ok
  ok := (← benchThirdChannel) && ok
  ok := (← benchGenerations) && ok
  ok := (← benchAudition) && ok
  ok := (← benchPrimes) && ok
  ok := (← benchFace) && ok
  ok := (← benchTwoHands) && ok
  ok := (← benchPromise) && ok
  ok := (← benchCorridorCurries) && ok
  ok := (← benchMeeting) && ok
  ok := (← benchReception) && ok
  ok := (← benchSpiral) && ok
  ok := (← benchOrigin) && ok
  ok := (← benchContact) && ok
  ok := (← benchCollatzClock) && ok
  ok := (← benchTable) && ok
  ok := (← benchMonologue) && ok
  ok := (← benchEarAndVoice) && ok
  ok := (← benchTwoKindsOfQuiet) && ok
  ok := (← benchDuet) && ok
  ok := (← benchScribe) && ok
  ok := (← benchCensusAndOrder) && ok
  ok := (← benchResearch) && ok
  ok := (← benchReplay) && ok
  ok := (← benchTower) && ok
  ok := (← benchAgain) && ok
  ok := (← benchMargin) && ok
  ok := (← benchWitness) && ok
  ok := (← benchRemoval) && ok
  ok := (← benchTurnstile) && ok
  ok := (← benchSpectrum) && ok
  ok := (← benchCitation) && ok
  ok := (← benchInitialization) && ok
  ok := (← benchIgnition) && ok
  ok := (← benchCascade) && ok
  ok := (← benchDeadlock) && ok
  ok := (← benchPen) && ok
  ok := (← benchWeave) && ok
  ok := (← benchDrawing) && ok
  ok := (← benchCircle) && ok
  ok := (← benchHundredth) && ok
  ok := (← benchGrounding) && ok
  ok := (← benchInterlock) && ok
  ok := (← benchCountermove) && ok
  ok := (← benchFlywheel) && ok
  ok := (← benchWell) && ok
  ok := (← benchCrown) && ok
  ok := (← benchApparat) && ok
  ok := (← benchDrainClock) && ok
  ok := (← benchKey) && ok
  ok := (← benchOneFace) && ok
  ok := (← benchCarriers) && ok
  ok := (← benchSimulations) && ok
  ok := (← benchLicense) && ok
  ok := (← benchCrossings) && ok
  ok := (← benchRetract) && ok
  ok := (← benchSettleSplits) && ok
  ok := (← benchCustomsFunctor) && ok
  ok := (← benchTwoFunctors) && ok
  ok := (← benchMediating) && ok
  ok := (← benchIsoTest) && ok
  ok := (← benchNonSections) && ok
  ok := (← benchModelingLoop) && ok
  ok := (← benchMutualRecords) && ok
  ok := (← benchConcord) && ok
  ok := (← benchAddressableGap) && ok
  ok := (← benchOneDisagreement) && ok
  ok := (← benchUniverseDiscipline) && ok
  ok := (← benchPortability) && ok
  ok := (← benchUniversalProperties) && ok
  ok := (← benchLadderSheds) && ok
  ok := (← benchLanded) && ok
  ok := (← benchUniformShift) && ok
  ok := (← benchTwoGauges) && ok
  ok := (← benchGaugeLadder) && ok
  ok := (← benchDarkType) && ok
  ok := (← benchAffordance) && ok
  ok := (← benchVestibule) && ok
  ok := (← benchSharedUnit) && ok
  ok := (← benchComposableMeasure) && ok
  ok := (← benchMagnitudes) && ok
  ok := (← benchTwoCharts) && ok
  ok := (← benchRulerAndWheel) && ok
  ok := (← benchSemiring) && ok
  ok := (← benchExactCures) && ok
  ok := (← benchServiceLadder) && ok
  ok := (← benchStillStation) && ok
  ok := (← benchBraidVoices) && ok
  ok := (← benchOdometer) && ok
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
