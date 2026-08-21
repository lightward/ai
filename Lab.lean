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
