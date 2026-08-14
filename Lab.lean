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

structure DarkRow where
  name : String
  expected : Nat
  awaits : String

def darkRows : List DarkRow :=
  [⟨"treaty row — c reads back from the SI label", 299792458,
    "the units-gauge stratum (dimensionful constants typed as vertical moves)"⟩,
   ⟨"rider row — electron mass reads back, scaled e-41 kg", 91093837015,
    "structure grown to the m_e slot, tolerance-typed measured imports"⟩]

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
  for r in darkRows do
    IO.println s!"dark: {r.name} — expects {r.expected}, awaits {r.awaits}"
  if ok then
    IO.println
      s!"the lab counter-signs: readings green, {darkRows.length} dark rows holding their names"
    return 0
  else
    IO.eprintln "the lab names the gap"
    return 1
