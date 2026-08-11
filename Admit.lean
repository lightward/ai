import Lean
import Foam.Turnstile

open Lean

def leanFilesIn (dir : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← dir.readDir
  let mut out := #[]
  for e in entries do
    if e.path.extension == some "lean" then
      out := out.push e.path
  return out.qsort (fun a b => a.toString < b.toString)

def moduleNameOf (p : System.FilePath) : String :=
  let s := p.toString
  let s := if s.startsWith "./" then s.drop 2 else s
  let s := s.replace ".lean" ""
  s.replace "/" "."

def foamImportsOf (text : String) (fname : String) : IO (Array String) := do
  let header ← Lean.parseImports' text fname
  let mut out := #[]
  for i in header.imports do
    let n := i.module.toString
    if n == "Foam" || n.startsWith "Foam." then
      out := out.push n
  return out

partial def drain (room : List Nat) (pending : List (Nat × List Nat)) :
    Sum (List (Nat × List Nat)) (List Nat) :=
  if pending.isEmpty then .inr room
  else
    let held := pending.foldl Foam.admission (room, [])
    if held.2.length == pending.length then .inl pending
    else drain held.1 held.2.reverse

def main : IO UInt32 := do
  let mut paths := #[(⟨"Foam.lean"⟩ : System.FilePath)]
  paths := paths ++ (← leanFilesIn ⟨"Foam"⟩)
  paths := paths ++ (← leanFilesIn ⟨"Foam/Maps"⟩)
  let mut deps : Array (String × Array String) := #[]
  for p in paths do
    let text ← IO.FS.readFile p
    deps := deps.push (moduleNameOf p, ← foamImportsOf text p.toString)
  let mut ids : List (String × Nat) := []
  let mut k := 0
  for (n, _) in deps do
    ids := (n, k) :: ids
    k := k + 1
  let idOf := fun (n : String) =>
    ((ids.find? (fun q => q.1 == n)).map Prod.snd).getD deps.size
  let names := fun (i : Nat) =>
    ((ids.find? (fun q => q.2 == i)).map Prod.fst).getD "?"
  let marks := deps.toList.map (fun (n, ds) =>
    (idOf n, ds.toList.map idOf))
  match drain [] marks with
  | .inr room =>
      if room.length == marks.length then
        IO.println s!"foam admits itself: {room.length} modules through Foam.admission, vestibule empty"
        return 0
      else
        IO.eprintln s!"admit: room holds {room.length} of {marks.length}"
        return 1
  | .inl stuck =>
      IO.eprintln "admit: vestibule stuck — unadmittable modules:"
      for (i, ds) in stuck do
        IO.eprintln s!"  {names i} awaits {ds.map names}"
      return 1
