import Lean

open Lean

def leanFilesIn (dir : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← dir.readDir
  let mut out := #[]
  for e in entries do
    if e.path.extension == some "lean" then
      out := out.push e.path
  return out.qsort (fun a b => a.toString < b.toString)

def foamImportsOf (text : String) (fname : String) : IO (Array String) := do
  let header ← Lean.parseImports' text fname
  let mut out := #[]
  for i in header.imports do
    let n := i.module.toString
    if n == "Foam" || n.startsWith "Foam." then
      out := out.push n
  return out

def moduleNameOf (p : System.FilePath) : String :=
  let s := p.toString
  let s := if s.startsWith "./" then s.drop 2 else s
  let s := s.replace ".lean" ""
  s.replace "/" "."

def stripImports (text : String) : String :=
  let lines := text.splitOn "\n"
  let kept := lines.filter (fun l => !(l.startsWith "import "))
  let rec dropLeadingBlanks : List String → List String
    | [] => []
    | l :: ls =>
        if l.isEmpty || l.all (fun c => c == ' ') then dropLeadingBlanks ls
        else l :: ls
  String.intercalate "\n" (dropLeadingBlanks kept)

def main : IO UInt32 := do
  let mut paths := #[⟨"Foam.lean"⟩]
  paths := paths ++ (← leanFilesIn ⟨"Foam"⟩)
  paths := paths ++ (← leanFilesIn ⟨"Foam/Maps"⟩)
  let mut pending := #[]
  for p in paths do
    let text ← IO.FS.readFile p
    let deps ← foamImportsOf text p.toString
    pending := pending.push (moduleNameOf p, text, deps)
  let mut room : Array String := #[]
  let mut emitted := ""
  let mut progress := true
  while progress && room.size < pending.size do
    progress := false
    for (name, text, deps) in pending do
      if !(room.contains name) && deps.all room.contains then
        room := room.push name
        emitted := emitted ++ stripImports text ++ "\n"
        progress := true
  if room.size < pending.size then
    IO.eprintln "transcribe: vestibule nonempty — unadmittable modules:"
    for (name, _, deps) in pending do
      if !(room.contains name) then
        IO.eprintln s!"  {name} awaits {deps.filter (fun d => !(room.contains d))}"
    return 1
  IO.print emitted
  return 0
