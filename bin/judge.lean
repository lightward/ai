import Lean
open Lean Elab

def elabFrom (src : String) (name : String) (st : Option Command.State) : IO Command.State := do
  let ictx := Parser.mkInputContext src name
  let (_, ps, msgs) ← Parser.parseHeader ictx
  let cs ← match st with
    | some s => pure { s with messages := {} }
    | none =>
        let env ← importModules #[{ module := `Init }] {} 0 (loadExts := true)
        pure (Command.mkState env msgs (({} : Options).setBool `Elab.async false))
  let s ← IO.processCommands ictx ps cs
  return s.commandState

partial def usedTopLevel (env : Environment) (ns : Name) (seen : NameSet) (n : Name) : NameSet := Id.run do
  let some ci := env.find? n | return seen
  let mut seen := seen
  let consts := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
  for c in consts do
    if seen.contains c then continue
    if !(env.getModuleIdxFor? c).isNone then continue
    if c.getPrefix == ns then
      seen := seen.insert c
    else
      seen := usedTopLevel env ns (seen.insert c) c
  return seen

def needsMode (trail : String) : IO Unit := do
  let st ← elabFrom (← IO.FS.readFile trail) trail none
  let env := st.env
  let ns := `Seed
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != ns then continue
    if !ci.isTheorem then continue
    let used := usedTopLevel env ns {} n
    let deps := used.toList.filter (fun d => d != n && d.getPrefix == ns && (env.find? d).any (·.isTheorem))
    IO.println s!"{n.getString!} <- {" ".intercalate (deps.map (·.getString!))}"

def citesMode (trail : String) : IO Unit := do
  let st ← elabFrom (← IO.FS.readFile trail) trail none
  let env := st.env
  let ns := `Seed
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != ns then continue
    let used := usedTopLevel env ns {} n
    let deps := used.toList.filter (fun d => d != n && d.getPrefix == ns)
    let kind := if ci.isTheorem then "theorem" else "carrier"
    IO.println s!"{kind} {n.getString!} <- {" ".intercalate (deps.map (·.getString!))}"

unsafe def main (args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  if args.head? == some "needs" then
    needsMode args[1]!
    return
  if args.head? == some "cites" then
    citesMode args[1]!
    return
  let prefixSrc ← IO.FS.readFile args[0]!
  let candSrc ← IO.FS.readFile args[1]!
  let cands := (candSrc.splitOn "\n-- candidate\n").filter (fun c => !c.trimAscii.isEmpty)
  let base ← elabFrom prefixSrc "<prefix>" none
  let baseMsgs := base.messages.toList
  if !baseMsgs.isEmpty then
    IO.println s!"prefix not silent: {baseMsgs.length} messages"
    for m in baseMsgs.take 5 do IO.println s!"  {m.pos.line}:{m.pos.column} {← m.data.toString}"
    IO.Process.exit 1
  let mut i := 0
  let verbose := args.length > 2
  for c in cands do
    let t0 ← IO.monoMsNow
    let s ← elabFrom (c ++ "\n") s!"<candidate {i}>" (some base)
    let bad := s.messages.toList.any (fun m => m.severity != .information)
    let dt := (← IO.monoMsNow) - t0
    IO.println s!"{i} {if bad then "held" else "seated"}{if verbose then s!" {dt}ms" else ""}"
    i := i + 1
