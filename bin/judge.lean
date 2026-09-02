import Lean
open Lean Elab

def elabFrom (src : String) (name : String) (st : Option Command.State) : IO Command.State := do
  let ictx := Parser.mkInputContext src name
  let (_, ps, msgs) ← Parser.parseHeader ictx
  let cs ← match st with
    | some s => pure { s with messages := {} }
    | none =>
        let env ← importModules #[{ module := `Init }] {} 0 (loadExts := true)
        pure (Command.mkState env msgs {})
  let s ← IO.processCommands ictx ps cs
  return s.commandState

unsafe def main (args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
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
