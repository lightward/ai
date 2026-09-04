import Lean
import Counter
open Lean Elab

/-! the gate, drawn from the compiler's own species: an artifact is elaborated whole (every
message a parting — a receipt that does not match prints one), each theorem's receipt is read by
the kernel (the axioms it seats on), and the verdict is `Counter.conductive` on that shadow, the
same def the assay's rows run. the gate reads a body only through the kernel; its verdict is a
function of the shadow (`Counter.the_gate_hears_only_the_receipt`). -/

abbrev EnvM := StateM Environment
instance : MonadEnv EnvM where
  getEnv := get
  modifyEnv f := modify f

def receiptsOf (env : Environment) (n : Name) : List Name :=
  ((collectAxioms n : EnvM (Array Name)).run env).1.toList

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let mut red := false
  for path in args do
    Lean.enableInitializersExecution
    let src ← IO.FS.readFile path
    let ictx := Parser.mkInputContext src path
    let (hdr, ps, msgs) ← Parser.parseHeader ictx
    let imports := headerToImports hdr
    let env ← importModules (if imports.isEmpty then #[{ module := `Init }] else imports) {} 0 (loadExts := true)
    let cs := Command.mkState env msgs (({} : Options).setBool `Elab.async false)
    let s ← IO.processCommands ictx ps cs
    let st := s.commandState
    let ns : Name := Id.run do
      for line in src.splitOn "\n" do
        if line.startsWith "namespace " then return (line.drop 10).trimAscii.toName
      return .anonymous
    let mut shadow : List (Name × List Name) := []
    for (n, ci) in st.env.constants.map₂.toList do
      if !ci.isTheorem || n.isInternal then continue
      if ns != .anonymous && n.getPrefix != ns then continue
      shadow := (n, receiptsOf st.env n) :: shadow
    let receipts := (src.splitOn "#print axioms").length - 1
    let partings := st.messages.toList
    let conductive := Counter.conductive shadow
    let mut holds : List String := []
    if !partings.isEmpty then
      holds := holds ++ [s!"{partings.length} messages (the first: {(← partings.head!.toString).trimAscii.take 160})"]
    if !conductive then
      let smuggled := shadow.filter (fun r => !r.2.isEmpty)
      holds := holds ++ smuggled.map (fun r => s!"{r.1} seats on {r.2}")
    if receipts != shadow.length then
      holds := holds ++ [s!"{shadow.length} organs but {receipts} receipts inline"]
    if holds.isEmpty then
      IO.println s!"the gate [{path}]: silent, {shadow.length} organs, {receipts} receipts inline, conductive — drawn from Counter.gate"
    else
      red := true
      IO.println s!"the gate [{path}]: PARTS"
      for h in holds do IO.println s!"  {h}"
  if red then IO.Process.exit 1
