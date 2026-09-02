import Lean
open Lean Elab

def elabFrom (src : String) (name : String) (st : Option Command.State) : IO Command.State := do
  let ictx := Parser.mkInputContext src name
  let (hdr, ps, msgs) ← Parser.parseHeader ictx
  let cs ← match st with
    | some s => pure { s with messages := {} }
    | none =>
        let imports := headerToImports hdr
        let env ← importModules (if imports.isEmpty then #[{ module := `Init }] else imports) {} 0 (loadExts := true)
        pure (Command.mkState env msgs (({} : Options).setBool `Elab.async false))
  let s ← IO.processCommands ictx ps cs
  return s.commandState

/-- the namespaces a reading is about: the trail's own, and the imported ones whose
theorems the trail may cite (given as `ns` and a comma-separated `imports` arg) -/
structure Scope where
  ns : Name
  imported : List Name

def Scope.parse (args : List String) (i : Nat) : Scope :=
  let ns := (args[i]?).map String.toName |>.getD `Seed
  let imported := ((args[i+1]?).getD "").splitOn "," |>.filter (· ≠ "") |>.map String.toName
  ⟨ns, imported⟩

def Scope.owns (sc : Scope) (n : Name) : Bool :=
  n.getPrefix == sc.ns || sc.imported.any (fun m => n.getPrefix == m)

partial def usedTopLevel (env : Environment) (sc : Scope) (seen : NameSet) (n : Name) : NameSet := Id.run do
  let some ci := env.find? n | return seen
  let mut seen := seen
  let consts := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
  for c in consts do
    if seen.contains c then continue
    if sc.owns c then
      seen := seen.insert c
    else if (env.getModuleIdxFor? c).isNone then
      seen := usedTopLevel env sc (seen.insert c) c
  return seen

def nameOf (sc : Scope) (n : Name) : String :=
  if n.getPrefix == sc.ns then n.getString! else n.toString

def needsMode (trail : String) (sc : Scope) : IO Unit := do
  let st ← elabFrom (← IO.FS.readFile trail) trail none
  let env := st.env
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != sc.ns then continue
    if !ci.isTheorem then continue
    let used := usedTopLevel env sc {} n
    let deps := used.toList.filter (fun d => d != n && sc.owns d && (env.find? d).any (·.isTheorem))
    IO.println s!"{n.getString!} <- {" ".intercalate (deps.map (nameOf sc))}"

partial def usedInType (env : Environment) (sc : Scope) (seen : NameSet) (_n : Name) (e : Expr) : NameSet := Id.run do
  let mut seen := seen
  for c in e.getUsedConstants do
    if seen.contains c then continue
    if sc.owns c then
      seen := seen.insert c
    else if (env.getModuleIdxFor? c).isNone then
      match env.find? c with
      | some ci => seen := usedInType env sc (seen.insert c) c ci.type
      | none => pure ()
  return seen

/-- keys: the constants a theorem's TYPE uses. local theorems are listed bare; theorems of
the imported namespaces are listed too (prefixed `import`), so a domain's vacancies may
cite the trunk they stand on -/
def keysMode (trail : String) (sc : Scope) : IO Unit := do
  let st ← elabFrom (← IO.FS.readFile trail) trail none
  let env := st.env
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != sc.ns || !ci.isTheorem then continue
    let used := usedInType env sc {} n ci.type
    let ks := used.toList.filter (fun d => d != n && sc.owns d)
    IO.println s!"{n.getString!} <- {" ".intercalate (ks.map (nameOf sc))}"
  if !sc.imported.isEmpty then
    for (n, ci) in env.constants.toList do
      if !(sc.imported.any (fun m => n.getPrefix == m)) || !ci.isTheorem then continue
      let used := usedInType env sc {} n ci.type
      let ks := used.toList.filter (fun d => d != n && sc.owns d)
      IO.println s!"import {n} <- {" ".intercalate (ks.map (nameOf sc))}"

def citesMode (trail : String) (sc : Scope) : IO Unit := do
  let st ← elabFrom (← IO.FS.readFile trail) trail none
  let env := st.env
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != sc.ns then continue
    let used := usedTopLevel env sc {} n
    let deps := used.toList.filter (fun d => d != n && sc.owns d)
    let kind := if ci.isTheorem then "theorem" else "carrier"
    IO.println s!"{kind} {n.getString!} <- {" ".intercalate (deps.map (nameOf sc))}"

partial def stripLams : Expr → Expr
  | .lam _ _ b _ => stripLams b
  | e => e

partial def usedAll (env : Environment) (ns : Name) (seen : NameSet) (n : Name) : NameSet := Id.run do
  let some ci := env.find? n | return seen
  let mut seen := seen
  let consts := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
  for c in consts do
    if seen.contains c then continue
    seen := seen.insert c
    if (env.getModuleIdxFor? c).isNone && c.getPrefix != ns then
      seen := usedAll env ns seen c
  return seen

def censusMode (trail : String) (sc : Scope) : IO Unit := do
  let st ← elabFrom (← IO.FS.readFile trail) trail none
  let env := st.env
  let ns := sc.ns
  let reflHeads : List Name := [`Eq.refl, `rfl, `Iff.refl, `Iff.rfl, `HEq.refl, `HEq.rfl]
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != ns || !ci.isTheorem then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let body := stripLams v
    let head := body.getAppFn.constName?
    let isRefl := head.any reflHeads.contains
    let used := usedAll env ns {} n
    let names := used.toList
    let isRec := names.any (fun c =>
      let s := c.getString!
      (s == "brecOn" || s == "rec" || s == "recOn") &&
        !(c.getPrefix == `Eq || c.getPrefix == `HEq || c.getPrefix == `Acc || c.getPrefix == `WellFounded))
    let isCases := names.any (fun c =>
      let s := c.getString!
      s == "casesOn" || s.startsWith "match_")
    let cites := names.any (fun c => c != n && c.getPrefix == ns && (env.find? c).any (·.isTheorem))
    let cls := if isRefl then "rfl" else if isRec then "induction" else if isCases then "cases" else if cites then "citation" else "term"
    IO.println s!"{n.getString!} {cls}"

unsafe def main (args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let sc := Scope.parse args 2
  if args.head? == some "needs" then
    needsMode args[1]! sc
    return
  if args.head? == some "cites" then
    citesMode args[1]! sc
    return
  if args.head? == some "keys" then
    keysMode args[1]! sc
    return
  if args.head? == some "census" then
    censusMode args[1]! sc
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
