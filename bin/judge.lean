import Lean
import Pieces
open Lean Elab

def elabFrom (src : String) (name : String) (st : Option Command.State) (extra : Array Import := #[]) : IO Command.State := do
  let ictx := Parser.mkInputContext src name
  let (hdr, ps, msgs) ← Parser.parseHeader ictx
  let cs ← match st with
    | some s => pure { s with messages := {} }
    | none =>
        let imports := headerToImports hdr ++ extra
        let env ← importModules (if imports.isEmpty then #[{ module := `Init }] else imports) {} 0 (loadExts := true)
        pure (Command.mkState env msgs (({} : Options).setBool `Elab.async false))
  let s ← IO.processCommands ictx ps cs
  return s.commandState

/-- the same, keeping every command's syntax: a body as Syntax, not a string -/
def elabCommands (src : String) (name : String) : IO (Command.State × Array Syntax) := do
  let ictx := Parser.mkInputContext src name
  let (hdr, ps, msgs) ← Parser.parseHeader ictx
  let env ← importModules (headerToImports hdr) {} 0 (loadExts := true)
  let cs := Command.mkState env msgs (({} : Options).setBool `Elab.async false)
  let s ← IO.processCommands ictx ps cs
  return (s.commandState, s.commands)

/-- the namespaces a reading is about: the trail's own, and the imported ones whose
theorems the trail may cite (given as `ns` and a comma-separated `imports` arg) -/
structure Scope where
  ns : Name
  imported : List Name

def Scope.parse (args : List String) (i : Nat) : Scope :=
  let ns := (args[i]?).map String.toName |>.getD `Foam
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

partial def codomain : Expr → Expr
  | .forallE _ _ b _ => codomain b
  | e => e

/-- kinds: every carrier (non-theorem) of the namespace with the sort of its codomain —
`prop` (a relation; no `#guard` row can decide it, its theorems are its treaty), `sort`
(a type; rows evaluate its inhabitants, never the name), or `data` (a row can compute it) -/
def kindsMode (trail : String) (sc : Scope) : IO Unit := do
  let st ← elabFrom (← IO.FS.readFile trail) trail none
  let env := st.env
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != sc.ns || ci.isTheorem then continue
    let k := match codomain ci.type with
      | .sort l => if l == Level.zero then "prop" else "sort"
      | _ => "data"
    IO.println s!"{n.getString!} {k}"

/-- a body as a SHAPE: every name that is a theorem of the house, or resolves to nothing in the
environment (a binder, a hypothesis, a name `intro` or `cases` brought in), becomes a hole `?`;
the theorem's own name (a structural recursion's call) becomes `?self`; carriers, constructors,
and core stay — they are what the shape is about. two bodies with one shape are one shape -/
partial def abstractSyntax (env : Environment) (sc : Scope) (self : Name) (stx : Syntax) : Syntax :=
  match stx with
  | .ident info _ n _ =>
    if n.isAnonymous then stx else
    let resolves := [n, sc.ns ++ n] ++ sc.imported.map (· ++ n)
    let found := resolves.filterMap env.find?
    if n == self || sc.ns ++ n == self then mkIdent (Name.mkSimple "?self")
    else if found.isEmpty then mkIdent (Name.mkSimple "?")
    else if found.any (·.isTheorem) && found.any (fun ci => sc.owns ci.name) then mkIdent (Name.mkSimple "?")
    else .ident info (toString n).toRawSubstring n []
  | .node i k args =>
    -- a field (`.trans`, `.1`) and a hygiene mark are structure, not names
    if k == `hygieneInfo then stx
    else if k == ``Lean.Parser.Term.proj then .node i k (args.modify 0 (abstractSyntax env sc self))
    else .node i k (args.map (abstractSyntax env sc self))
  | _ => stx

def squeeze (s : String) : String :=
  (" ".intercalate ((s.splitOn " ").filter (· ≠ ""))).replace "\n" " "

/-- shapes: every theorem's body abstracted, then the census of shapes — how many bodies each
shape covers, which is what bodies-as-shapes can carry -/
def shapesMode (trail : String) (sc : Scope) : IO Unit := do
  let (st, cmds) ← elabCommands (← IO.FS.readFile trail) trail
  let env := st.env
  let mut rows : Array (Name × String × String) := #[]
  for c in cmds do
    if !c.isOfKind ``Lean.Parser.Command.declaration then continue
    let d := c[1]
    if !d.isOfKind ``Lean.Parser.Command.theorem then continue
    let name := sc.ns ++ d[1][0].getId
    let val := d[3]
    let mode := if val.isOfKind ``Lean.Parser.Command.declValSimple then
                  (if val[1].isOfKind ``Lean.Parser.Term.byTactic then "tactic" else "term")
                else "equations"
    let body := if val.isOfKind ``Lean.Parser.Command.declValSimple then val[1] else val
    let shape := squeeze ((abstractSyntax env sc name body).reprint.getD "<no reprint>")
    rows := rows.push (name, mode, shape)
  let mut groups : Std.HashMap String (Array Name) := {}
  for (n, m, sh) in rows do
    let key := m ++ "\t" ++ sh
    groups := groups.insert key ((groups.getD key #[]).push n)
  let sorted := groups.toArray.qsort (fun a b => a.2.size > b.2.size)
  IO.println s!"the shapes: {rows.size} bodies, {sorted.size} shapes"
  for (key, names) in sorted do
    let parts := key.splitOn "\t"
    IO.println s!"{names.size}\t{parts.headD ""}\t{(parts.getD 1 "").take 160}"
    if names.size > 1 then IO.println s!"\t\t{" ".intercalate (names.map (fun n => n.getString!)).toList}"

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
  if args.head? == some "census" then
    censusMode args[1]! sc
    return
  if args.head? == some "kinds" then
    kindsMode args[1]! sc
    return
  if args.head? == some "shapes" then
    shapesMode args[1]! sc
    return
  if args.head? == some "pieces" then
    -- the pieces in the order the crawl offers them, and the knobs, read from bin/Pieces.lean
    IO.println s!"budget {Pieces.budget}"
    IO.println s!"reach {Pieces.reach}"
    for (n, t) in Pieces.pieces do IO.println s!"{n}\t{t}"
    return
  let prefixSrc ← IO.FS.readFile args[0]!
  let candSrc ← IO.FS.readFile args[1]!
  let cands := (candSrc.splitOn "\n-- candidate\n").filter (fun c => !c.trimAscii.isEmpty)
  -- a trial imports the pieces; the artifact never does (the judge reports each seated body expanded)
  let base ← elabFrom prefixSrc "<prefix>" none #[{ module := `Pieces }]
  let baseMsgs := base.messages.toList
  if !baseMsgs.isEmpty then
    IO.println s!"prefix not silent: {baseMsgs.length} messages"
    for m in baseMsgs.take 5 do IO.println s!"  {m.pos.line}:{m.pos.column} {← m.data.toString}"
    IO.Process.exit 1
  let mut i := 0
  let verbose := args.length > 2
  let sentences := args.length > 2 && args[2]! == "vv"
  for c in cands do
    let t0 ← IO.monoMsNow
    let s ← elabFrom ("#seat " ++ c ++ "\n") s!"<candidate {i}>" (some base)
    let msgs := s.messages.toList
    let bad := msgs.any (fun m => m.severity != .information)
    let dt := (← IO.monoMsNow) - t0
    IO.println s!"{i} {if bad then "held" else "seated"}{if verbose then s!" {dt}ms" else ""}"
    if !bad then
      -- the body as elaborated, pieces expanded: one line per line, each behind `| `
      for m in msgs do
        if m.severity == .information then
          let txt ← m.data.toString
          for l in txt.splitOn "\n" do IO.println s!"| {l}"
    if sentences && bad then
      for m in msgs do
        if m.severity != .information then
          let txt ← m.data.toString
          for l in (txt.splitOn "\n").take 24 do
            IO.println s!"    {l}"
    i := i + 1
