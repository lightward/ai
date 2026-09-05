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
def elabCommands (src : String) (name : String) (extra : Array Import := #[]) : IO (Command.State × Array Syntax) := do
  let ictx := Parser.mkInputContext src name
  let (hdr, ps, msgs) ← Parser.parseHeader ictx
  let env ← importModules (headerToImports hdr ++ extra) {} 0 (loadExts := true)
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
    IO.println s!"\t\t{" ".intercalate (names.map (fun n => n.getString!)).toList}"

/-- a body as a PIECE: the searches' winners inverted. every recorded citation form — `(apply T <;> …)`,
`(apply (T _).trans (by …) <;> …)`, `(rw [T]; …)`, `exact T …`, a cited application in a term —
becomes the search that found it; the carriers a `dsimp only` unfolds become the vacancy's own
(`{defs}`); the theorem's own name becomes `{self}`; locals, constructors, and core stay verbatim.
what is left citing a theorem after that is a hole no search reaches, and the body is unrendered -/
def isCite (env : Environment) (sc : Scope) (n : Name) : Bool :=
  if n.isAnonymous then false else
  let found := ([n, sc.ns ++ n] ++ sc.imported.map (· ++ n)).filterMap env.find?
  found.any (·.isTheorem) && found.any (fun ci => sc.owns ci.name)

partial def citesAny (env : Environment) (sc : Scope) : Syntax → Bool
  | .ident _ _ n _ => isCite env sc n
  | .node _ _ args => args.any (citesAny env sc)
  | _ => false

def placeholder (s : String) : Syntax :=
  Syntax.ident SourceInfo.none s.toRawSubstring (Name.mkSimple s) []

def seqItems (seq : Syntax) : Array Syntax := Id.run do
  if seq.getKind == ``Lean.Parser.Tactic.tacticSeq && seq[0].getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
    let args := seq[0][0].getArgs
    let mut out := #[]
    for i in [0:args.size] do
      if i % 2 == 0 then out := out.push args[i]!
    return out
  else return #[]

/-- a piece of syntax parsed from its text — the trail elaborated with the pieces imported, so the
searches' names are tokens -/
def parseAs (env : Environment) (cat : Name) (s : String) : Syntax :=
  match Parser.runParserCategory env cat s with
  | .ok x => x
  | .error _ => .missing

def isChainHead (e : Syntax) : Bool :=
  e.isOfKind ``Lean.Parser.Term.app && e[0].isOfKind ``Lean.Parser.Term.proj && e[0][2].getId == `trans

/-- the leftmost name of a term: the head of an application, a projection, a paren -/
partial def headName : Syntax → Option Name
  | .ident _ _ n _ => some n
  | stx =>
    if stx.isOfKind ``Lean.Parser.Term.app || stx.isOfKind ``Lean.Parser.Term.proj then headName stx[0]
    else if stx.isOfKind ``Lean.Parser.Term.paren then headName stx[1]
    else none

/-- the statement's own binder names — the parameters and named hypotheses a search at the goal
reads from the local context: the names in binder position, in the signature's binders and its ∀s -/
partial def sigBinders (stx : Syntax) : NameSet :=
  match stx with
  | .node _ k args =>
    let here : NameSet :=
      if k == ``Lean.Parser.Term.explicitBinder || k == ``Lean.Parser.Term.implicitBinder
          || k == ``Lean.Parser.Term.strictImplicitBinder || k == ``Lean.Parser.Term.instBinder then
        stx[1].getArgs.foldl (fun acc a => if a.isIdent then acc.insert a.getId else acc) {}
      else if k == ``Lean.Parser.Term.forall then
        stx[1].getArgs.foldl (fun acc a =>
          if a.isIdent then acc.insert a.getId
          else if a.getKind == ``Lean.Parser.Term.binderIdent && a[0].isIdent then acc.insert a[0].getId
          else acc) {}
      else {}
    args.foldl (fun acc a => acc.union (sigBinders a)) here
  | _ => {}

partial def render (env : Environment) (sc : Scope) (self : Name) (hyps : NameSet) (stx : Syntax) : Syntax :=
  let seek := parseAs env `tactic "piece_seek"
  let hole := parseAs env `term "(by piece_seek)"
  -- a citation or a statement hypothesis AT THE HEAD of a term is what a search at the goal finds;
  -- one deeper inside a term is reached by the rules below at its own position, and the term's
  -- structure around it stays
  let cites (s : Syntax) := (headName s).any fun n => isCite env sc n || hyps.contains n
  let rec rwCites (s : Syntax) : Bool := match s with
    | .node _ k args => (k == ``Lean.Parser.Tactic.rwRule && args.size > 0 && cites args[args.size - 1]!) || args.any rwCites
    | _ => false
  -- the closer after a rewrite or a chain is kept beside the generic ones: an exemplar's own
  -- closing move is a move the search may need
  let seekWith (kind : String) (closer : Syntax) : Syntax :=
    let c := ((render env sc self hyps closer).reprint.getD "").trimAscii.toString
    let flat := " ".intercalate (((c.replace "\n" " ").splitOn " ").filter (· ≠ ""))
    let own := if flat == "rfl" || flat == "assumption" || flat == "piece_seek" || flat.isEmpty then "" else s!" | {flat}"
    parseAs env `tactic s!"{kind} (first | rfl | assumption{own} | piece_seek)"
  -- a replacement keeps the whitespace the original ended in, so the layout it sat in survives
  let put (new : Syntax) : Syntax := new.setTailInfo stx.getTailInfo
  let isSelf (s : Syntax) := s.isIdent && (s.getId == self || sc.ns ++ s.getId == self)
  match stx with
  | .ident _ _ n _ =>
    if n == self || sc.ns ++ n == self then put (placeholder "{self}")
    else if citesAny env sc stx then put hole else stx
  | .node i k args =>
    -- a parenthesized winner: `(apply e <;> side)`, `(rw [t]; closers)`
    let items := if k == ``Lean.Parser.Tactic.paren then seqItems stx[1] else #[]
    if items.size == 1 && items[0]!.isOfKind ``Lean.Parser.Tactic.«tactic_<;>_»
        && items[0]![0].isOfKind ``Lean.Parser.Tactic.apply && cites items[0]![0][1] then
      let target := items[0]![0][1]
      if isChainHead target then
        -- `(apply (T _).trans (by C) <;> …)`: the chain's far end is C
        let far := target[1][0]
        let closer := if far.isOfKind ``Lean.Parser.Term.paren && far[1].isOfKind ``Lean.Parser.Term.byTactic then far[1][1] else far
        put (seekWith "piece_chain_seek" closer)
      else put seek
    else if items.size == 2 && items[0]!.isOfKind ``Lean.Parser.Tactic.rwSeq && rwCites items[0]! then
      put (seekWith "piece_rw_seek" items[1]!)
    else if k == ``Lean.Parser.Tactic.exact && cites stx[1] && !(citesAny env sc stx[1] && isSelf stx[1][0]) then put seek
    -- the carriers unfolded are the vacancy's own
    else if k == ``Lean.Parser.Tactic.dsimp then
      let args := args.map fun a =>
        if a.getKind == `null && a.getNumArgs == 3 && a[0].isAtom && a[0].getAtomVal == "[" then
          a.setArg 1 (mkNullNode #[placeholder "{defs}"])
        else a
      .node i k args
    -- a cited application in a term: the hole, searched where the term determines its type
    else if k == ``Lean.Parser.Term.app && stx[0].isIdent && citesAny env sc stx[0] && !isSelf stx[0] then put hole
    else
      let args := args.map (render env sc self hyps)
      -- a fan whose alternatives rendered alike keeps one of each
      if k == ``Lean.Parser.Tactic.first && args.size == 2 then
        let groups := args[1]!.getArgs
        let kept := groups.foldl (fun (acc : Array Syntax) g =>
          if acc.any (fun x => x.reprint == g.reprint) then acc else acc.push g) #[]
        .node i k #[args[0]!, args[1]!.setArgs kept]
      else .node i k args
  | _ => stx

/-- a fan blanked: every `first` node's alternatives replaced by one mark, so two bodies that
differ only in which branch closed which goal read as one SKELETON -/
partial def blankFans (stx : Syntax) : Syntax :=
  match stx with
  | .node i k args =>
    if k == ``Lean.Parser.Tactic.first && args.size == 2 then
      .node i k #[args[0]!, mkNullNode #[placeholder "…"]]
    else .node i k (args.map blankFans)
  | _ => stx

/-- a token's trailing whitespace replaced -/
def withTrailing (stx : Syntax) (ws : String) : Syntax :=
  match stx.getTailInfo with
  | .original lead pos _ endPos => stx.setTailInfo (.original lead pos ws.toRawSubstring endPos)
  | _ => stx

/-- the fans of one skeleton unioned: at each `first`, every alternative any member of the group
ran, the most-run first (ties in the order met); outside the fans the members agree by
construction. an alternative is read squeezed to one line — a recorded winner is parenthesized,
and inside parens the layout is position-free — and the fan is re-parsed from its text; a fan
with an alternative that cannot be squeezed keeps its own -/
partial def unionFans (env : Environment) (e : Syntax) (others : Array Syntax) : Syntax :=
  match e with
  | .node i k args =>
    if k == ``Lean.Parser.Tactic.first && args.size == 2 then
      let all := (#[e] ++ others).flatMap fun o => if o.getKind == k && o.getNumArgs == 2 then o[1].getArgs else #[]
      let flat (s : String) : String := " ".intercalate (((s.replace "\n" " ").splitOn " ").filter (· ≠ ""))
      let texts := all.map fun g => flat (g[1].reprint.getD "")
      let unsqueezable := all.any fun g =>
        let t := (g[1].reprint.getD "").trimAscii.toString
        t.contains '\n' && !t.startsWith "("
      if unsqueezable then .node i k args else
      let distinct := texts.foldl (fun (acc : Array (String × Nat × Nat)) s =>
        match acc.findIdx? (·.1 == s) with
        | some j => acc.modify j (fun (s, n, ix) => (s, n + 1, ix))
        | none => acc.push (s, 1, acc.size)) #[]
      let sorted := distinct.qsort fun a b => a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)
      let text := "first " ++ " ".intercalate (sorted.map fun (s, _, _) => "| " ++ s).toList
      let parsed := parseAs env `tactic text
      if parsed.isMissing then .node i k args else parsed.setTailInfo e.getTailInfo
    else
      let args := args.mapIdx fun j a => unionFans env a (others.filterMap fun o => if o.getNumArgs > j then some o[j] else none)
      .node i k args
  | _ => e

/-- templates: every theorem's body as a piece, one exemplar per skeleton with its fans unioned, in
census order — the pieces list derived from the bodies in scope. a line per piece: count, mode,
exemplar, template (newlines as ⏎); a body that still cites where no search reaches is unrendered -/
def templatesMode (trail : String) (sc : Scope) : IO Unit := do
  let source ← IO.FS.readFile trail
  let (st, cmds) ← elabCommands source trail #[{ module := `Pieces }]
  let env := st.env
  let mut rows : Array (Name × String × Syntax) := #[]
  let mut unrendered : Array Name := #[]
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
    let r := render env sc name (sigBinders d[2]) body
    if citesAny env sc r then unrendered := unrendered.push name
    else rows := rows.push (name, mode, r)
  let mut groups : Std.HashMap String (Array (Name × Syntax)) := {}
  let mut order : Array String := #[]
  for (n, m, r) in rows do
    let key := m ++ "\t" ++ ((blankFans r).reprint.getD "").trimAscii.toString
    if !groups.contains key then order := order.push key
    groups := groups.insert key ((groups.getD key #[]).push (n, r))
  let sorted := (order.map fun k => (k, groups.getD k #[])).qsort (fun a b => a.2.size > b.2.size)
  IO.println s!"the templates: {rows.size + unrendered.size} bodies, {sorted.size} pieces; {unrendered.size} unrendered: {" ".intercalate (unrendered.map (·.getString!)).toList}"
  for (key, members) in sorted do
    let mode := (key.splitOn "\t").headD ""
    let (exemplar, r) := members[0]!
    let t := unionFans env r (members.extract 1 members.size |>.map (·.2))
    let tpl := (t.reprint.getD "").trimAscii.toString.replace "\n" "⏎"
    IO.println s!"{members.size}\t{mode}\t{exemplar.getString!}\t{tpl}"

/-- the component of a tuple a projection chain reads: `x.1` is 0, `x.2.1` is 1, a bare `x.2.2` is
the last (`snd` all the way down ends in the last component) -/
partial def compDepth (b : Expr) (k : Nat) : Option Nat :=
  if b.isAppOfArity ``Prod.snd 3 then compDepth (b.getArg! 2) (k + 1)
  else if b.isAppOfArity ``Prod.fst 3 then some k
  else if b.isBVar then some k
  else none

/-- a literal list's elements, as constant names -/
partial def listItems (e : Expr) : Option (List Name) :=
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then
    match (e.getArg! 1).getAppFn.constName?, listItems (e.getArg! 2) with
    | some c, some rest => some (c :: rest) | _, _ => none
  else none

/-- an enum, by name -/
def isEnumName (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo ii) => !ii.isRec && ii.ctors.all fun c => match env.find? c with
    | some (.ctorInfo ci) => ci.numFields == 0 | _ => false
  | _ => false

/-- an enum's SQL type: its short name in snake case -/
def enumSQL (n : Name) : String := Id.run do
  let mut out := ""
  for c in n.getString!.toList do
    if c.isUpper then out := out ++ (if out.isEmpty then "" else "_") ++ toString c.toLower else out := out.push c
  return out

/-- a literal list: the cons chain to its nil, with the element type -/
partial def listLiteral? (e : Expr) : Option (List Expr × Expr) :=
  if e.isAppOfArity ``List.nil 1 then some ([], e.getArg! 0)
  else if e.isAppOfArity ``List.cons 3 then
    (listLiteral? (e.getArg! 2)).map fun (xs, t) => (e.getArg! 1 :: xs, t)
  else none

/-- a column name Postgres would refuse bare gets a trailing underscore; the drawer and the
translator apply the same rule -/
def reservedSQL : List String := "user table order group from select where to end check default primary references in is on all and or not as by into join case when then else null limit offset union values with using cast column constraint create do for grant having only some window distinct desc asc any array between except fetch foreign intersect lateral returning unique".splitOn " "
def colSQL (f : String) : String := if reservedSQL.contains f then f ++ "_" else f
def tableSQL (n : Name) : String := colSQL (enumSQL n)

/-- a structure the shadow keeps as a table: none of its fields is a type (a Face is a kind) -/
def isTableStruct (env : Environment) (sn : Name) : Bool :=
  isStructure env sn && (getStructureFields env sn).all fun f =>
    match env.find? (sn ++ f) with
    | some pi => Id.run do
      let mut t := pi.type
      while t.isForall do t := t.bindingBody!
      return !t.isSort
    | none => false

/-- a fragment of the list vocabulary, read into SQL: projections are columns, `cons` prepends,
a house def is a call, `And`/`Eq`/`∈` are themselves, `cond` is `CASE`, and the joinMap-over-a-cond
shape is an aggregate over the child rows; anything outside the fragment is marked unread -/
partial def toSQL (env : Environment) (self : Nat) (e : Expr) : String :=
  let go := toSQL env self
  let col (c : Name) := colSQL c.getString!
  -- the element type of an array, for an empty one
  let elemSQL (t : Expr) : String := match t.constName? with
    | some ``Nat => "integer" | some ``Bool => "boolean"
    | some c => if isEnumName env c then enumSQL c else "integer"
    | none => "integer"
  -- a predicate applied to the element `x` of an array
  let pred (p : Expr) : String := match p with
    | .lam _ _ body _ => toSQL env self (body.instantiate1 (.const `x []))
    | _ => go (mkApp p (.const `x []))
  -- a chain of pair projections is a component: `.1` is c0, `.2.1` c1, `.2.2` c2
  let rec comp (e : Expr) (k : Nat) : Option (Nat × Expr) :=
    if e.isAppOfArity ``Prod.fst 3 then some (k, e.getArg! 2)
    else if e.isAppOfArity ``Prod.snd 3 then
      match comp (e.getArg! 2) (k + 1) with
      | some r => some r
      | none => some (k + 1, e.getArg! 2)
    else match e with
      | .proj ``Prod 0 b => some (k, b)
      | .proj ``Prod 1 b => (match comp b (k + 1) with | some r => some r | none => some (k + 1, b))
      | _ => none
  match comp e 0 with
  | some (k, base) => s!"({go base}).c{k}"
  | none =>
  match e with
  | .bvar i => if i == self then "row" else s!"${i}"
  | .const ``Bool.true _ => "true"
  | .const ``Bool.false _ => "false"
  | .const ``List.nil _ => "ARRAY[]::integer[]"
  | .const `x _ => "x"
  | .const c _ =>
    -- a constructor of an enum is its literal; a marker (`row`, `p1`) prints by name
    match env.find? c with
    | some (.ctorInfo ci) => if isEnumName env ci.induct then s!"'{c.getString!}'" else s!"⟨unread {c}⟩"
    | none => if c.getPrefix == .anonymous then c.toString else s!"⟨unread {c}⟩"
    | _ => s!"⟨unread {c}⟩"
  | .app .. =>
    let f := e.getAppFn; let args := e.getAppArgs
    match listLiteral? e with
    | some ([], t) => s!"ARRAY[]::{elemSQL t}[]"
    | some (xs, t) => s!"ARRAY[{", ".intercalate (xs.map go)}]::{elemSQL t}[]"
    | none =>
    match f.constName?, args.size with
    | some ``And, 2 => s!"({go args[0]!} AND {go args[1]!})"
    | some ``Bool.and, 2 => s!"({go args[0]!} AND {go args[1]!})"
    | some ``Bool.or, 2 => s!"({go args[0]!} OR {go args[1]!})"
    | some ``Bool.not, 1 => s!"(NOT {go args[0]!})"
    | some ``Eq, 3 => s!"({go args[1]!} = {go args[2]!})"
    -- a membership through a subquery, so any element type reads and a subselect is not the row form
    | some ``Membership.mem, 5 => s!"({go args[4]!} = ANY(SELECT unnest({go args[3]!})))"
    | some ``List.cons, 3 => s!"array_prepend({go args[1]!}, {go args[2]!})"
    | some ``cond, 4 => s!"(CASE WHEN {go args[1]!} THEN {go args[2]!} ELSE {go args[3]!} END)"
    | some ``List.length, 2 => s!"cardinality({go args[1]!})"
    -- over rows (a list of pairs is a child table's rows, kept whole): the alias is the row, the
    -- order its own position; over scalars: the element with its ordinality
    | some ``List.filter, 3 =>
      if args[0]!.isAppOf ``Prod then s!"ARRAY(SELECT x FROM unnest({go args[2]!}) AS x WHERE {pred args[1]!} ORDER BY (x).position)"
      else s!"ARRAY(SELECT x FROM unnest({go args[2]!}) WITH ORDINALITY AS u(x, o) WHERE {pred args[1]!} ORDER BY o)"
    | some ``List.map, 4 =>
      if args[0]!.isAppOf ``Prod then s!"ARRAY(SELECT {pred args[2]!} FROM unnest({go args[3]!}) AS x ORDER BY (x).position)"
      else s!"ARRAY(SELECT {pred args[2]!} FROM unnest({go args[3]!}) WITH ORDINALITY AS u(x, o) ORDER BY o)"
    | some ``List.sum, 4 => s!"(SELECT coalesce(sum(x), 0) FROM unnest({go args[3]!}) AS x)"
    -- a face applied to a row at a probe: a column of the face's function (the drawer names the table)
    | some `Face.Face.obs, 3 =>
      let F := args[0]!
      match F.getAppFn.constName? with
      | some fn => s!"FACEOBS[{fn.getString!}]({", ".intercalate (F.getAppArgs.toList.map go)})({go args[1]!}; {go args[2]!})"
      | none => s!"⟨unread Face.obs⟩"
    | some ``Nat.beq, 2 => s!"({go args[0]!} = {go args[1]!})"
    | some ``Nat.ble, 2 => s!"({go args[0]!} <= {go args[1]!})"
    | some ``HAdd.hAdd, 6 => s!"({go args[4]!} + {go args[5]!})"
    | some `Room.everyone, 3 => s!"({go args[1]!} <@ {go args[2]!})"   -- every member enrolled: containment
    | some `Room.backed, 4 => s!"({go args[3]!} <@ {go args[2]!})"
    | some `Room.enrolled, 4 => s!"({go args[3]!} = ANY(SELECT unnest({go args[2]!})))"
    | some `Room.joinMap, n =>
      -- joinMap (fun p => cond p.q p.f []) xs: the rows of xs where q, their f's flattened in order;
      -- with xs left implicit (a bare `joinMap f`), the rows are the argument itself
      if n < 3 then s!"⟨unread joinMap⟩" else
      match args[2]! with
      | .lam _ _ (.app (.app (.app (.app (.const ``cond _) _) q) f) (.app (.const ``List.nil _) _)) _ =>
        s!"AGG[{toSQL env 0 q} → {toSQL env 0 f}]({if n ≥ 4 then go args[3]! else "row"})"
      -- a joinMap over any other lambda: each element's list, flattened in order
      | .lam .. => if n ≥ 4 then s!"ARRAY(SELECT m FROM unnest({go args[3]!}) WITH ORDINALITY AS u(x, o), unnest({pred args[2]!}) WITH ORDINALITY AS v(m, i) ORDER BY o, i)" else s!"⟨unread joinMap⟩"
      | _ => s!"⟨unread joinMap⟩"
    | some c, _ =>
      if isStructure env c.getPrefix && (getStructureFields env c.getPrefix).contains c.getString!.toName then
        -- a projection: `row.field`; on anything but the row (an argument, an element), a lookup
        -- of the field on the structure's table by id — a pair keeps its component
        let base := args[args.size - 1]!
        if base == .bvar self || base == .const `row [] || c.getPrefix == ``Prod then s!"{go base}.{col c}"
        else if isTableStruct env c.getPrefix then s!"(SELECT {col c} FROM {tableSQL c.getPrefix} WHERE id = {go base})"
        else s!"⟨unread {c}⟩"
      else if c.getString! == "beq" && isEnumName env c.getPrefix && args.size == 2 then
        s!"({go args[0]!} = {go args[1]!})"
      else if c.getPrefix == `Room || c.getPrefix == `Roster || c.getPrefix.getString! == "Treaty" then
        -- a house call; a bare function argument (a comparator) is not a column
        s!"{c.getString!}({", ".intercalate (args.toList.filter (fun a => !((a.isConst && a != .const `x []) || a.isLambda)) |>.map go)})"
      else s!"⟨unread {c}⟩"
    | none, _ => s!"⟨unread⟩"
  | .proj sn i b => match (getStructureFields env sn)[i]? with
    | some f => if b == .bvar self || b == .const `row [] || sn == ``Prod then s!"{go b}.{colSQL f.getString!}" else if isTableStruct env sn then s!"(SELECT {colSQL f.getString!} FROM {tableSQL sn} WHERE id = {go b})" else "⟨unread⟩"
    | none => "⟨unread⟩"
  | .lit (.natVal n) => toString n
  | _ => "⟨unread⟩"

/-- the data-model shadow, read from the kernel: every structure of the stream and of its house
imports that the stream's vocabulary names (`table`), every enum (`type`), every seat — a def
whose value is a literal list of an enum's constructors (`seat`), and every reader — a def
`State → Probe → Ans` — with the field each probe lands on, found by reducing the reader at that
probe and taking the projection at its head (`reader`); and which theorems cite which seats -/
def schemaMode (trail : String) (sc : Scope) : IO Unit := do
  let st ← elabFrom (← IO.FS.readFile trail) trail none
  let env := st.env
  let mut vocab : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != sc.ns then continue
    vocab := vocab ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then vocab := vocab ++ v.getUsedConstants
  let isEnum (ii : InductiveVal) : Bool := !ii.isRec && ii.ctors.all fun c => match env.find? c with
    | some (.ctorInfo ci) => ci.numFields == 0 | _ => false
  let mut seen : Array Name := #[]
  for c in vocab ++ (env.constants.map₂.toList.map (·.1)).toArray do
    if seen.contains c || !sc.owns c then continue
    seen := seen.push c
    match env.find? c with
    | some (.inductInfo ii) =>
      if isEnum ii then IO.println s!"type {c} {" ".intercalate (ii.ctors.map (·.getString!))}"
      else if isStructure env c then
        let mut cols : Array String := #[]
        let mut data := true
        for f in getStructureFields env c do
          if let some pi := env.find? (c ++ f) then
            -- the field's type is the projection's codomain, after its self binder
            let mut t := pi.type
            while t.isForall do t := t.bindingBody!
            if t.isSort then data := false
            cols := cols.push s!"{f}:{t}"
        -- a structure with a Type-valued field (a Face) is a kind, not a table
        if data then IO.println s!"table {c} {" ".intercalate cols.toList}"
    | _ => pure ()
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != sc.ns || ci.isTheorem then continue
    let some v := ci.value? | continue
    match listItems v with
    | some (c :: cs) =>
      if let some (.ctorInfo ci') := env.find? c then
        if let some (.inductInfo ii) := env.find? ci'.induct then
          if isEnum ii then IO.println s!"seat {n.getString!} {ci'.induct} {" ".intercalate ((c :: cs).map (·.getString!))}"
    | _ => pure ()
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != sc.ns || ci.isTheorem then continue
    let ty := ci.type
    if !ty.isForall then continue
    let stateTy := ty.bindingDomain!
    let rest := ty.bindingBody!
    if !rest.isForall then continue
    let probeTy := rest.bindingDomain!
    let some (.inductInfo pii) := env.find? (probeTy.getAppFn.constName?.getD .anonymous) | continue
    if !isEnum pii then continue
    let some stateName := stateTy.getAppFn.constName? | continue
    if !isStructure env stateName then continue
    let fields := getStructureFields env stateName
    let arms ← (Meta.MetaM.toIO (ctxCore := { fileName := trail, fileMap := default }) (sCore := { env := env }) do
      Meta.withLocalDeclD `r stateTy fun r => do
        let mut arms : Array String := #[]
        for c in pii.ctors do
          let e ← Meta.whnf (mkAppN (.const n []) #[r, .const c []])
          -- a direct arm reduces to a projection NODE (`r.3`), an arm under a map keeps the
          -- projection FUNCTION (`Room.guests r`); read both
          let mut hit : Option Name := none
          for i in [0:fields.size] do
            let f := fields[i]!
            if (e.find? fun s => s.isAppOf (stateName ++ f) || (match s with | .proj sn idx _ => sn == stateName && idx == i | _ => false)).isSome then
              hit := some f; break
          -- an arm `List.map (fun x => x.2.2) (field r)` reads one component of each element: name it
          let comp : String := match e with
            | .app (.app (.app (.app (.const ``List.map _) _) _) (.lam _ _ body _)) _ =>
              match compDepth body 0 with | some k => s!"#{k}" | none => ""
            | _ => ""
          if let some f := hit then arms := arms.push s!"{c.getString!}={f}{comp}"
        pure arms)
    if !arms.1.isEmpty then IO.println s!"reader {n.getString!} {stateName} {pii.name} {" ".intercalate arms.1.toList}"
  -- faces: a def whose type, after its parameters, is a Face over a table with an enum (or Unit)
  -- probe — each probe's reading reduced at the probe, the parameters as p1…, the row as `row`
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != sc.ns || ci.isTheorem then continue
    let mut ty := ci.type
    while ty.isForall do ty := ty.bindingBody!
    if ty.getAppFn.constName? != some `Face.Face then continue
    let res ← (Meta.MetaM.toIO (ctxCore := { fileName := trail, fileMap := default }) (sCore := { env := env }) do
      Meta.forallTelescope ci.type fun ps _ => do
        let F := mkAppN (.const n []) ps
        let stateTy ← Meta.whnf (← Meta.mkProjection F `State)
        let probeTy ← Meta.whnf (← Meta.mkProjection F `Probe)
        let ansTy ← Meta.whnf (← Meta.mkProjection F `Ans)
        let some stateName := stateTy.getAppFn.constName? | return none
        if !isTableStruct env stateName then return none
        let probeName := probeTy.getAppFn.constName?.getD .anonymous
        let ctors : List Name ← if probeName == ``Unit then pure [``Unit.unit] else
          match env.find? probeName with
          | some (.inductInfo ii) => if isEnumName env probeName then pure ii.ctors else return none
          | _ => return none
        let obs ← Meta.mkProjection F `obs
        let markers := ps.mapIdx fun i _ => Expr.const (Name.mkSimple s!"p{i + 1}") []
        let arms : Array String ← Meta.withLocalDeclD `r stateTy fun r => do
          let mut arms : Array String := #[]
          for c in ctors do
            let e ← Meta.whnf (mkAppN obs #[r, .const c []])
            let e ← Meta.reduce e (skipTypes := true) (skipProofs := true)
            let e := (e.replaceFVars ps markers).replaceFVar r (.const `row [])
            arms := arms.push s!"{if c == ``Unit.unit then "unit" else c.getString!}={toSQL env 1000 e}"
          return arms
        let ansSQL := match ansTy.getAppFn.constName? with
          | some ``Nat => "integer" | some ``Bool => "boolean" | some ``List => "integer[]" | _ => "integer[]"
        return some s!"face {n.getString!} {stateName} {probeName} params={ps.size} ans={ansSQL} {" ".intercalate arms.toList}")
    if let some line := res.1 then IO.println line
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != sc.ns || !ci.isTheorem then continue
    let used := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
    let seats := used.filter fun c => c.getPrefix == sc.ns && (env.find? c).any (fun ci' => !ci'.isTheorem && ci'.type.isAppOf ``List)
    if !seats.isEmpty then IO.println s!"cites {n.getString!} {" ".intercalate (seats.toList.map (·.getString!))}"
  -- the derived: a def over a table's row — a view (data), a constraint (prop), a clerk (state to
  -- state, a procedure) — with its body printed for the drawer's fragment, and the theorems that
  -- describe it (those whose statement names it)
  let mut derivedSeen : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList ++ (vocab.toList.filterMap fun c => (env.find? c).map (c, ·)) do
    if !(sc.owns n) || ci.isTheorem || derivedSeen.contains n then continue
    derivedSeen := derivedSeen.push n
    let some v := ci.value? | continue
    let mut ty := ci.type
    let mut args : Array String := #[]
    while ty.isForall do
      args := args.push s!"{ty.bindingName!}:{ty.bindingDomain!}"
      ty := ty.bindingBody!
    if args.isEmpty then continue
    -- the printed type carries universe annotations (`List.{0} Roster.Party`); shed them
    let shed (t : String) : String := Id.run do
      let mut out := ""; let mut skip := false
      let cs := t.toList
      for i in [0:cs.length] do
        let c := cs[i]!
        if !skip && c == '.' && i + 1 < cs.length && cs[i+1]! == '{' then
          skip := true
        else if skip then
          if c == '}' then skip := false
        else
          out := out.push c
      return out
    let firstTy := shed ((args[0]!.splitOn ":").getD 1 "")
    -- the arguments after the row, as the shadow types them: a number an integer, a list or a
    -- tuple an array, a table an id, a Bool a boolean
    let sqlTy (t : String) : String :=
      let t := (shed t).trimAscii.toString
      if t == "Nat" then "integer" else if t == "Bool" then "boolean"
      else if t.startsWith "List " && isEnumName env (t.drop 5).trimAscii.toString.toName then enumSQL (t.drop 5).trimAscii.toString.toName ++ "[]"
      else if t.startsWith "List (List " || t.startsWith "List List " then "integer[][]"
      else if t.startsWith "List " then "integer[]"
      else if (t.splitOn "×").length > 1 then "integer[]"
      else if isEnumName env t.toName then enumSQL t.toName
      else if isStructure env t.toName then "integer" else "integer[]"
    let argtypes := ",".intercalate ((args.toList.drop 1).map fun a => sqlTy ((a.splitOn ":").getD 1 ""))
    let over := firstTy.splitOn " " |>.headD ""
    -- only defs whose first argument is a table (a structure of the shadow) or a list of one
    let listOf := (firstTy.startsWith "List ") && isStructure env ((firstTy.drop 5).trimAscii.toString.toName)
    let overName := if listOf then (firstTy.drop 5).trimAscii.toString.toName else over.toName
    let isTable := !listOf && isStructure env overName
    -- a def over an enum is a rule: read by reducing it at each constructor (one argument), or as
    -- its body over positional parameters (more)
    if isEnumName env overName then
      let retSQL := sqlTy s!"{ty}"
      let params := ",".intercalate (args.toList.map fun a => sqlTy ((a.splitOn ":").getD 1 ""))
      let some (.inductInfo ii) := env.find? overName | continue
      if args.size == 1 then
        let arms ← (Meta.MetaM.toIO (ctxCore := { fileName := trail, fileMap := default }) (sCore := { env := env }) do
          let mut arms : Array String := #[]
          for c in ii.ctors do
            let e ← Meta.whnf (mkAppN (.const n []) #[.const c []])
            let e ← Meta.reduce e (skipTypes := true) (skipProofs := true)
            arms := arms.push s!"WHEN '{c.getString!}' THEN {toSQL env 1000 e}"
          pure arms)
        IO.println s!"rule {n.getString!} depth=1 ret={retSQL} params={params} :: CASE $0 {" ".intercalate arms.1.toList} END"
      else
        let mut body := v
        let mut depth := 0
        while body.isLambda do body := body.bindingBody!; depth := depth + 1
        IO.println s!"rule {n.getString!} depth={depth} ret={retSQL} params={params} :: {toSQL env 1000 body}"
      continue
    if !(isTable || listOf) then continue
    let kind := if ty.isProp || ty.isConstOf ``Bool then "prop" else if ty.isSort then "sort" else if isTable && ty.getAppFn.constName? == some overName then "clerk" else "data"
    let mut body := v
    let mut depth := 0
    while body.isLambda do body := body.bindingBody!; depth := depth + 1
    -- the row is the first argument: de Bruijn index depth - 1 at the body
    let depth' := if depth == 0 then 1 else depth
    let sql := if kind == "clerk" then
        -- a constructor with fields: name each as `field = expr`, keeping only those not the row's own
        let args := body.getAppArgs
        let fields := getStructureFields env overName
        let sets := (List.range fields.size).filterMap fun i =>
          match args[i]?, fields[i]? with
          | some a, some f =>
            let same := match a with
              | .app (.const c _) (.bvar j) => c == overName ++ f && j == depth' - 1
              | .proj sn j (.bvar k) => sn == overName && j == i && k == depth' - 1
              | _ => false
            if same then none else some s!"{f} = {toSQL env (depth' - 1) a}"
          | _, _ => none
        "SET " ++ ", ".intercalate sets
      else toSQL env (depth' - 1) body
    let describers := (env.constants.map₂.toList.filter fun (m, ci') => m.getPrefix == sc.ns && ci'.isTheorem && ci'.type.getUsedConstants.contains n).map (·.1.getString!)
    -- a def the fragment cannot read may be read BY A THEOREM: `∀ x, g x = n x` (or `n x = g x`)
    -- with g readable — the shadow draws from the proof, and names it
    let mut sql := sql
    let mut byThm := ""
    if sql.startsWith "⟨unread" then
      for (m, ci') in env.constants.toList do
        if !(sc.owns m) || !ci'.isTheorem then continue
        let mut t := ci'.type
        while t.isForall do t := t.bindingBody!
        if t.isAppOfArity ``Eq 3 then
          let l := t.getArg! 1; let r := t.getArg! 2
          let isSelf (e : Expr) := e.isApp && e.getAppFn.constName? == some n && e.getAppArgs.all (·.isBVar)
          let mentions (e : Expr) := e.getUsedConstants.contains n
          let other := if isSelf r && !mentions l then some l else if isSelf l && !mentions r then some r else none
          if let some o := other then
            let s' := toSQL env 0 o
            if !(s'.startsWith "⟨unread") && !((s'.splitOn "⟨unread").length > 1) then
              sql := s'.replace "$0" "row"; byThm := m.getString!; break
    IO.println s!"derived {n.getString!} {kind} over={firstTy} args={depth'} argtypes={argtypes} ret={sqlTy s!"{ty}"} :: {sql} | {" ".intercalate describers}{if byThm.isEmpty then "" else s!" @by {byThm}"}"

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
  if args.head? == some "templates" then
    templatesMode args[1]! sc
    return
  if args.head? == some "schema" then
    schemaMode args[1]! sc
    return
  if args.head? == some "pieces" then
    -- the pieces in the order the crawl offers them, and the knobs, read from bin/Pieces.lean
    IO.println s!"budget {Pieces.budget}"
    IO.println s!"reach {Pieces.reach}"
    for (n, t) in Pieces.pieces do IO.println s!"{n}\t{t}"
    return
  let prefixSrc ← IO.FS.readFile args[0]!
  let candSrc ← IO.FS.readFile args[1]!
  -- candidates come grouped by vacancy (`-- vacancy` between groups, `-- candidate` within), in
  -- the pieces' order: a group stops at its first seat, because the cascade takes the first seated
  -- piece anyway — the rest are reported `skipped`, never elaborated (the probe, `vv`, sees all)
  let groups := (candSrc.splitOn "\n-- vacancy\n").map fun grp =>
    (grp.splitOn "\n-- candidate\n").filter (fun c => !c.trimAscii.isEmpty)
  -- a trial imports the pieces; the artifact never does (the judge reports each seated body expanded)
  let base ← elabFrom prefixSrc "<prefix>" none #[{ module := `Pieces }]
  let baseMsgs := base.messages.toList
  if !baseMsgs.isEmpty then
    IO.println s!"prefix not silent: {baseMsgs.length} messages"
    for m in baseMsgs.take 5 do IO.println s!"  {m.pos.line}:{m.pos.column} {← m.data.toString}"
    IO.Process.exit 1
  let mut i := 0
  let mut judged := 0
  let verbose := args.length > 2
  let sentences := args.length > 2 && args[2]! == "vv"
  for grp in groups do
   let mut seatedYet := false
   for c in grp do
    if seatedYet && !sentences then
      IO.println s!"{i} skipped"
      i := i + 1
      continue
    judged := judged + 1
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
    if !bad then seatedYet := true
    i := i + 1
  IO.println s!"judged {judged}"
