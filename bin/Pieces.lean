import Lean
open Lean Elab Command

/-! the pieces: the ordered proof shapes the crawl tries when a vacancy has a statement and no
body — Baba-style pieces that are also rules, each a Lean macro over three DERIVED lists: the
vacancy's citations (its signature's vocabulary, ranked), its applicable hypotheses, and the
carriers its statement names. a trial imports this module; the artifact never does — the judge
reports each seated body with the pieces expanded, and that expansion is what the module grows.
`budget` is the fuel a candidate may burn (Lean's own maxHeartbeats); `reach` caps how many seated
theorems a vacancy's citations may reach for. -/

namespace Pieces

-- the pieces' names (`ih`, `x`, `.trans`) must print as written: the expansion is re-parsed
-- by the artifact's gate, and a hygiene-marked name (`ih✝`) would not re-parse
set_option hygiene false

def budget : Nat := 20000
def reach : Nat := 12

/-- the order the crawl offers the pieces in; `{cites}` `{hyps}` `{defs}` are the three lists -/
def pieces : List (String × String) := [
  ("rfl", "rfl"),
  ("Iff.rfl", "Iff.rfl"),
  ("fun _ => rfl", "fun _ => rfl"),
  ("fun _ _ => rfl", "fun _ _ => rfl"),
  ("intros; rfl", "by (intros; rfl)"),
  ("cite", "by piece_cite [{cites}] [{hyps}] [{defs}]"),
  ("home-cite", "by piece_home_cite [{cites}] [{hyps}] [{defs}]"),
  ("chain", "by piece_chain [{cites}] [{hyps}] [{defs}]"),
  ("pane", "by piece_pane [{cites}] [{hyps}] [{defs}]"),
  ("induction", "by piece_induct_1st [{cites}] [{hyps}] [{defs}]"),
  ("induction-2nd", "by piece_induct_2nd [{cites}] [{hyps}] [{defs}]"),
  ("induction-3rd", "by piece_induct_3rd [{cites}] [{hyps}] [{defs}]"),
  ("induction-two-ih", "by piece_induct_two_ih [{cites}] [{hyps}] [{defs}]"),
  ("induction-two-ih-2nd", "by piece_induct_two_ih_2nd [{cites}] [{hyps}] [{defs}]"),
  ("home-cite-recurse", "by piece_home_cite_recurse [{cites}] [{hyps}] [{defs}]"),
  ("home-cite-recurse-2nd", "by piece_home_cite_recurse_2nd [{cites}] [{hyps}] [{defs}]")]

abbrev Seq := TSyntax ``Lean.Parser.Tactic.tacticSeq
abbrev Tac := TSyntax `tactic

def firstOf {m : Type → Type} [Monad m] [MonadQuotation m] (alts : Array Seq) : m Tac := do
  if alts.isEmpty then `(tactic| fail) else `(tactic| first $[| $alts]*)

def has (xs : Array Ident) (n : Ident) : Bool := xs.any (·.getId == n.getId)

def dedup (xs ys : Array Ident) : Array Ident := xs ++ ys.filter (fun y => !has xs y)

/-- the cite: a citation — or one of the statement's own hypotheses — with its side goals closed
by assumption, rfl, or ONE more name from the same list (a lemma that takes a lemma as an
argument; a side goal that is a hypothesis applied). every side alternative must CLOSE or fail: a
bare `apply` can succeed leaving goals, `first` counts that as success, and the outer alternative
commits with work undone. a hypothesis whose type is a def hides its ∀ from `apply`: `exact h _`. -/
def citeFull (cs hs : Array Ident) : MacroM Tac := do
  let names := dedup cs hs
  let mut alts : Array Seq := #[]
  for t in names do
    let mut sides : Array Seq := #[← `(tacticSeq| assumption), ← `(tacticSeq| rfl)]
    for m in names do
      if m.getId == t.getId then continue
      sides := sides.push (← `(tacticSeq| (apply $m <;> (first | assumption | rfl))))
      if has hs m then sides := sides.push (← `(tacticSeq| (exact $m _)))
    let side ← firstOf sides
    alts := alts.push (← `(tacticSeq| (apply $t <;> $side)))
    if has hs t then alts := alts.push (← `(tacticSeq| (exact $t _)))
  firstOf alts

/-- the one-deep cite over the few most akin — what a rewrite or a chain alternative may carry -/
def citeCompact (cs hs : Array Ident) : MacroM Tac := do
  let names := dedup (cs.take 4) hs
  let mut alts : Array Seq := #[]
  for t in names do
    alts := alts.push (← `(tacticSeq| (apply $t <;> (first | assumption | rfl))))
    if has hs t then alts := alts.push (← `(tacticSeq| (exact $t _)))
  firstOf alts

/-- rewrites as ATOMIC alternatives, each with its own closers: a rewrite that succeeds in the
wrong place fails and backtracks instead of poisoning the moves after it; the hypotheses first -/
def rwAlts (cs hs : Array Ident) (closers : Tac) : MacroM (Array Seq) := do
  let names := dedup hs (cs.take 4)
  names.mapM fun t => `(tacticSeq| (rw [$t:ident]; $closers))

/-- the term chain: a cited law or hypothesis at arity 0–3, composed by `.trans` (or
`.symm.trans`) with one more close — `(c2 _ _).trans (c1 _ _)` — each alternative atomic -/
def chainAlts (cs hs : Array Ident) (closers : Tac) : MacroM (Array Seq) := do
  let names := dedup hs (cs.take 6)
  let mut out : Array Seq := #[]
  for t in names do
    for k in [0, 1, 2, 3] do
      let holes : Array Term := Array.replicate k (← `(_))
      let app ← `(($t $holes*))
      out := out.push (← `(tacticSeq| exact ($app).trans (by $closers:tactic)))
      out := out.push (← `(tacticSeq| exact ($app).symm.trans (by $closers:tactic)))
  return out

/-! per-goal search: the cite slot of every piece is `piece_seek`, a tactic that reads the goal in
front of it — its applicable hypotheses from the local context (kernel-grade: whatever is a Prop),
its citations from the theorems already in the environment (at trial time the environment IS the
seated pool, so no list is passed), ranked by the goal's own vocabulary weighted by rarity — tries
them, and records the syntax that won. `#seat` substitutes each winner back into the expansion, so
the artifact carries exactly the citations that closed goals. a hint existed because a side
goal's vocabulary differs from its statement's; a search at the goal sees it. -/

/-- a constant of the house: declared in this file, or in a module that is not core -/
def house (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    let r := m.getRoot
    !(r == `Init || r == `Lean || r == `Std || r == `Lake || r == `Pieces)

/-- a top-level theorem of the house: `Ns.name`, never an auxiliary one namespace down -/
def topLevel (n : Name) : Bool := !n.getPrefix.isAnonymous && n.getPrefix.getPrefix.isAnonymous

/-- the vocabulary of a type: its constants, and one unfolding through the house's own defs
(a carrier's value names what the carrier is about) -/
def vocab (env : Environment) (e : Expr) : NameSet := Id.run do
  let mut out : NameSet := {}
  for c in e.getUsedConstants do
    out := out.insert c
    if house env c then
      if let some ci := env.find? c then
        if !ci.isTheorem then
          if let some v := ci.value? then
            for d in v.getUsedConstants do out := out.insert d
  return out

structure Pool where
  size : Nat
  theorems : Array (Name × NameSet)
  df : Std.HashMap Name Nat
  n : Nat

initialize poolRef : IO.Ref (Option Pool) ← IO.mkRef none
initialize seekTrace : IO.Ref (Array (Nat × Syntax)) ← IO.mkRef #[]

/-- the pool: every top-level theorem of the house in the environment, with its vocabulary, and
the document frequency of every word — computed once per environment size -/
def pool (env : Environment) : IO Pool := do
  let size := env.constants.map₂.foldl (fun n _ _ => n + 1) 0
  if let some p ← poolRef.get then
    if p.size == size then return p
  let mut ths : Array (Name × NameSet) := #[]
  for (n, ci) in env.constants.map₂.toList do
    if ci.isTheorem && topLevel n && (n.toString.splitOn "__p").length == 1 then
      ths := ths.push (n, vocab env ci.type)
  for (n, ci) in env.constants.map₁.toList do
    if ci.isTheorem && topLevel n && house env n then
      ths := ths.push (n, vocab env ci.type)
  let mut df : Std.HashMap Name Nat := {}
  for (_, k) in ths do
    for c in k.toList do df := df.insert c (df.getD c 0 + 1)
  let p := { size := size, theorems := ths, df := df, n := ths.size }
  poolRef.set (some p)
  return p

def weight (p : Pool) (c : Name) : Float :=
  Float.log ((p.n.toFloat + 1) / ((p.df.getD c 0).toFloat + 1))

/-- the citations in reach of a goal: shared rarity normalized by the candidate's own vocabulary
(a tight lemma that shares most of its words outranks a crown that shares a few of its many) -/
def inReach (p : Pool) (goal : NameSet) (exclude : Name) : Array Name := Id.run do
  let mut scored : Array (Float × Name) := #[]
  for (t, k) in p.theorems do
    if t == exclude then continue
    let shared := k.toList.foldl (fun a c => if goal.contains c then a + weight p c else a) 0.0
    if shared == 0.0 then continue
    let own := k.toList.foldl (fun a c => a + weight p c) 0.0
    scored := scored.push (shared / Float.sqrt (if own == 0.0 then 1.0 else own), t)
  let sorted := scored.qsort (fun a b => a.1 > b.1)
  return (sorted.take reach).map (·.2)

syntax (name := seek) "piece_seek" (num)? (" !")? : tactic

initialize seekCounter : IO.Ref Nat ← IO.mkRef 1000000

/-- a name as the artifact can read it: bare inside its own namespace (inside `namespace Face` the
word `Face` is the structure), qualified when imported -/
def nameFor (ns t : Name) : Name :=
  if ns.isPrefixOf t && ns != .anonymous then t.replacePrefix ns .anonymous else t

/-- the winners at each stamp, as one `first` fan (a seek inside `all_goals` wins once per goal);
a seek never reached is `fail` -/
partial def substitute (wins : Std.HashMap Nat (Array Syntax)) (stx : Syntax) : MacroM Syntax := do
  if stx.isOfKind ``seek then
    let k := if stx[1].getNumArgs == 0 then 0 else stx[1][0].toNat
    match wins.get? k with
    | some ws =>
      if ws.size == 1 then return ws[0]!
      let alts ← ws.mapM fun w => `(tacticSeq| $(TSyntax.mk w):tactic)
      return ← `(tactic| first $[| $alts]*)
    | none => return ← `(tactic| fail)
  match stx with
  | .node i k args => return .node i k (← args.mapM (substitute wins))
  | _ => return stx

open Tactic in
/-- the moves at this goal, in order: each hypothesis applied (its side goals closed by
assumption, rfl, or one more name), each citation in reach likewise; the first that closes the
goal is recorded under this seek's stamp -/
@[tactic seek] def evalSeek : Tactic := fun stx => do
  let stamp := if stx[1].getNumArgs == 0 then 0 else stx[1][0].toNat
  let leaf := stx[2].getNumArgs > 0
  let ns ← getCurrNamespace
  let env ← getEnv
  let p ← pool env
  let g ← getMainGoal
  let decl ← g.getDecl
  -- the theorem under trial is `name__pK`; it must not cite itself — and against a finished
  -- module (the tighten) `name` itself stands in the environment, the shortest route of all
  let dn := (← Lean.Elab.Term.getDeclName?).getD .anonymous
  let self := ((dn.toString.splitOn "__p").headD dn.toString).toName
  let hyps ← g.withContext do
    let mut hs : Array Ident := #[]
    for d in (← getLCtx) do
      -- an inaccessible name (`a✝`, from `intros`) would not re-parse in the artifact; `assumption` reaches it
      if d.isImplementationDetail || d.userName.hasMacroScopes then continue
      if ← Meta.isProp d.type then hs := hs.push (mkIdent d.userName)
    return hs
  let goalKey ← g.withContext do
    let mut k := vocab env (← instantiateMVars decl.type)
    for d in (← getLCtx) do
      -- a hypothesis introduced under a `constructor` carries its type as an assigned metavariable;
      -- the vocabulary walk sees nothing there until it is instantiated
      if !d.isImplementationDetail && (← Meta.isProp d.type) then
        for c in (vocab env (← instantiateMVars d.type)).toList do k := k.insert c
    return k
  let cites := (inReach p goalKey self).map (fun t => mkIdent (nameFor ns t))
  let names := hyps ++ cites
  let isHyp (n : Ident) := hyps.any (·.getId == n.getId)
  let gs ← getGoals
  for t in names do
    -- a side goal is closed by assumption, rfl, or ONE more search at that goal (a leaf: its own
    -- side goals by assumption or rfl only) — the side goal's vocabulary is its own, which is what
    -- a route used to carry
    let k ← seekCounter.modifyGet fun n => (n, n + 1)
    let side ← if leaf then `(tactic| first | assumption | rfl)
               else `(tactic| first | assumption | rfl | piece_seek $(Syntax.mkNumLit (toString k)):num !)
    let mut cands : Array Tac := #[← `(tactic| (apply $t <;> $side))]
    if isHyp t then cands := cands.push (← `(tactic| (exact $t _)))
    for cand in cands do
      let s ← saveState
      try
        setGoals [g]
        -- strict: with recovery on, an elaboration error is logged and the term becomes `sorry`,
        -- which would read as a win; without it the error throws and the next move is tried
        withoutRecover (evalTactic cand)
        if (← getGoals).isEmpty then
          -- the side searches' winners, substituted: the recorded move is exactly what closed
          let trace ← seekTrace.get
          let ws := (trace.filter (·.1 == k)).map (·.2)
          let mut wins : Std.HashMap Nat (Array Syntax) := {}
          for w in ws do
            let cur := wins.getD k #[]
            if !cur.any (fun x => x.reprint == w.reprint) then wins := wins.insert k (cur.push w)
          let cand' ← liftMacroM <| substitute wins cand.raw
          seekTrace.modify (·.push (stamp, cand'))
          setGoals (gs.filter (· != g))
          return
        s.restore
      catch _ =>
        s.restore
  let ctx ← g.withContext do
    let mut m : MessageData := m!""
    for d in (← getLCtx) do
      if !d.isImplementationDetail && (← Meta.isProp d.type) then m := m ++ m!"\n  {d.userName} : {d.type}"
    return m
  throwError "piece_seek: nothing in reach closes{indentExpr decl.type}\nwith:{ctx}\nkey: {goalKey.toList}\ntried: {names.map (·.getId)}"

syntax (name := cite) "piece_cite" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
syntax (name := homeCite) "piece_home_cite" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
syntax (name := chain) "piece_chain" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
syntax (name := pane) "piece_pane" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
syntax (name := induct1) "piece_induct_1st" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
syntax (name := induct2) "piece_induct_2nd" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
syntax (name := induct3) "piece_induct_3rd" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
syntax (name := inductTwo) "piece_induct_two_ih" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
syntax (name := inductTwo2) "piece_induct_two_ih_2nd" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
syntax (name := hcr) "piece_home_cite_recurse" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
syntax (name := hcr2) "piece_home_cite_recurse_2nd" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic

macro_rules
  | `(tactic| piece_cite [$_cs,*] [$_hs,*] [$_ds,*]) => do
    let c ← `(tactic| piece_seek)
    -- parenthesized: inside `(…)` the layout is position-free, so the expansion re-parses however
    -- the formatter breaks its lines (a bare `by intros;` + newline ends the sequence early)
    `(tactic| (intros; $c:tactic))

macro_rules
  | `(tactic| piece_home_cite [$_cs,*] [$_hs,*] [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    `(tactic| (intros; (try dsimp only [$[$ds:ident],*] at *); intros; first | rfl | assumption | $c:tactic))

macro_rules
  | `(tactic| piece_chain [$cs,*] [$hs,*] [$ds,*]) => do
    let closers ← `(tactic| first | rfl | assumption | piece_seek)
    let alts ← chainAlts cs.getElems hs.getElems closers
    let body ← firstOf (#[← `(tacticSeq| rfl), ← `(tacticSeq| assumption)] ++ alts)
    `(tactic| (intros; (try dsimp only [$[$ds:ident],*] at *); intros; $body:tactic))

macro_rules
  | `(tactic| piece_pane [$_cs,*] [$_hs,*] [$_ds,*]) => do
    let c ← `(tactic| piece_seek)
    -- `(repeat' …)` parenthesized: `repeat'` takes a tactic SEQUENCE, and on one line it would swallow
    -- the `all_goals` after it (one failed iteration, zero repeats, the goal untouched)
    `(tactic| (intros; (repeat' constructor); all_goals (intros; first | rfl | $c:tactic)))

/-- the base case, or any case the closers reach without the hypothesis -/
def baseCase (c : Tac) : MacroM Seq := `(tacticSeq| (intros; first | rfl | assumption | $c:tactic))

/-- the one-IH moves: the IH itself at some arity, `congrArg` over it, a rewrite by it, a chain
from it; then the same after reducing along the statement's own carriers -/
def ihMoves (c : Tac) (ds : Array Ident) (home : Bool) : MacroM (Array Seq) := do
  let mut out : Array Seq := #[
    ← `(tacticSeq| exact ih), ← `(tacticSeq| exact ih _), ← `(tacticSeq| exact ih _ _),
    ← `(tacticSeq| exact congrArg _ ih), ← `(tacticSeq| exact congrArg _ (ih _)), ← `(tacticSeq| exact congrArg _ (ih _ _)),
    ← `(tacticSeq| (rw [ih])), ← `(tacticSeq| (rw [ih]; $c:tactic)),
    ← `(tacticSeq| exact (ih _).trans (by $c:tactic)), ← `(tacticSeq| exact (ih _ _).trans (by $c:tactic)),
    ← `(tacticSeq| exact (ih _ _ _).trans (by $c:tactic))]
  if home then
    out := out.push (← `(tacticSeq| (dsimp only [$[$ds:ident],*]; first
      | exact congrArg _ ih
      | exact congrArg _ (ih _)
      | (rw [ih])
      | (rw [ih]; $c:tactic)
      | (rw [ih _]; $c:tactic)
      | exact (ih _).trans (by $c:tactic)
      | exact (ih _ _).trans (by $c:tactic))))
  return out

/-- the two-IH moves: the joint `congr (congrArg _ ih₁) ih₂` is the inverted triangle between two
upright ones -/
def twoIhMoves (c : Tac) (ds : Array Ident) (home : Bool) : MacroM (Array Seq) := do
  let mut out : Array Seq := #[
    ← `(tacticSeq| exact congr (congrArg _ ih₁) ih₂)]
  if home then out := out.push (← `(tacticSeq| exact congrArg₂ _ ih₁ ih₂))
  out := out ++ #[
    ← `(tacticSeq| (rw [ih₁, ih₂])), ← `(tacticSeq| (rw [ih₁, ih₂]; $c:tactic)),
    ← `(tacticSeq| (rw [ih₁ _, ih₂ _])), ← `(tacticSeq| (rw [ih₁ _, ih₂ _]; $c:tactic)),
    ← `(tacticSeq| exact congr (congrArg _ (ih₁ _)) (ih₂ _)),
    ← `(tacticSeq| exact (congr (congrArg _ (ih₁ _)) (ih₂ _)).trans (by $c:tactic))]
  if home then
    out := out ++ #[
      ← `(tacticSeq| exact (by $c:tactic : _ = _).trans (congr (congrArg _ ih₁) ih₂)),
      ← `(tacticSeq| exact (by $c:tactic : _ = _).trans (congr (congrArg _ (ih₁ _)) (ih₂ _))),
      ← `(tacticSeq| (dsimp only [$[$ds:ident],*]; first
        | exact congr (congrArg _ ih₁) ih₂
        | exact congr (congrArg _ (ih₁ _)) (ih₂ _)
        | (rw [ih₁, ih₂])
        | (rw [ih₁ _, ih₂ _])
        | (rw [ih₁, ih₂]; $c:tactic)
        | (rw [ih₁ _, ih₂ _]; $c:tactic)
        | exact (congr (congrArg _ (ih₁ _)) (ih₂ _)).trans (by $c:tactic)
        | exact (by $c:tactic : _ = _).trans (congr (congrArg _ ih₁) ih₂)))]
  return out

macro_rules
  | `(tactic| piece_induct_1st [$_cs,*] [$_hs,*] [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    let moves ← firstOf (← ihMoves c ds.getElems true)
    `(tactic| (intro x; induction x; all_goals (first | $(← baseCase c) | (rename_i ih; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_2nd [$_cs,*] [$_hs,*] [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    let moves ← firstOf (← ihMoves c ds.getElems false)
    `(tactic| (intro _ y; induction y; all_goals (first | $(← baseCase c) | (rename_i ih; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_3rd [$_cs,*] [$_hs,*] [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    let moves ← firstOf (← ihMoves c ds.getElems false)
    `(tactic| (intro _ _ z; induction z; all_goals (first | $(← baseCase c) | (rename_i ih; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_two_ih [$_cs,*] [$_hs,*] [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    let moves ← firstOf (← twoIhMoves c ds.getElems true)
    `(tactic| (intro x; induction x; all_goals (first | $(← baseCase c) | (rename_i ih₁ ih₂; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_two_ih_2nd [$_cs,*] [$_hs,*] [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    let moves ← firstOf (← twoIhMoves c ds.getElems false)
    `(tactic| (intro _ y; induction y; all_goals (first | $(← baseCase c) | (rename_i ih₁ ih₂; intros; $moves:tactic))))

/-- home → cite → recurse: reduce the goal along its own carriers before any closer lands, then
tighten by the citations, then close by the recursion — two IHs first, then one; rewrites by the
cited names and the statement's own hypotheses as atomic alternatives -/
def homeCiteRecurse (cs hs ds : Array Ident) (second : Bool) : MacroM Tac := do
  let c ← `(tactic| piece_seek)
  let compact ← `(tactic| piece_seek)
  let twoClosers ← `(tactic| first | rfl | exact congr (congrArg _ ih₁) ih₂ | exact congr (congrArg _ (ih₁ _)) (ih₂ _) | (rw [ih₁, ih₂]) | (rw [ih₁ _, ih₂ _]) | (rw [ih₁, ih₂]; $compact:tactic) | (rw [ih₁ _, ih₂ _]; $compact:tactic))
  let oneClosers ← `(tactic| first | rfl | exact ih | exact ih _ | exact ih _ _ | exact congrArg _ ih | exact congrArg _ (ih _) | (rw [ih]) | (rw [ih _]) | (rw [ih]; $compact:tactic) | (rw [ih _]; $compact:tactic))
  let two : Array Seq := #[
    ← `(tacticSeq| rfl),
    ← `(tacticSeq| exact congr (congrArg _ ih₁) ih₂),
    ← `(tacticSeq| exact congr (congrArg _ (ih₁ _)) (ih₂ _)),
    ← `(tacticSeq| (rw [ih₁, ih₂])), ← `(tacticSeq| (rw [ih₁ _, ih₂ _])),
    ← `(tacticSeq| (rw [ih₁, ih₂]; $c:tactic)), ← `(tacticSeq| (rw [ih₁ _, ih₂ _]; $c:tactic)),
    ← `(tacticSeq| exact (congr (congrArg _ (ih₁ _)) (ih₂ _)).trans (by $c:tactic)),
    ← `(tacticSeq| exact (by $c:tactic : _ = _).trans (congr (congrArg _ ih₁) ih₂))]
  let two := two ++ (← rwAlts cs hs twoClosers)
  let one : Array Seq := #[
    ← `(tacticSeq| rfl),
    ← `(tacticSeq| exact ih), ← `(tacticSeq| exact ih _), ← `(tacticSeq| exact ih _ _),
    ← `(tacticSeq| exact congrArg _ ih), ← `(tacticSeq| exact congrArg _ (ih _)), ← `(tacticSeq| exact congrArg _ (ih _ _)),
    ← `(tacticSeq| (rw [ih])), ← `(tacticSeq| (rw [ih _])), ← `(tacticSeq| (rw [ih _ _])),
    ← `(tacticSeq| (rw [ih]; $c:tactic)), ← `(tacticSeq| (rw [ih _]; $c:tactic)),
    ← `(tacticSeq| exact (ih _).trans (by $c:tactic)), ← `(tacticSeq| exact (ih _ _).trans (by $c:tactic))]
  let one := one ++ (← rwAlts cs hs oneClosers)
  let twoT ← firstOf two
  let oneT ← firstOf one
  let base ← baseCase c
  if second then
    `(tactic| (intro _ y; induction y; all_goals (first
      | $base
      | (rename_i ih₁ ih₂; intros; (try dsimp only [$[$ds:ident],*] at *); $twoT:tactic)
      | (rename_i ih; intros; (try dsimp only [$[$ds:ident],*] at *); $oneT:tactic))))
  else
    `(tactic| (intro x; induction x; all_goals (first
      | $base
      | (rename_i ih₁ ih₂; intros; (try dsimp only [$[$ds:ident],*] at *); $twoT:tactic)
      | (rename_i ih; intros; (try dsimp only [$[$ds:ident],*] at *); $oneT:tactic))))

macro_rules
  | `(tactic| piece_home_cite_recurse [$cs,*] [$hs,*] [$ds,*]) => homeCiteRecurse cs.getElems hs.getElems ds.getElems false
macro_rules
  | `(tactic| piece_home_cite_recurse_2nd [$cs,*] [$hs,*] [$ds,*]) => homeCiteRecurse cs.getElems hs.getElems ds.getElems true

/-- expand only the pieces' own macros, leaving Lean's (`rw`, `try`) as written; `piece_seek` is
a tactic, not a macro, and stays -/
partial def expandOurs (stx : Syntax) : MacroM Syntax := do
  if let .node _ k _ := stx then
    if (`Pieces).isPrefixOf k && k != ``seek then
      if let some stx' ← Macro.expandMacro? stx then return ← expandOurs stx'
  match stx with
  | .node i k args => return .node i k (← args.mapM expandOurs)
  | _ => return stx

/-- stamp every seek with its own number, so its winners can be found again -/
partial def stamp (stx : Syntax) : StateT Nat MacroM Syntax := do
  if stx.isOfKind ``seek then
    let k ← get; set (k + 1)
    return ← `(tactic| piece_seek $(Syntax.mkNumLit (toString k)):num)
  match stx with
  | .node i k args => return .node i k (← args.mapM stamp)
  | _ => return stx

/-- seat: elaborate the command with the pieces expanded, and report the body that was
elaborated — the expansion is what the module grows; the artifact never imports the pieces -/
elab "#seat " c:command : command => do
  let c' ← liftMacroM <| expandOurs c
  let (c', _) ← liftMacroM <| (stamp c').run 0
  seekTrace.set #[]
  elabCommand c'
  let trace ← seekTrace.get
  let mut wins : Std.HashMap Nat (Array Syntax) := {}
  for (k, w) in trace do
    let ws := wins.getD k #[]
    if ws.any (fun x => x.reprint == w.reprint) then continue
    wins := wins.insert k (ws.push w)
  let c'' ← liftMacroM <| substitute wins c'
  match c''.find? (·.isOfKind ``Lean.Parser.Command.declValSimple) with
  | some dv => logInfo m!"{dv[1]}"
  | none => logInfo m!"{c''}"

end Pieces
