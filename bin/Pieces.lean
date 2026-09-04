import Lean
open Lean Elab Command

/-! the pieces: the ordered proof shapes the crawl tries when a vacancy has a statement and no
body — Baba-style pieces that are also rules, each a Lean macro over one DERIVED list, the
carriers its statement names (to unfold first, so a goal reduces to its home); every citation,
hypothesis, rewrite, and chain is found by a search AT THE GOAL (`piece_seek`, `piece_rw_seek`,
`piece_chain_seek`). a trial imports this module; the artifact never does — the judge reports each
seated body with the pieces expanded and the searches' winners substituted, and that is what the
module grows. `budget` is the fuel a candidate may burn (Lean's own maxHeartbeats); `reach` caps how
many theorems a search tries at one goal. -/

namespace Pieces

-- the pieces' names (`ih`, `x`, `.trans`) must print as written: the expansion is re-parsed
-- by the artifact's gate, and a hygiene-marked name (`ih✝`) would not re-parse
set_option hygiene false

def budget : Nat := 20000
def reach : Nat := 12

/-- the order the crawl offers the pieces in; `{defs}` is the statement's own carriers -/
def pieces : List (String × String) := [
  ("rfl", "rfl"),
  ("Iff.rfl", "Iff.rfl"),
  ("fun _ => rfl", "fun _ => rfl"),
  ("fun _ _ => rfl", "fun _ _ => rfl"),
  ("intros; rfl", "by (intros; rfl)"),
  ("decide", "by decide"),
  ("cite", "by piece_cite [{defs}]"),
  ("home-cite", "by piece_home_cite [{defs}]"),
  ("chain", "by piece_chain [{defs}]"),
  ("home-rw", "by piece_home_rw [{defs}]"),
  ("home-induct", "by piece_home_induct [{defs}]"),
  ("pane", "by piece_pane [{defs}]"),
  ("induction", "by piece_induct_1st [{defs}]"),
  ("induction-2nd", "by piece_induct_2nd [{defs}]"),
  ("induction-3rd", "by piece_induct_3rd [{defs}]"),
  ("induction-two-ih", "by piece_induct_two_ih [{defs}]"),
  ("induction-two-ih-2nd", "by piece_induct_two_ih_2nd [{defs}]"),
  ("home-cite-recurse", "by piece_home_cite_recurse [{defs}]"),
  ("home-cite-recurse-2nd", "by piece_home_cite_recurse_2nd [{defs}]")]

abbrev Seq := TSyntax ``Lean.Parser.Tactic.tacticSeq
abbrev Tac := TSyntax `tactic

def firstOf {m : Type → Type} [Monad m] [MonadQuotation m] (alts : Array Seq) : m Tac := do
  if alts.isEmpty then `(tactic| fail) else `(tactic| first $[| $alts]*)

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

/-- the conclusion of a type: what stands after its binders -/
partial def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | e => e

/-- the logical head of a conclusion, as a class: `Eq`, `Ne`/`Not`, `And`, `Or`, `Iff`; a theorem
whose conclusion's class differs from the goal's cannot `apply` — filtered before the cap, so
that siblings sharing a goal's rare words do not crowd out the one lemma of the right shape -/
def headClass (e : Expr) : Option Name :=
  match (conclusion e).getAppFn.constName? with
  | some ``Eq => some ``Eq
  | some ``Ne => some ``Not
  | some ``Not => some ``Not
  | some ``And => some ``And
  | some ``Or => some ``Or
  | some ``Iff => some ``Iff
  | _ => none

/-- the citations in reach of a goal: shared rarity normalized by the candidate's own vocabulary
(a tight lemma that shares most of its words outranks a crown that shares a few of its many) -/
def inReach (p : Pool) (goal : NameSet) (exclude : Name) (keep : Name → Bool := fun _ => true) : Array Name := Id.run do
  let mut scored : Array (Float × Name) := #[]
  for (t, k) in p.theorems do
    if t == exclude || !keep t then continue
    let shared := k.toList.foldl (fun a c => if goal.contains c then a + weight p c else a) 0.0
    if shared == 0.0 then continue
    let own := k.toList.foldl (fun a c => a + weight p c) 0.0
    scored := scored.push (shared / Float.sqrt (if own == 0.0 then 1.0 else own), t)
  let sorted := scored.qsort (fun a b => a.1 > b.1)
  return (sorted.take reach).map (·.2)

syntax (name := seek) "piece_seek" (num)? (" !")? : tactic
syntax (name := rwSeek) "piece_rw_seek" (num)? " (" tactic ")" : tactic
syntax (name := chainSeek) "piece_chain_seek" (num)? (" !")? " (" tactic ")" : tactic

syntax (name := memSeek) "piece_mem_seek" (num)? : tactic
def isSeek (k : SyntaxNodeKind) : Bool := k == ``seek || k == ``rwSeek || k == ``chainSeek || k == ``memSeek
def stampOf (stx : Syntax) : Nat := if stx[1].getNumArgs == 0 then 0 else stx[1][0].toNat

initialize seekCounter : IO.Ref Nat ← IO.mkRef 1000000

/-- a name as the artifact can read it: bare inside its own namespace (inside `namespace Face` the
word `Face` is the structure), qualified when imported -/
def nameFor (ns t : Name) : Name :=
  if ns.isPrefixOf t && ns != .anonymous then t.replacePrefix ns .anonymous else t

/-- the winners at each stamp, as one `first` fan (a seek inside `all_goals` wins once per goal);
a seek never reached is `fail` -/
partial def substitute (wins : Std.HashMap Nat (Array Syntax)) (stx : Syntax) : MacroM Syntax := do
  if isSeek stx.getKind then
    let k := stampOf stx
    match wins.get? k with
    | some ws =>
      if ws.size == 1 then return ws[0]!
      let alts ← ws.mapM fun w => `(tacticSeq| $(TSyntax.mk w):tactic)
      return ← `(tactic| first $[| $alts]*)
    | none => return ← `(tactic| fail)
  match stx with
  | .node i k args =>
    let args ← args.mapM (substitute wins)
    -- a side search that never fired leaves `| fail` in a `first`: drop it, so the body reads as
    -- exactly its citations (a `first` keeps at least one alternative)
    if k == ``Lean.Parser.Tactic.first && args.size == 2 then
      let groups := args[1]!.getArgs
      let kept := groups.filter fun g => !(((g.getArg 1).reprint.getD "").trim == "fail")
      if !kept.isEmpty && kept.size < groups.size then
        return .node i k #[args[0]!, args[1]!.setArgs kept]
    return .node i k args
  | _ => return stx

def isEqn (e : Expr) : Bool := let c := conclusion e; c.isAppOf ``Eq || c.isAppOf ``Iff

open Tactic

/-- what a search reads at a goal: the applicable hypotheses (accessible Props — an inaccessible
name, `a✝` from `intros`, would not re-parse in the artifact, and `assumption` reaches it), the
goal's vocabulary (its target and every Prop hypothesis, INSTANTIATED — a goal split by
`constructor` carries its context types as assigned metavariables, and the walk sees nothing there
otherwise), and the theorem under trial (`name__pK`), which must not cite itself — against a
finished module `name` itself stands in the environment, the shortest route of all -/
structure Sight where
  hyps : Array (Ident × Expr)
  key : NameSet
  self : Name
  ns : Name

def sight (g : MVarId) : TacticM Sight := do
  let env ← getEnv
  let ns ← getCurrNamespace
  let dn := (← Lean.Elab.Term.getDeclName?).getD .anonymous
  let self := ((dn.toString.splitOn "__p").headD dn.toString).toName
  g.withContext do
    let mut hs : Array (Ident × Expr) := #[]
    let mut k := vocab env (← instantiateMVars (← g.getType))
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if !(← Meta.isProp d.type) then continue
      let ty ← instantiateMVars d.type
      for c in (vocab env ty).toList do k := k.insert c
      if !d.userName.hasMacroScopes then hs := hs.push (mkIdent d.userName, ty)
    return { hyps := hs, key := k, self := self, ns := ns }

/-- the search loop: each candidate tried STRICT against the goal alone (with recovery on, an
elaboration error is logged and the term becomes `sorry`, which would read as a win); the first
that closes it is recorded under the stamp with its nested winners substituted, so the recorded
move is exactly what closed; the trace rolls back on every failure, so only the successful path
is ever recorded -/
def search (stamp : Nat) (g : MVarId) (cands : Array Tac) : TacticM Bool := do
  let gs ← getGoals
  for cand in cands do
    let s ← saveState
    let len := (← seekTrace.get).size
    try
      setGoals [g]
      withoutRecover (evalTactic cand)
      if (← getGoals).isEmpty then
        let trace ← seekTrace.get
        let mut wins : Std.HashMap Nat (Array Syntax) := {}
        for (j, w) in trace.extract len trace.size do
          let cur := wins.getD j #[]
          if !cur.any (fun x => x.reprint == w.reprint) then wins := wins.insert j (cur.push w)
        let cand' ← liftMacroM <| substitute wins cand.raw
        seekTrace.modify fun t => (t.take len).push (stamp, cand')
        setGoals (gs.filter (· != g))
        return true
      s.restore
      seekTrace.modify (·.take len)
    catch _ =>
      s.restore
      seekTrace.modify (·.take len)
  return false

def fresh : TacticM Nat := seekCounter.modifyGet fun n => (n, n + 1)

/-- the cite at this goal: each hypothesis applied (its side goals closed by assumption, rfl, or
ONE more search at that goal — a leaf, its own sides by assumption or rfl only — because a side
goal's vocabulary is its own, which is what a route used to carry), then each citation in reach
likewise; a def-typed hypothesis hides its ∀ from `apply`, so `exact h _` beside it -/
@[tactic seek] def evalSeek : Tactic := fun stx => do
  let stamp := stampOf stx
  let leaf := stx[2].getNumArgs > 0
  let g ← getMainGoal
  let si ← sight g
  let p ← pool (← getEnv)
  let hyps := si.hyps.map (·.1)
  let env ← getEnv
  let goalHead := headClass (← instantiateMVars (← g.getType))
  let reach := inReach p si.key si.self (fun t =>
    match goalHead, (env.find? t).bind (fun ci => headClass ci.type) with
    | some gh, some th => gh == th || th == ``And   -- a conjunction's projections may match
    | _, _ => true)
  let cites := reach.map (fun t => mkIdent (nameFor si.ns t))
  let names := hyps ++ cites
  -- a conjunction, cited or held, is closed through its projections: `h.2`, `(t _ _).2.2` —
  -- the pane-of-projections shape a crown's hand writes; the arity is the explicit binders
  let conj (ty : Expr) : TacticM (Option Nat) := do
    let mut e := ty; let mut n := 0
    while e.isForall do
      if e.bindingInfo!.isExplicit then n := n + 1
      e := e.bindingBody!
    let e' : Expr ← try g.withContext (Meta.whnfD e) catch _ => pure e
    return if Expr.isAppOf e' ``And then some n else none
  let mut cands : Array Tac := #[]
  for t in names do
    let k ← fresh
    let side ← if leaf then `(tactic| first | assumption | rfl | decide | piece_mem_seek $(Syntax.mkNumLit (toString k)):num)
               else `(tactic| first | assumption | rfl | decide | piece_mem_seek $(Syntax.mkNumLit (toString k)):num | piece_seek $(Syntax.mkNumLit (toString k)):num !)
    cands := cands.push (← `(tactic| (apply $t <;> $side)))
    let isHyp := hyps.any (·.getId == t.getId)
    if isHyp then cands := cands.push (← `(tactic| (exact $t _)))
    let ty? ← if isHyp then pure ((si.hyps.find? (·.1.getId == t.getId)).map (·.2))
              else pure ((env.find? (si.ns ++ t.getId)).orElse (fun _ => env.find? t.getId) |>.map (·.type))
    if let some ty := ty? then
      -- an equation cited REVERSED: `exact (t _).symm` — a chain's far end often reads right to left
      if isEqn ty then
        let mut e := ty; let mut n := 0
        while e.isForall do
          if e.bindingInfo!.isExplicit then n := n + 1
          e := e.bindingBody!
        let holes : Array Term := Array.replicate n (← `(_))
        cands := cands.push (← `(tactic| (apply (($t $holes*)).symm <;> $side)))
      if let some n ← conj ty then
        let holes : Array Term := Array.replicate n (← `(_))
        let app ← `(($t $holes*))
        for path in [[1], [2], [2, 1], [2, 2], [2, 2, 1], [2, 2, 2], [2, 2, 2, 1], [2, 2, 2, 2]] do
          let mut e : Term := app
          for i in path do
            e ← if i == 1 then `(($e).1) else `(($e).2)
          cands := cands.push (← `(tactic| (apply $e <;> $side)))
  if ← search stamp g cands then return
  throwError "piece_seek: nothing in reach closes{indentExpr (← g.getType)}\ntried: {names.map (·.getId)}"

/-- a membership at this goal, from its constructors: the head, or the tail of a membership one
deeper — recorded as the constructor term it found, up to twelve deep -/
@[tactic memSeek] def evalMemSeek : Tactic := fun stx => do
  let stamp := stampOf stx
  let g ← getMainGoal
  let mut cands : Array Tac := #[]
  let mut inner : Tac ← `(tactic| exact List.Mem.head _)
  for _ in [0:12] do
    cands := cands.push inner
    inner ← `(tactic| (apply List.Mem.tail; $inner:tactic))
  if ← search stamp g cands then return
  throwError "piece_mem_seek: no membership by constructors closes{indentExpr (← g.getType)}"

/-- the rewrite at this goal: each equation-shaped hypothesis, then each equation or iff in reach,
as an ATOMIC alternative with the piece's own closers after it — a rewrite that lands in the
wrong place fails and backtracks instead of poisoning the moves after it -/
@[tactic rwSeek] def evalRwSeek : Tactic := fun stx => do
  let stamp := stampOf stx
  let closers : Tac := ⟨stx[3]⟩
  let g ← getMainGoal
  let si ← sight g
  let env ← getEnv
  let p ← pool env
  let hyps := (si.hyps.filter (fun (_, ty) => isEqn ty)).map (·.1)
  let cites := ((inReach p si.key si.self).filter fun t => (env.find? t).any (fun ci => isEqn ci.type)).map
    (fun t => mkIdent (nameFor si.ns t))
  let names := hyps ++ cites
  let cands ← names.mapM fun t => `(tactic| (rw [$t:ident]; $closers:tactic))
  if ← search stamp g cands then return
  throwError "piece_rw_seek: no rewrite in reach closes{indentExpr (← g.getType)}\ntried: {names.map (·.getId)}"

/-- the chain at this goal: a hypothesis or an equation in reach at arity 0–3, composed by `.trans`
or `.symm.trans` with the piece's own closers — `(c2 _ _).trans (c1 _ _)` -/
@[tactic chainSeek] def evalChainSeek : Tactic := fun stx => do
  let stamp := stampOf stx
  let leaf := stx[2].getNumArgs > 0
  let closers : Tac := ⟨stx[4]⟩
  -- a chain's far end may itself be a chain, one level deep (a three-link chain)
  let k ← fresh
  let closers ← if leaf then pure closers
                else `(tactic| first | $closers:tactic | piece_chain_seek $(Syntax.mkNumLit (toString k)):num ! ($closers:tactic))
  let g ← getMainGoal
  let si ← sight g
  let env ← getEnv
  let p ← pool env
  let hyps := (si.hyps.filter (fun (_, ty) => isEqn ty)).map (·.1)
  let cites := (((inReach p si.key si.self).filter fun t => (env.find? t).any (fun ci => isEqn ci.type)).take 6).map
    (fun t => mkIdent (nameFor si.ns t))
  let names := hyps ++ cites
  let mut cands : Array Tac := #[]
  for t in names do
    for k in [0, 1, 2, 3] do
      let holes : Array Term := Array.replicate k (← `(_))
      let app ← `(($t $holes*))
      -- `apply`, not `exact`: an explicit proof argument the unifier cannot fill (a hypothesis
      -- `h : gl.Perm gl'`) stays a side goal, and assumption closes it
      cands := cands.push (← `(tactic| (apply ($app).trans (by $closers:tactic) <;> first | assumption | rfl | decide)))
      cands := cands.push (← `(tactic| (apply ($app).symm.trans (by $closers:tactic) <;> first | assumption | rfl | decide)))
  if ← search stamp g cands then return
  throwError "piece_chain_seek: no chain in reach closes{indentExpr (← g.getType)}\ntried: {names.map (·.getId)}"


syntax (name := cite) "piece_cite" "[" ident,* "]" : tactic
syntax (name := homeCite) "piece_home_cite" "[" ident,* "]" : tactic
syntax (name := chain) "piece_chain" "[" ident,* "]" : tactic
syntax (name := homeRw) "piece_home_rw" "[" ident,* "]" : tactic
syntax (name := homeInduct) "piece_home_induct" "[" ident,* "]" : tactic
syntax (name := pane) "piece_pane" "[" ident,* "]" : tactic
syntax (name := induct1) "piece_induct_1st" "[" ident,* "]" : tactic
syntax (name := induct2) "piece_induct_2nd" "[" ident,* "]" : tactic
syntax (name := induct3) "piece_induct_3rd" "[" ident,* "]" : tactic
syntax (name := inductTwo) "piece_induct_two_ih" "[" ident,* "]" : tactic
syntax (name := inductTwo2) "piece_induct_two_ih_2nd" "[" ident,* "]" : tactic
syntax (name := hcr) "piece_home_cite_recurse" "[" ident,* "]" : tactic
syntax (name := hcr2) "piece_home_cite_recurse_2nd" "[" ident,* "]" : tactic

macro_rules
  | `(tactic| piece_cite [$_ds,*]) => do
    let c ← `(tactic| piece_seek)
    -- parenthesized: inside `(…)` the layout is position-free, so the expansion re-parses however
    -- the formatter breaks its lines (a bare `by intros;` + newline ends the sequence early)
    `(tactic| (intros; $c:tactic))

macro_rules
  | `(tactic| piece_home_cite [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    `(tactic| (intros; (try dsimp only [$[$ds:ident],*] at *); intros; first | rfl | assumption | $c:tactic))

macro_rules
  | `(tactic| piece_chain [$ds,*]) => do
    let closers ← `(tactic| first | rfl | assumption | piece_seek)
    `(tactic| (intros; (try dsimp only [$[$ds:ident],*] at *); intros; first | rfl | assumption | piece_chain_seek ($closers:tactic)))

/-- home → split → close: reduce along the statement's own carriers, then split the first variable
(a face whose observation is a match on its probe reduces only once the probe is a constructor),
then close each case by rfl, assumption, or a search -/
macro_rules
  | `(tactic| piece_home_induct [$ds,*]) => do
    `(tactic| (intros; (try dsimp only [$[$ds:ident],*] at *); intro x; induction x; all_goals (intros; first | rfl | assumption | piece_seek)))

/-- home → rewrite → close: reduce along the statement's own carriers, then one rewrite found at
the goal, then a close — a hypothesis that steers a `cond` (`hb : backed … = false`) is a rewrite,
and in term mode the hole for it carries information the unifier cannot recover -/
macro_rules
  | `(tactic| piece_home_rw [$ds,*]) => do
    let closers ← `(tactic| first | rfl | assumption | piece_seek)
    `(tactic| (intros; (try dsimp only [$[$ds:ident],*] at *); intros; first | rfl | assumption | piece_rw_seek ($closers:tactic)))

macro_rules
  | `(tactic| piece_pane [$_ds,*]) => do
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
  | `(tactic| piece_induct_1st [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    let moves ← firstOf (← ihMoves c ds.getElems true)
    `(tactic| (intro x; induction x; all_goals (first | $(← baseCase c) | (rename_i ih; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_2nd [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    let moves ← firstOf (← ihMoves c ds.getElems false)
    `(tactic| (intro _ y; induction y; all_goals (first | $(← baseCase c) | (rename_i ih; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_3rd [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    let moves ← firstOf (← ihMoves c ds.getElems false)
    `(tactic| (intro _ _ z; induction z; all_goals (first | $(← baseCase c) | (rename_i ih; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_two_ih [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    let moves ← firstOf (← twoIhMoves c ds.getElems true)
    `(tactic| (intro x; induction x; all_goals (first | $(← baseCase c) | (rename_i ih₁ ih₂; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_two_ih_2nd [$ds,*]) => do
    let c ← `(tactic| piece_seek)
    let moves ← firstOf (← twoIhMoves c ds.getElems false)
    `(tactic| (intro _ y; induction y; all_goals (first | $(← baseCase c) | (rename_i ih₁ ih₂; intros; $moves:tactic))))

/-- home → cite → recurse: reduce the goal along its own carriers before any closer lands, then
tighten by the citations, then close by the recursion — two IHs first, then one; rewrites by the
cited names and the statement's own hypotheses as atomic alternatives -/
def homeCiteRecurse (ds : Array Ident) (second : Bool) : MacroM Tac := do
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
  let two := two.push (← `(tacticSeq| piece_rw_seek ($twoClosers:tactic)))
  let one : Array Seq := #[
    ← `(tacticSeq| rfl),
    ← `(tacticSeq| exact ih), ← `(tacticSeq| exact ih _), ← `(tacticSeq| exact ih _ _),
    ← `(tacticSeq| exact congrArg _ ih), ← `(tacticSeq| exact congrArg _ (ih _)), ← `(tacticSeq| exact congrArg _ (ih _ _)),
    ← `(tacticSeq| (rw [ih])), ← `(tacticSeq| (rw [ih _])), ← `(tacticSeq| (rw [ih _ _])),
    ← `(tacticSeq| (rw [ih]; $c:tactic)), ← `(tacticSeq| (rw [ih _]; $c:tactic)),
    ← `(tacticSeq| exact (ih _).trans (by $c:tactic)), ← `(tacticSeq| exact (ih _ _).trans (by $c:tactic))]
  let one := one.push (← `(tacticSeq| piece_rw_seek ($oneClosers:tactic)))
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
  | `(tactic| piece_home_cite_recurse [$ds,*]) => homeCiteRecurse ds.getElems false
macro_rules
  | `(tactic| piece_home_cite_recurse_2nd [$ds,*]) => homeCiteRecurse ds.getElems true

/-- expand only the pieces' own macros, leaving Lean's (`rw`, `try`) as written; `piece_seek` is
a tactic, not a macro, and stays -/
partial def expandOurs (stx : Syntax) : MacroM Syntax := do
  if let .node _ k _ := stx then
    if (`Pieces).isPrefixOf k && !isSeek k then
      if let some stx' ← Macro.expandMacro? stx then return ← expandOurs stx'
  match stx with
  | .node i k args => return .node i k (← args.mapM expandOurs)
  | _ => return stx

/-- stamp every seek with its own number, so its winners can be found again -/
partial def stamp (stx : Syntax) : StateT Nat MacroM Syntax := do
  if isSeek stx.getKind then
    let k ← get; set (k + 1)
    let stx := stx.setArg 1 (mkNullNode #[Syntax.mkNumLit (toString k)])
    match stx with
    | .node i kind args => return .node i kind (← args.mapM stamp)
    | _ => return stx
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
  -- the vow at the trial: a candidate that seats on an axiom (`decide` through a derived
  -- `DecidableEq` smuggles `propext`) is refused here, not at the artifact's gate
  if let some declId := c'.find? (·.isOfKind ``Lean.Parser.Command.declId) then
    let name := (← getCurrNamespace) ++ declId[0].getId
    if (← getEnv).contains name then
      let axioms ← collectAxioms name
      if !axioms.isEmpty then
        throwError "{name} depends on axioms: {axioms}"
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
