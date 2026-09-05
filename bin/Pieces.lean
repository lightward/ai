import Lean
open Lean Elab Command

/-! the act of the compiler: the searches. a piece is a proof shape with the citations put back as
searches — and since 2026-09-05 the pieces are DERIVED from the bodies in scope (the grown modules
a germ stands on and the germ's own hand bodies, rendered by `bin/judge.lean templates`), so this
file keeps no list of shapes. what it keeps is what a shape cannot say: the search at the goal
(`piece_seek`, `piece_rw_seek`, `piece_chain_seek`, `piece_mem_seek`), the fan as a seek over its own
alternatives (`piece_first`), and `#seat`, which elaborates a candidate and reports the body with
every search's winner substituted — that expansion is what the module grows. a trial imports this
module; the artifact never does. `budget` is the fuel a candidate may burn (Lean's own
maxHeartbeats); `reach` caps how many theorems a search tries at one goal. -/

namespace Pieces

-- the pieces' names (`ih`, `x`, `.trans`) must print as written: the expansion is re-parsed
-- by the artifact's gate, and a hygiene-marked name (`ih✝`) would not re-parse
set_option hygiene false

def budget : Nat := 20000
def reach : Nat := 12

abbrev Tac := TSyntax `tactic

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

/-- a top-level theorem of the house: `Ns.name` where `Ns` is a namespace, never an auxiliary one
namespace down (`Face.Plan.rec`, `Face.foo.match_1` — whose prefix is itself a constant) -/
def topLevel (env : Environment) (n : Name) : Bool :=
  !n.getPrefix.isAnonymous && !env.contains n.getPrefix

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
  storey : Std.HashMap Name Nat   -- a theorem's storey: its module's index, the local module highest

/-- a constant's storey: its module's index in the import order (Room below Face below Witness
below the customer), the module being grown highest of all -/
def storeyOf (env : Environment) (n : Name) : Nat :=
  match env.getModuleIdxFor? n with
  | some idx => idx.toNat
  | none => env.header.moduleNames.size

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
    if ci.isTheorem && topLevel env n && (n.toString.splitOn "__p").length == 1 then
      ths := ths.push (n, vocab env ci.type)
  for (n, ci) in env.constants.map₁.toList do
    if ci.isTheorem && topLevel env n && house env n then
      ths := ths.push (n, vocab env ci.type)
  let mut df : Std.HashMap Name Nat := {}
  for (_, k) in ths do
    for c in k.toList do df := df.insert c (df.getD c 0 + 1)
  let mut st : Std.HashMap Name Nat := {}
  for (t, _) in ths do st := st.insert t (storeyOf env t)
  let p := { size := size, theorems := ths, df := df, n := ths.size, storey := st }
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
def inReach (p : Pool) (goal : NameSet) (exclude : Name) (keep : Name → Bool := fun _ => true)
    (goalStorey : Nat := 0) : Array Name := Id.run do
  -- by affinity alone. the lines as the order (the goal's own storey first, then below) was tried
  -- and refuted: with the reach filled by same-storey siblings, the lower-storey lemma a body
  -- needs (Room's list laws at a Face goal) fell past the cap — Face refused four, Witness one,
  -- EIH four. the storey is kept on the pool for the reading, not the ranking
  -- a WINDOW PER STOREY: the reach is shared out across the storeys present (Room, Face,
  -- Witness, the customer), each keeping its own top few by affinity, so a goal is offered the best
  -- of every level at once rather than the best of a pile that one storey's siblings can own; the
  -- picks are then tried in affinity order. the window is stacked; nothing reads across levels
  let _ := goalStorey
  let mut scored : Array (Float × Name) := #[]
  for (t, k) in p.theorems do
    if t == exclude || !keep t then continue
    let shared := k.toList.foldl (fun a c => if goal.contains c then a + weight p c else a) 0.0
    if shared == 0.0 then continue
    let own := k.toList.foldl (fun a c => a + weight p c) 0.0
    scored := scored.push (shared / Float.sqrt (if own == 0.0 then 1.0 else own), t)
  let sorted := scored.qsort (fun a b => a.1 > b.1)
  let storeys := (sorted.map (fun x => p.storey.getD x.2 0)).toList.eraseDups
  let quota := reach   -- a full window per storey: each level tried at the reach's own width
  let mut picked : Array (Float × Name) := #[]
  for st in storeys do
    picked := picked ++ (sorted.filter (fun x => p.storey.getD x.2 0 == st)).take quota
  -- the leftover of the reach, if a storey had fewer than its share, by affinity over the rest
  for x in sorted do
    if picked.size ≥ reach then break
    if !picked.any (·.2 == x.2) then picked := picked.push x
  return (picked.qsort (fun a b => a.1 > b.1)).map (·.2)

syntax (name := seek) "piece_seek" (num)? (" !")? : tactic
syntax (name := rwSeek) "piece_rw_seek" (num)? " (" tactic ")" : tactic
syntax (name := chainSeek) "piece_chain_seek" (num)? (" !")? " (" tactic ")" : tactic

syntax (name := memSeek) "piece_mem_seek" (num)? : tactic
/-- a `first` fan of a piece, as a seek over its own alternatives: the branch that closed is recorded,
so the artifact carries it and not the fan -/
syntax (name := firstSeek) "piece_first" (num)? withPosition((ppDedent(ppLine) colGe "| " tacticSeq)+) : tactic
def isSeek (k : SyntaxNodeKind) : Bool := k == ``seek || k == ``rwSeek || k == ``chainSeek || k == ``memSeek || k == ``firstSeek
def stampOf (stx : Syntax) : Nat := if stx[1].getNumArgs == 0 then 0 else stx[1][0].toNat

initialize seekCounter : IO.Ref Nat ← IO.mkRef 1000000

/-- a name as the artifact can read it: bare inside its own namespace (inside `namespace Face` the
word `Face` is the structure), qualified when imported -/
def nameFor (ns t : Name) : Name :=
  if ns.isPrefixOf t && ns != .anonymous then t.replacePrefix ns .anonymous else t

/-- an alternative that contains a `fail` anywhere — a seek never reached, or a rewrite that fails on
purpose after it lands — cannot be the one that closed the goal -/
partial def containsFail : Syntax → Bool
  | .node _ k args =>
    -- `t <;> fail` is not dead: it closes exactly when t leaves nothing, which is what the trial
    -- meant by a fan that never ran; only the left side is read
    if args.size == 3 && args[1]!.isAtom && args[1]!.getAtomVal == "<;>" then containsFail args[0]!
    else k == ``Lean.Parser.Tactic.fail || args.any containsFail
  | _ => false

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
    -- an alternative that cannot close (a side search that never fired, a rewrite-then-fail
    -- probe) is dropped from its `first`, so the body reads as the moves that could have
    -- closed it (a `first` keeps at least one alternative)
    if k == ``Lean.Parser.Tactic.first && args.size == 2 then
      let groups := args[1]!.getArgs
      let kept := groups.filter fun g => !(containsFail g)
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
def fresh : TacticM Nat := seekCounter.modifyGet fun n => (n, n + 1)

/-- a sequence of exactly one tactic, as that tactic -/
def singleTactic? (seq : Syntax) : Option Syntax :=
  if seq.getKind == ``Lean.Parser.Tactic.tacticSeq && seq[0].getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
    let items := seq[0][0].getArgs
    if items.size == 1 then some items[0]! else none
  else none

/-- every `first` of a candidate becomes a seek over its own alternatives -/
partial def firstsToSeeks (stx : Syntax) : MacroM Syntax := do
  let stx ← match stx with
    | .node i k args => pure (Syntax.node i k (← args.mapM firstsToSeeks))
    | _ => pure stx
  match stx with
  | `(tactic| first $[| $alts]*) => `(tactic| piece_first $[| $alts]*)
  | _ => return stx

/-- a seek built at runtime carries no stamp yet: give it one from the counter -/
partial def freshen (stx : Syntax) : TacticM Syntax := do
  let stx ← if isSeek stx.getKind && stx[1].getNumArgs == 0 then
      pure (stx.setArg 1 (mkNullNode #[Syntax.mkNumLit (toString (← fresh))]))
    else pure stx
  match stx with
  | .node i k args => return .node i k (← args.mapM freshen)
  | _ => return stx

def search (stamp : Nat) (g : MVarId) (cands : Array Tac) : TacticM Bool := do
  let gs ← getGoals
  for cand₀ in cands do
    let cand : Tac := TSyntax.mk (← freshen (← liftMacroM <| firstsToSeeks cand₀.raw))
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


/-- a fan tried in order, each alternative strict and rolled back on failure exactly as Lean's
`first` would; the one that ran is recorded under the stamp with its nested winners substituted -/
@[tactic firstSeek] def evalFirstSeek : Tactic := fun stx => do
  let stamp := stampOf stx
  let alts := stx[2].getArgs.map (·[1])
  for alt in alts do
    let s ← saveState
    let len := (← seekTrace.get).size
    try
      withoutRecover (evalTactic alt)
      let trace ← seekTrace.get
      let mut wins : Std.HashMap Nat (Array Syntax) := {}
      for (j, w) in trace.extract len trace.size do
        let cur := wins.getD j #[]
        if !cur.any (fun x => x.reprint == w.reprint) then wins := wins.insert j (cur.push w)
      let alt' ← liftMacroM <| substitute wins alt
      let win ← match singleTactic? alt' with
        | some t => pure t
        | none => `(tactic| ($(TSyntax.mk alt'):tacticSeq))
      seekTrace.modify fun t => (t.take len).push (stamp, win)
      return
    catch _ =>
      s.restore
      seekTrace.modify (·.take len)
  throwError "piece_first: no alternative ran"

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
  let goalStorey := si.key.toList.foldl (fun m c => if house env c then max m (storeyOf env c) else m) 0
  let reach := inReach p si.key si.self (fun t =>
    match goalHead, (env.find? t).bind (fun ci => headClass ci.type) with
    | some gh, some th => gh == th || th == ``And   -- a conjunction's projections may match
    | _, _ => true) goalStorey
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
    -- choosing the witness: `apply t` may leave a data goal the conclusion did not fix — a probe
    -- `p : F.Probe` whose type is an ENUM (an inductive with only nullary constructors); the side
    -- goals that would fix it are tried before anyone chooses it. so, speculatively: apply, read the
    -- leftover enum goal's binder name from its tag, and offer `apply t (p := C)` for each
    -- constructor, closers after — the winner is plain Lean with a named argument
    let env ← getEnv
    let isEnum (c : Name) : Bool := match env.find? c with
      | some (.ctorInfo ci) => ci.numFields == 0 | _ => false
    let s0 ← saveState
    let mut enumGoals : Array (Name × List Name) := #[]
    try
      setGoals [g]
      withoutRecover (evalTactic (← `(tactic| apply $t)))
      for g' in (← getGoals) do
        let ty ← g'.withContext (do Meta.whnfD (← instantiateMVars (← g'.getType)))
        if let some (.inductInfo ii) := env.find? (ty.getAppFn.constName?.getD .anonymous) then
          if !ii.isRec && ii.ctors.all isEnum then
            let tag ← g'.getTag
            if !tag.isAnonymous && !tag.hasMacroScopes then enumGoals := enumGoals.push (tag, ii.ctors)
    catch _ => pure ()
    s0.restore
    if enumGoals.size == 1 then
      let (tag, ctors) := enumGoals[0]!
      for c in ctors do
        let cid := mkIdent (nameFor si.ns c)
        let tagId := mkIdent tag
        cands := cands.push (← `(tactic| (apply $t ($tagId := $cid) <;> $side)))
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
  let goalStorey := si.key.toList.foldl (fun m c => if house env c then max m (storeyOf env c) else m) 0
  let cites := ((inReach p si.key si.self (goalStorey := goalStorey)).filter fun t => (env.find? t).any (fun ci => isEqn ci.type)).map
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
  let goalStorey := si.key.toList.foldl (fun m c => if house env c then max m (storeyOf env c) else m) 0
  let cites := (((inReach p si.key si.self (goalStorey := goalStorey)).filter fun t => (env.find? t).any (fun ci => isEqn ci.type)).take 6).map
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

/-- seat: elaborate the candidate with every fan a seek and every seek stamped, and report the
body with the winners substituted — that is what the module grows; the artifact never imports
the pieces -/
elab "#seat " c:command : command => do
  let c' ← liftMacroM <| firstsToSeeks c
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
  | none =>
    -- an equations body: the alternatives themselves, as the body the module grows
    match c''.find? (·.isOfKind ``Lean.Parser.Command.declValEqns) with
    | some dv => logInfo m!"{dv}"
    | none => logInfo m!"{c''}"

end Pieces
