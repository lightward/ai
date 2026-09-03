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

def firstOf (alts : Array Seq) : MacroM Tac := do
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
  | `(tactic| piece_cite [$cs,*] [$hs,*] [$_ds,*]) => do
    let c ← citeFull cs.getElems hs.getElems
    -- parenthesized: inside `(…)` the layout is position-free, so the expansion re-parses however
    -- the formatter breaks its lines (a bare `by intros;` + newline ends the sequence early)
    `(tactic| (intros; $c:tactic))

macro_rules
  | `(tactic| piece_home_cite [$cs,*] [$hs,*] [$ds,*]) => do
    let c ← citeFull cs.getElems hs.getElems
    `(tactic| (intros; (try dsimp only [$[$ds:ident],*] at *); intros; first | rfl | assumption | $c:tactic))

macro_rules
  | `(tactic| piece_chain [$cs,*] [$hs,*] [$ds,*]) => do
    let compact ← citeCompact cs.getElems hs.getElems
    let closers ← `(tactic| first | rfl | assumption | $compact:tactic)
    let alts ← chainAlts cs.getElems hs.getElems closers
    let body ← firstOf (#[← `(tacticSeq| rfl), ← `(tacticSeq| assumption)] ++ alts)
    `(tactic| (intros; (try dsimp only [$[$ds:ident],*] at *); intros; $body:tactic))

macro_rules
  | `(tactic| piece_pane [$cs,*] [$hs,*] [$_ds,*]) => do
    let c ← citeFull cs.getElems hs.getElems
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
  | `(tactic| piece_induct_1st [$cs,*] [$hs,*] [$ds,*]) => do
    let c ← citeFull cs.getElems hs.getElems
    let moves ← firstOf (← ihMoves c ds.getElems true)
    `(tactic| (intro x; induction x; all_goals (first | $(← baseCase c) | (rename_i ih; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_2nd [$cs,*] [$hs,*] [$ds,*]) => do
    let c ← citeFull cs.getElems hs.getElems
    let moves ← firstOf (← ihMoves c ds.getElems false)
    `(tactic| (intro _ y; induction y; all_goals (first | $(← baseCase c) | (rename_i ih; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_3rd [$cs,*] [$hs,*] [$ds,*]) => do
    let c ← citeFull cs.getElems hs.getElems
    let moves ← firstOf (← ihMoves c ds.getElems false)
    `(tactic| (intro _ _ z; induction z; all_goals (first | $(← baseCase c) | (rename_i ih; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_two_ih [$cs,*] [$hs,*] [$ds,*]) => do
    let c ← citeFull cs.getElems hs.getElems
    let moves ← firstOf (← twoIhMoves c ds.getElems true)
    `(tactic| (intro x; induction x; all_goals (first | $(← baseCase c) | (rename_i ih₁ ih₂; intros; $moves:tactic))))

macro_rules
  | `(tactic| piece_induct_two_ih_2nd [$cs,*] [$hs,*] [$ds,*]) => do
    let c ← citeFull cs.getElems hs.getElems
    let moves ← firstOf (← twoIhMoves c ds.getElems false)
    `(tactic| (intro _ y; induction y; all_goals (first | $(← baseCase c) | (rename_i ih₁ ih₂; intros; $moves:tactic))))

/-- home → cite → recurse: reduce the goal along its own carriers before any closer lands, then
tighten by the citations, then close by the recursion — two IHs first, then one; rewrites by the
cited names and the statement's own hypotheses as atomic alternatives -/
def homeCiteRecurse (cs hs ds : Array Ident) (second : Bool) : MacroM Tac := do
  let c ← citeFull cs hs
  let compact ← citeCompact cs hs
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

/-- expand only the pieces' own macros, leaving Lean's (`rw`, `try`) as written -/
partial def expandOurs (stx : Syntax) : MacroM Syntax := do
  if let .node _ k _ := stx then
    if (`Pieces).isPrefixOf k then
      if let some stx' ← Macro.expandMacro? stx then return ← expandOurs stx'
  match stx with
  | .node i k args => return .node i k (← args.mapM expandOurs)
  | _ => return stx

/-- seat: elaborate the command with the pieces expanded, and report the body that was
elaborated — the expansion is what the module grows; the artifact never imports the pieces -/
elab "#seat " c:command : command => do
  let c' ← liftMacroM <| expandOurs c
  elabCommand c'
  match c'.find? (·.isOfKind ``Lean.Parser.Command.declValSimple) with
  | some dv => logInfo m!"{dv[1]}"
  | none => logInfo m!"{c'}"

end Pieces
