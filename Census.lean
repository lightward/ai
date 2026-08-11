import Lean

open Lean

def leanModulesIn (dir : System.FilePath) (prefixName : String) :
    IO (Array Name) := do
  let entries ← dir.readDir
  let mut out := #[]
  for e in entries do
    if e.path.extension == some "lean" then
      let stem := e.path.fileStem.getD ""
      out := out.push (prefixName ++ stem).toName
  return out.qsort (fun a b => a.toString < b.toString)

def autoDetail (n : Name) : Bool :=
  n.isInternalDetail
    || n.components.any (fun c =>
        let s := c.toString
        s.startsWith "match_" || s.startsWith "proof_"
          || s.startsWith "eq_" || s.startsWith "noConfusion"
          || s.startsWith "below" || s.startsWith "brec"
          || s.startsWith "ibelow" || s.startsWith "binduction"
          || s == "casesOn" || s == "recOn" || s == "recAux"
          || s == "ctorIdx" || s == "ctorElim" || s == "ctorElimType"
          || s == "toCtorIdx" || s == "ofNat" || s == "elim"
          || s == "mk" || s == "inj" || s == "injEq"
          || s == "sizeOf_spec" || s == "ctorName"
          || s == "ndrec" || s == "ndrecOn" || s == "withCtorType")

def keepKind (env : Environment) (n : Name) (c : ConstantInfo) : Bool :=
  match c with
  | .defnInfo _ => (env.getProjectionFnInfo? n).isNone
  | .thmInfo _ => (env.getProjectionFnInfo? n).isNone
  | .inductInfo _ => true
  | _ => false

def rawUses (c : ConstantInfo) : Array Name :=
  c.type.getUsedConstants
    ++ (match c.value? (allowOpaque := true) with
        | some v => v.getUsedConstants
        | none => #[])

def underFoam (n : Name) : Bool :=
  n.toString == "Foam" || n.toString.startsWith "Foam."

partial def crawl (env : Environment) (inCensus : Name → Bool)
    (seen : Array Name) (work : List Name) (out : Array Name) :
    Array Name :=
  match work with
  | [] => out
  | u :: rest =>
      if seen.contains u then crawl env inCensus seen rest out
      else
        let seen := seen.push u
        if !(underFoam u) then crawl env inCensus seen rest out
        else if inCensus u then
          crawl env inCensus seen rest
            (if out.contains u then out else out.push u)
        else
          match env.constants.find? u with
          | some c =>
              crawl env inCensus seen ((rawUses c).toList ++ rest) out
          | none => crawl env inCensus seen rest out

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut mods := #[`Foam]
  mods := mods ++ (← leanModulesIn ⟨"Foam"⟩ "Foam.")
  mods := mods ++ (← leanModulesIn ⟨"Foam/Maps"⟩ "Foam.Maps.")
  let env ← importModules (mods.map (fun m => { module := m })) {}
  let mut names : Array Name := #[]
  for (n, c) in env.constants.toList do
    if underFoam n && !(autoDetail n) && keepKind env n c then
      names := names.push n
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  let mut out := "{\n  \"census\": [\n"
  out := out ++ String.intercalate ",\n"
    (sorted.toList.map (fun n => s!"    \"{n}\""))
  out := out ++ "\n  ],\n  \"kind\": {\n"
  let mut kindRows : List String := []
  let mut aliasRows : List String := []
  let mut rows : List String := []
  for n in sorted do
    match env.constants.find? n with
    | none => pure ()
    | some c =>
        let k := match c with
          | .thmInfo _ => "thm"
          | .defnInfo _ => "def"
          | .inductInfo _ => "ind"
          | _ => "other"
        kindRows := kindRows ++ [s!"    \"{n}\": \"{k}\""]
        match c.value? (allowOpaque := true) with
        | some (.const t _) => aliasRows := aliasRows ++ [s!"    \"{n}\": \"{t}\""]
        | _ => pure ()
        let deps := crawl env (fun u => sorted.contains u)
          #[n] (rawUses c).toList #[]
        let sortedDeps := deps.qsort (fun a b => a.toString < b.toString)
        rows := rows ++ [s!"    \"{n}\": ["
          ++ String.intercalate ", "
              (sortedDeps.toList.map (fun d => s!"\"{d}\"")) ++ "]"]
  out := out ++ String.intercalate ",\n" kindRows
  out := out ++ "\n  },\n  \"alias\": {\n"
  out := out ++ String.intercalate ",\n" aliasRows
  out := out ++ "\n  },\n  \"graph\": {\n"
  out := out ++ String.intercalate ",\n" rows ++ "\n  }\n}"
  IO.println out
  return 0
