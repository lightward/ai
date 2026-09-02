-- primings: the ordered moves the crawl tries when a vacancy has a statement
-- and no body. each priming is a Lean proof shape — a piece that is also a
-- rule. the crawl offers them in this order and seats the first that reads
-- silent; what no priming regrows is carried from the trail and NAMED as the
-- trail's own remainder. one macro: {cite} expands to the vacancy's need-list
-- (the names its trail-proof cites, in trail order) as
--   first | (apply n1 <;> (first | assumption | rfl)) | (apply n2 <;> …) | …
-- a second macro: {defs} expands to the carriers (defs) the vacancy's statement
-- cites, comma-separated, for `dsimp only [{defs}]` — let the goal reduce along
-- its own definitions before a closer unifies against it.
-- a third: {rws} expands to `try rw [n1]; try rw [n2]; …` over the need-list —
-- the cite move in rewrite clothing, applied in order, each one optional.
-- grammar: a line `-- priming: <name>` opens a priming; the lines until the
-- next opener are its body. a line `-- budget: <heartbeats>` sets the fuel each
-- candidate may burn (Lean's own maxHeartbeats); a shape that cannot close within
-- it is held, not ground — the remainder is what the fuel cannot reach.

-- budget: 20000

-- priming: rfl
rfl

-- priming: Iff.rfl
Iff.rfl

-- priming: fun _ => rfl
fun _ => rfl

-- priming: fun _ _ => rfl
fun _ _ => rfl

-- priming: intros; rfl
by intros; rfl

-- priming: cite
by intros; {cite}

-- priming: pane
by
  intros
  repeat' constructor
  all_goals (intros; first | rfl | {cite})

-- priming: induction
by
  intro x
  induction x
  all_goals (first
    | (intros; first | rfl | assumption | {cite})
    | (rename_i ih; intros; first
        | exact ih
        | exact ih _
        | exact ih _ _
        | exact congrArg _ ih
        | exact congrArg _ (ih _)
        | exact congrArg _ (ih _ _)
        | (rw [ih])
        | (rw [ih]; {cite})
        | exact (ih _).trans (by {cite})
        | exact (ih _ _).trans (by {cite})
        | exact (ih _ _ _).trans (by {cite})
        | (dsimp only [{defs}]; first
            | exact congrArg _ ih
            | exact congrArg _ (ih _)
            | (rw [ih])
            | (rw [ih]; {cite})
            | (rw [ih _]; {cite})
            | exact (ih _).trans (by {cite})
            | exact (ih _ _).trans (by {cite}))))

-- priming: induction-2nd
by
  intro _ y
  induction y
  all_goals (first
    | (intros; first | rfl | assumption | {cite})
    | (rename_i ih; intros; first
        | exact ih
        | exact ih _
        | exact ih _ _
        | exact congrArg _ ih
        | exact congrArg _ (ih _)
        | exact congrArg _ (ih _ _)
        | (rw [ih])
        | (rw [ih]; {cite})
        | exact (ih _).trans (by {cite})
        | exact (ih _ _).trans (by {cite})
        | exact (ih _ _ _).trans (by {cite})))

-- priming: induction-3rd
by
  intro _ _ z
  induction z
  all_goals (first
    | (intros; first | rfl | assumption | {cite})
    | (rename_i ih; intros; first
        | exact ih
        | exact ih _
        | exact ih _ _
        | exact congrArg _ ih
        | exact congrArg _ (ih _)
        | exact congrArg _ (ih _ _)
        | (rw [ih])
        | (rw [ih]; {cite})
        | exact (ih _).trans (by {cite})
        | exact (ih _ _).trans (by {cite})
        | exact (ih _ _ _).trans (by {cite})))

-- priming: induction-two-ih
by
  intro x
  induction x
  all_goals (first
    | (intros; first | rfl | assumption | {cite})
    | (rename_i ih₁ ih₂; intros; first
        | exact congr (congrArg _ ih₁) ih₂
        | exact congrArg₂ _ ih₁ ih₂
        | (rw [ih₁, ih₂])
        | (rw [ih₁, ih₂]; {cite})
        | (rw [ih₁ _, ih₂ _])
        | (rw [ih₁ _, ih₂ _]; {cite})
        | exact congr (congrArg _ (ih₁ _)) (ih₂ _)
        | exact (congr (congrArg _ (ih₁ _)) (ih₂ _)).trans (by {cite})
        | exact (by {cite} : _ = _).trans (congr (congrArg _ ih₁) ih₂)
        | exact (by {cite} : _ = _).trans (congr (congrArg _ (ih₁ _)) (ih₂ _))
        | (dsimp only [{defs}]; first
            | exact congr (congrArg _ ih₁) ih₂
            | exact congr (congrArg _ (ih₁ _)) (ih₂ _)
            | (rw [ih₁, ih₂])
            | (rw [ih₁ _, ih₂ _])
            | (rw [ih₁, ih₂]; {cite})
            | (rw [ih₁ _, ih₂ _]; {cite})
            | exact (congr (congrArg _ (ih₁ _)) (ih₂ _)).trans (by {cite})
            | exact (by {cite} : _ = _).trans (congr (congrArg _ ih₁) ih₂))))

-- priming: induction-two-ih-2nd
by
  intro _ y
  induction y
  all_goals (first
    | (intros; first | rfl | assumption | {cite})
    | (rename_i ih₁ ih₂; intros; first
        | exact congr (congrArg _ ih₁) ih₂
        | (rw [ih₁, ih₂])
        | (rw [ih₁ _, ih₂ _])
        | exact congr (congrArg _ (ih₁ _)) (ih₂ _)
        | exact (congr (congrArg _ (ih₁ _)) (ih₂ _)).trans (by {cite})))

-- priming: home-cite-recurse
by
  intro x
  induction x
  all_goals (first
    | (intros; first | rfl | assumption | {cite})
    | (rename_i ih₁ ih₂; intros; (try dsimp only [{defs}] at *); {rws}; first
        | rfl
        | exact congr (congrArg _ ih₁) ih₂
        | exact congr (congrArg _ (ih₁ _)) (ih₂ _)
        | (rw [ih₁, ih₂])
        | (rw [ih₁ _, ih₂ _])
        | (rw [ih₁, ih₂]; {cite})
        | (rw [ih₁ _, ih₂ _]; {cite})
        | exact (congr (congrArg _ (ih₁ _)) (ih₂ _)).trans (by {cite})
        | exact (by {cite} : _ = _).trans (congr (congrArg _ ih₁) ih₂))
    | (rename_i ih; intros; (try dsimp only [{defs}] at *); {rws}; first
        | rfl
        | exact ih
        | exact ih _
        | exact ih _ _
        | exact congrArg _ ih
        | exact congrArg _ (ih _)
        | exact congrArg _ (ih _ _)
        | (rw [ih])
        | (rw [ih _])
        | (rw [ih _ _])
        | (rw [ih]; {cite})
        | (rw [ih _]; {cite})
        | exact (ih _).trans (by {cite})
        | exact (ih _ _).trans (by {cite})))

-- priming: home-cite-recurse-2nd
by
  intro _ y
  induction y
  all_goals (first
    | (intros; first | rfl | assumption | {cite})
    | (rename_i ih₁ ih₂; intros; (try dsimp only [{defs}] at *); {rws}; first
        | rfl
        | exact congr (congrArg _ ih₁) ih₂
        | exact congr (congrArg _ (ih₁ _)) (ih₂ _)
        | (rw [ih₁, ih₂])
        | (rw [ih₁ _, ih₂ _])
        | (rw [ih₁, ih₂]; {cite})
        | (rw [ih₁ _, ih₂ _]; {cite})
        | exact (congr (congrArg _ (ih₁ _)) (ih₂ _)).trans (by {cite})
        | exact (by {cite} : _ = _).trans (congr (congrArg _ ih₁) ih₂))
    | (rename_i ih; intros; (try dsimp only [{defs}] at *); {rws}; first
        | rfl
        | exact ih
        | exact ih _
        | exact ih _ _
        | exact congrArg _ ih
        | exact congrArg _ (ih _)
        | exact congrArg _ (ih _ _)
        | (rw [ih])
        | (rw [ih _])
        | (rw [ih _ _])
        | (rw [ih]; {cite})
        | (rw [ih _]; {cite})
        | exact (ih _).trans (by {cite})
        | exact (ih _ _).trans (by {cite})))
