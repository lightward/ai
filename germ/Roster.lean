import Room
open Room

namespace Roster

structure Party where
  name : Nat
  rsvp : Bool
  meals : List Nat

def sheet : List Party → List Nat :=
  joinMap (fun p => cond p.rsvp p.meals [])

def heads : List Party → Nat
  | [] => 0
  | p :: gl => cond p.rsvp p.meals.length 0 + heads gl

theorem the_sheet_counts_the_heads : ∀ gl : List Party, (sheet gl).length = heads gl
  | [] => rfl
  | p :: gl => by
      show (cond p.rsvp p.meals [] ++ sheet gl).length = cond p.rsvp p.meals.length 0 + heads gl
      cases h : p.rsvp with
      | true =>
          show (p.meals ++ sheet gl).length = p.meals.length + heads gl
          rw [lengths_add, the_sheet_counts_the_heads gl]
      | false =>
          show (sheet gl).length = 0 + heads gl
          rw [zero_add, the_sheet_counts_the_heads gl]

theorem a_yes_reaches_the_sheet {p : Party} {gl : List Party} (hp : p ∈ gl)
    (hr : p.rsvp = true) {m : Nat} (hm : m ∈ p.meals) : m ∈ sheet gl :=
  mem_joinMap_intro hp (by show m ∈ cond p.rsvp p.meals []; rw [hr]; exact hm)

theorem reseating_keeps_the_heads {gl gl' : List Party} (h : gl.Perm gl') : heads gl = heads gl' := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (cond a.rsvp a.meals.length 0 + ·) ih
  | swap a b l =>
      show cond b.rsvp b.meals.length 0 + (cond a.rsvp a.meals.length 0 + heads l)
        = cond a.rsvp a.meals.length 0 + (cond b.rsvp b.meals.length 0 + heads l)
      exact Nat.add_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem reseating_keeps_the_sheets_count {gl gl' : List Party} (h : gl.Perm gl') :
    (sheet gl).length = (sheet gl').length := sorry

end Roster
