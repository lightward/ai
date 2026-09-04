import Face
open Room Face

namespace Seek

def seeker (close : Nat → Bool) : Machine Nat (List Nat) :=
  ⟨List Nat, [], fun t m => cond (close m) (t ++ [m]) t, fun t => t⟩

def replay (close : Nat → Bool) : Machine Nat (List Nat) :=
  replayer (seeker close)

theorem a_failed_move_leaves_no_trace (close : Nat → Bool) (t : List Nat) (m : Nat)
    (h : close m = false) : park (seeker close) t [m] = t := sorry

theorem a_closing_move_is_recorded (close : Nat → Bool) (t : List Nat) (m : Nat)
    (h : close m = true) : park (seeker close) t [m] = t ++ [m] := sorry

theorem the_trace_is_the_closing_moves (close : Nat → Bool) :
    ∀ (w t : List Nat), park (seeker close) t w = t ++ w.filter close
  | [], t => (the_append_rests t).symm
  | m :: w, t => by
      show park (seeker close) (cond (close m) (t ++ [m]) t) w = t ++ List.filter close (m :: w)
      cases h : close m with
      | true =>
          show park (seeker close) (t ++ [m]) w = t ++ List.filter close (m :: w)
          rw [the_trace_is_the_closing_moves close w (t ++ [m]), the_appends_regroup]
          show t ++ (m :: List.filter close w) = t ++ List.filter close (m :: w)
          rw [List.filter, h]
      | false =>
          show park (seeker close) t w = t ++ List.filter close (m :: w)
          rw [the_trace_is_the_closing_moves close w t]
          show t ++ List.filter close w = t ++ List.filter close (m :: w)
          rw [List.filter, h]

theorem the_replay_is_the_search (close : Nat → Bool) (w : List Nat) :
    behavior (replay close) w = behavior (seeker close) w := sorry

theorem the_search_is_the_replay (close : Nat → Bool) (w : List Nat) :
    behavior (seeker close) w = behavior (replay close) w := sorry

theorem the_audition_cannot_part_them (close : Nat → Bool) :
    ∀ q, sound (airGap Nat (List Nat)) (seeker close) q = sound (airGap Nat (List Nat)) (replay close) q := sorry

theorem the_search_starts_empty (close : Nat → Bool) : (seeker close).s0 = [] := sorry

theorem the_search_and_its_replay_are_alike (close : Nat → Bool) :
    alike (airGap Nat (List Nat)) (seeker close) (replay close) := sorry

theorem the_search_has_no_memory (close : Nat → Bool) (w : List Nat) :
    behavior (seeker close) w = w.filter close := sorry

end Seek
