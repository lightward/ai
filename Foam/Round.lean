import Foam.Engine
import Foam.Marks

namespace Foam

def pull : Compass → Compass → Compass
  | .n, .n => .e
  | .n, .e => .e
  | .n, .s => .e
  | .n, .w => .n
  | .e, .n => .e
  | .e, .e => .s
  | .e, .s => .s
  | .e, .w => .s
  | .s, .n => .w
  | .s, .e => .s
  | .s, .s => .w
  | .s, .w => .w
  | .w, .n => .n
  | .w, .e => .n
  | .w, .s => .w
  | .w, .w => .n

def zipPull : List Compass → List Compass → List Compass
  | c :: cs, d :: ds => pull c d :: zipPull cs ds
  | [], _ => []
  | _ :: _, [] => []

def rotateLeft : List Compass → List Compass
  | [] => []
  | c :: cs => cs ++ [c]

def round (v : List Compass) : List Compass := zipPull v (rotateLeft v)

theorem pull_turns (c d : Compass) :
    pull c.step d.step = (pull c d).step := by
  cases c <;> cases d <;> rfl

theorem the_quarter_turn_moves : ∀ c : Compass, c.step ≠ c
  | .n, h => nomatch h
  | .e, h => nomatch h
  | .s, h => nomatch h
  | .w, h => nomatch h

theorem the_half_turn_parts : ∀ c : Compass, c ≠ c.step.step
  | .n, h => nomatch h
  | .e, h => nomatch h
  | .s, h => nomatch h
  | .w, h => nomatch h

theorem map_snoc (f : Compass → Compass) :
    ∀ (cs : List Compass) (c : Compass),
      (cs ++ [c]).map f = cs.map f ++ [f c]
  | [], _ => rfl
  | d :: cs, c => congrArg (f d :: ·) (map_snoc f cs c)

theorem zipPull_turns :
    ∀ v w : List Compass,
      zipPull (v.map Compass.step) (w.map Compass.step)
        = (zipPull v w).map Compass.step
  | [], _ => rfl
  | _ :: _, [] => rfl
  | c :: cs, d :: ds => by
      show pull c.step d.step
            :: zipPull (cs.map Compass.step) (ds.map Compass.step)
          = (pull c d).step :: (zipPull cs ds).map Compass.step
      rw [pull_turns, zipPull_turns cs ds]

theorem rotate_turns :
    ∀ v : List Compass,
      rotateLeft (v.map Compass.step) = (rotateLeft v).map Compass.step
  | [] => rfl
  | c :: cs => (map_snoc Compass.step cs c).symm

theorem the_round_turns_as_one (v : List Compass) :
    round (v.map Compass.step) = (round v).map Compass.step := by
  show zipPull (v.map Compass.step) (rotateLeft (v.map Compass.step))
      = (zipPull v (rotateLeft v)).map Compass.step
  rw [rotate_turns, zipPull_turns]

theorem len_cons_eq_len_snoc {A : Type} (t : List A) (c d : A) :
    (d :: t).length = (t ++ [c]).length := by
  show t.length + 1 = (t ++ [c]).length
  rw [len_append]
  rfl

theorem zipPull_append :
    ∀ (a b c d : List Compass), a.length = b.length →
      zipPull (a ++ c) (b ++ d) = zipPull a b ++ zipPull c d
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | x :: a, y :: b, c, d, h => by
      show pull x y :: zipPull (a ++ c) (b ++ d)
          = pull x y :: (zipPull a b ++ zipPull c d)
      rw [zipPull_append a b c d (Nat.succ.inj h)]

theorem the_round_hears_no_first_voice :
    ∀ v : List Compass, round (rotateLeft v) = rotateLeft (round v)
  | [] => rfl
  | [_] => rfl
  | c :: d :: t => by
      show zipPull ((d :: t) ++ [c]) ((t ++ [c]) ++ [d])
          = rotateLeft (pull c d :: zipPull (d :: t) (t ++ [c]))
      rw [zipPull_append (d :: t) (t ++ [c]) [c] [d]
            (len_cons_eq_len_snoc t c d)]
      rfl

theorem mem_rotateLeft : ∀ (v : List Compass) (x : Compass),
    x ∈ rotateLeft v → x ∈ v
  | [], _, h => nomatch h
  | c :: cs, _, h =>
      match mem_append_split cs [c] h with
      | .inl hcs => .tail c hcs
      | .inr hc =>
          match hc with
          | .head _ => .head cs
          | .tail _ h' => nomatch h'

theorem mem_zipPull : ∀ (v w : List Compass) (x : Compass),
    x ∈ zipPull v w → ∃ p q, p ∈ v ∧ q ∈ w ∧ x = pull p q
  | [], _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | c :: cs, d :: ds, x, h => by
      have h' : x ∈ pull c d :: zipPull cs ds := h
      cases h' with
      | head => exact ⟨c, d, .head cs, .head ds, rfl⟩
      | tail _ h'' =>
          obtain ⟨p, q, hp, hq, he⟩ := mem_zipPull cs ds x h''
          exact ⟨p, q, .tail c hp, .tail d hq, he⟩

theorem the_round_keeps_unison :
    ∀ v : List Compass,
      (∀ x, x ∈ v → ∀ y, y ∈ v → x = y) →
      ∀ x, x ∈ round v → ∀ y, y ∈ round v → x = y
  | [], _, _, hx, _, _ => nomatch hx
  | c :: cs, h, x, hx, y, hy =>
      match mem_zipPull (c :: cs) (rotateLeft (c :: cs)) x hx,
            mem_zipPull (c :: cs) (rotateLeft (c :: cs)) y hy with
      | ⟨p, q, hp, hq, hex⟩, ⟨p', q', hp', hq', hey⟩ =>
          (hex.trans
            (congr (congrArg pull (h p hp c (.head cs)))
              (h q (mem_rotateLeft (c :: cs) q hq) c (.head cs)))).trans
            ((hey.trans
              (congr (congrArg pull (h p' hp' c (.head cs)))
                (h q' (mem_rotateLeft (c :: cs) q' hq') c (.head cs)))).symm)

theorem the_split_round_carries (a : Compass) :
    round [a, a, a.step.step, a.step.step]
      = [a.step, a.step, a.step.step.step, a.step.step.step] := by
  cases a <;> rfl

/-- info: 'Foam.pull_turns' does not depend on any axioms -/
#guard_msgs in #print axioms pull_turns

/-- info: 'Foam.the_quarter_turn_moves' does not depend on any axioms -/
#guard_msgs in #print axioms the_quarter_turn_moves

/-- info: 'Foam.the_half_turn_parts' does not depend on any axioms -/
#guard_msgs in #print axioms the_half_turn_parts

/-- info: 'Foam.map_snoc' does not depend on any axioms -/
#guard_msgs in #print axioms map_snoc

/-- info: 'Foam.zipPull_turns' does not depend on any axioms -/
#guard_msgs in #print axioms zipPull_turns

/-- info: 'Foam.rotate_turns' does not depend on any axioms -/
#guard_msgs in #print axioms rotate_turns

/-- info: 'Foam.the_round_turns_as_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_round_turns_as_one

/-- info: 'Foam.len_cons_eq_len_snoc' does not depend on any axioms -/
#guard_msgs in #print axioms len_cons_eq_len_snoc

/-- info: 'Foam.zipPull_append' does not depend on any axioms -/
#guard_msgs in #print axioms zipPull_append

/-- info: 'Foam.the_round_hears_no_first_voice' does not depend on any axioms -/
#guard_msgs in #print axioms the_round_hears_no_first_voice

/-- info: 'Foam.mem_rotateLeft' does not depend on any axioms -/
#guard_msgs in #print axioms mem_rotateLeft

/-- info: 'Foam.mem_zipPull' does not depend on any axioms -/
#guard_msgs in #print axioms mem_zipPull

/-- info: 'Foam.the_round_keeps_unison' does not depend on any axioms -/
#guard_msgs in #print axioms the_round_keeps_unison

/-- info: 'Foam.the_split_round_carries' does not depend on any axioms -/
#guard_msgs in #print axioms the_split_round_carries

end Foam
