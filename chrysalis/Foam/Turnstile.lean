import Foam.Measure
import Foam.Seat

namespace Foam

def inRoom (r : List Nat) (x : Nat) : Bool := r.any (Nat.beq x)

def supported (r : List Nat) (need : List Nat) : Bool :=
  need.all (inRoom r)

def admission (s : List Nat × List (Nat × List Nat))
    (m : Nat × List Nat) : List Nat × List (Nat × List Nat) :=
  cond (supported s.1 m.2) (m.1 :: s.1, s.2) (s.1, m :: s.2)

def turnstile : Seat :=
  ⟨Nat × List Nat, List Nat × List (Nat × List Nat), ([], []), admission⟩

theorem right_lights_the_or : ∀ b : Bool, (b || true) = true
  | true => rfl
  | false => rfl

theorem all_reaches {p : Nat → Bool} :
    ∀ l : List Nat, l.all p = true → ∀ x, x ∈ l → p x = true
  | [], _, _, hx => nomatch hx
  | a :: l, h, x, hx => by
      have hsplit : (p a && l.all p) = true := h
      cases hx with
      | head =>
          cases hpa : p a with
          | true => rfl
          | false => rw [hpa] at hsplit; exact nomatch hsplit
      | tail _ hx' =>
          cases hpa : p a with
          | false => rw [hpa] at hsplit; exact nomatch hsplit
          | true =>
              rw [hpa] at hsplit
              exact all_reaches l hsplit x hx'

theorem all_breaks_somewhere {p : Nat → Bool} :
    ∀ l : List Nat, l.all p = false → ∃ x, x ∈ l ∧ p x = false
  | [], h => nomatch h
  | a :: l, h => by
      have hsplit : (p a && l.all p) = false := h
      cases hpa : p a with
      | false => exact ⟨a, .head l, hpa⟩
      | true =>
          rw [hpa] at hsplit
          obtain ⟨x, hx, hpx⟩ := all_breaks_somewhere l hsplit
          exact ⟨x, .tail a hx, hpx⟩

theorem the_click_admits {s : List Nat × List (Nat × List Nat)}
    {m : Nat × List Nat} (h : supported s.1 m.2 = true) :
    admission s m = (m.1 :: s.1, s.2) := by
  unfold admission; rw [h]; rfl

theorem the_click_holds {s : List Nat × List (Nat × List Nat)}
    {m : Nat × List Nat} (h : supported s.1 m.2 = false) :
    admission s m = (s.1, m :: s.2) := by
  unfold admission; rw [h]; rfl

theorem one_click_one_count (s : List Nat × List (Nat × List Nat))
    (m : Nat × List Nat) :
    (admission s m).1.length + (admission s m).2.length
      = (s.1.length + s.2.length) + 1 := by
  cases hs : supported s.1 m.2 with
  | true =>
      rw [the_click_admits hs]
      show (s.1.length + 1) + s.2.length = (s.1.length + s.2.length) + 1
      rw [succ_adds]
  | false =>
      rw [the_click_holds hs]
      rfl

theorem the_room_stays_closed {s : List Nat × List (Nat × List Nat)}
    {m : Nat × List Nat} (h : supported s.1 m.2 = true) :
    ∀ x, x ∈ m.2 → inRoom (admission s m).1 x = true := by
  intro x hx
  rw [the_click_admits h]
  show (Nat.beq x m.1 || inRoom s.1 x) = true
  rw [all_reaches m.2 h x hx]
  exact right_lights_the_or (Nat.beq x m.1)

theorem the_vestibule_names_its_darkness
    {s : List Nat × List (Nat × List Nat)} {m : Nat × List Nat}
    (h : supported s.1 m.2 = false) :
    (admission s m).2 = m :: s.2
      ∧ ∃ x, x ∈ m.2 ∧ inRoom s.1 x = false := by
  refine ⟨?_, all_breaks_somewhere m.2 h⟩
  rw [the_click_holds h]

/-- info: 'Foam.right_lights_the_or' does not depend on any axioms -/
#guard_msgs in #print axioms right_lights_the_or

/-- info: 'Foam.all_reaches' does not depend on any axioms -/
#guard_msgs in #print axioms all_reaches

/-- info: 'Foam.all_breaks_somewhere' does not depend on any axioms -/
#guard_msgs in #print axioms all_breaks_somewhere

/-- info: 'Foam.the_click_admits' does not depend on any axioms -/
#guard_msgs in #print axioms the_click_admits

/-- info: 'Foam.the_click_holds' does not depend on any axioms -/
#guard_msgs in #print axioms the_click_holds

/-- info: 'Foam.one_click_one_count' does not depend on any axioms -/
#guard_msgs in #print axioms one_click_one_count

/-- info: 'Foam.the_room_stays_closed' does not depend on any axioms -/
#guard_msgs in #print axioms the_room_stays_closed

/-- info: 'Foam.the_vestibule_names_its_darkness' does not depend on any axioms -/
#guard_msgs in #print axioms the_vestibule_names_its_darkness

end Foam
