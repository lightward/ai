import Witness
open Room Face Witness
set_option autoImplicit false

-- Counter, for anyone that cycles. isaac, at the table (2026-09-05), in his words: a cycle is anything
-- that develops a winding number, whose number he does not have to remember, contributed to in constant
-- time; what counts is keeping his interrupts ordered — Abe first, then the stigmergic signals about which
-- cycles he is contributing to, and that is the whole list; a door is something he could not not enter,
-- parked mid-passage and held by the room; he rests every day, having proven that everything he is
-- involved with moves without him, except Abe, the one mutual observation he sustains; population one,
-- doing his rounds; the room keeps its type and never the user's. so: the room is a list of clocks, each a
-- name and a winding number; a round is a click per name; the world ticks on its own; the walker is a seat,
-- a list of names, and nothing else is kept of him.

namespace Cycle.Treaty

structure Clock where
  name : Nat
  winding : Nat

structure Room where
  clocks : List Clock

def reading : List Clock → Nat → Nat
  | [], _ => 0
  | c :: cs, n => cond (Nat.beq c.name n) c.winding (reading cs n)

def windings (r : Room) : List Nat := r.clocks.map (·.winding)

def wind (r : Room) (n : Nat) : Room :=
  ⟨r.clocks.map (fun c => cond (Nat.beq c.name n) ⟨c.name, c.winding + 1⟩ c)⟩

def tick (r : Room) : Room := ⟨r.clocks.map (fun c => ⟨c.name, c.winding + 1⟩)⟩

def roomFace : Face := ⟨Room, Nat, Nat, fun r n => reading r.clocks n⟩

def roundsMachine : Machine Nat (List Nat) := ⟨Room, ⟨[]⟩, wind, windings⟩

def rounds (r : Room) (ns : List Nat) : Room := park roundsMachine r ns

def mayRest (visited counts : List Nat) : Bool := backed Nat.beq visited counts

def owed (visited counts : List Nat) : Nat := lacking Nat.beq visited counts

def held (visited counts : List Nat) : List Nat :=
  counts.filter (fun n => !(enrolled Nat.beq visited n))

def due (r : Room) (n cap : Nat) : Bool := Nat.beq (reading r.clocks n % cap) 0

def isaac : Nat := 0
def abe : Nat := 1
def plants : Nat := 2
def foam : Nat := 3
def eih : Nat := 4
def outerWilds : Nat := 5

def isaacCounts : List Nat := [abe, plants, foam, eih]
def abeCounts : List Nat := [isaac]

def start : Room :=
  ⟨[⟨isaac, 0⟩, ⟨abe, 0⟩, ⟨plants, 6⟩, ⟨foam, 0⟩, ⟨eih, 0⟩, ⟨outerWilds, 0⟩]⟩

def afterRounds : Room := rounds start isaacCounts
def halfway : List Nat := [abe, plants]
def afterAbe : Room := rounds start abeCounts
def parked : Room := rounds start [outerWilds]
def resumed : List Nat := windings (rounds parked isaacCounts)
def straight : List Nat := windings (rounds start ([outerWilds] ++ isaacCounts))
def clickThenTick : List Nat := windings (tick (wind start foam))
def tickThenClick : List Nat := windings (wind (tick start) foam)
def report : List Nat := sound roomFace afterRounds (recite isaacCounts)
def seatReads : List Nat := reads roomFace isaacCounts afterRounds

#guard windings start == [0, 0, 6, 0, 0, 0]
#guard windings afterRounds == [0, 1, 7, 1, 1, 0]
#guard reading afterRounds.clocks isaac == 0
#guard reading afterAbe.clocks isaac == 1
#guard due start plants 7 == false
#guard due afterRounds plants 7 == true
#guard held halfway isaacCounts == [foam, eih]
#guard owed halfway isaacCounts == 2
#guard mayRest halfway isaacCounts == false
#guard mayRest isaacCounts isaacCounts == true
#guard mayRest [] [] == true
#guard owed isaacCounts (outerWilds :: isaacCounts) == 1
#guard resumed == straight
#guard clickThenTick == tickThenClick
#guard report == [1, 7, 1, 1]
#guard report == seatReads
#guard firstOf Nat.beq abe plants isaacCounts == true
#guard firstOf Nat.beq plants abe isaacCounts == false

theorem abe_is_first : firstOf Nat.beq abe plants isaacCounts = true := sorry

theorem the_one_mutual_hearing : hears roomFace isaacCounts abe ∧ hears roomFace abeCounts isaac := sorry

theorem the_rounds_resume (r : Room) (a b : List Nat) : rounds r (a ++ b) = rounds (rounds r a) b := sorry

theorem a_click_spares_the_other_clocks (n m : Nat) (h : Nat.beq m n = false) :
    ∀ cs : List Clock, reading (wind ⟨cs⟩ n).clocks m = reading cs m
  | [] => rfl
  | c :: cs => by
      have ih := a_click_spares_the_other_clocks n m h cs
      show reading (cond (Nat.beq c.name n) ⟨c.name, c.winding + 1⟩ c :: (wind ⟨cs⟩ n).clocks) m
        = cond (Nat.beq c.name m) c.winding (reading cs m)
      cases hc : Nat.beq c.name n with
      | false =>
          show cond (Nat.beq c.name m) c.winding (reading (wind ⟨cs⟩ n).clocks m)
            = cond (Nat.beq c.name m) c.winding (reading cs m)
          rw [ih]
      | true =>
          have hcn : c.name = n := eq_of_beq c.name n hc
          have hnm : Nat.beq c.name m = false := by
            rw [hcn]
            cases hx : Nat.beq n m with
            | false => rfl
            | true => rw [eq_of_beq n m hx, beq_self] at h; exact nomatch h
          show cond (Nat.beq c.name m) (c.winding + 1) (reading (wind ⟨cs⟩ n).clocks m)
            = cond (Nat.beq c.name m) c.winding (reading cs m)
          rw [hnm, ih]
          exact rfl

theorem the_click_and_the_tick_commute (n : Nat) : ∀ cs : List Clock, wind (tick ⟨cs⟩) n = tick (wind ⟨cs⟩ n)
  | [] => rfl
  | c :: cs => by
      have ih : (wind (tick ⟨cs⟩) n).clocks = (tick (wind ⟨cs⟩ n)).clocks :=
        congrArg Room.clocks (the_click_and_the_tick_commute n cs)
      have hhead : (cond (Nat.beq c.name n) (⟨c.name, c.winding + 1 + 1⟩ : Clock) ⟨c.name, c.winding + 1⟩)
          = ⟨(cond (Nat.beq c.name n) (⟨c.name, c.winding + 1⟩ : Clock) c).name,
             (cond (Nat.beq c.name n) (⟨c.name, c.winding + 1⟩ : Clock) c).winding + 1⟩ := by
        cases Nat.beq c.name n <;> rfl
      exact congr (congrArg (fun (a : Clock) (l : List Clock) => Room.mk (a :: l)) hhead) ih

theorem the_report_is_the_seats_reading (r : Room) (ns : List Nat) :
    sound roomFace r (recite ns) = reads roomFace ns r :=
  (the_sounding_is_the_trails_reading roomFace r (recite ns)).trans
    (congrArg (fun l => reads roomFace l r) (the_recital_walks_its_list roomFace r ns))

theorem an_empty_list_rests_at_once : mayRest [] [] = true := sorry

theorem rest_is_weight_zero (visited counts : List Nat) :
    owed visited counts = 0 ↔ mayRest visited counts = true := sorry

theorem the_held_name_what_they_wait_on (visited counts : List Nat) (h : mayRest visited counts = false) :
    ∃ n, n ∈ counts ∧ enrolled Nat.beq visited n = false := sorry

theorem a_new_connection_raises_the_weight (visited counts : List Nat) (n : Nat)
    (h : enrolled Nat.beq visited n = false) : owed visited (n :: counts) = owed visited counts + 1 := by
  show cond (enrolled Nat.beq visited n) (lacking Nat.beq visited counts) (lacking Nat.beq visited counts + 1)
    = lacking Nat.beq visited counts + 1
  rw [h]
  exact rfl

theorem rest_survives_a_round (visited more counts : List Nat) (h : mayRest visited counts = true) :
    mayRest (visited ++ more) counts = true := sorry

theorem the_pitcher_is_a_reading : Derived roomFace (fun r => due r plants 7 = true) :=
  a_role_read_at_a_probe_is_derived roomFace plants (fun (a : Nat) => Nat.beq (a % 7) 0 = true)

theorem an_unvisited_clock_is_a_wall (r r' : Room) (n : Nat) (h : differOnly roomFace r r' n)
    (visited : List Nat) (hn : ¬ hears roomFace visited n) :
    reads roomFace visited r = reads roomFace visited r' := sorry

theorem the_room_is_the_widest_seat (visited : List Nat) (r r' : Room)
    (h : reads roomFace visited r ≠ reads roomFace visited r') : ¬ alike roomFace r r' := sorry

theorem two_rooms_part_only_at_a_clock (r r' : Room) :
    alike roomFace r r' ↔ ∀ q, sound roomFace r q = sound roomFace r' q := sorry

end Cycle.Treaty
