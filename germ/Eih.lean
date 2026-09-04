import Witness
open Room Face Witness

namespace Eih

structure Party where
  name : Nat
  rsvp : Bool
  meals : List Nat

def sheet : List Party → List Nat :=
  joinMap (fun p => cond p.rsvp p.meals [])

def heads : List Party → Nat
  | [] => 0
  | p :: gl => cond p.rsvp p.meals.length 0 + heads gl

structure Room where
  guests : List Party
  delivered : List Nat
  ledger : List (Nat × Nat × Nat)
  timeline : List Nat
  bach : List Nat
  confirmed : List Nat

def deliver (r : Room) : Room := { r with delivered := sheet r.guests }

def withGuests (r : Room) (gl : List Party) : Room := { r with guests := gl }

def withBach (r : Room) (b : List Nat) : Room := { r with bach := b }

def withConfirmed (r : Room) (c : List Nat) : Room := { r with confirmed := c }

def withLine (r : Room) (e : Nat × Nat × Nat) : Room := { r with ledger := e :: r.ledger }

def allClear (r : Room) (members : List Nat) : Prop :=
  r.delivered = sheet r.guests ∧ everyone Nat.beq members r.confirmed = true

inductive Ask where
  | guests | sheet | ledger | timeline | bach | confirmed

def Ask.code : Ask → Nat
  | .guests => 0 | .sheet => 1 | .ledger => 2 | .timeline => 3 | .bach => 4 | .confirmed => 5

def Ask.beq (a b : Ask) : Bool := Nat.beq a.code b.code

def readRoom (r : Room) : Ask → List Nat
  | .guests => r.guests.map (·.name)
  | .sheet => r.delivered
  | .ledger => r.ledger.map (·.2.2)
  | .timeline => r.timeline
  | .bach => r.bach
  | .confirmed => r.confirmed

def roomFace : Face := ⟨Room, Ask, List Nat, readRoom⟩

def roomSeat : List Ask := [.guests, .sheet, .ledger, .timeline, .bach, .confirmed]

def coupleSeat : List Ask := [.guests, .sheet, .ledger, .timeline]

def lindaSeat : List Ask := [.guests, .timeline]

def bestManSeat : List Ask := [.timeline, .bach]

def catererSeat : List Ask := [.timeline, .sheet]

def humanSeats : List (List Ask) := [coupleSeat, lindaSeat, bestManSeat, catererSeat]

inductive VendorAsk where
  | timeline | mine

def vendorFace (v : Nat) : Face :=
  ⟨Room, VendorAsk, List Nat, fun r q => match q with
    | .timeline => r.timeline
    | .mine => (r.ledger.filter (fun e => Nat.beq e.1 v)).map (·.2.2)⟩

def makerFace : Face := ⟨Room, Unit, Nat, fun r _ => r.guests.length⟩

structure Channel where
  audience : List Nat

structure File where
  channel : Channel

def visible (f : File) (m : Nat) : Prop := m ∈ f.channel.audience

inductive Role where
  | couple | planner | vendor | party

def joinsFree : Role → Bool := fun _ => true

def pays : Role → Bool
  | .couple => true | .vendor => true | .planner => true | .party => false

def partnerView : List Nat := [0, 1, 2, 3, 4, 5]

def dayOfView : List Nat := [0, 1, 2, 3, 4]

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

theorem the_delivery_is_the_sheet (r : Room) : (deliver r).delivered = sheet r.guests := sorry

theorem the_delivery_moves_no_guest (r : Room) : (deliver r).guests = r.guests := sorry

theorem everyone_clear_means_everyone_confirmed (r : Room) (members : List Nat)
    (h : allClear r members) : ∀ m, m ∈ members → enrolled Nat.beq r.confirmed m = true := sorry

theorem reseating_keeps_the_heads {gl gl' : List Party} (h : gl.Perm gl') : heads gl = heads gl' := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (cond a.rsvp a.meals.length 0 + ·) ih
  | swap a b l =>
      show cond b.rsvp b.meals.length 0 + (cond a.rsvp a.meals.length 0 + heads l)
        = cond a.rsvp a.meals.length 0 + (cond b.rsvp b.meals.length 0 + heads l)
      exact Nat.add_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem a_line_touches_only_the_ledger (r : Room) (e : Nat × Nat × Nat) :
    differOnly roomFace (withLine r e) r .ledger :=
  fun q hq => by cases q <;> first | rfl | exact absurd rfl hq

theorem the_bach_touches_only_the_bach (r : Room) (b : List Nat) :
    differOnly roomFace (withBach r b) r .bach :=
  fun q hq => by cases q <;> first | rfl | exact absurd rfl hq

theorem the_receipt_touches_only_the_receipt (r : Room) (c : List Nat) :
    differOnly roomFace (withConfirmed r c) r .confirmed :=
  fun q hq => by cases q <;> first | rfl | exact absurd rfl hq

theorem the_guests_touch_only_the_guests (r : Room) (gl : List Party) :
    differOnly roomFace (withGuests r gl) r .guests :=
  fun q hq => by cases q <;> first | rfl | exact absurd rfl hq

theorem a_vendor_never_sees_anothers_invoice (v w : Nat) (hvw : Nat.beq w v = false) (r : Room)
    (amount to : Nat) :
    alike (vendorFace v) (withLine r (w, to, amount)) r := by
  intro q
  cases q with
  | timeline => rfl
  | mine =>
      show ((( w, to, amount) :: r.ledger).filter (fun e => Nat.beq e.1 v)).map (·.2.2)
        = (r.ledger.filter (fun e => Nat.beq e.1 v)).map (·.2.2)
      rw [List.filter, hvw]

theorem an_ask_reads_itself : ∀ q : Ask, Ask.beq q q = true := sorry

theorem a_quiet_seat_does_not_hear_it (s : List Ask) (p : Ask) (h : enrolled Ask.beq s p = false) :
    ¬ hears roomFace s p := sorry

theorem everyone_clear_means_rose_ate (r : Room) (members : List Nat) (h : allClear r members)
    {p : Party} (hp : p ∈ r.guests) (hr : p.rsvp = true) {m : Nat} (hm : m ∈ p.meals) :
    m ∈ r.delivered := by
  rw [h.1]
  exact a_yes_reaches_the_sheet hp hr hm

theorem reseating_keeps_the_sheets_count {gl gl' : List Party} (h : gl.Perm gl') :
    (sheet gl).length = (sheet gl').length := sorry

end Eih
