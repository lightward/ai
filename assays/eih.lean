import Witness
import Roster
open Room Face Witness Roster
set_option autoImplicit false

namespace Eih.Treaty

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

def rose : Party := ⟨1, true, [2, 3]⟩

def linda : Party := ⟨2, true, [1]⟩

def cousin : Party := ⟨3, false, [1, 1]⟩

def guestList : List Party := [linda, cousin, rose]

def demo : Room := ⟨guestList, [], [(7, 1, 900), (8, 1, 1200)], [10, 11, 12], [42], [1, 2]⟩

#guard sheet guestList == [1, 2, 3]
#guard heads guestList == 3
#guard (deliver demo).delivered == [1, 2, 3]
#guard demo.delivered == []
#guard readRoom (deliver demo) .sheet == [1, 2, 3]
#guard readRoom demo .guests == [2, 3, 1]

def floristSees : List Nat := (vendorFace 7).obs demo .mine
#guard floristSees == [900]

def djSees : List Nat := (vendorFace 8).obs demo .mine
#guard djSees == [1200]

def catererSees : List (List Nat) := reads roomFace catererSeat (deliver demo)
#guard catererSees == [[10, 11, 12], [1, 2, 3]]

def lindaSees : List (List Nat) := reads roomFace lindaSeat demo
#guard lindaSees == [[2, 3, 1], [10, 11, 12]]

def bestManSees : List (List Nat) := reads roomFace bestManSeat demo
#guard bestManSees == [[10, 11, 12], [42]]

def coupleSees : List (List Nat) := reads roomFace coupleSeat demo
#guard coupleSees == [[2, 3, 1], [], [900, 1200], [10, 11, 12]]

def roomSees : List (List Nat) := reads roomFace roomSeat demo
#guard roomSees.length == 6

def makerSees : Nat := makerFace.obs demo ()
#guard makerSees == 3
#guard dayOfView.all (enrolled Nat.beq partnerView)
#guard joinsFree .party && !(pays .party)

def moreGuests : Room := withGuests demo (rose :: guestList)

def makerSeesMore : Nat := makerFace.obs moreGuests ()
#guard makerSeesMore == 4

def catererSeesMore : List (List Nat) := reads roomFace catererSeat moreGuests
#guard catererSeesMore == reads roomFace catererSeat demo

def newBach : Room := withBach demo [43]

def bestManSeesNew : List (List Nat) := reads roomFace bestManSeat newBach
#guard bestManSeesNew == [[10, 11, 12], [43]]

def coupleSeesNew : List (List Nat) := reads roomFace coupleSeat newBach
#guard coupleSeesNew == coupleSees

def allConfirmed : Room := withConfirmed demo [1, 2, 7, 8]

def roomSeesConfirmed : List (List Nat) := reads roomFace roomSeat allConfirmed
#guard roomSeesConfirmed != roomSees

def lindaSeesConfirmed : List (List Nat) := reads roomFace lindaSeat allConfirmed
#guard lindaSeesConfirmed == lindaSees

def withInvoice : Room := withLine demo (9, 1, 300)

def lindaSeesInvoice : List (List Nat) := reads roomFace lindaSeat withInvoice
#guard lindaSeesInvoice == lindaSees

def humanEars : List Ask := earshot roomFace humanSeats
#guard humanEars.length == 10
#guard enrolled Ask.beq humanEars .confirmed == false
#guard enrolled Ask.beq humanEars .ledger == true
#guard everyone Nat.beq [1, 2] demo.confirmed
#guard !(everyone Nat.beq [1, 2, 7] demo.confirmed)

theorem the_delivery_is_the_sheet (r : Room) : (deliver r).delivered = sheet r.guests := sorry

theorem the_delivery_moves_no_guest (r : Room) : (deliver r).guests = r.guests := sorry

theorem everyone_clear_means_everyone_confirmed (r : Room) (members : List Nat)
    (h : allClear r members) : ∀ m, m ∈ members → enrolled Nat.beq r.confirmed m = true := sorry

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

theorem linda_never_sees_the_ledger (r : Room) (e : Nat × Nat × Nat) :
    reads roomFace lindaSeat (withLine r e) = reads roomFace lindaSeat r := sorry

theorem the_caterer_never_sees_the_ledger (r : Room) (e : Nat × Nat × Nat) :
    reads roomFace catererSeat (withLine r e) = reads roomFace catererSeat r := sorry

theorem the_caterer_never_sees_the_guests (r : Room) (gl : List Party) :
    reads roomFace catererSeat (withGuests r gl) = reads roomFace catererSeat r := sorry

theorem the_bach_parts_the_best_man (r : Room) (b : List Nat) (hb : b ≠ r.bach) :
    reads roomFace bestManSeat (withBach r b) ≠ reads roomFace bestManSeat r :=
  the_seat_that_hears_it_reads_it roomFace (x := withBach r b) (y := r) (p := .bach) hb bestManSeat (List.Mem.tail _ (List.Mem.head _))

theorem the_receipt_parts_the_room (r : Room) (c : List Nat) (hc : c ≠ r.confirmed) :
    reads roomFace roomSeat (withConfirmed r c) ≠ reads roomFace roomSeat r :=
  the_seat_that_hears_it_reads_it roomFace (x := withConfirmed r c) (y := r) (p := .confirmed) hc roomSeat
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))

theorem the_room_covers_itself : covers roomFace [roomSeat] := sorry

theorem the_room_witnesses_the_license (x y : Room)
    (hw : witnessed roomFace [roomSeat] x y) : alike roomFace x y := sorry

theorem the_caterer_reads_the_delivery (r : Room) :
    readRoom (deliver r) .sheet = sheet r.guests := sorry

theorem a_file_is_never_wider_than_its_channel (f : File) (m : Nat) :
    visible f m ↔ m ∈ f.channel.audience := sorry

theorem join_and_pay_are_unrelated : ∀ ρ : Role, joinsFree ρ = true := sorry

theorem the_party_never_pays : pays .party = false := sorry

theorem lanes_shrink_never_lock : dayOfView.all (enrolled Nat.beq partnerView) = true := sorry

theorem the_maker_sees_shape_not_content (r : Room) (gl gl' : List Party)
    (h : gl.length = gl'.length) : alike makerFace (withGuests r gl) (withGuests r gl') := sorry

theorem everyone_clear_means_rose_ate (r : Room) (members : List Nat) (h : allClear r members)
    {p : Party} (hp : p ∈ r.guests) (hr : p.rsvp = true) {m : Nat} (hm : m ∈ p.meals) :
    m ∈ r.delivered := by
  rw [h.1]
  exact a_yes_reaches_the_sheet hp hr hm

theorem a_quiet_seat_does_not_hear_it (s : List Ask) (p : Ask) (h : enrolled Ask.beq s p = false) :
    ¬ hears roomFace s p := sorry

theorem no_human_hears_the_receipt : ¬ hears roomFace (earshot roomFace humanSeats) .confirmed := sorry

theorem the_bach_wall (r : Room) (b : List Nat) (hb : b ≠ r.bach) :
    reads roomFace coupleSeat (withBach r b) = reads roomFace coupleSeat r
      ∧ reads roomFace bestManSeat (withBach r b) ≠ reads roomFace bestManSeat r := sorry

theorem the_room_alone_holds_the_receipt (r : Room) (c : List Nat) (hc : c ≠ r.confirmed) :
    reads roomFace coupleSeat (withConfirmed r c) = reads roomFace coupleSeat r
      ∧ reads roomFace lindaSeat (withConfirmed r c) = reads roomFace lindaSeat r
      ∧ reads roomFace roomSeat (withConfirmed r c) ≠ reads roomFace roomSeat r := sorry

theorem the_humans_witness_no_license (r : Room) (c : List Nat) (hc : c ≠ r.confirmed) :
    witnessed roomFace humanSeats (withConfirmed r c) r ∧ ¬ alike roomFace (withConfirmed r c) r := by
  refine ⟨fun s hs => ?_, fun ha => hc (ha .confirmed)⟩
  refine a_wall_hides_the_probe roomFace (the_receipt_touches_only_the_receipt r c) s ?_
  exact fun hp => no_human_hears_the_receipt (mem_joinMap_intro hs hp)

theorem everyone_is_here (r : Room) (members : List Nat) (h : allClear r members)
    {p : Party} (hp : p ∈ r.guests) (hr : p.rsvp = true) {m : Nat} (hm : m ∈ p.meals)
    (c : List Nat) (hc : c ≠ r.confirmed) {gl gl' : List Party} (hperm : gl.Perm gl') :
    m ∈ r.delivered
      ∧ (∀ x, x ∈ members → enrolled Nat.beq r.confirmed x = true)
      ∧ (sheet r.guests).length = heads r.guests
      ∧ heads gl = heads gl'
      ∧ reads roomFace roomSeat (withConfirmed r c) ≠ reads roomFace roomSeat r
      ∧ witnessed roomFace humanSeats (withConfirmed r c) r := sorry

end Eih.Treaty
