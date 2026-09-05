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

def canSee (f : File) (m : Nat) : Bool := enrolled Nat.beq f.channel.audience m

inductive Role where
  | couple | planner | vendor | venue | party

def Role.code : Role → Nat
  | .couple => 0 | .planner => 1 | .vendor => 2 | .venue => 3 | .party => 4

def Role.beq (a b : Role) : Bool := Nat.beq a.code b.code

def joinsFree : Role → Bool := fun _ => true

def pays : Role → Bool
  | .couple => true | .vendor => true | .planner => true | .venue => true | .party => false

structure Request where
  audience : List Nat
  sender : Nat
  confirmed : List Nat

def asked (q : Request) : List Nat := q.audience.filter (fun m => !(Nat.beq m q.sender))

def tally (q : Request) : Nat := (q.confirmed.filter (enrolled Nat.beq (asked q))).length

def heardBy (q : Request) (m : Nat) : List Nat := cond (enrolled Nat.beq q.audience m) q.confirmed []

def confirm (q : Request) (m : Nat) : Request := { q with confirmed := m :: q.confirmed }

def samePage : List Request → Nat → Nat
  | [], _ => 0
  | q :: qs, v => cond (enrolled Nat.beq q.audience v) (tally q + samePage qs v) (samePage qs v)

inductive Thing where
  | wedding | season

def owner : Thing → Role
  | .wedding => .couple | .season => .vendor

structure Bill where
  thing : Thing
  payer : Role

def lawful (b : Bill) : Bool := Role.beq b.payer (owner b.thing) || (Role.beq b.payer .vendor && Role.beq (owner b.thing) .couple)

inductive Page where
  | floorPlan | guestList | samePage | invoices | budget | guests | site | team | dayOf | tasks

def Page.code : Page → Nat
  | .floorPlan => 0 | .guestList => 1 | .samePage => 2 | .invoices => 3 | .budget => 4
  | .guests => 5 | .site => 6 | .team => 7 | .dayOf => 8 | .tasks => 9

def Page.beq (a b : Page) : Bool := Nat.beq a.code b.code

def roles : List Role := [.couple, .planner, .vendor, .venue, .party]

def pages : List Page := [.floorPlan, .guestList, .samePage, .invoices, .budget, .guests, .site, .team, .dayOf, .tasks]

def seen : Role → List Page
  | .couple => pages
  | .planner => [.floorPlan, .guestList, .samePage, .invoices, .team, .dayOf, .tasks]
  | .vendor => [.floorPlan, .samePage, .invoices, .team, .dayOf, .tasks]
  | .venue => [.floorPlan, .samePage, .invoices, .team, .dayOf, .tasks]
  | .party => [.floorPlan, .guestList, .samePage, .team, .dayOf, .tasks]

def edited : Role → List Page
  | .couple => pages
  | .planner => [.floorPlan, .guestList, .invoices, .team, .dayOf, .tasks]
  | .vendor => [.invoices, .dayOf, .tasks]
  | .venue => [.floorPlan, .invoices, .dayOf, .tasks]
  | .party => [.floorPlan, .guestList, .dayOf, .tasks]

def sees (ρ : Role) (p : Page) : Bool := enrolled Page.beq (seen ρ) p

def edits (ρ : Role) (p : Page) : Bool := enrolled Page.beq (edited ρ) p

def withinSight : Bool := roles.all (fun ρ => pages.all (fun p => !(edits ρ p) || sees ρ p))

structure Member where
  user : Nat
  role : Role
  kind : Nat
  dayLane : Bool
  arrival : Nat
  phone : Nat

def vendorSide (m : Member) : Bool :=
  Role.beq m.role .vendor || (Role.beq m.role .venue || Role.beq m.role .planner)

def vendorRoomMembers (roster : List Member) : List Member := roster.filter vendorSide

def vendorRoomAudience (roster : List Member) : List Nat := (vendorRoomMembers roster).map (·.user)

def channelAudience (roster : List Member) (p : Member → Bool) : List Nat := (roster.filter p).map (·.user)

def vendorRoomRequestOf (roster : List Member) (sender : Nat) (confirmed : List Nat) : Request :=
  ⟨vendorRoomAudience roster, sender, confirmed⟩

structure Task where
  owner : Nat
  assignee : Nat
  done : Bool

def mayClose (m : Member) (t : Task) : Bool :=
  Nat.beq m.user t.owner || (Role.beq m.role .couple || Role.beq m.role .planner)

def close (t : Task) : Task := { t with done := true }

def assign (t : Task) (to : Nat) : Task := { t with assignee := to }

structure DayOfEdit where
  who : Nat
  row : Nat
  before : Nat
  after : Nat

def dayOfLog : Machine DayOfEdit (List DayOfEdit) := ledger DayOfEdit

def undo : List Nat → List Nat
  | [] => []
  | [_] => []
  | x :: y :: w => x :: undo (y :: w)

structure Table where
  shape : Nat
  occupants : List Nat

def venueTable (t : Table) : Nat × Nat := (t.shape, t.occupants.length)

def venueChart (c : List Table) : List (Nat × Nat) := c.map venueTable

def total : List Nat → Nat
  | [] => 0
  | x :: xs => x + total xs

def seasonView (rs : List Room) (v : Nat) : List (List Nat) := rs.map (fun r => (vendorFace v).obs r .mine)

def seasonOwed (rs : List Room) (v : Nat) : Nat := total (joinMap (fun r => (vendorFace v).obs r .mine) rs)

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

def everyoneChannel : Request := ⟨[1, 2, 7, 8, 9], 1, [7, 8]⟩
def vendorRoomRequest : Request := ⟨[7, 8, 9], 9, [7]⟩
def maya : Nat := 1
def jordan : Nat := 7
#guard asked everyoneChannel == [2, 7, 8, 9]
#guard tally everyoneChannel == 2
#guard heardBy everyoneChannel jordan == [7, 8]
#guard heardBy everyoneChannel maya == [7, 8]
#guard heardBy vendorRoomRequest maya == []
#guard heardBy vendorRoomRequest jordan == [7]
#guard tally (confirm everyoneChannel 2) == 3
#guard samePage [everyoneChannel, vendorRoomRequest] maya == 2
#guard samePage [everyoneChannel, vendorRoomRequest] jordan == 3
def coveredWedding : Bill := ⟨.wedding, .vendor⟩
def ownWedding : Bill := ⟨.wedding, .couple⟩
def strayBill : Bill := ⟨.season, .couple⟩
#guard lawful coveredWedding && lawful ownWedding && !(lawful strayBill)
#guard Role.beq (owner coveredWedding.thing) .couple
#guard withinSight
#guard sees .venue .floorPlan && edits .venue .floorPlan && !(sees .venue .guestList)
#guard sees .vendor .floorPlan && !(edits .vendor .floorPlan)
#guard pays .venue && joinsFree .venue && !(pays .party)
def vendorRoomChannel : Channel := ⟨[7, 8, 9]⟩
def vendorRoomFile : File := ⟨vendorRoomChannel⟩
#guard !(canSee vendorRoomFile maya)
#guard canSee vendorRoomFile jordan

def mayaM : Member := ⟨1, .couple, 0, false, 15, 0⟩
def lindaM : Member := ⟨2, .party, 0, true, 14, 0⟩
def jordanM : Member := ⟨7, .vendor, 1, false, 12, 0⟩
def djM : Member := ⟨8, .vendor, 2, false, 13, 0⟩
def sofiaM : Member := ⟨9, .vendor, 3, false, 11, 0⟩
def roster : List Member := [mayaM, lindaM, jordanM, djM, sofiaM]
#guard vendorRoomAudience roster == [7, 8, 9]
#guard !(enrolled Nat.beq (vendorRoomAudience roster) 1)
#guard !(enrolled Nat.beq (vendorRoomAudience roster) 2)
#guard (vendorRoomRequestOf roster 9 [7]).audience == vendorRoomRequest.audience
#guard vendorRoomAudience [mayaM, lindaM, jordanM] == [7]
def loadIn : Task := ⟨7, 7, false⟩
#guard mayClose jordanM loadIn && mayClose mayaM loadIn && !(mayClose sofiaM loadIn)
#guard (close loadIn).done
#guard (assign loadIn 9).assignee == 9
#guard undo [1, 2, 3] == [1, 2]
#guard undo [1] == []
def firstEdit : DayOfEdit := ⟨9, 3, 100, 130⟩
def secondEdit : DayOfEdit := ⟨7, 5, 600, 615⟩
#guard (behavior dayOfLog [firstEdit, secondEdit]).length == 2
#guard (behavior dayOfLog [firstEdit, secondEdit]).map (·.who) == [9, 7]
def headTable : Table := ⟨0, [1, 2, 3]⟩
def table2 : Table := ⟨1, [4]⟩
#guard venueChart [headTable, table2] == [(0, 3), (1, 1)]
#guard venueChart [⟨0, [4, 5, 6]⟩, table2] == venueChart [headTable, table2]
#guard seasonView [demo, withInvoice] 7 == [[900], [900]]
#guard seasonView [demo, withInvoice] 9 == [[], [300]]
#guard seasonOwed [demo, withInvoice] 7 == 1800
#guard seasonOwed [demo, withInvoice] 9 == 300

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

theorem a_vendor_sees_only_their_own (v : Nat) (r : Room) :
    (vendorFace v).obs r .mine = (r.ledger.filter (fun e => Nat.beq e.1 v)).map (·.2.2) := rfl

theorem linda_never_sees_the_ledger (r : Room) (e : Nat × Nat × Nat) :
    reads roomFace lindaSeat (withLine r e) = reads roomFace lindaSeat r := sorry

theorem the_caterer_never_sees_the_ledger (r : Room) (e : Nat × Nat × Nat) :
    reads roomFace catererSeat (withLine r e) = reads roomFace catererSeat r := sorry

theorem the_caterer_never_sees_the_guests (r : Room) (gl : List Party) :
    reads roomFace catererSeat (withGuests r gl) = reads roomFace catererSeat r := sorry

theorem the_bach_parts_the_best_man (r : Room) (b : List Nat) (hb : b ≠ r.bach) :
    reads roomFace bestManSeat (withBach r b) ≠ reads roomFace bestManSeat r := sorry

theorem the_receipt_parts_the_room (r : Room) (c : List Nat) (hc : c ≠ r.confirmed) :
    reads roomFace roomSeat (withConfirmed r c) ≠ reads roomFace roomSeat r := sorry

theorem the_room_covers_itself : covers roomFace [roomSeat] := sorry

theorem the_room_witnesses_the_license (x y : Room)
    (hw : witnessed roomFace [roomSeat] x y) : alike roomFace x y := sorry

theorem the_caterer_reads_the_delivery (r : Room) :
    readRoom (deliver r) .sheet = sheet r.guests := sorry

theorem a_file_is_never_wider_than_its_channel (f : File) (m : Nat) :
    visible f m ↔ m ∈ f.channel.audience := sorry

theorem a_vendor_room_file_is_absent_from_the_couples_files (f : File) (couple : Nat)
    (h : canSee f couple = false) : ¬ visible f couple :=
  the_unenrolled_are_no_member Nat.beq beq_self f.channel.audience couple h

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

theorem the_audience_hears_the_receipt_by_name (q : Request) (m : Nat)
    (h : enrolled Nat.beq q.audience m = true) : heardBy q m = q.confirmed := by
  show cond (enrolled Nat.beq q.audience m) q.confirmed [] = q.confirmed
  rw [h]
  exact rfl

theorem outside_the_audience_hears_no_receipt (q : Request) (m x : Nat)
    (h : enrolled Nat.beq q.audience m = false) : heardBy (confirm q x) m = heardBy q m := by
  show cond (enrolled Nat.beq q.audience m) (x :: q.confirmed) []
      = cond (enrolled Nat.beq q.audience m) q.confirmed []
  rw [h]
  exact rfl

theorem the_sender_is_never_asked (q : Request) : ¬ q.sender ∈ asked q := by
  intro h
  have hq := filter_holds q.audience h
  have hs : (!(Nat.beq q.sender q.sender)) = true := hq
  rw [beq_self] at hs
  exact nomatch hs

theorem the_same_page_counts_only_within_earshot (q : Request) (qs : List Request) (v : Nat)
    (h : enrolled Nat.beq q.audience v = false) : samePage (q :: qs) v = samePage qs v := by
  show cond (enrolled Nat.beq q.audience v) (tally q + samePage qs v) (samePage qs v) = samePage qs v
  rw [h]
  exact rfl

theorem the_same_page_hears_its_own_earshot (q : Request) (qs : List Request) (v : Nat)
    (h : enrolled Nat.beq q.audience v = true) : samePage (q :: qs) v = tally q + samePage qs v := by
  show cond (enrolled Nat.beq q.audience v) (tally q + samePage qs v) (samePage qs v) = tally q + samePage qs v
  rw [h]
  exact rfl

theorem a_covered_wedding_is_still_the_couples (b : Bill) (h : b.thing = .wedding) : owner b.thing = .couple := by
  rw [h]
  rfl

theorem the_payer_is_the_owner_or_the_host (b : Bill) (h : lawful b = true) :
    Role.beq b.payer (owner b.thing) = true ∨ (Role.beq b.payer .vendor = true ∧ Role.beq (owner b.thing) .couple = true) := by
  cases hp : Role.beq b.payer (owner b.thing) with
  | true => exact Or.inl rfl
  | false =>
      have h' : (Role.beq b.payer (owner b.thing) || (Role.beq b.payer .vendor && Role.beq (owner b.thing) .couple)) = true := h
      rw [hp] at h'
      exact Or.inr (and_reads _ _ h')

theorem edit_is_within_sight : withinSight = true := rfl

theorem the_venue_edits_the_floor_and_never_sees_the_list :
    edits .venue .floorPlan = true ∧ sees .venue .guestList = false := ⟨rfl, rfl⟩

theorem a_vendor_sees_the_floor_and_edits_nothing_there :
    sees .vendor .floorPlan = true ∧ edits .vendor .floorPlan = false := ⟨rfl, rfl⟩

theorem the_couple_is_never_in_the_vendor_room (roster : List Member) (m : Member) (hc : m.role = .couple) :
    ¬ m ∈ vendorRoomMembers roster := fun h => by
  have hp : vendorSide m = true := filter_holds roster h
  have hf : vendorSide m = false := by
    cases m with
    | mk u r k l a p =>
        cases r with
        | couple => rfl
        | planner => exact nomatch hc
        | vendor => exact nomatch hc
        | venue => exact nomatch hc
        | party => exact nomatch hc
  exact nomatch (hf.symm.trans hp)

theorem the_wedding_party_is_never_in_the_vendor_room (roster : List Member) (m : Member) (hc : m.role = .party) :
    ¬ m ∈ vendorRoomMembers roster := fun h => by
  have hp : vendorSide m = true := filter_holds roster h
  have hf : vendorSide m = false := by
    cases m with
    | mk u r k l a p =>
        cases r with
        | couple => exact nomatch hc
        | planner => exact nomatch hc
        | vendor => exact nomatch hc
        | venue => exact nomatch hc
        | party => rfl
  exact nomatch (hf.symm.trans hp)

theorem a_vendor_is_in_the_vendor_room (roster : List Member) (m : Member) (hm : m ∈ roster) (hv : m.role = .vendor) :
    m ∈ vendorRoomMembers roster :=
  mem_filter_intro roster hm (by
    cases m with
    | mk u r k l a p =>
        cases r with
        | couple => exact nomatch hv
        | planner => exact nomatch hv
        | vendor => rfl
        | venue => exact nomatch hv
        | party => exact nomatch hv)

theorem the_vendor_room_is_derived_from_the_roster (roster : List Member) :
    vendorRoomAudience roster = channelAudience roster vendorSide := rfl

theorem an_audience_is_members (roster : List Member) (p : Member → Bool) (u : Nat)
    (h : u ∈ channelAudience roster p) : ∃ m, m ∈ roster ∧ m.user = u := by
  obtain ⟨m, hm, he⟩ := mem_map_back (roster.filter p) h
  exact ⟨m, mem_of_mem_filter roster hm, he⟩

theorem the_owner_may_close (m : Member) (t : Task) (h : Nat.beq m.user t.owner = true) : mayClose m t = true := by
  show (Nat.beq m.user t.owner || (Role.beq m.role .couple || Role.beq m.role .planner)) = true
  rw [h]
  exact rfl

theorem the_couple_may_close (m : Member) (t : Task) (h : m.role = .couple) : mayClose m t = true := by
  show (Nat.beq m.user t.owner || (Role.beq m.role .couple || Role.beq m.role .planner)) = true
  rw [h]
  cases Nat.beq m.user t.owner <;> rfl

theorem a_vendor_may_not_close_anothers (m : Member) (t : Task) (h1 : Nat.beq m.user t.owner = false)
    (h2 : m.role = .vendor) : mayClose m t = false := by
  show (Nat.beq m.user t.owner || (Role.beq m.role .couple || Role.beq m.role .planner)) = false
  rw [h1, h2]
  exact rfl

theorem every_edit_is_kept (w : List DayOfEdit) : behavior dayOfLog w = w :=
  the_ledger_parks_the_word w []

theorem the_last_edit_undoes (e : Nat) : ∀ w : List Nat, undo (w ++ [e]) = w
  | [] => rfl
  | [_] => rfl
  | x :: y :: w => congrArg (x :: ·) (the_last_edit_undoes e (y :: w))

theorem the_venue_reads_counts_not_names (t : Table) (occ occ' : List Nat) (h : occ.length = occ'.length) :
    venueTable { t with occupants := occ } = venueTable { t with occupants := occ' } := by
  show (t.shape, occ.length) = (t.shape, occ'.length)
  rw [h]

theorem a_season_reads_each_room_as_the_vendor (rs : List Room) (v : Nat) :
    seasonView rs v = rs.map (fun r => (vendorFace v).obs r .mine) := rfl

theorem the_seasons_sum_is_over_my_own_invoices (rs : List Room) (v : Nat) :
    seasonOwed rs v = total (joinMap (fun r => (vendorFace v).obs r .mine) rs) := rfl

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
