import Witness
open Room Face Witness
set_option autoImplicit false

namespace Everyone.Treaty

inductive Role where
  | couple | helper

def Role.code : Role → Nat
  | .couple => 0 | .helper => 1

def Role.beq (a b : Role) : Bool := Nat.beq a.code b.code

def roles : List Role := [.couple, .helper]

inductive Page where
  | home | seatingChart | guestList | samePage | invoices | budget | guests | site | team | dayOf | tasks | files | guide | profile | vendorChat | mySeason

def Page.code : Page → Nat
  | .home => 0 | .seatingChart => 1 | .guestList => 2 | .samePage => 3 | .invoices => 4 | .budget => 5 | .guests => 6 | .site => 7 | .team => 8 | .dayOf => 9 | .tasks => 10 | .files => 11 | .guide => 12 | .profile => 13 | .vendorChat => 14 | .mySeason => 15

def Page.beq (a b : Page) : Bool := Nat.beq a.code b.code

def pages : List Page := [.home, .seatingChart, .guestList, .samePage, .invoices, .budget, .guests, .site, .team, .dayOf, .tasks, .files, .guide, .profile, .vendorChat, .mySeason]

inductive Ask where
  | guests | headcount | timeline | invoices

def Ask.code : Ask → Nat
  | .guests => 0 | .headcount => 1 | .timeline => 2 | .invoices => 3

def Ask.beq (a b : Ask) : Bool := Nat.beq a.code b.code

def asks : List Ask := [.guests, .headcount, .timeline, .invoices]

structure Room where
  guests : List Nat
  delivered : List Nat
  timeline : List Nat
  invoices : List Nat

def readRoom (r : Room) : Ask → List Nat
  | .guests => r.guests
  | .headcount => r.delivered
  | .timeline => r.timeline
  | .invoices => r.invoices

def roomFace : Face := ⟨Room, Ask, List Nat, readRoom⟩

def seenPaid : Role → List Page
  | .couple => [.home, .seatingChart, .guestList, .samePage, .invoices, .budget, .guests, .site, .team, .dayOf, .tasks, .files, .guide, .profile]
  | .helper => [.home, .seatingChart, .samePage, .invoices, .team, .dayOf, .tasks, .files, .guide, .profile, .vendorChat]

def seenUnpaid : Role → List Page
  | .couple => [.home, .seatingChart, .guestList, .samePage, .invoices, .budget, .guests, .site, .team, .dayOf, .tasks, .files, .guide, .profile]
  | .helper => [.home, .seatingChart, .guestList, .samePage, .team, .dayOf, .tasks, .files, .guide, .profile]

def seen (ρ : Role) (paid : Bool) : List Page := cond paid (seenPaid ρ) (seenUnpaid ρ)

def sees (ρ : Role) (paid : Bool) (p : Page) : Bool := enrolled Page.beq (seen ρ paid) p

def editedPaid : Role → List Page
  | .couple => [.home, .seatingChart, .guestList, .samePage, .invoices, .budget, .guests, .site, .team, .dayOf, .tasks, .files, .guide, .profile]
  | .helper => [.invoices, .dayOf, .tasks, .files, .profile, .vendorChat]

def editedUnpaid : Role → List Page
  | .couple => [.home, .seatingChart, .guestList, .samePage, .invoices, .budget, .guests, .site, .team, .dayOf, .tasks, .files, .guide, .profile]
  | .helper => [.seatingChart, .guestList, .dayOf, .tasks, .files, .profile]

def edited (ρ : Role) (paid : Bool) : List Page := cond paid (editedPaid ρ) (editedUnpaid ρ)

def edits (ρ : Role) (paid : Bool) (p : Page) : Bool := enrolled Page.beq (edited ρ paid) p

def coupleSeat : List Ask := [.guests, .headcount, .timeline, .invoices]

def catererSeat : List Ask := [.timeline, .headcount]

def bestManSeat : List Ask := [.timeline]

def venueSeat : List Ask := [.timeline, .headcount]

def withGuests (r : Room) (x : List Nat) : Room := { r with guests := x }

def withTime (r : Room) (x : Nat) : Room := { r with timeline := x :: r.timeline }

def withInvoice (r : Room) (x : Nat) : Room := { r with invoices := x :: r.invoices }

def demo : Room := ⟨[2, 3, 1], [], [10, 11, 12], []⟩
def later : Room := withTime demo 9
def billed : Room := withInvoice demo 1200

def catererInDemo : List (List Nat) := reads roomFace catererSeat demo
#guard catererInDemo == [[10, 11, 12], []]
def bestManInLater : List (List Nat) := reads roomFace bestManSeat later
#guard bestManInLater == [[9, 10, 11, 12]]
def coupleInLater : List (List Nat) := reads roomFace coupleSeat later
#guard coupleInLater == [[2, 3, 1], [], [9, 10, 11, 12], []]
def coupleInBilled : List (List Nat) := reads roomFace coupleSeat billed
#guard coupleInBilled == [[2, 3, 1], [], [10, 11, 12], [1200]]
def catererInBilled : List (List Nat) := reads roomFace catererSeat billed
#guard catererInBilled == [[10, 11, 12], []]
def venueInBilled : List (List Nat) := reads roomFace venueSeat billed
#guard venueInBilled == [[10, 11, 12], []]
def bestManInBilled : List (List Nat) := reads roomFace bestManSeat billed
#guard bestManInBilled == [[10, 11, 12]]
#guard sees .helper true .invoices == true
#guard sees .helper false .invoices == false
#guard sees .couple true .invoices == true
#guard sees .couple true .vendorChat == false
#guard sees .helper true .vendorChat == true
#guard sees .helper false .vendorChat == false
#guard sees .couple true .mySeason == false
#guard sees .helper false .mySeason == false
#guard sees .helper false .guests == false
#guard sees .helper false .site == false
#guard sees .helper false .budget == false
#guard sees .helper false .seatingChart == true
#guard sees .helper false .dayOf == true
#guard sees .helper true .invoices == true
#guard sees .helper true .guests == false
#guard sees .helper true .invoices == true
#guard sees .helper true .guests == false
#guard sees .helper true .site == false
#guard sees .helper true .vendorChat == true
#guard sees .helper true .vendorChat == true
#guard sees .helper true .invoices == true
#guard sees .helper true .guests == false
#guard sees .helper true .budget == false
#guard roles.all (fun ρ => edits ρ true .dayOf && edits ρ false .dayOf)

theorem withGuests_changes_nothing_the_caterer_hears (r : Room) (x : List Nat) :
    reads roomFace catererSeat (withGuests r x) = reads roomFace catererSeat r := sorry

theorem withGuests_changes_nothing_the_bestMan_hears (r : Room) (x : List Nat) :
    reads roomFace bestManSeat (withGuests r x) = reads roomFace bestManSeat r := sorry

theorem withGuests_changes_nothing_the_venue_hears (r : Room) (x : List Nat) :
    reads roomFace venueSeat (withGuests r x) = reads roomFace venueSeat r := sorry

theorem withInvoice_changes_nothing_the_caterer_hears (r : Room) (x : Nat) :
    reads roomFace catererSeat (withInvoice r x) = reads roomFace catererSeat r := sorry

theorem withInvoice_changes_nothing_the_bestMan_hears (r : Room) (x : Nat) :
    reads roomFace bestManSeat (withInvoice r x) = reads roomFace bestManSeat r := sorry

theorem withInvoice_changes_nothing_the_venue_hears (r : Room) (x : Nat) :
    reads roomFace venueSeat (withInvoice r x) = reads roomFace venueSeat r := sorry

end Everyone.Treaty
