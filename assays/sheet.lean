import Witness
open Room Face Witness
set_option autoImplicit false

namespace Sheet.Treaty

inductive Role where
  | couple | helper

def Role.code : Role → Nat
  | .couple => 0 | .helper => 1

def Role.beq (a b : Role) : Bool := Nat.beq a.code b.code

def roles : List Role := [.couple, .helper]

inductive Page where
  | floorPlan | guestList | samePage | invoices | budget | guests | site | team | dayOf | tasks

def Page.code : Page → Nat
  | .floorPlan => 0 | .guestList => 1 | .samePage => 2 | .invoices => 3 | .budget => 4 | .guests => 5 | .site => 6 | .team => 7 | .dayOf => 8 | .tasks => 9

def Page.beq (a b : Page) : Bool := Nat.beq a.code b.code

def pages : List Page := [.floorPlan, .guestList, .samePage, .invoices, .budget, .guests, .site, .team, .dayOf, .tasks]

inductive Ask where
  | guests | sheet | timeline | bachelor

def Ask.code : Ask → Nat
  | .guests => 0 | .sheet => 1 | .timeline => 2 | .bachelor => 3

def Ask.beq (a b : Ask) : Bool := Nat.beq a.code b.code

def asks : List Ask := [.guests, .sheet, .timeline, .bachelor]

structure Room where
  guests : List Nat
  delivered : List Nat
  timeline : List Nat
  bachelor : List Nat

def readRoom (r : Room) : Ask → List Nat
  | .guests => r.guests
  | .sheet => r.delivered
  | .timeline => r.timeline
  | .bachelor => r.bachelor

def roomFace : Face := ⟨Room, Ask, List Nat, readRoom⟩

def seenPaid : Role → List Page
  | .couple => pages
  | .helper => [.floorPlan, .samePage, .invoices, .team, .dayOf, .tasks]

def seenUnpaid : Role → List Page
  | .couple => pages
  | .helper => [.floorPlan, .guestList, .samePage, .team, .dayOf, .tasks]

def seen (ρ : Role) (paid : Bool) : List Page := cond paid (seenPaid ρ) (seenUnpaid ρ)

def sees (ρ : Role) (paid : Bool) (p : Page) : Bool := enrolled Page.beq (seen ρ paid) p

def editedPaid : Role → List Page
  | .couple => pages
  | .helper => [.invoices, .dayOf, .tasks]

def editedUnpaid : Role → List Page
  | .couple => pages
  | .helper => [.floorPlan, .guestList, .dayOf, .tasks]

def edited (ρ : Role) (paid : Bool) : List Page := cond paid (editedPaid ρ) (editedUnpaid ρ)

def edits (ρ : Role) (paid : Bool) (p : Page) : Bool := enrolled Page.beq (edited ρ paid) p

def coupleSeat : List Ask := [.guests, .sheet, .timeline]

def catererSeat : List Ask := [.timeline, .sheet]

def bestManSeat : List Ask := [.timeline, .bachelor]

def withBachelor (r : Room) (x : List Nat) : Room := { r with bachelor := x }

def withGuests (r : Room) (x : List Nat) : Room := { r with guests := x }

def withTime (r : Room) (x : Nat) : Room := { r with timeline := x :: r.timeline }

def demo : Room := ⟨[2, 3, 1], [], [10, 11, 12], [42]⟩
def newBachelor : Room := withBachelor demo [43]

def catererInDemo : List (List Nat) := reads roomFace catererSeat demo
#guard catererInDemo == [[10, 11, 12], []]
def bestManInNewBachelor : List (List Nat) := reads roomFace bestManSeat newBachelor
#guard bestManInNewBachelor == [[10, 11, 12], [43]]
def coupleInNewBachelor : List (List Nat) := reads roomFace coupleSeat newBachelor
#guard coupleInNewBachelor == [[2, 3, 1], [], [10, 11, 12]]
#guard sees .helper true .invoices == true
#guard sees .helper false .invoices == false
#guard sees .couple true .invoices == true
#guard roles.all (fun ρ => edits ρ true .dayOf && edits ρ false .dayOf)

theorem withBachelor_changes_nothing_the_couple_hears (r : Room) (x : List Nat) :
    reads roomFace coupleSeat (withBachelor r x) = reads roomFace coupleSeat r := sorry

theorem withBachelor_changes_nothing_the_caterer_hears (r : Room) (x : List Nat) :
    reads roomFace catererSeat (withBachelor r x) = reads roomFace catererSeat r := sorry

theorem withGuests_changes_nothing_the_caterer_hears (r : Room) (x : List Nat) :
    reads roomFace catererSeat (withGuests r x) = reads roomFace catererSeat r := sorry

theorem withGuests_changes_nothing_the_bestMan_hears (r : Room) (x : List Nat) :
    reads roomFace bestManSeat (withGuests r x) = reads roomFace bestManSeat r := sorry

end Sheet.Treaty
