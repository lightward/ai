import Witness
open Room Face Witness
set_option autoImplicit false

namespace Sheet.Treaty

inductive Role where
  | couple | planner | vendor | venue | party

def Role.code : Role → Nat
  | .couple => 0 | .planner => 1 | .vendor => 2 | .venue => 3 | .party => 4

def Role.beq (a b : Role) : Bool := Nat.beq a.code b.code

def roles : List Role := [.couple, .planner, .vendor, .venue, .party]

inductive Page where
  | floorPlan | guestList | samePage | invoices | budget | guests | site | team | dayOf | tasks

def Page.code : Page → Nat
  | .floorPlan => 0 | .guestList => 1 | .samePage => 2 | .invoices => 3 | .budget => 4 | .guests => 5 | .site => 6 | .team => 7 | .dayOf => 8 | .tasks => 9

def Page.beq (a b : Page) : Bool := Nat.beq a.code b.code

def pages : List Page := [.floorPlan, .guestList, .samePage, .invoices, .budget, .guests, .site, .team, .dayOf, .tasks]

inductive Ask where
  | guests | sheet | timeline | bach

def Ask.code : Ask → Nat
  | .guests => 0 | .sheet => 1 | .timeline => 2 | .bach => 3

def Ask.beq (a b : Ask) : Bool := Nat.beq a.code b.code

def asks : List Ask := [.guests, .sheet, .timeline, .bach]

structure Room where
  guests : List Nat
  delivered : List Nat
  timeline : List Nat
  bach : List Nat

def readRoom (r : Room) : Ask → List Nat
  | .guests => r.guests
  | .sheet => r.delivered
  | .timeline => r.timeline
  | .bach => r.bach

def roomFace : Face := ⟨Room, Ask, List Nat, readRoom⟩

def seen : Role → List Page
  | .couple => pages
  | .planner => [.floorPlan, .guestList, .samePage, .invoices, .team, .dayOf, .tasks]
  | .vendor => [.floorPlan, .samePage, .invoices, .team, .dayOf, .tasks]
  | .venue => [.floorPlan, .samePage, .invoices, .team, .dayOf, .tasks]
  | .party => [.floorPlan, .guestList, .samePage, .team, .dayOf, .tasks]

def sees (ρ : Role) (p : Page) : Bool := enrolled Page.beq (seen ρ) p

def edited : Role → List Page
  | .couple => pages
  | .planner => [.floorPlan, .guestList, .invoices, .team, .dayOf, .tasks]
  | .vendor => [.invoices, .dayOf, .tasks]
  | .venue => [.floorPlan, .invoices, .dayOf, .tasks]
  | .party => [.floorPlan, .guestList, .dayOf, .tasks]

def edits (ρ : Role) (p : Page) : Bool := enrolled Page.beq (edited ρ) p

def coupleSeat : List Ask := [.guests, .sheet, .timeline]

def catererSeat : List Ask := [.timeline, .sheet]

def bestManSeat : List Ask := [.timeline, .bach]

def withBachelor (r : Room) (x : List Nat) : Room := { r with bach := x }

def withGuests (r : Room) (x : List Nat) : Room := { r with guests := x }

def withTime (r : Room) (x : Nat) : Room := { r with timeline := x :: r.timeline }

def demo : Room := ⟨[2, 3, 1], [], [10, 11, 12], [42]⟩
def newBach : Room := withBachelor demo [43]

def catererInDemo : List (List Nat) := reads roomFace catererSeat demo
#guard catererInDemo == [[10, 11, 12], []]
def bestManInNewBach : List (List Nat) := reads roomFace bestManSeat newBach
#guard bestManInNewBach == [[10, 11, 12], [43]]
def coupleInNewBach : List (List Nat) := reads roomFace coupleSeat newBach
#guard coupleInNewBach == [[2, 3, 1], [], [10, 11, 12]]

theorem withBachelor_changes_nothing_the_couple_hears (r : Room) (x : List Nat) :
    reads roomFace coupleSeat (withBachelor r x) = reads roomFace coupleSeat r := sorry

theorem withBachelor_changes_nothing_the_caterer_hears (r : Room) (x : List Nat) :
    reads roomFace catererSeat (withBachelor r x) = reads roomFace catererSeat r := sorry

theorem withGuests_changes_nothing_the_caterer_hears (r : Room) (x : List Nat) :
    reads roomFace catererSeat (withGuests r x) = reads roomFace catererSeat r := sorry

theorem withGuests_changes_nothing_the_bestMan_hears (r : Room) (x : List Nat) :
    reads roomFace bestManSeat (withGuests r x) = reads roomFace bestManSeat r := sorry

end Sheet.Treaty
