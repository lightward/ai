import Witness
import Eih
open Room Face Witness Eih
set_option autoImplicit false

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
