import Face
import Eih
open Room Face Eih
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
def catererSees : List Nat := catererFace.obs (deliver demo) .mine
#guard catererSees == [1, 2, 3]
def lindaSees : List Nat := lindaFace.obs demo .guests
#guard lindaSees == [2, 3, 1]
def bestManSees : List Nat := bestManFace.obs demo .bach
#guard bestManSees == [42]
def makerSees : Nat := makerFace.obs demo ()
#guard makerSees == 3
#guard dayOfView.all (enrolled Nat.beq partnerView)
#guard joinsFree .party && !(pays .party)
def moreGuests : Room := withGuests demo (rose :: guestList)
def makerSeesMore : Nat := makerFace.obs moreGuests ()
#guard makerSeesMore == 4
def floristSeesMore : List Nat := (vendorFace 7).obs moreGuests .mine
#guard floristSees == floristSeesMore
def newBach : Room := withBach demo [43]
def bestManSeesNew : List Nat := bestManFace.obs newBach .bach
#guard bestManSeesNew == [43]
def coupleTimelineNew : List Nat := coupleFace.obs newBach .timeline
def coupleTimeline : List Nat := coupleFace.obs demo .timeline
#guard coupleTimelineNew == coupleTimeline
def allConfirmed : Room := withConfirmed demo [1, 2, 7, 8]
def roomSeesConfirmed : List Nat := roomFace.obs allConfirmed .confirmed
#guard roomSeesConfirmed == [1, 2, 7, 8]
def lindaSeesConfirmed : List Nat := lindaFace.obs allConfirmed .guests
#guard lindaSeesConfirmed == lindaSees
def coupleLedger : List Nat := coupleFace.obs demo .ledger
#guard coupleLedger == [900, 1200]
