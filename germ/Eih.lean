import Face
open Room Face

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

def allClear (r : Room) (members : List Nat) : Prop :=
  r.delivered = sheet r.guests ∧ ∀ m, m ∈ members → m ∈ r.confirmed

inductive Ask where
  | guests | sheet | ledger | timeline | bach | confirmed

def readRoom (r : Room) : Ask → List Nat
  | .guests => r.guests.map (·.name)
  | .sheet => r.delivered
  | .ledger => r.ledger.map (·.2.2)
  | .timeline => r.timeline
  | .bach => r.bach
  | .confirmed => r.confirmed

def roomFace : Face := ⟨Room, Ask, List Nat, readRoom⟩

inductive CoupleAsk where
  | guests | sheet | ledger | timeline

def coupleFace : Face :=
  rehear roomFace (fun q : CoupleAsk => match q with
    | .guests => Ask.guests | .sheet => Ask.sheet | .ledger => Ask.ledger | .timeline => Ask.timeline)

inductive LindaAsk where
  | guests | timeline

def lindaFace : Face :=
  rehear roomFace (fun q : LindaAsk => match q with | .guests => Ask.guests | .timeline => Ask.timeline)

inductive BestManAsk where
  | timeline | bach

def bestManFace : Face :=
  rehear roomFace (fun q : BestManAsk => match q with | .timeline => Ask.timeline | .bach => Ask.bach)

inductive VendorAsk where
  | timeline | mine

def vendorFace (v : Nat) : Face :=
  ⟨Room, VendorAsk, List Nat, fun r q => match q with
    | .timeline => r.timeline
    | .mine => (r.ledger.filter (fun e => Nat.beq e.1 v)).map (·.2.2)⟩

def catererFace : Face :=
  rehear roomFace (fun q : VendorAsk => match q with | .timeline => Ask.timeline | .mine => Ask.sheet)

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
    (h : allClear r members) : ∀ m, m ∈ members → m ∈ r.confirmed := sorry

theorem reseating_keeps_the_heads {gl gl' : List Party} (h : gl.Perm gl') : heads gl = heads gl' := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (cond a.rsvp a.meals.length 0 + ·) ih
  | swap a b l =>
      show cond b.rsvp b.meals.length 0 + (cond a.rsvp a.meals.length 0 + heads l)
        = cond a.rsvp a.meals.length 0 + (cond b.rsvp b.meals.length 0 + heads l)
      exact Nat.add_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem the_florist_never_sees_the_guests (v : Nat) (r : Room) (gl : List Party) :
    alike (vendorFace v) (withGuests r gl) r := sorry

theorem linda_never_sees_the_ledger (r : Room) (e : Nat × Nat × Nat) :
    alike lindaFace { r with ledger := e :: r.ledger } r := sorry

theorem a_vendor_never_sees_anothers_invoice (v w : Nat) (hvw : Nat.beq w v = false) (r : Room)
    (amount to : Nat) :
    alike (vendorFace v) { r with ledger := (w, to, amount) :: r.ledger } r := by
  intro q
  cases q with
  | timeline => rfl
  | mine =>
      show ((( w, to, amount) :: r.ledger).filter (fun e => Nat.beq e.1 v)).map (·.2.2)
        = (r.ledger.filter (fun e => Nat.beq e.1 v)).map (·.2.2)
      rw [List.filter, hvw]

theorem the_bach_wall (r : Room) (b : List Nat) (hb : b ≠ r.bach) :
    alike coupleFace (withBach r b) r ∧ ¬ alike bestManFace (withBach r b) r :=
  ⟨fun q => match q with | .guests => rfl | .sheet => rfl | .ledger => rfl | .timeline => rfl,
   fun h => hb (h .bach)⟩

theorem the_room_alone_holds_the_receipt (r : Room) (c : List Nat) (hc : c ≠ r.confirmed) :
    alike coupleFace (withConfirmed r c) r ∧ alike lindaFace (withConfirmed r c) r
      ∧ ¬ alike roomFace (withConfirmed r c) r :=
  ⟨fun q => match q with | .guests => rfl | .sheet => rfl | .ledger => rfl | .timeline => rfl,
   fun q => match q with | .guests => rfl | .timeline => rfl,
   fun h => hc (h .confirmed)⟩

theorem the_caterer_reads_the_delivery (r : Room) :
    catererFace.obs (deliver r) .mine = sheet r.guests := sorry

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

theorem reseating_keeps_the_sheets_count {gl gl' : List Party} (h : gl.Perm gl') :
    (sheet gl).length = (sheet gl').length := sorry

theorem everyone_is_here (r : Room) (members : List Nat) (h : allClear r members)
    {p : Party} (hp : p ∈ r.guests) (hr : p.rsvp = true) {m : Nat} (hm : m ∈ p.meals)
    (c : List Nat) (hc : c ≠ r.confirmed) {gl gl' : List Party} (hperm : gl.Perm gl') :
    m ∈ r.delivered
      ∧ (∀ x, x ∈ members → x ∈ r.confirmed)
      ∧ (sheet r.guests).length = heads r.guests
      ∧ heads gl = heads gl'
      ∧ ¬ alike roomFace (withConfirmed r c) r := sorry

end Eih
