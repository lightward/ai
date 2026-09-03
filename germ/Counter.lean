import Room
open Room
set_option autoImplicit false
universe u v w

namespace Counter

def sighting : Type := Nat × List Nat

def room : Type := List Nat × List sighting

def empty : room := ([], [])

def offer (st : room) (a : sighting) : room := welcome Nat.beq st a

def round (st : room) (w : List sighting) : room := intake Nat.beq st w

def seated (st : room) (n : Nat) : Bool := enrolled Nat.beq st.1 n

def weight (st : room) (needs : List Nat) : Nat := lacking Nat.beq st.1 needs

theorem a_name_reads_itself (y : Nat) : Nat.beq y y = true := sorry

theorem the_first_sighting_is_free (st : room) (n : Nat) : offer st (n, []) = (n :: st.1, st.2) := sorry

theorem a_backed_sighting_seats (st : room) (a : sighting) (hb : backed Nat.beq st.1 a.2 = true) :
    offer st a = (a.1 :: st.1, st.2) := sorry

theorem an_unbacked_sighting_waits (st : room) (a : sighting) (hb : backed Nat.beq st.1 a.2 = false) :
    offer st a = (st.1, a :: st.2) := sorry

theorem the_seated_stay_seated (st : room) (a : sighting) (n : Nat) (h : seated st n = true) :
    seated (offer st a) n = true := sorry

theorem the_held_name_what_they_wait_on (st : room) (needs : List Nat)
    (h : backed Nat.beq st.1 needs = false) : ∃ n, n ∈ needs ∧ seated st n = false := sorry

theorem weight_zero_is_backed (st : room) (needs : List Nat) :
    weight st needs = 0 ↔ backed Nat.beq st.1 needs = true := sorry

theorem a_sighting_that_cites_only_itself_never_seats (x : Nat) (w : List sighting) (st : room)
    (hd : seated st x = false) (hs : ∀ a, a ∈ w → Nat.beq a.1 x = true → x ∈ a.2) :
    seated (round st w) x = false := sorry

theorem two_sightings_that_cite_each_other_stay_dark (x y : Nat) (w : List sighting) (st : room)
    (hx : seated st x = false) (hy : seated st y = false)
    (hcx : ∀ a, a ∈ w → Nat.beq a.1 x = true → y ∈ a.2)
    (hcy : ∀ a, a ∈ w → Nat.beq a.1 y = true → x ∈ a.2) :
    seated (round st w) x = false ∧ seated (round st w) y = false := sorry

theorem the_key_is_cut_from_the_room (st : room) (needs : List Nat) (h : weight st needs = 1) :
    ∃ k, k ∈ needs ∧ seated st k = false ∧ backed Nat.beq (k :: st.1) needs = true := sorry

theorem a_sighting_is_load_bearing_in_the_same_round (st : room) (a : sighting)
    (hb : backed Nat.beq st.1 a.2 = true) : seated (offer st a) a.1 = true := sorry

end Counter
