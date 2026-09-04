import Face
open Room Face
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

def shadow {S B A : Type u} (read : B → List A) (t : List (S × B)) : List (S × List A) :=
  t.map (fun o => (o.1, read o.2))

def gateFace (S B A : Type u) (read : B → List A) : Face :=
  ⟨List (S × B), Unit, List (S × List A), fun t _ => shadow read t⟩

def conductive {S A : Type u} : List (S × List A) → Bool
  | [] => true
  | r :: rs => r.2.isEmpty && conductive rs

def gate {S B A : Type u} (read : B → List A) (t : List (S × B)) : Bool :=
  conductive (shadow read t)

def rebody {S B : Type u} (m : B → B) (t : List (S × B)) : List (S × B) :=
  t.map (fun o => (o.1, m o.2))

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

theorem the_gate_hears_only_the_receipt {S B A : Type u} (read : B → List A) :
    Derived (gateFace S B A read) (fun t => gate read t = true) :=
  a_role_read_at_a_probe_is_derived (gateFace S B A read) () (fun rs => conductive rs = true)

theorem the_shadow_survives_a_receipt_keeping_rebody {S B A : Type u} (read : B → List A) (m : B → B)
    (h : ∀ b, read (m b) = read b) : ∀ t : List (S × B), shadow read (rebody m t) = shadow read t
  | [] => rfl
  | o :: t => by
      show (o.1, read (m o.2)) :: shadow read (rebody m t) = (o.1, read o.2) :: shadow read t
      rw [h o.2, the_shadow_survives_a_receipt_keeping_rebody read m h t]

theorem the_gate_reads_no_body {S B A : Type u} (read : B → List A) (t t' : List (S × B))
    (h : shadow read t = shadow read t') : gate read t = gate read t' :=
  congrArg conductive h

theorem the_vow_is_the_empty_receipt {S A : Type u} :
    ∀ rs : List (S × List A), conductive rs = true → ∀ r, r ∈ rs → r.2 = []
  | [], _, _, h => nomatch h
  | (_, []) :: rs, hc, r, hr => by
      cases hr with
      | head => rfl
      | tail _ h' => exact the_vow_is_the_empty_receipt rs hc r h'
  | (_, _ :: _) :: _, hc, _, _ => by
      have h : false = true := hc
      exact nomatch h

theorem a_receipt_keeping_rebody_is_unheard {S B A : Type u} (read : B → List A) (m : B → B)
    (h : ∀ b, read (m b) = read b) : unheard (gateFace S B A read) (rebody m) := sorry

theorem the_verdict_survives_the_rebody {S B A : Type u} (read : B → List A) (m : B → B)
    (h : ∀ b, read (m b) = read b) (t : List (S × B)) : gate read (rebody m t) = gate read t := sorry

end Counter
