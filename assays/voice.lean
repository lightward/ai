import Witness
open Room Face Witness
set_option autoImplicit false

-- the voice as a tower of faces (isaac at the table, 2026-09-08: "if things get less interesting,
-- some W got dropped"). a field is where a voice has grain: the contexts it has heard. the face at
-- width k reads a context only up to k bytes long; wider is a wider face, and the tower is exact
-- (Face.the_widening_is_exact). two voices alike at width k and distinct are parted one width up
-- (a_wider_seat_reads_the_remainder), and two fields that cover every context up to k are alike at
-- k whatever they are (the saturation counter's voice met at twenty million charges). the
-- instrument is not the reading at one width but the PARTING WIDTH: the least k at which the faces
-- part two voices on what they have heard. below it the identification is licensed; at it the
-- remainder is real; the number is the reading.

namespace Voice.Treaty

structure Field where
  grain : List (List Nat)

def ctxBeq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs => Nat.beq a b && ctxBeq as bs

def has (f : Field) (c : List Nat) : Bool := enrolled ctxBeq f.grain c

def voiceFace (k : Nat) : Face :=
  ⟨Field, List Nat, Bool, fun f c => cond (Nat.ble c.length k) (has f c) false⟩

def agreeTo (k : Nat) (f g : Field) : Prop := ∀ c : List Nat, Nat.ble c.length k = true → has f c = has g c

def heard (f g : Field) : List (List Nat) := f.grain ++ g.grain

def partsAt (k : Nat) (f g : Field) : Bool :=
  (heard f g).any (fun c => Nat.ble c.length k && !(has f c == has g c))

def longest : List (List Nat) → Nat
  | [] => 0
  | c :: cs => cond (Nat.ble c.length (longest cs)) (longest cs) c.length

def widest (f g : Field) : Nat := longest (heard f g)

def partingFrom (f g : Field) : Nat → Nat → Nat
  | _, 0 => widest f g + 1
  | k, fuel + 1 => cond (partsAt k f g) k (partingFrom f g (k + 1) fuel)

def partingWidth (f g : Field) : Nat := partingFrom f g 0 (widest f g + 1)

def full (k : Nat) (f : Field) : Prop := ∀ c : List Nat, Nat.ble c.length k = true → has f c = true

def isaacVoice : Field := ⟨[[1], [2], [1, 2], [2, 3], [1, 2, 3], [1, 2, 3, 4, 5]]⟩
def fableVoice : Field := ⟨[[1], [2], [1, 2], [2, 3], [1, 2, 3], [2, 3, 4, 5, 6]]⟩
def quoted : Field := ⟨[[1], [2], [1, 2], [2, 3], [1, 2, 3], [1, 2, 3, 4, 5], [2, 3, 4, 5, 6]]⟩

def atThree : Bool := partsAt 3 isaacVoice fableVoice
def atFive : Bool := partsAt 5 isaacVoice fableVoice
def theWidth : Nat := partingWidth isaacVoice fableVoice
def quotedWidth : Nat := partingWidth quoted quoted
def readThree : Bool := (voiceFace 3).obs isaacVoice [1, 2, 3, 4, 5]
def readFive : Bool := (voiceFace 5).obs isaacVoice [1, 2, 3, 4, 5]

#guard atThree == false
#guard atFive == true
#guard theWidth == 5
#guard quotedWidth == 6
#guard readThree == false
#guard readFive == true
#guard widest isaacVoice fableVoice == 5

theorem ble_flips : ∀ a b : Nat, Nat.ble a b = false → Nat.ble b a = true
  | 0, 0, h => nomatch h
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, _ => rfl
  | a + 1, b + 1, h => ble_flips a b h

theorem the_longest_reaches_each (c : List Nat) :
    ∀ l : List (List Nat), c ∈ l → Nat.ble c.length (longest l) = true
  | [], h => nomatch h
  | d :: cs, h => by
      cases h with
      | head =>
          show Nat.ble c.length (cond (Nat.ble c.length (longest cs)) (longest cs) c.length) = true
          cases hb : Nat.ble c.length (longest cs) with
          | true => exact hb
          | false => exact ble_refl c.length
      | tail _ h' =>
          have ih := the_longest_reaches_each c cs h'
          show Nat.ble c.length (cond (Nat.ble d.length (longest cs)) (longest cs) d.length) = true
          cases hb : Nat.ble d.length (longest cs) with
          | true => exact ih
          | false => exact ble_trans c.length (longest cs) d.length ih (ble_flips d.length (longest cs) hb)

theorem the_face_at_a_width_reads_agreement (k : Nat) (f g : Field) :
    alike (voiceFace k) f g ↔ agreeTo k f g :=
  ⟨fun h c hc => by
      have hf : cond (Nat.ble c.length k) (has f c) false = cond (Nat.ble c.length k) (has g c) false := h c
      rw [hc] at hf
      exact hf,
   fun h c => by
      show cond (Nat.ble c.length k) (has f c) false = cond (Nat.ble c.length k) (has g c) false
      cases hc : Nat.ble c.length k with
      | true => exact h c hc
      | false => rfl⟩

theorem a_wider_agreement_is_a_narrower_one (k : Nat) (f g : Field) (h : agreeTo (k + 1) f g) :
    agreeTo k f g :=
  fun c hc => h c (ble_trans c.length k (k + 1) hc (ble_le_succ k))

theorem a_context_that_parts_parts_the_face (k : Nat) (f g : Field) (c : List Nat)
    (hc : Nat.ble c.length k = true) (hd : has f c ≠ has g c) : ¬ agreeTo k f g :=
  fun ha => hd (ha c hc)

theorem full_fields_are_alike (k : Nat) (f g : Field) (hf : full k f) (hg : full k g) :
    agreeTo k f g :=
  fun c hc => (hf c hc).trans (hg c hc).symm

theorem no_context_parts_a_voice_from_itself (k : Nat) (f : Field) :
    ∀ l : List (List Nat), l.any (fun c => Nat.ble c.length k && !(has f c == has f c)) = false
  | [] => rfl
  | c :: cs => by
      show ((Nat.ble c.length k && !(has f c == has f c))
        || List.any cs (fun c => Nat.ble c.length k && !(has f c == has f c))) = false
      have hp : (Nat.ble c.length k && !(has f c == has f c)) = false := by
        cases has f c <;> cases Nat.ble c.length k <;> rfl
      rw [hp]
      exact no_context_parts_a_voice_from_itself k f cs

theorem a_voice_never_parts_itself (k : Nat) (f : Field) : partsAt k f f = false :=
  no_context_parts_a_voice_from_itself k f (heard f f)

theorem nothing_is_heard_beyond_the_widest (f g : Field) (c : List Nat) (hc : c ∈ heard f g) :
    Nat.ble c.length (widest f g) = true :=
  the_longest_reaches_each c (heard f g) hc

end Voice.Treaty
