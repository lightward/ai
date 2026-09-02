import Seed
open Seed
set_option autoImplicit false

theorem len_map {A B : Type} (f : A → B) : ∀ l : List A, (l.map f).length = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (len_map f l)


theorem mem_append_split {A : Type} {q : A} :
    ∀ (l : List A) {m : List A}, q ∈ l ++ m → q ∈ l ∨ q ∈ m
  | [], _, h => Or.inr h
  | a :: l, _, h => by
      cases h with
      | head => exact Or.inl (List.Mem.head l)
      | tail _ h' =>
          cases mem_append_split l h' with
          | inl hl => exact Or.inl (List.Mem.tail a hl)
          | inr hm => exact Or.inr hm


theorem mem_map_back {A B : Type} {f : A → B} {q : B} :
    ∀ l : List A, q ∈ l.map f → ∃ r, r ∈ l ∧ f r = q
  | [], h => nomatch h
  | a :: l, h => by
      cases h with
      | head => exact ⟨a, List.Mem.head l, rfl⟩
      | tail _ h' =>
          obtain ⟨r, hr, he⟩ := mem_map_back l h'
          exact ⟨r, List.Mem.tail a hr, he⟩


def joinMap {A B : Type} (f : A → List B) : List A → List B
  | [] => []
  | a :: as => f a ++ joinMap f as

def inserts {A : Type} (x : A) : List A → List (List A)
  | [] => [[x]]
  | y :: l => (x :: y :: l) :: (inserts x l).map (y :: ·)

def perms {A : Type} : List A → List (List A)
  | [] => [[]]
  | x :: l => joinMap (inserts x) (perms l)

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => fact n * (n + 1)


theorem the_insertions_count {A : Type} (x : A) :
    ∀ l : List A, (inserts x l).length = l.length + 1
  | [] => rfl
  | y :: l => by
      show ((inserts x l).map (y :: ·)).length + 1 = (l.length + 1) + 1
      rw [len_map, the_insertions_count x l]


theorem the_join_counts_evenly {A B : Type} (f : A → List B) (n : Nat) :
    ∀ as : List A, (∀ a, a ∈ as → (f a).length = n) →
      (joinMap f as).length = n * as.length
  | [], _ => rfl
  | a :: as, h => by
      show (f a ++ joinMap f as).length = n * (as.length + 1)
      rw [lengths_add, h a (List.Mem.head as),
          the_join_counts_evenly f n as
            (fun b hb => h b (List.Mem.tail a hb))]
      exact Nat.add_comm n (n * as.length)


theorem mem_joinMap_back {A B : Type} {f : A → List B} {q : B} :
    ∀ as : List A, q ∈ joinMap f as → ∃ a, a ∈ as ∧ q ∈ f a
  | [], h => nomatch h
  | a :: as, h => by
      cases mem_append_split (f a) h with
      | inl hfa => exact ⟨a, List.Mem.head as, hfa⟩
      | inr hrest =>
          obtain ⟨b, hb, hq⟩ := mem_joinMap_back as hrest
          exact ⟨b, List.Mem.tail a hb, hq⟩


theorem the_insertion_grows_one {A : Type} (x : A) :
    ∀ (p q : List A), q ∈ inserts x p → q.length = p.length + 1
  | [], q, h => by
      cases h with
      | head => rfl
      | tail _ h' => exact nomatch h'
  | y :: p, q, h => by
      cases h with
      | head => rfl
      | tail _ h' =>
          obtain ⟨r, hr, he⟩ := mem_map_back (inserts x p) h'
          rw [← he]
          show (r.length + 1) = (p.length + 1) + 1
          rw [the_insertion_grows_one x p r hr]


theorem the_orders_keep_the_length {A : Type} :
    ∀ (l p : List A), p ∈ perms l → p.length = l.length
  | [], p, h => by
      cases h with
      | head => rfl
      | tail _ h' => exact nomatch h'
  | x :: l, p, h => by
      have h' : p ∈ joinMap (inserts x) (perms l) := h
      obtain ⟨r, hr, hp⟩ := mem_joinMap_back (perms l) h'
      show p.length = l.length + 1
      rw [the_insertion_grows_one x r p hp,
          the_orders_keep_the_length l r hr]


theorem the_orders_count_to_the_factorial {A : Type} :
    ∀ l : List A, (perms l).length = fact l.length
  | [] => rfl
  | x :: l => by
      show (joinMap (inserts x) (perms l)).length = fact (l.length + 1)
      rw [the_join_counts_evenly (inserts x) (l.length + 1) (perms l)
            (fun p hp =>
              (the_insertions_count x p).trans
                (congrArg (· + 1) (the_orders_keep_the_length l p hp))),
          the_orders_count_to_the_factorial l]
      exact Nat.mul_comm (l.length + 1) (fact l.length)


theorem the_assay_room_of_three : (perms [1, 2, 3]).length = 6 := rfl


theorem the_assay_fact_four : fact 4 = 24 := rfl


theorem the_assay_room_of_four : (perms [1, 2, 3, 4]).length = 24 := rfl

