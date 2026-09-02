import Seed
open Seed
set_option autoImplicit false

universe u v

inductive Apart {A : Type u} : List A → Prop
  | nil : Apart []
  | cons {a : A} {l : List A} :
      (∀ b, b ∈ l → a ≠ b) → Apart l → Apart (a :: l)


theorem apart_map {A : Type u} {B : Type v} {f : A → B}
    (hf : ∀ a b, f a = f b → a = b) :
    ∀ {xs : List A}, Apart xs → Apart (xs.map f)
  | [], _ => Apart.nil
  | x :: xs, Apart.cons hx hxs =>
      Apart.cons
        (fun _ hb he =>
          match mem_map_back xs hb with
          | ⟨a, ha, hfa⟩ => hx a ha (hf x a (he.trans hfa.symm)))
        (apart_map hf hxs)


theorem apart_append {A : Type u} :
    ∀ {xs : List A} (ys : List A), Apart xs → Apart ys →
      (∀ x, x ∈ xs → ∀ y, y ∈ ys → x ≠ y) → Apart (xs ++ ys)
  | [], _, _, hys, _ => hys
  | _ :: xs, ys, Apart.cons hx hxs, hys, hcross =>
      Apart.cons
        (fun b hb =>
          match mem_append_split xs hb with
          | Or.inl hbx => hx b hbx
          | Or.inr hby => hcross _ (List.Mem.head _) b hby)
        (apart_append ys hxs hys
          (fun a ha y hy => hcross a (List.Mem.tail _ ha) y hy))


theorem mem_cross_split :
    ∀ (ps : List Plan) {qs : List Plan} {x : Plan},
      x ∈ cross ps qs → ∃ l r, x = Plan.board l r ∧ l ∈ ps ∧ r ∈ qs
  | [], _, _, h => nomatch h
  | p :: ps, qs, _, h =>
      match mem_append_split (qs.map (Plan.board p)) h with
      | Or.inl hm =>
          match mem_map_back qs hm with
          | ⟨r, hr, he⟩ => ⟨p, r, he.symm, List.Mem.head _, hr⟩
      | Or.inr hc =>
          match mem_cross_split ps hc with
          | ⟨l, r, he, hl, hr⟩ => ⟨l, r, he, List.Mem.tail _ hl, hr⟩


theorem the_cross_keeps_apart {qs : List Plan} (hqs : Apart qs) :
    ∀ {ps : List Plan}, Apart ps → Apart (cross ps qs)
  | [], _ => Apart.nil
  | _ :: ps, Apart.cons hp hps =>
      apart_append (cross ps qs)
        (apart_map (fun _ _ h => (Plan.board.inj h).2) hqs)
        (the_cross_keeps_apart hqs hps)
        (fun _ hx _ hy he =>
          match mem_map_back qs hx, mem_cross_split ps hy with
          | ⟨_, _, hfr⟩, ⟨l', _, hy_eq, hl', _⟩ =>
              hp l' hl'
                (Plan.board.inj ((hfr.trans he).trans hy_eq)).1)


theorem the_room_repeats_no_plan : ∀ d : Nat, Apart (allPlans d)
  | 0 => Apart.cons (fun _ hb => nomatch hb) Apart.nil
  | d + 1 =>
      Apart.cons
        (fun _ hb =>
          match mem_cross_split (allPlans d) hb with
          | ⟨_, _, he, _, _⟩ => fun hg => nomatch hg.trans he)
        (the_cross_keeps_apart (the_room_repeats_no_plan d)
          (the_room_repeats_no_plan d))

