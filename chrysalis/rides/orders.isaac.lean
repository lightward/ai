import Seed
open Seed
set_option autoImplicit false


universe u v

theorem perm_refl {A : Type u} : ∀ l : List A, l.Perm l
  | [] => .nil
  | x :: l => .cons x (perm_refl l)


theorem the_insertion_is_a_shuffle {A : Type u} (x : A) :
    ∀ (r q : List A), q ∈ inserts x r → q.Perm (x :: r)
  | [], q, h => by
      cases h with
      | head => exact perm_refl [x]
      | tail _ h' => exact nomatch h'
  | y :: r, q, h => by
      cases h with
      | head => exact perm_refl (x :: y :: r)
      | tail _ h' =>
          obtain ⟨q', hq', he⟩ := mem_map_back (inserts x r) h'
          rw [← he]
          exact List.Perm.trans
            (List.Perm.cons y (the_insertion_is_a_shuffle x r q' hq'))
            (List.Perm.swap x y r)


theorem every_order_is_a_shuffle {A : Type u} :
    ∀ (l p : List A), p ∈ perms l → p.Perm l
  | [], p, h => by
      cases h with
      | head => exact .nil
      | tail _ h' => exact nomatch h'
  | x :: l, p, h => by
      have h' : p ∈ joinMap (inserts x) (perms l) := h
      obtain ⟨r, hr, hp⟩ := mem_joinMap_back (perms l) h'
      exact List.Perm.trans (the_insertion_is_a_shuffle x r p hp)
        (List.Perm.cons x (every_order_is_a_shuffle l r hr))


theorem perm_mem {A : Type u} {xs ys : List A} (h : xs.Perm ys) :
    ∀ a, a ∈ xs → a ∈ ys := by
  induction h with
  | nil => exact fun _ ha => ha
  | cons x _ ih =>
      intro a ha
      cases ha with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail _ (ih a h')
  | swap x y l =>
      intro a ha
      cases ha with
      | head => exact List.Mem.tail _ (List.Mem.head _)
      | tail _ h' =>
          cases h' with
          | head => exact List.Mem.head _
          | tail _ h'' => exact List.Mem.tail _ (List.Mem.tail _ h'')
  | trans _ _ ih₁ ih₂ => exact fun a ha => ih₂ a (ih₁ a ha)



theorem the_wedgings_stand_apart {A : Type u} (x : A) :
    ∀ p : List A, ¬ x ∈ p → Apart (inserts x p)
  | [], _ => .cons (fun _ hb => nomatch hb) .nil
  | y :: p, hx => by
      have hxy : x ≠ y := fun he => hx (by rw [he]; exact List.Mem.head p)
      have hxp : ¬ x ∈ p := fun hm => hx (List.Mem.tail y hm)
      refine Apart.cons ?_
        (apart_map (fun _ _ h => (List.cons.inj h).2)
          (the_wedgings_stand_apart x p hxp))
      intro q hq he
      obtain ⟨r, hr, hyr⟩ := mem_map_back (inserts x p) hq
      exact hxy (List.cons.inj (he.trans hyr.symm)).1


theorem the_wedge_remembers_its_word {A : Type u} (x : A) :
    ∀ (p p' q : List A), q ∈ inserts x p → q ∈ inserts x p' →
      ¬ x ∈ p → ¬ x ∈ p' → p = p'
  | [], [], _, _, _, _, _ => rfl
  | [], y' :: p', q, h₁, h₂, _, hx' => by
      cases h₁ with
      | head =>
          cases h₂ with
          | tail _ h₂' =>
              obtain ⟨r', _, he'⟩ := mem_map_back (inserts x p') h₂'
              exact absurd
                (show x ∈ y' :: p' from by
                  rw [← (List.cons.inj he').1]
                  exact List.Mem.head p')
                hx'
      | tail _ h₁' => exact nomatch h₁'
  | y :: p, [], q, h₁, h₂, hx, _ => by
      cases h₂ with
      | head =>
          cases h₁ with
          | tail _ h₁' =>
              obtain ⟨r, _, he⟩ := mem_map_back (inserts x p) h₁'
              exact absurd
                (show x ∈ y :: p from by
                  rw [← (List.cons.inj he).1]
                  exact List.Mem.head p)
                hx
      | tail _ h₂' => exact nomatch h₂'
  | y :: p, y' :: p', q, h₁, h₂, hx, hx' => by
      have hxy : x ≠ y := fun he => hx (by rw [he]; exact List.Mem.head p)
      have hxy' : x ≠ y' :=
        fun he => hx' (by rw [he]; exact List.Mem.head p')
      cases h₁ with
      | head =>
          cases h₂ with
          | head => rfl
          | tail _ h₂' =>
              obtain ⟨r', _, he'⟩ := mem_map_back (inserts x p') h₂'
              exact (hxy' (List.cons.inj he').1.symm).elim
      | tail _ h₁' =>
          obtain ⟨r, hr, he⟩ := mem_map_back (inserts x p) h₁'
          cases h₂ with
          | head => exact (hxy (List.cons.inj he).1.symm).elim
          | tail _ h₂' =>
              obtain ⟨r', hr', he'⟩ := mem_map_back (inserts x p') h₂'
              have hyy : y = y' := (List.cons.inj (he.trans he'.symm)).1
              have hrr : r = r' := (List.cons.inj (he.trans he'.symm)).2
              have hpp : p = p' :=
                the_wedge_remembers_its_word x p p' r hr
                  (by rw [hrr]; exact hr')
                  (fun hm => hx (List.Mem.tail y hm))
                  (fun hm => hx' (List.Mem.tail y' hm))
              rw [hyy, hpp]


theorem apart_joinMap {A : Type u} {B : Type v} (f : A → List B) :
    ∀ as : List A, Apart as → (∀ a, a ∈ as → Apart (f a)) →
      (∀ a, a ∈ as → ∀ b, b ∈ as → a ≠ b →
        ∀ q, q ∈ f a → ¬ q ∈ f b) →
      Apart (joinMap f as)
  | [], _, _, _ => .nil
  | a :: as, .cons ha has, hfib, hdisj => by
      refine apart_append (joinMap f as) (hfib a (List.Mem.head as))
        ?_ ?_
      · exact apart_joinMap f as has
          (fun b hb => hfib b (List.Mem.tail a hb))
          (fun b hb c hc =>
            hdisj b (List.Mem.tail a hb) c (List.Mem.tail a hc))
      · intro q hq q' hq' he
        obtain ⟨b, hb, hqb⟩ := mem_joinMap_back as hq'
        have hqfb : q ∈ f b := by rw [he]; exact hqb
        exact hdisj a (List.Mem.head as) b (List.Mem.tail a hb)
          (ha b hb) q hq hqfb


theorem the_orders_repeat_never {A : Type u} :
    ∀ l : List A, Apart l → Apart (perms l)
  | [], _ => .cons (fun _ hb => nomatch hb) .nil
  | x :: l, .cons hx hl => by
      have hxl : ¬ x ∈ l := fun hm => hx x hm rfl
      have hxp : ∀ p, p ∈ perms l → ¬ x ∈ p := fun p hp hm =>
        hxl (perm_mem (every_order_is_a_shuffle l p hp) x hm)
      show Apart (joinMap (inserts x) (perms l))
      exact apart_joinMap (inserts x) (perms l)
        (the_orders_repeat_never l hl)
        (fun p hp => the_wedgings_stand_apart x p (hxp p hp))
        (fun p hp p' hp' hne q hq hq' =>
          hne (the_wedge_remembers_its_word x p p' q hq hq'
            (hxp p hp) (hxp p' hp')))

