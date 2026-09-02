import Seed
open Seed
set_option autoImplicit false

theorem succ_adds (a b : Nat) : (a + 1) + b = (a + b) + 1 :=
  (click_slides a b).symm


theorem ble_refl : ∀ n : Nat, Nat.ble n n = true
  | 0 => rfl
  | n + 1 => ble_refl n

theorem ble_le_succ : ∀ n : Nat, Nat.ble n (n + 1) = true
  | 0 => rfl
  | n + 1 => ble_le_succ n


theorem ble_trans : ∀ (a b c : Nat),
    Nat.ble a b = true → Nat.ble b c = true → Nat.ble a c = true
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, _, h1, _ => nomatch h1
  | _ + 1, _ + 1, 0, _, h2 => nomatch h2
  | a + 1, b + 1, c + 1, h1, h2 => ble_trans a b c h1 h2





theorem ble_le_add : ∀ a b : Nat, Nat.ble a (a + b) = true
  | a, 0 => ble_refl a
  | a, b + 1 =>
      ble_trans a (a + b) ((a + b) + 1) (ble_le_add a b) (ble_le_succ (a + b))

theorem ble_le_add_left : ∀ a b : Nat, Nat.ble b (a + b) = true
  | 0, b => by rw [zero_add]; exact ble_refl b
  | a + 1, b => by
      rw [succ_adds]
      exact ble_trans b (a + b) ((a + b) + 1)
        (ble_le_add_left a b) (ble_le_succ (a + b))



theorem the_reading_is_positive :
    ∀ p : Plan, ∃ m : Nat, reading p = m + 1
  | .ground => ⟨0, rfl⟩
  | .board l r =>
      match the_reading_is_positive l with
      | ⟨a, ha⟩ =>
          ⟨a + reading r, by
            show reading l + reading r = (a + reading r) + 1
            rw [ha, succ_adds]⟩



universe u v

theorem mem_map_intro {A : Type u} {B : Type v} (f : A → B) :
    ∀ {x : A} {xs : List A}, x ∈ xs → f x ∈ xs.map f
  | _, _ :: _, List.Mem.head _ => List.Mem.head _
  | _, _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_map_intro f h)

theorem mem_append_left {A : Type u} (ys : List A) :
    ∀ {x : A} {xs : List A}, x ∈ xs → x ∈ xs ++ ys
  | _, _ :: _, List.Mem.head _ => List.Mem.head _
  | _, _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_append_left ys h)

theorem mem_append_right {A : Type u} :
    ∀ (xs : List A) {x : A} {ys : List A}, x ∈ ys → x ∈ xs ++ ys
  | [], _, _, h => h
  | _ :: xs, _, _, h => List.Mem.tail _ (mem_append_right xs h)



theorem mem_cross {qs : List Plan} {r : Plan} (hr : r ∈ qs) :
    ∀ {ps : List Plan} {l : Plan}, l ∈ ps → Plan.board l r ∈ cross ps qs
  | _ :: ps, _, List.Mem.head _ =>
      mem_append_left (cross ps qs) (mem_map_intro (Plan.board _) hr)
  | p :: _, _, List.Mem.tail _ h =>
      mem_append_right (qs.map (Plan.board p)) (mem_cross hr h)




theorem the_horizon_holds_every_reading :
    ∀ (n : Nat) (p : Plan),
      Nat.ble (reading p) (n + 1) = true → p ∈ allPlans n
  | 0, .ground, _ => List.Mem.head _
  | _ + 1, .ground, _ => List.Mem.head _
  | 0, .board l r, h =>
      match the_reading_is_positive l, the_reading_is_positive r with
      | ⟨a, ha⟩, ⟨b, hb⟩ => by
          have e : (a + 1) + (b + 1) = ((a + b) + 1) + 1 :=
            congrArg (· + 1) (succ_adds a b)
          have h0 : Nat.ble (reading l + reading r) 1 = true := h
          rw [ha, hb, e] at h0
          exact nomatch h0
  | n + 1, .board l r, h =>
      match the_reading_is_positive l, the_reading_is_positive r with
      | ⟨a, ha⟩, ⟨b, hb⟩ =>
          have e : (a + 1) + (b + 1) = ((a + b) + 1) + 1 :=
            congrArg (· + 1) (succ_adds a b)
          have h' : Nat.ble ((a + b) + 1) (n + 1) = true := by
            have h0 : Nat.ble (reading l + reading r) ((n + 1) + 1) = true := h
            rw [ha, hb, e] at h0
            exact h0
          have hL : l ∈ allPlans n :=
            the_horizon_holds_every_reading n l (by
              rw [ha]
              exact ble_trans (a + 1) ((a + b) + 1) (n + 1)
                (ble_le_add a b) h')
          have hR : r ∈ allPlans n :=
            the_horizon_holds_every_reading n r (by
              rw [hb]
              exact ble_trans (b + 1) ((a + b) + 1) (n + 1)
                (ble_le_add_left a b) h')
          List.Mem.tail _ (mem_cross hR hL)


theorem eq_of_beq : ∀ a b : Nat, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | a + 1, b + 1, h => congrArg (· + 1) (eq_of_beq a b h)

theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n


theorem mem_of_mem_filter {A : Type u} {q : A → Bool} {x : A} :
    ∀ xs : List A, x ∈ xs.filter q → x ∈ xs
  | [], h => nomatch h
  | a :: xs, h => by
      cases hq : q a with
      | true =>
          rw [List.filter_cons_of_pos hq] at h
          cases h with
          | head => exact List.Mem.head _
          | tail _ h' => exact List.Mem.tail _ (mem_of_mem_filter xs h')
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq)] at h
          exact List.Mem.tail _ (mem_of_mem_filter xs h)

theorem filter_holds {A : Type u} {q : A → Bool} {x : A} :
    ∀ xs : List A, x ∈ xs.filter q → q x = true
  | [], h => nomatch h
  | a :: xs, h => by
      cases hq : q a with
      | true =>
          rw [List.filter_cons_of_pos hq] at h
          cases h with
          | head => exact hq
          | tail _ h' => exact filter_holds xs h'
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq)] at h
          exact filter_holds xs h



theorem mem_filter_intro {A : Type u} {q : A → Bool} {x : A} :
    ∀ xs : List A, x ∈ xs → q x = true → x ∈ xs.filter q
  | [], h, _ => nomatch h
  | a :: xs, h, hx => by
      cases h with
      | head =>
          rw [List.filter_cons_of_pos hx]
          exact List.Mem.head _
      | tail _ h' =>
          cases hq : q a with
          | true =>
              rw [List.filter_cons_of_pos hq]
              exact List.Mem.tail _ (mem_filter_intro xs h' hx)
          | false =>
              rw [List.filter_cons_of_neg (ne_true_of_eq_false hq)]
              exact mem_filter_intro xs h' hx


theorem apart_filter {A : Type u} {q : A → Bool} :
    ∀ {xs : List A}, Apart xs → Apart (xs.filter q)
  | [], _ => Apart.nil
  | a :: xs, Apart.cons ha hxs => by
      cases hq : q a with
      | true =>
          rw [List.filter_cons_of_pos hq]
          exact Apart.cons
            (fun b hb => ha b (mem_of_mem_filter xs hb))
            (apart_filter hxs)
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq)]
          exact apart_filter hxs


theorem the_census_is_exact (k : Nat) :
    Apart ((allPlans k).filter (fun p => Nat.beq (reading p) (k + 1)))
      ∧ ∀ p : Plan,
          p ∈ (allPlans k).filter (fun p => Nat.beq (reading p) (k + 1))
            ↔ reading p = k + 1 :=
  ⟨apart_filter (the_room_repeats_no_plan k),
   fun p =>
     ⟨fun h =>
        have hq :=
          filter_holds (A := Plan)
            (q := fun p => Nat.beq (reading p) (k + 1))
            (x := p) (allPlans k) h
        eq_of_beq _ _ hq,
      fun h =>
        mem_filter_intro (allPlans k)
          (the_horizon_holds_every_reading k p
            (by rw [h]; exact ble_refl (k + 1)))
          (by rw [h]; exact beq_self (k + 1))⟩⟩



