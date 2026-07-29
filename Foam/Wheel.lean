import Foam.Marks

namespace Foam

def turnN {n : Nat} (m : Fin n → Fin n) : Nat → Fin n → Fin n
  | 0, s => s
  | k + 1, s => m (turnN m k s)

inductive Apart {A : Type} : List A → Prop
  | nil : Apart []
  | cons {a : A} {l : List A} :
      (∀ b, b ∈ l → a ≠ b) → Apart l → Apart (a :: l)

theorem fin_eq_of_val_eq {n : Nat} : ∀ {x y : Fin n}, x.val = y.val → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

def dropTop {n : Nat} : List (Fin (n + 1)) → List (Fin n)
  | [] => []
  | x :: l =>
      if h : x.val < n then ⟨x.val, h⟩ :: dropTop l else dropTop l

theorem mem_dropTop_back {n : Nat} :
    ∀ (l : List (Fin (n + 1))) (c : Fin n), c ∈ dropTop l →
      ∃ b, b ∈ l ∧ b.val = c.val
  | [], _, hc => nomatch hc
  | x :: l, c, hc => by
      unfold dropTop at hc
      by_cases hx : x.val < n
      · rw [dif_pos hx] at hc
        cases hc with
        | head => exact ⟨x, .head l, rfl⟩
        | tail _ hc' =>
            obtain ⟨b, hb, he⟩ := mem_dropTop_back l c hc'
            exact ⟨b, .tail x hb, he⟩
      · rw [dif_neg hx] at hc
        obtain ⟨b, hb, he⟩ := mem_dropTop_back l c hc
        exact ⟨b, .tail x hb, he⟩

theorem dropTop_apart {n : Nat} :
    ∀ l : List (Fin (n + 1)), Apart l → Apart (dropTop l)
  | [], _ => .nil
  | x :: l, .cons hx hl => by
      unfold dropTop
      by_cases hxn : x.val < n
      · rw [dif_pos hxn]
        exact .cons
          (fun c hc he => by
            obtain ⟨b, hb, hbv⟩ := mem_dropTop_back l c hc
            exact hx b hb (fin_eq_of_val_eq
              ((congrArg Fin.val he).trans hbv.symm)))
          (dropTop_apart l hl)
      · rw [dif_neg hxn]
        exact dropTop_apart l hl

theorem dropTop_keeps {n : Nat} :
    ∀ l : List (Fin (n + 1)), (∀ b, b ∈ l → b.val < n) →
      (dropTop l).length = l.length
  | [], _ => rfl
  | x :: l, h => by
      unfold dropTop
      rw [dif_pos (h x (.head l))]
      exact congrArg (· + 1) (dropTop_keeps l (fun b hb => h b (.tail x hb)))

theorem dropTop_length {n : Nat} :
    ∀ l : List (Fin (n + 1)), Apart l → l.length ≤ (dropTop l).length + 1
  | [], _ => Nat.zero_le 1
  | x :: l, .cons hx hl => by
      unfold dropTop
      by_cases hxn : x.val < n
      · rw [dif_pos hxn]
        exact Nat.succ_le_succ (dropTop_length l hl)
      · have hxtop : x.val = n :=
          Nat.le_antisymm (succ_le_succ_inv x.isLt)
            (match Nat.lt_or_ge x.val n with
             | .inl hlt => absurd hlt hxn
             | .inr hge => hge)
        have hbelow : ∀ b, b ∈ l → b.val < n := fun b hb =>
          match Nat.lt_or_ge b.val n with
          | .inl hlt => hlt
          | .inr hge =>
              have hbn : b.val = n :=
                Nat.le_antisymm (succ_le_succ_inv b.isLt) hge
              absurd (fin_eq_of_val_eq (hxtop.trans hbn.symm)) (hx b hb)
        rw [dif_neg hxn, dropTop_keeps l hbelow]
        exact Nat.le_refl _

theorem apart_le : ∀ (n : Nat) (l : List (Fin n)), Apart l → l.length ≤ n
  | 0, [], _ => Nat.le_refl 0
  | 0, x :: _, _ => x.elim0
  | n + 1, l, hl =>
      le_trans (dropTop_length l hl)
        (Nat.succ_le_succ (apart_le n (dropTop l) (dropTop_apart l hl)))

theorem mem_or_not {A : Type} (deq : DecidableEq A) (a : A) :
    ∀ l : List A, a ∈ l ∨ ¬ a ∈ l
  | [] => .inr (fun h => nomatch h)
  | b :: l =>
      match deq a b with
      | .isTrue h => .inl (h ▸ List.Mem.head l)
      | .isFalse hne =>
          match mem_or_not deq a l with
          | .inl h => .inl (.tail b h)
          | .inr hn => .inr (fun hmem => by
              cases hmem with
              | head => exact hne rfl
              | tail _ h' => exact hn h')

theorem rungs_length : ∀ k : Nat, (rungs k).length = k
  | 0 => rfl
  | k + 1 => congrArg (· + 1) (rungs_length k)

theorem meet_or_apart {n : Nat} (m : Fin n → Fin n) (s : Fin n) :
    ∀ k : Nat,
      (∃ i j, i < j ∧ j < k ∧ turnN m i s = turnN m j s)
        ∨ Apart ((rungs k).map (fun i => turnN m i s))
  | 0 => .inr .nil
  | k + 1 =>
      match meet_or_apart m s k with
      | .inl ⟨i, j, hij, hjk, he⟩ => .inl ⟨i, j, hij, Nat.le.step hjk, he⟩
      | .inr hap =>
          match mem_or_not (fun a b => inferInstance) (turnN m k s)
              ((rungs k).map (fun i => turnN m i s)) with
          | .inl hmem =>
              match mem_map_back (rungs k) hmem with
              | ⟨i, hi, he⟩ =>
                  .inl ⟨i, k, the_walked_lie_below k i hi, Nat.le.refl, he⟩
          | .inr hno =>
              .inr (.cons (fun b hb hvb => by cases hvb; exact hno hb) hap)

theorem the_bounded_walk_returns {n : Nat} (m : Fin n → Fin n) (s : Fin n) :
    ∃ i j : Nat, i < j ∧ turnN m i s = turnN m j s :=
  match meet_or_apart m s (n + 1) with
  | .inl ⟨i, j, hij, _, he⟩ => ⟨i, j, hij, he⟩
  | .inr hap =>
      absurd
        (show n + 1 ≤ n from by
          have h := apart_le n ((rungs (n + 1)).map (fun i => turnN m i s)) hap
          rw [len_map, rungs_length] at h
          exact h)
        (no_number_is_below_itself n)

/-- info: 'Foam.fin_eq_of_val_eq' does not depend on any axioms -/
#guard_msgs in #print axioms fin_eq_of_val_eq

/-- info: 'Foam.mem_dropTop_back' does not depend on any axioms -/
#guard_msgs in #print axioms mem_dropTop_back

/-- info: 'Foam.dropTop_apart' does not depend on any axioms -/
#guard_msgs in #print axioms dropTop_apart

/-- info: 'Foam.dropTop_keeps' does not depend on any axioms -/
#guard_msgs in #print axioms dropTop_keeps

/-- info: 'Foam.dropTop_length' does not depend on any axioms -/
#guard_msgs in #print axioms dropTop_length

/-- info: 'Foam.apart_le' does not depend on any axioms -/
#guard_msgs in #print axioms apart_le

/-- info: 'Foam.mem_or_not' does not depend on any axioms -/
#guard_msgs in #print axioms mem_or_not

/-- info: 'Foam.rungs_length' does not depend on any axioms -/
#guard_msgs in #print axioms rungs_length

/-- info: 'Foam.meet_or_apart' does not depend on any axioms -/
#guard_msgs in #print axioms meet_or_apart

/-- info: 'Foam.the_bounded_walk_returns' does not depend on any axioms -/
#guard_msgs in #print axioms the_bounded_walk_returns

end Foam
