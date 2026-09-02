import Foam.Concentration

namespace Foam

def IsPre (p m : List Bool) : Prop := ∃ t : List Bool, p ++ t = m

inductive MarkFree : List (List Bool) → Prop
  | nil : MarkFree []
  | cons {m : List Bool} {ms : List (List Bool)} :
      (∀ m', List.Mem m' ms → ¬ IsPre m m' ∧ ¬ IsPre m' m) →
      MarkFree ms → MarkFree (m :: ms)

inductive AllDiff : List (List Bool) → Prop
  | nil : AllDiff []
  | cons {w : List Bool} {ws : List (List Bool)} :
      (∀ w', List.Mem w' ws → w ≠ w') →
      AllDiff ws → AllDiff (w :: ws)

theorem two_pow_clears_the_line : ∀ k : Nat, k + 1 ≤ 2 ^ k
  | 0 => Nat.le_refl 1
  | k + 1 => by
      rw [show (2 : Nat) ^ (k + 1) = 2 ^ k * 2 from rfl, nat_mul_two]
      show (k + 1) + 1 ≤ 2 ^ k + 2 ^ k
      exact Nat.add_le_add (two_pow_clears_the_line k)
        (le_trans (Nat.succ_le_succ (Nat.zero_le k)) (two_pow_clears_the_line k))

theorem two_pow_pos (k : Nat) : 0 < 2 ^ k :=
  le_trans (Nat.succ_le_succ (Nat.zero_le k)) (two_pow_clears_the_line k)

theorem pow_splits : ∀ a b : Nat, 2 ^ (a + b) = 2 ^ a * 2 ^ b
  | _, 0 => (Nat.mul_one _).symm
  | a, b + 1 => by
      show 2 ^ (a + b) * 2 = 2 ^ a * (2 ^ b * 2)
      rw [pow_splits a b, FInt.nat_mul_assoc]

theorem sub_then_add_recovers (a b : Nat) : a ≤ (a - b) + b := by
  cases Nat.lt_or_ge a b with
  | inl hlt =>
      rw [FInt.sub_eq_zero_of_le (Nat.le_of_lt hlt), nothing_added]
      exact Nat.le_of_lt hlt
  | inr hge =>
      obtain ⟨d, hd⟩ := Nat.le.dest hge
      rw [← hd, FInt.add_sub_cancel_left, Nat.add_comm]
      exact Nat.le_refl _

theorem natSumOver_map (v : List Bool → Nat) (g : List Bool → List Bool) :
    ∀ B : List (List Bool),
      natSumOver v (B.map g) = natSumOver (fun w => v (g w)) B
  | [] => rfl
  | w :: B => congrArg (v (g w) + ·) (natSumOver_map v g B)

theorem natSumOver_const (c : Nat) :
    ∀ B : List (List Bool), natSumOver (fun _ => c) B = B.length * c
  | [] => (Nat.zero_mul c).symm
  | w :: B => by
      show c + natSumOver (fun _ => c) B = (B.length + 1) * c
      rw [natSumOver_const c B, succ_mul', Nat.add_comm c]

theorem natSumOver_add (v u : List Bool → Nat) :
    ∀ B : List (List Bool),
      natSumOver (fun w => v w + u w) B = natSumOver v B + natSumOver u B
  | [] => rfl
  | w :: B => by
      show (v w + u w) + natSumOver (fun w => v w + u w) B
          = (v w + natSumOver v B) + (u w + natSumOver u B)
      rw [natSumOver_add v u B, nat_swap_mid]

theorem natSumOver_mono {v u : List Bool → Nat} :
    ∀ B : List (List Bool), (∀ w, List.Mem w B → v w ≤ u w) →
      natSumOver v B ≤ natSumOver u B
  | [], _ => Nat.le_refl 0
  | w :: B, h =>
      Nat.add_le_add (h w (.head B))
        (natSumOver_mono B (fun w' hw' => h w' (.tail w hw')))

theorem pool_length :
    ∀ B : List (List Bool), (pool B).length = natSumOver List.length B
  | [] => rfl
  | w :: B => by
      show (w ++ pool B).length = w.length + natSumOver List.length B
      rw [len_append, pool_length B]

def tailsT : List (List Bool) → List (List Bool)
  | [] => []
  | [] :: ms => tailsT ms
  | (true :: t) :: ms => t :: tailsT ms
  | (false :: _) :: ms => tailsT ms

def tailsF : List (List Bool) → List (List Bool)
  | [] => []
  | [] :: ms => tailsF ms
  | (true :: _) :: ms => tailsF ms
  | (false :: t) :: ms => t :: tailsF ms

def hasEmpty : List (List Bool) → Bool
  | [] => false
  | [] :: _ => true
  | (_ :: _) :: ms => hasEmpty ms

theorem no_empty_of_hasEmpty_false :
    ∀ ms : List (List Bool), hasEmpty ms = false →
      ∀ m, List.Mem m ms → m ≠ []
  | [], _, _, hm => nomatch hm
  | [] :: _, h, _, _ => nomatch show true = false from h
  | (a :: t) :: ms, h, m, hm => by
      cases hm with
      | head => intro he; cases he
      | tail _ hm' => exact no_empty_of_hasEmpty_false ms h m hm'

theorem mem_of_hasEmpty_true :
    ∀ ms : List (List Bool), hasEmpty ms = true → List.Mem [] ms
  | [], h => nomatch show false = true from h
  | [] :: ms, _ => .head ms
  | (_ :: _) :: ms, h => .tail _ (mem_of_hasEmpty_true ms h)

theorem the_empty_mark_stands_alone :
    ∀ ms : List (List Bool), MarkFree ms → List.Mem [] ms → ms = [([] : List Bool)]
  | [], _, hm => nomatch hm
  | m :: ms, hf, hm => by
      match hf with
      | .cons hc _ =>
        cases hm with
        | head =>
            cases ms with
            | nil => rfl
            | cons m' ms' => exact ((hc m' (.head ms')).1 ⟨m', rfl⟩).elim
        | tail _ hm' => exact ((hc [] hm').2 ⟨m, rfl⟩).elim

theorem mem_tailsT :
    ∀ ms t, List.Mem t (tailsT ms) → List.Mem (true :: t) ms
  | [], _, h => nomatch h
  | [] :: ms, t, h => .tail _ (mem_tailsT ms t h)
  | (true :: _) :: ms, t, h => by
      cases h with
      | head => exact .head _
      | tail _ h' => exact .tail _ (mem_tailsT ms t h')
  | (false :: _) :: ms, t, h => .tail _ (mem_tailsT ms t h)

theorem mem_tailsF :
    ∀ ms t, List.Mem t (tailsF ms) → List.Mem (false :: t) ms
  | [], _, h => nomatch h
  | [] :: ms, t, h => .tail _ (mem_tailsF ms t h)
  | (true :: _) :: ms, t, h => .tail _ (mem_tailsF ms t h)
  | (false :: _) :: ms, t, h => by
      cases h with
      | head => exact .head _
      | tail _ h' => exact .tail _ (mem_tailsF ms t h')

theorem ispre_cons (b : Bool) {p m : List Bool} (h : IsPre p m) :
    IsPre (b :: p) (b :: m) :=
  match h with
  | ⟨t, ht⟩ => ⟨t, congrArg (b :: ·) ht⟩

theorem tailsT_free : ∀ ms : List (List Bool), MarkFree ms → MarkFree (tailsT ms)
  | [], _ => .nil
  | [] :: ms, hf => match hf with | .cons _ hf' => tailsT_free ms hf'
  | (true :: _t) :: ms, hf =>
      match hf with
      | .cons hc hf' =>
          .cons (fun t' ht' =>
              ⟨fun hp => (hc (true :: t') (mem_tailsT ms t' ht')).1
                  (ispre_cons true hp),
               fun hp => (hc (true :: t') (mem_tailsT ms t' ht')).2
                  (ispre_cons true hp)⟩)
            (tailsT_free ms hf')
  | (false :: _) :: ms, hf =>
      match hf with | .cons _ hf' => tailsT_free ms hf'

theorem tailsF_free : ∀ ms : List (List Bool), MarkFree ms → MarkFree (tailsF ms)
  | [], _ => .nil
  | [] :: ms, hf => match hf with | .cons _ hf' => tailsF_free ms hf'
  | (true :: _) :: ms, hf =>
      match hf with | .cons _ hf' => tailsF_free ms hf'
  | (false :: _t) :: ms, hf =>
      match hf with
      | .cons hc hf' =>
          .cons (fun t' ht' =>
              ⟨fun hp => (hc (false :: t') (mem_tailsF ms t' ht')).1
                  (ispre_cons false hp),
               fun hp => (hc (false :: t') (mem_tailsF ms t' ht')).2
                  (ispre_cons false hp)⟩)
            (tailsF_free ms hf')

theorem tailsT_len (L : Nat) (ms : List (List Bool))
    (hlen : ∀ m, List.Mem m ms → m.length ≤ L + 1) :
    ∀ t, List.Mem t (tailsT ms) → t.length ≤ L :=
  fun t ht => succ_le_succ_inv (hlen (true :: t) (mem_tailsT ms t ht))

theorem tailsF_len (L : Nat) (ms : List (List Bool))
    (hlen : ∀ m, List.Mem m ms → m.length ≤ L + 1) :
    ∀ t, List.Mem t (tailsF ms) → t.length ≤ L :=
  fun t ht => succ_le_succ_inv (hlen (false :: t) (mem_tailsF ms t ht))

theorem split_sum (L : Nat) :
    ∀ ms : List (List Bool), (∀ m, List.Mem m ms → m ≠ []) →
      natSumOver (fun m => 2 ^ (L + 1 - m.length)) ms
        = natSumOver (fun t => 2 ^ (L - t.length)) (tailsT ms)
          + natSumOver (fun t => 2 ^ (L - t.length)) (tailsF ms)
  | [], _ => rfl
  | [] :: ms, h => ((h [] (.head ms)) rfl).elim
  | (true :: t) :: ms, h => by
      show 2 ^ (L + 1 - (t.length + 1))
            + natSumOver (fun m => 2 ^ (L + 1 - m.length)) ms
          = (2 ^ (L - t.length)
              + natSumOver (fun t => 2 ^ (L - t.length)) (tailsT ms))
            + natSumOver (fun t => 2 ^ (L - t.length)) (tailsF ms)
      rw [Nat.succ_sub_succ, split_sum L ms (fun m hm => h m (.tail _ hm)),
          adding_associates]
  | (false :: t) :: ms, h => by
      show 2 ^ (L + 1 - (t.length + 1))
            + natSumOver (fun m => 2 ^ (L + 1 - m.length)) ms
          = natSumOver (fun t => 2 ^ (L - t.length)) (tailsT ms)
            + (2 ^ (L - t.length)
                + natSumOver (fun t => 2 ^ (L - t.length)) (tailsF ms))
      rw [Nat.succ_sub_succ, split_sum L ms (fun m hm => h m (.tail _ hm)),
          adding_associates,
          Nat.add_comm (2 ^ (L - t.length))
            (natSumOver (fun t => 2 ^ (L - t.length)) (tailsT ms)),
          ← adding_associates]

theorem the_antichain_measure_is_bounded :
    ∀ (L : Nat) (ms : List (List Bool)), MarkFree ms →
      (∀ m, List.Mem m ms → m.length ≤ L) →
      natSumOver (fun m => 2 ^ (L - m.length)) ms ≤ 2 ^ L
  | 0, [], _, _ => Nat.zero_le 1
  | 0, m :: ms, hf, hlen => by
      have hm0 : m = [] := by
        cases m with
        | nil => rfl
        | cons a t => exact nomatch hlen (a :: t) (.head ms)
      subst hm0
      cases ms with
      | nil => exact Nat.le_refl 1
      | cons m' ms' =>
          have hm'0 : m' = [] := by
            cases m' with
            | nil => rfl
            | cons a t => exact nomatch hlen (a :: t) (.tail _ (.head ms'))
          subst hm'0
          match hf with
          | .cons hc _ => exact ((hc [] (.head ms')).1 ⟨[], rfl⟩).elim
  | L + 1, ms, hf, hlen => by
      cases hE : hasEmpty ms with
      | true =>
          rw [the_empty_mark_stands_alone ms hf (mem_of_hasEmpty_true ms hE)]
          exact Nat.le_refl _
      | false =>
          rw [split_sum L ms (no_empty_of_hasEmpty_false ms hE),
              show (2 : Nat) ^ (L + 1) = 2 ^ L + 2 ^ L from by
                rw [show (2 : Nat) ^ (L + 1) = 2 ^ L * 2 from rfl, nat_mul_two]]
          exact Nat.add_le_add
            (the_antichain_measure_is_bounded L (tailsT ms)
              (tailsT_free ms hf) (tailsT_len L ms hlen))
            (the_antichain_measure_is_bounded L (tailsF ms)
              (tailsF_free ms hf) (tailsF_len L ms hlen))

def maxLen : List (List Bool) → Nat
  | [] => 0
  | m :: ms => if m.length ≤ maxLen ms then maxLen ms else m.length

theorem le_maxLen : ∀ (ms : List (List Bool)) (m : List Bool),
    List.Mem m ms → m.length ≤ maxLen ms
  | [], _, hm => nomatch hm
  | m' :: ms, m, hm => by
      cases hm with
      | head =>
          show m'.length ≤ if m'.length ≤ maxLen ms then maxLen ms else m'.length
          by_cases hc : m'.length ≤ maxLen ms
          · rw [if_pos hc]; exact hc
          · rw [if_neg hc]; exact Nat.le_refl _
      | tail _ hm' =>
          show m.length ≤ if m'.length ≤ maxLen ms then maxLen ms else m'.length
          by_cases hc : m'.length ≤ maxLen ms
          · rw [if_pos hc]; exact le_maxLen ms m hm'
          · rw [if_neg hc]
            cases Nat.lt_or_ge (maxLen ms) m'.length with
            | inl hlt => exact le_trans (le_maxLen ms m hm') (Nat.le_of_lt hlt)
            | inr hge => exact (hc hge).elim

theorem mem_append_split {A : Type} {w : A} :
    ∀ (X Y : List A), List.Mem w (X ++ Y) → List.Mem w X ∨ List.Mem w Y
  | [], _, h => Or.inr h
  | x :: X, Y, h => by
      cases h with
      | head => exact Or.inl (.head X)
      | tail _ h' =>
          cases mem_append_split X Y h' with
          | inl hx => exact Or.inl (.tail x hx)
          | inr hy => exact Or.inr hy

theorem mem_map_back {A B : Type} {g : A → B} {x : B} :
    ∀ ws : List A, List.Mem x (ws.map g) → ∃ w, List.Mem w ws ∧ g w = x
  | [], h => nomatch h
  | w :: ws, h => by
      cases h with
      | head => exact ⟨w, .head ws, rfl⟩
      | tail _ h' =>
          obtain ⟨w', hw', he⟩ := mem_map_back ws h'
          exact ⟨w', .tail w hw', he⟩

theorem alldiff_map {g : List Bool → List Bool}
    (hg : ∀ a b, g a = g b → a = b) :
    ∀ {ws : List (List Bool)}, AllDiff ws → AllDiff (ws.map g)
  | [], _ => .nil
  | w :: ws, .cons hne hd =>
      .cons (fun x hx hgw => by
          obtain ⟨w', hw', he⟩ := mem_map_back ws hx
          exact hne w' hw' (hg w w' (hgw.trans he.symm)))
        (alldiff_map hg hd)

theorem alldiff_append :
    ∀ (X Y : List (List Bool)), AllDiff X → AllDiff Y →
      (∀ x y, List.Mem x X → List.Mem y Y → x ≠ y) →
      AllDiff (X ++ Y)
  | [], _, _, hY, _ => hY
  | x :: X, Y, .cons hne hdX, hY, hcross =>
      .cons (fun w' hw' => by
          cases mem_append_split X Y hw' with
          | inl hx => exact hne w' hx
          | inr hy => exact hcross x w' (.head X) hy)
        (alldiff_append X Y hdX hY
          (fun a b ha hb => hcross a b (.tail x ha) hb))

theorem the_book_repeats_no_word : ∀ n : Nat, AllDiff (book n)
  | 0 => .cons (fun _ hw' => nomatch hw') .nil
  | n + 1 => by
      show AllDiff ((book n).map (true :: ·) ++ (book n).map (false :: ·))
      exact alldiff_append _ _
        (alldiff_map (fun _ _ h => (List.cons.inj h).2)
          (the_book_repeats_no_word n))
        (alldiff_map (fun _ _ h => (List.cons.inj h).2)
          (the_book_repeats_no_word n))
        (fun x y hx hy he => by
          obtain ⟨wx, _, hex⟩ := mem_map_back (book n) hx
          obtain ⟨wy, _, hey⟩ := mem_map_back (book n) hy
          rw [← hex, ← hey] at he
          exact nomatch (List.cons.inj he).1)

theorem markfree_map (n : Nat) (f : List Bool → List Bool)
    (hpf : ∀ w1 w2, List.Mem w1 (book n) → List.Mem w2 (book n) → w1 ≠ w2 →
      ¬ ∃ t : List Bool, f w1 ++ t = f w2) :
    ∀ ws : List (List Bool), AllDiff ws →
      (∀ w, List.Mem w ws → List.Mem w (book n)) →
      MarkFree (ws.map f)
  | [], _, _ => .nil
  | w :: ws, .cons hne hd, hsub =>
      .cons (fun x hx => by
          obtain ⟨w', hw', he⟩ := mem_map_back ws hx
          subst he
          exact ⟨hpf w w' (hsub w (.head ws)) (hsub w' (.tail w hw'))
                   (hne w' hw'),
                 hpf w' w (hsub w' (.tail w hw')) (hsub w (.head ws))
                   (fun heq => hne w' hw' heq.symm)⟩)
        (markfree_map n f hpf ws hd (fun w' hw' => hsub w' (.tail w hw')))

theorem the_line_under_the_curve (L n ℓ : Nat) (hn : n ≤ L) :
    2 ^ (L - n) * ((n + 1) - ℓ) ≤ 2 ^ (L - ℓ) := by
  cases Nat.lt_or_ge n ℓ with
  | inl hlt =>
      rw [FInt.sub_eq_zero_of_le hlt]
      exact Nat.zero_le _
  | inr hge =>
      obtain ⟨d, hd⟩ := Nat.le.dest hge
      obtain ⟨e, he⟩ := Nat.le.dest hn
      rw [← he, ← hd, FInt.add_sub_cancel_left,
          show (ℓ + d) + 1 = ℓ + (d + 1) from rfl, FInt.add_sub_cancel_left,
          show (ℓ + d) + e = ℓ + (d + e) from (adding_associates ℓ d e).symm,
          FInt.add_sub_cancel_left,
          pow_splits d e, Nat.mul_comm ((2 : Nat) ^ d) (2 ^ e)]
      exact Nat.mul_le_mul_left (2 ^ e) (two_pow_clears_the_line d)

theorem the_marks_pay_the_depth (n : Nat) (f : List Bool → List Bool)
    (hpf : ∀ w1 w2, List.Mem w1 (book n) → List.Mem w2 (book n) → w1 ≠ w2 →
      ¬ ∃ t : List Bool, f w1 ++ t = f w2) :
    n * (book n).length ≤ (pool ((book n).map f)).length := by
  rw [the_book_has_two_to_the_n n, pool_length, Nat.mul_comm n ((2 : Nat) ^ n)]
  have hfree : MarkFree ((book n).map f) :=
    markfree_map n f hpf (book n) (the_book_repeats_no_word n) (fun _ h => h)
  have hlen : ∀ m, List.Mem m ((book n).map f) →
      m.length ≤ n + maxLen ((book n).map f) :=
    fun m hm => le_trans (le_maxLen _ m hm) (Nat.le_add_left _ n)
  have hpoint := natSumOver_mono ((book n).map f)
    (fun m _ => the_line_under_the_curve (n + maxLen ((book n).map f)) n
      m.length (Nat.le_add_right n _))
  rw [natSumOver_mul] at hpoint
  have hchain := le_trans hpoint
    (the_antichain_measure_is_bounded (n + maxLen ((book n).map f))
      ((book n).map f) hfree hlen)
  rw [FInt.add_sub_cancel_left, pow_splits n (maxLen ((book n).map f)),
      Nat.mul_comm ((2 : Nat) ^ n) (2 ^ maxLen ((book n).map f))] at hchain
  have hcap := Nat.le_of_mul_le_mul_left hchain
    (two_pow_pos (maxLen ((book n).map f)))
  have hsum := natSumOver_mono ((book n).map f)
    (fun m _ => sub_then_add_recovers (n + 1) m.length)
  rw [natSumOver_const, natSumOver_add, len_map,
      the_book_has_two_to_the_n n] at hsum
  have h2 := le_trans hsum (Nat.add_le_add_right hcap _)
  rw [show (2 : Nat) ^ n * (n + 1) = 2 ^ n * n + 2 ^ n from rfl,
      Nat.add_comm ((2 : Nat) ^ n)
        (natSumOver List.length ((book n).map f))] at h2
  exact cancel_add_right _ h2

/-- info: 'Foam.two_pow_clears_the_line' does not depend on any axioms -/
#guard_msgs in #print axioms two_pow_clears_the_line

/-- info: 'Foam.two_pow_pos' does not depend on any axioms -/
#guard_msgs in #print axioms two_pow_pos

/-- info: 'Foam.pow_splits' does not depend on any axioms -/
#guard_msgs in #print axioms pow_splits

/-- info: 'Foam.sub_then_add_recovers' does not depend on any axioms -/
#guard_msgs in #print axioms sub_then_add_recovers

/-- info: 'Foam.natSumOver_map' does not depend on any axioms -/
#guard_msgs in #print axioms natSumOver_map

/-- info: 'Foam.natSumOver_const' does not depend on any axioms -/
#guard_msgs in #print axioms natSumOver_const

/-- info: 'Foam.natSumOver_add' does not depend on any axioms -/
#guard_msgs in #print axioms natSumOver_add

/-- info: 'Foam.natSumOver_mono' does not depend on any axioms -/
#guard_msgs in #print axioms natSumOver_mono

/-- info: 'Foam.pool_length' does not depend on any axioms -/
#guard_msgs in #print axioms pool_length

/-- info: 'Foam.no_empty_of_hasEmpty_false' does not depend on any axioms -/
#guard_msgs in #print axioms no_empty_of_hasEmpty_false

/-- info: 'Foam.mem_of_hasEmpty_true' does not depend on any axioms -/
#guard_msgs in #print axioms mem_of_hasEmpty_true

/-- info: 'Foam.the_empty_mark_stands_alone' does not depend on any axioms -/
#guard_msgs in #print axioms the_empty_mark_stands_alone

/-- info: 'Foam.mem_tailsT' does not depend on any axioms -/
#guard_msgs in #print axioms mem_tailsT

/-- info: 'Foam.mem_tailsF' does not depend on any axioms -/
#guard_msgs in #print axioms mem_tailsF

/-- info: 'Foam.ispre_cons' does not depend on any axioms -/
#guard_msgs in #print axioms ispre_cons

/-- info: 'Foam.tailsT_free' does not depend on any axioms -/
#guard_msgs in #print axioms tailsT_free

/-- info: 'Foam.tailsF_free' does not depend on any axioms -/
#guard_msgs in #print axioms tailsF_free

/-- info: 'Foam.tailsT_len' does not depend on any axioms -/
#guard_msgs in #print axioms tailsT_len

/-- info: 'Foam.tailsF_len' does not depend on any axioms -/
#guard_msgs in #print axioms tailsF_len

/-- info: 'Foam.split_sum' does not depend on any axioms -/
#guard_msgs in #print axioms split_sum

/-- info: 'Foam.the_antichain_measure_is_bounded' does not depend on any axioms -/
#guard_msgs in #print axioms the_antichain_measure_is_bounded

/-- info: 'Foam.le_maxLen' does not depend on any axioms -/
#guard_msgs in #print axioms le_maxLen

/-- info: 'Foam.mem_append_split' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_split

/-- info: 'Foam.mem_map_back' does not depend on any axioms -/
#guard_msgs in #print axioms mem_map_back

/-- info: 'Foam.alldiff_map' does not depend on any axioms -/
#guard_msgs in #print axioms alldiff_map

/-- info: 'Foam.alldiff_append' does not depend on any axioms -/
#guard_msgs in #print axioms alldiff_append

/-- info: 'Foam.the_book_repeats_no_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_book_repeats_no_word

/-- info: 'Foam.markfree_map' does not depend on any axioms -/
#guard_msgs in #print axioms markfree_map

/-- info: 'Foam.the_line_under_the_curve' does not depend on any axioms -/
#guard_msgs in #print axioms the_line_under_the_curve

/-- info: 'Foam.the_marks_pay_the_depth' does not depend on any axioms -/
#guard_msgs in #print axioms the_marks_pay_the_depth

end Foam
