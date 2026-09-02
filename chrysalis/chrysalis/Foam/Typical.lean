import Foam.Census

namespace Foam

def shelfSum (n : Nat) : Nat → Nat
  | 0 => classCount n 0
  | k + 1 => shelfSum n k + classCount n (k + 1)

theorem shelfSum_stacks (n : Nat) :
    ∀ m : Nat, shelfSum (n + 1) (m + 1) = shelfSum n m + shelfSum n (m + 1)
  | 0 => by
      show classCount (n + 1) 0 + classCount (n + 1) (0 + 1)
          = classCount n 0 + (classCount n 0 + classCount n (0 + 1))
      rw [the_census_stacks n 0, the_census_starts_at_one (n + 1),
          ← the_census_starts_at_one n]
  | m + 1 => by
      show shelfSum (n + 1) (m + 1) + classCount (n + 1) (m + 2)
          = shelfSum n (m + 1)
            + (shelfSum n (m + 1) + classCount n (m + 2))
      rw [shelfSum_stacks n m, the_census_stacks n (m + 1), nat_swap_mid]
      rfl

theorem the_census_sums_whole : ∀ n : Nat, shelfSum n n = 2 ^ n
  | 0 => rfl
  | n + 1 => by
      rw [shelfSum_stacks n n,
          show shelfSum n (n + 1) = shelfSum n n + classCount n (n + 1)
            from rfl,
          the_census_ends n (n + 1) (Nat.le_refl (n + 1)), Nat.add_zero,
          the_census_sums_whole n,
          show (2 : Nat) ^ (n + 1) = 2 ^ n * 2 from rfl, nat_mul_two]

theorem the_climb_to_the_middle (n : Nat) :
    ∀ d k : Nat, k + d ≤ n →
      classCount (2 * n) k ≤ classCount (2 * n) (k + d)
  | 0, _, _ => Nat.le_refl _
  | d + 1, k, h => by
      have hk1 : k + 1 ≤ n :=
        le_trans (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le d)) k) h
      have hrise : 2 * k + 1 ≤ 2 * n := by
        have h2 : 2 * (k + 1) ≤ 2 * n := Nat.mul_le_mul_left 2 hk1
        rw [Nat.left_distrib, Nat.mul_one] at h2
        exact le_of_succ_le h2
      have hshift : (k + 1) + d ≤ n := by
        rw [succ_adds k d]
        exact h
      exact le_trans (the_census_rises_to_the_middle (2 * n) k hrise)
        ((succ_adds k d : (k + 1) + d = k + (d + 1)) ▸
          the_climb_to_the_middle n d (k + 1) hshift)

theorem the_middle_holds_the_most (n : Nat) :
    ∀ k : Nat, k ≤ 2 * n → classCount (2 * n) k ≤ classCount (2 * n) n := by
  have below : ∀ j : Nat, j ≤ n →
      classCount (2 * n) j ≤ classCount (2 * n) n := by
    intro j hj
    obtain ⟨d, hd⟩ := Nat.le.dest hj
    have hle : j + d ≤ n := by rw [hd]; exact Nat.le_refl n
    have hclimb := the_climb_to_the_middle n d j hle
    rw [hd] at hclimb
    exact hclimb
  intro k hk
  cases Nat.lt_or_ge k n with
  | inl hlt => exact below k (Nat.le_of_lt hlt)
  | inr hge =>
      obtain ⟨m, hm⟩ := Nat.le.dest hk
      have hmn : m ≤ n := by
        apply cancel_add_left k
        rw [hm, show 2 * n = n + n from by
              rw [Nat.mul_comm 2 n, nat_mul_two]]
        exact Nat.add_le_add_right hge n
      rw [the_census_is_symmetric (2 * n) k hk,
          show 2 * n - k = m from by rw [← hm, FInt.add_sub_cancel_left]]
      exact below m hmn

theorem shelf_le_share (n : Nat) :
    ∀ m : Nat, m ≤ 2 * n →
      shelfSum (2 * n) m ≤ (m + 1) * classCount (2 * n) n
  | 0, _ => by
      rw [succ_mul' 0 (classCount (2 * n) n), Nat.zero_mul, nothing_added]
      exact the_middle_holds_the_most n 0 (Nat.zero_le _)
  | m + 1, h => by
      show shelfSum (2 * n) m + classCount (2 * n) (m + 1)
          ≤ ((m + 1) + 1) * classCount (2 * n) n
      rw [succ_mul' (m + 1)]
      exact Nat.add_le_add (shelf_le_share n m (le_of_succ_le h))
        (the_middle_holds_the_most n (m + 1) h)

theorem the_middle_shelf_holds_its_share (n : Nat) :
    2 ^ (2 * n) ≤ (2 * n + 1) * classCount (2 * n) n := by
  rw [← the_census_sums_whole (2 * n)]
  exact shelf_le_share n (2 * n) (Nat.le_refl _)

theorem append_nil' : ∀ l : List Bool, l ++ [] = l
  | [] => rfl
  | a :: l => congrArg (a :: ·) (append_nil' l)

theorem eq_of_beq' : ∀ a b : Nat, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | a + 1, b + 1, h => congrArg Nat.succ (eq_of_beq' a b h)

theorem book_words_have_length :
    ∀ (L : Nat) (w : List Bool), w ∈ book L → w.length = L
  | 0, _, hw => by
      cases hw with
      | head => rfl
      | tail _ h => exact nomatch h
  | L + 1, w, hw => by
      cases mem_append_split _ _ hw with
      | inl h =>
          obtain ⟨w', hw', he⟩ := mem_map_back (book L) h
          rw [← he]
          show w'.length + 1 = L + 1
          rw [book_words_have_length L w' hw']
      | inr h =>
          obtain ⟨w', hw', he⟩ := mem_map_back (book L) h
          rw [← he]
          show w'.length + 1 = L + 1
          rw [book_words_have_length L w' hw']

theorem markfree_of_distinct_equal_length {L : Nat} :
    ∀ ms : List (List Bool), AllDiff ms →
      (∀ m, m ∈ ms → m.length = L) → MarkFree ms
  | [], _, _ => .nil
  | m :: ms, .cons hne hd, hlen =>
      have key : ∀ (a b : List Bool), a.length = L → b.length = L →
          a ≠ b → ¬ IsPre a b := fun a b ha hb hab ⟨t, ht⟩ => by
        have h1 : (a ++ t).length = b.length := congrArg List.length ht
        rw [len_append, ha, hb] at h1
        have ht0 : t.length = 0 := by
          rw [show t.length = (L + t.length) - L from
                (FInt.add_sub_cancel_left L t.length).symm,
              h1, Nat.sub_self]
        cases t with
        | nil => exact hab (by rw [← ht, append_nil'])
        | cons x t' => exact nomatch ht0
      .cons (fun m' hm' =>
          ⟨key m m' (hlen m (.head ms)) (hlen m' (.tail m hm')) (hne m' hm'),
           key m' m (hlen m' (.tail m hm')) (hlen m (.head ms))
             (fun he => hne m' hm' he.symm)⟩)
        (markfree_of_distinct_equal_length ms hd
          (fun x hx => hlen x (.tail m hx)))

theorem mem_of_mem_filter {A : Type} {q : A → Bool} {x : A} :
    ∀ l : List A, x ∈ List.filter q l → x ∈ l
  | [], h => nomatch h
  | a :: l, h => by
      cases hq : q a with
      | true =>
          rw [List.filter_cons_of_pos (l := l) hq] at h
          cases h with
          | head => exact .head l
          | tail _ h' => exact .tail a (mem_of_mem_filter l h')
      | false =>
          rw [List.filter_cons_of_neg (l := l) (ne_true_of_eq_false hq)] at h
          exact .tail a (mem_of_mem_filter l h)

theorem filter_holds {A : Type} {q : A → Bool} {x : A} :
    ∀ l : List A, x ∈ List.filter q l → q x = true
  | [], h => nomatch h
  | a :: l, h => by
      cases hq : q a with
      | true =>
          rw [List.filter_cons_of_pos (l := l) hq] at h
          cases h with
          | head => exact hq
          | tail _ h' => exact filter_holds l h'
      | false =>
          rw [List.filter_cons_of_neg (l := l) (ne_true_of_eq_false hq)] at h
          exact filter_holds l h

theorem alldiff_filter {q : List Bool → Bool} :
    ∀ ws : List (List Bool), AllDiff ws → AllDiff (List.filter q ws)
  | [], _ => .nil
  | w :: ws, .cons hne hd => by
      cases hq : q w with
      | true =>
          rw [List.filter_cons_of_pos (l := ws) hq]
          exact .cons (fun w' hw' => hne w' (mem_of_mem_filter ws hw'))
            (alldiff_filter ws hd)
      | false =>
          rw [List.filter_cons_of_neg (l := ws) (ne_true_of_eq_false hq)]
          exact alldiff_filter ws hd

theorem alldiff_map_on {g : List Bool → List Bool} :
    ∀ ws : List (List Bool),
      (∀ a b, a ∈ ws → b ∈ ws → g a = g b → a = b) → AllDiff ws →
      AllDiff (ws.map g)
  | [], _, _ => .nil
  | w :: ws, hinj, .cons hne hd =>
      .cons (fun x hx hgx => by
          obtain ⟨w', hw', he⟩ := mem_map_back ws hx
          exact hne w' hw'
            (hinj w w' (.head ws) (.tail w hw') (hgx.trans he.symm)))
        (alldiff_map_on ws
          (fun a b ha hb => hinj a b (.tail w ha) (.tail w hb)) hd)

theorem a_class_marked_into_a_book_is_counted (L : Nat)
    (ms : List (List Bool)) (hd : AllDiff ms)
    (hin : ∀ m, m ∈ ms → m ∈ book L) :
    ms.length ≤ 2 ^ L := by
  have hfree : MarkFree ms :=
    markfree_of_distinct_equal_length ms hd
      (fun m hm => book_words_have_length L m (hin m hm))
  have hk := the_antichain_measure_is_bounded L ms hfree
    (fun m hm => by
      rw [book_words_have_length L m (hin m hm)]
      exact Nat.le_refl L)
  have h1 : natSumOver (fun _ => (1 : Nat)) ms
      ≤ natSumOver (fun m => 2 ^ (L - m.length)) ms :=
    natSumOver_mono ms (fun m hm => by
      rw [book_words_have_length L m (hin m hm), Nat.sub_self]
      exact Nat.le_refl 1)
  rw [natSumOver_const 1 ms, Nat.mul_one] at h1
  exact le_trans h1 hk

theorem marking_the_middle_pays_the_breadth (n L : Nat)
    (f : List Bool → List Bool)
    (hmap : ∀ w, w ∈ book (2 * n) → freq w true = n → f w ∈ book L)
    (hinj : ∀ w1 w2, w1 ∈ book (2 * n) → w2 ∈ book (2 * n) →
      freq w1 true = n → freq w2 true = n → w1 ≠ w2 → f w1 ≠ f w2) :
    2 ^ (2 * n) ≤ (2 * n + 1) * 2 ^ L := by
  have hmem : ∀ w, w ∈ List.filter
      (fun w => Nat.beq (freq w true) n) (book (2 * n)) →
      w ∈ book (2 * n) ∧ freq w true = n :=
    fun w hw => ⟨mem_of_mem_filter _ hw,
      eq_of_beq' (freq w true) n
        (filter_holds (q := fun w => Nat.beq (freq w true) n) _ hw)⟩
  have hd2 : AllDiff ((List.filter
      (fun w => Nat.beq (freq w true) n) (book (2 * n))).map f) :=
    alldiff_map_on _
      (fun a b ha hb hg =>
        if h : a = b then h else
          absurd hg (hinj a b (hmem a ha).1 (hmem b hb).1
            (hmem a ha).2 (hmem b hb).2 h))
      (alldiff_filter _ (the_book_repeats_no_word (2 * n)))
  have hbound := a_class_marked_into_a_book_is_counted L
    ((List.filter (fun w => Nat.beq (freq w true) n) (book (2 * n))).map f)
    hd2
    (fun m hm => by
      obtain ⟨w', hw', he⟩ := mem_map_back _ hm
      rw [← he]
      exact hmap w' (hmem w' hw').1 (hmem w' hw').2)
  rw [len_map] at hbound
  exact le_trans (the_middle_shelf_holds_its_share n)
    (Nat.mul_le_mul_left (2 * n + 1) hbound)

theorem marking_the_band_pays_the_breadth (b c : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ (L : Nat) (f : List Bool → List Bool),
        (∀ w, w ∈ book n → nearBalance b n w = true → f w ∈ book L) →
        (∀ w1 w2, w1 ∈ book n → w2 ∈ book n →
          nearBalance b n w1 = true → nearBalance b n w2 = true →
          w1 ≠ w2 → f w1 ≠ f w2) →
        c * 2 ^ n ≤ (c + 1) * 2 ^ L := by
  obtain ⟨N, hN⟩ := the_deviants_are_outnumbered b c
  refine ⟨N, fun n hn L f hmap hinj => ?_⟩
  have hmem : ∀ w, w ∈ List.filter (fun w => nearBalance b n w) (book n) →
      w ∈ book n ∧ nearBalance b n w = true :=
    fun w hw => ⟨mem_of_mem_filter _ hw,
      filter_holds (q := fun w => nearBalance b n w) _ hw⟩
  have hd2 : AllDiff ((List.filter
      (fun w => nearBalance b n w) (book n)).map f) :=
    alldiff_map_on _
      (fun u v hu hv hg =>
        if h : u = v then h else
          absurd hg (hinj u v (hmem u hu).1 (hmem v hv).1
            (hmem u hu).2 (hmem v hv).2 h))
      (alldiff_filter _ (the_book_repeats_no_word n))
  have hbound := a_class_marked_into_a_book_is_counted L
    ((List.filter (fun w => nearBalance b n w) (book n)).map f)
    hd2
    (fun m hm => by
      obtain ⟨w', hw', he⟩ := mem_map_back _ hm
      rw [← he]
      exact hmap w' (hmem w' hw').1 (hmem w' hw').2)
  rw [len_map] at hbound
  have hout := hN n hn
  have hpart := filter_partition (fun w => nearBalance b n w) (book n)
  rw [the_book_has_two_to_the_n n] at hpart
  rw [← hpart, Nat.left_distrib]
  exact le_trans
    (Nat.add_le_add_left hout
      (c * (List.filter (fun w => nearBalance b n w) (book n)).length))
    (le_trans
      (Nat.le_of_eq
        (succ_mul' c
          (List.filter (fun w => nearBalance b n w) (book n)).length).symm)
      (Nat.mul_le_mul_left (c + 1) hbound))

/-- info: 'Foam.shelfSum_stacks' does not depend on any axioms -/
#guard_msgs in #print axioms shelfSum_stacks

/-- info: 'Foam.the_census_sums_whole' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_sums_whole

/-- info: 'Foam.the_climb_to_the_middle' does not depend on any axioms -/
#guard_msgs in #print axioms the_climb_to_the_middle

/-- info: 'Foam.the_middle_holds_the_most' does not depend on any axioms -/
#guard_msgs in #print axioms the_middle_holds_the_most

/-- info: 'Foam.shelf_le_share' does not depend on any axioms -/
#guard_msgs in #print axioms shelf_le_share

/-- info: 'Foam.the_middle_shelf_holds_its_share' does not depend on any axioms -/
#guard_msgs in #print axioms the_middle_shelf_holds_its_share

/-- info: 'Foam.append_nil'' does not depend on any axioms -/
#guard_msgs in #print axioms append_nil'

/-- info: 'Foam.eq_of_beq'' does not depend on any axioms -/
#guard_msgs in #print axioms eq_of_beq'

/-- info: 'Foam.book_words_have_length' does not depend on any axioms -/
#guard_msgs in #print axioms book_words_have_length

/-- info: 'Foam.markfree_of_distinct_equal_length' does not depend on any axioms -/
#guard_msgs in #print axioms markfree_of_distinct_equal_length

/-- info: 'Foam.mem_of_mem_filter' does not depend on any axioms -/
#guard_msgs in #print axioms mem_of_mem_filter

/-- info: 'Foam.filter_holds' does not depend on any axioms -/
#guard_msgs in #print axioms filter_holds

/-- info: 'Foam.alldiff_filter' does not depend on any axioms -/
#guard_msgs in #print axioms alldiff_filter

/-- info: 'Foam.alldiff_map_on' does not depend on any axioms -/
#guard_msgs in #print axioms alldiff_map_on

/-- info: 'Foam.a_class_marked_into_a_book_is_counted' does not depend on any axioms -/
#guard_msgs in #print axioms a_class_marked_into_a_book_is_counted

/-- info: 'Foam.marking_the_middle_pays_the_breadth' does not depend on any axioms -/
#guard_msgs in #print axioms marking_the_middle_pays_the_breadth

/-- info: 'Foam.marking_the_band_pays_the_breadth' does not depend on any axioms -/
#guard_msgs in #print axioms marking_the_band_pays_the_breadth

end Foam
