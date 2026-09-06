namespace Room

universe u v w u' v' w' u''

def carries {S : Type u} {T : Type u'} {P : Type v} {A : Type w}
    (f : S → P → A) (g : T → P → A) (h : S → T) : Prop :=
  ∀ s p, g (h s) p = f s p

def oddNat : Nat → Bool
  | 0 => false
  | n + 1 => !(oddNat n)

def enrolled {A : Type u} (beq : A → A → Bool) : List A → A → Bool
  | [], _ => false
  | y :: r, x => beq y x || enrolled beq r x

def backed {A : Type u} (beq : A → A → Bool) (room : List A) : List A → Bool
  | [] => true
  | n :: needs => enrolled beq room n && backed beq room needs

def welcome {A : Type u} (beq : A → A → Bool)
    (st : List A × List (A × List A)) (arr : A × List A) :
    List A × List (A × List A) :=
  cond (backed beq st.1 arr.2) (arr.1 :: st.1, st.2) (st.1, arr :: st.2)

def joinMap {A : Type u} {B : Type v} (f : A → List B) : List A → List B
  | [] => []
  | a :: as => f a ++ joinMap f as

def inserts {A : Type u} (x : A) : List A → List (List A)
  | [] => [[x]]
  | y :: l => (x :: y :: l) :: (inserts x l).map (y :: ·)

def perms {A : Type u} : List A → List (List A)
  | [] => [[]]
  | x :: l => joinMap (inserts x) (perms l)

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => fact n * (n + 1)

inductive Apart {A : Type u} : List A → Prop
  | nil : Apart []
  | cons {a : A} {l : List A} :
      (∀ b, b ∈ l → a ≠ b) → Apart l → Apart (a :: l)

def sameRatio (a b c d : Nat) : Prop := a * d = c * b

def trade {A : Type u} (beq : A → A → Bool) (a b : A) (x : A) : A :=
  cond (beq x a) b (cond (beq x b) a x)

def firstOf {A : Type u} (beq : A → A → Bool) (a b : A) : List A → Bool
  | [] => false
  | x :: p => cond (beq x a) true (cond (beq x b) false (firstOf beq a b p))

def roomCap : Nat → Nat
  | 0 => 1
  | d + 1 => roomCap d + roomCap d

def words : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (words n).map (true :: ·) ++ (words n).map (false :: ·)

def again {α : Sort u} (Φ : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => Φ (again Φ n a)

def inc : List Bool → List Bool
  | [] => []
  | false :: bs => true :: bs
  | true :: bs => false :: inc bs

def dec : List Bool → List Bool
  | [] => []
  | true :: bs => false :: bs
  | false :: bs => true :: dec bs

def zeros : Nat → List Bool
  | 0 => []
  | n + 1 => false :: zeros n

def val : List Bool → Nat
  | [] => 0
  | b :: bs => cond b 1 0 + (val bs + val bs)

def clockAt (n t : Nat) : List Bool :=
  again inc t (zeros n)

def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1

def collatzStep (n : Nat) : Nat :=
  cond (oddNat n) (3 * n + 1) (halve n)

def intake {A : Type u} (beq : A → A → Bool) :
    List A × List (A × List A) → List (A × List A) → List A × List (A × List A)
  | st, [] => st
  | st, arr :: w => intake beq (welcome beq st arr) w

def lacking {A : Type u} (beq : A → A → Bool) (room : List A) : List A → Nat
  | [] => 0
  | n :: needs =>
      cond (enrolled beq room n) (lacking beq room needs) (lacking beq room needs + 1)

def everyone (beq : Nat → Nat → Bool) (members confirmed : List Nat) : Bool :=
  backed beq confirmed members

theorem the_carriers_compose {S : Type u} {T : Type u'} {U : Type u''} {P : Type v} {A : Type w}
    (f : S → P → A) (g : T → P → A) (k : U → P → A) (h : S → T) (h' : T → U)
    (c1 : carries f g h) (c2 : carries g k h') :
    carries f k (fun s => h' (h s)) := sorry

theorem the_carrier_merges_only_the_alike {S : Type u} {T : Type u'} {P : Type v} {A : Type w}
    (f : S → P → A) (g : T → P → A) (h : S → T) (c : carries f g h)
    {s s' : S} (he : h s = h s') : ∀ p, f s p = f s' p :=
  fun p => ((c s p).symm.trans (congrArg (fun x => g x p) he)).trans (c s' p)

theorem a_retraction_merges_nothing {S : Type u} {T : Type u'} (h : S → T) (r : T → S)
    (hr : ∀ x, r (h x) = x) {s s' : S} (hm : h s = h s') : s = s' :=
  (hr s).symm.trans ((congrArg r hm).trans (hr s'))

theorem the_terminus_takes_every_carrier {S : Type u} {P : Type v} {A : Type w}
    (f : S → P → A) (h : S → (P → A)) (c : carries f (fun g p => g p) h) :
    ∀ s p, h s p = f s p := sorry

theorem the_first_mark_reads {A : Type w} {a b : A} {l m : List A}
    (h : a :: l = b :: m) : a = b :=
  congrArg (fun x => x.headD a) h

theorem the_backed_are_seated {A : Type u} (beq : A → A → Bool)
    (st : List A × List (A × List A)) (arr : A × List A)
    (hb : backed beq st.1 arr.2 = true) :
    welcome beq st arr = (arr.1 :: st.1, st.2) :=
  by (intros; (try dsimp only [backed, welcome] at *); intros; (rw [hb]; rfl))

theorem the_unbacked_wait {A : Type u} (beq : A → A → Bool)
    (st : List A × List (A × List A)) (arr : A × List A)
    (hb : backed beq st.1 arr.2 = false) :
    welcome beq st arr = (st.1, arr :: st.2) := sorry

theorem mem_append_split {A : Type u} {q : A} :
    ∀ (l : List A) {m : List A}, q ∈ l ++ m → q ∈ l ∨ q ∈ m
  | [], _, h => Or.inr h
  | a :: l, _, h => by
      cases h with
      | head => exact Or.inl (List.Mem.head l)
      | tail _ h' =>
          cases mem_append_split l h' with
          | inl hl => exact Or.inl (List.Mem.tail a hl)
          | inr hm => exact Or.inr hm

theorem mem_map_back {A : Type u} {B : Type v} {f : A → B} {q : B} :
    ∀ l : List A, q ∈ l.map f → ∃ r, r ∈ l ∧ f r = q
  | [], h => nomatch h
  | a :: l, h => by
      cases h with
      | head => exact ⟨a, List.Mem.head l, rfl⟩
      | tail _ h' =>
          obtain ⟨r, hr, he⟩ := mem_map_back l h'
          exact ⟨r, List.Mem.tail a hr, he⟩

theorem ble_trans : ∀ (a b c : Nat),
    Nat.ble a b = true → Nat.ble b c = true → Nat.ble a c = true
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, _, h1, _ => nomatch h1
  | _ + 1, _ + 1, 0, _, h2 => nomatch h2
  | a + 1, b + 1, c + 1, h1, h2 => ble_trans a b c h1 h2

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

theorem eq_of_beq : ∀ a b : Nat, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | a + 1, b + 1, h => congrArg (· + 1) (eq_of_beq a b h)

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

theorem mem_splits {A : Type u} {x : A} :
    ∀ {l : List A}, x ∈ l → ∃ v₁ v₂ : List A, l = v₁ ++ x :: v₂
  | _ :: t, List.Mem.head _ => ⟨[], t, rfl⟩
  | a :: _, List.Mem.tail _ h =>
      match mem_splits h with
      | ⟨v₁, v₂, he⟩ => ⟨a :: v₁, v₂, congrArg (a :: ·) he⟩

theorem perm_symm {A : Type u} {xs ys : List A} (h : xs.Perm ys) :
    ys.Perm xs := by
  induction h with
  | nil => exact .nil
  | cons x _ ih => exact .cons x ih
  | swap x y l => exact .swap y x l
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁

theorem perm_length {A : Type u} {xs ys : List A} (h : xs.Perm ys) :
    xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg (· + 1) ih
  | swap => rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem beq_no {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y) {x y : A} (hxy : x ≠ y) :
    beq x y = false := by
  cases h : beq x y with
  | false => rfl
  | true => exact absurd (hE x y h) hxy

theorem ne_of_beq_no {A : Type u} {beq : A → A → Bool}
    (hR : ∀ x : A, beq x x = true) {x y : A} (h : beq x y = false) :
    x ≠ y :=
  fun he =>
    nomatch (((congrArg (fun z => beq z y) he).symm.trans h).symm.trans
      (hR y))

theorem map_congr_mem {A : Type u} {B : Type v} (f g : A → B) :
    ∀ w : List A, (∀ x, x ∈ w → f x = g x) → w.map f = w.map g
  | [], _ => rfl
  | x :: w, h => by
      show f x :: w.map f = g x :: w.map g
      rw [h x (List.Mem.head w),
          map_congr_mem f g w (fun y hy => h y (List.Mem.tail x hy))]

theorem perm_append_left {A : Type u} {v w : List A} (h : v.Perm w) :
    ∀ u : List A, (u ++ v).Perm (u ++ w)
  | [] => h
  | x :: u => List.Perm.cons x (perm_append_left h u)

theorem perm_map {A : Type u} {B : Type v} (f : A → B) {xs ys : List A}
    (h : xs.Perm ys) : (xs.map f).Perm (ys.map f) := by
  induction h with
  | nil => exact .nil
  | cons x _ ih => exact .cons (f x) ih
  | swap x y l => exact .swap (f x) (f y) (l.map f)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem apart_drop {A : Type u} :
    ∀ (u w : List A), Apart (u ++ w) → Apart w
  | [], _, h => h
  | _ :: u, w, h => by
      cases h with
      | cons _ hrest => exact apart_drop u w hrest

theorem mem_insert_middle {A : Type u} {y : A} :
    ∀ (v1 : List A) {x : A} {v2 : List A}, y ∈ v1 ++ v2 → y ∈ v1 ++ x :: v2
  | [], x, _, h => List.Mem.tail x h
  | z :: v1, _, _, h => by
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail z (mem_insert_middle v1 h')

theorem filter_congr_mem {A : Type u} (q r : A → Bool) :
    ∀ L : List A, (∀ x, x ∈ L → q x = r x) → L.filter q = L.filter r
  | [], _ => rfl
  | x :: L, h => by
      have hx := h x (List.Mem.head L)
      have hrest := filter_congr_mem q r L
        (fun y hy => h y (List.Mem.tail x hy))
      cases hq : q x with
      | true =>
          rw [List.filter_cons_of_pos hq,
              List.filter_cons_of_pos (hx.symm.trans hq), hrest]
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq),
              List.filter_cons_of_neg
                (ne_true_of_eq_false (hx.symm.trans hq)),
              hrest]

theorem filter_map_commutes {A : Type u} {B : Type v} (f : A → B) (q : B → Bool) :
    ∀ L : List A,
      (L.map f).filter q = (L.filter (fun x => q (f x))).map f
  | [] => rfl
  | x :: L => by
      show (f x :: L.map f).filter q
          = ((x :: L).filter (fun y => q (f y))).map f
      cases hq : q (f x) with
      | true =>
          rw [List.filter_cons_of_pos hq,
              List.filter_cons_of_pos (p := fun y => q (f y)) hq]
          show f x :: (L.map f).filter q
              = f x :: (L.filter (fun y => q (f y))).map f
          rw [filter_map_commutes f q L]
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq),
              List.filter_cons_of_neg (p := fun y => q (f y))
                (ne_true_of_eq_false hq)]
          exact filter_map_commutes f q L

theorem perm_filter {A : Type u} (q : A → Bool) {xs ys : List A}
    (h : xs.Perm ys) : (xs.filter q).Perm (ys.filter q) := by
  induction h with
  | nil => exact .nil
  | cons x _ ih =>
      cases hq : q x with
      | true =>
          rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos hq]
          exact .cons x ih
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq),
              List.filter_cons_of_neg (ne_true_of_eq_false hq)]
          exact ih
  | swap x y l =>
      cases hqx : q x with
      | true =>
          cases hqy : q y with
          | true =>
              rw [List.filter_cons_of_pos hqy,
                  List.filter_cons_of_pos hqx,
                  List.filter_cons_of_pos hqx,
                  List.filter_cons_of_pos hqy]
              exact .swap x y (l.filter q)
          | false =>
              rw [List.filter_cons_of_neg (ne_true_of_eq_false hqy),
                  List.filter_cons_of_pos hqx,
                  List.filter_cons_of_pos hqx,
                  List.filter_cons_of_neg (ne_true_of_eq_false hqy)]
      | false =>
          cases hqy : q y with
          | true =>
              rw [List.filter_cons_of_pos hqy,
                  List.filter_cons_of_neg (ne_true_of_eq_false hqx),
                  List.filter_cons_of_neg (ne_true_of_eq_false hqx),
                  List.filter_cons_of_pos hqy]
          | false =>
              rw [List.filter_cons_of_neg (ne_true_of_eq_false hqy),
                  List.filter_cons_of_neg (ne_true_of_eq_false hqx),
                  List.filter_cons_of_neg (ne_true_of_eq_false hqx),
                  List.filter_cons_of_neg (ne_true_of_eq_false hqy)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem the_tick_unwinds : ∀ s : List Bool, dec (inc s) = s
  | [] => rfl
  | false :: _ => rfl
  | true :: bs => congrArg (true :: ·) (the_tick_unwinds bs)

theorem the_unwind_ticks : ∀ s : List Bool, inc (dec s) = s
  | [] => rfl
  | true :: _ => rfl
  | false :: bs => congrArg (false :: ·) (the_unwind_ticks bs)

theorem the_step_merges_the_riders :
    collatzStep 1 = collatzStep 8 ∧ (1 : Nat) ≠ 8 :=
  by decide

theorem no_inverse_unsteps_the_collatz :
    ¬ ∃ g : Nat → Nat, ∀ n, g (collatzStep n) = n :=
  fun ⟨_, hg⟩ => nomatch (Nat.succ.inj ((hg 1).symm.trans (hg 8)))

theorem and_reads : ∀ a b : Bool, (a && b) = true → a = true ∧ b = true := sorry

theorem the_held_name_their_darkness {A : Type u} (beq : A → A → Bool) (room : List A) :
    ∀ needs : List A, backed beq room needs = false →
      ∃ n, n ∈ needs ∧ enrolled beq room n = false := by
  intro needs
  induction needs with
  | nil =>
      intro h
      have h' : (true : Bool) = false := h
      exact nomatch h'
  | cons n' needs ih =>
      intro h
      cases he : enrolled beq room n' with
      | false => exact ⟨n', .head _, he⟩
      | true =>
          have hh : (enrolled beq room n' && backed beq room needs) = false := h
          rw [he] at hh
          obtain ⟨n, hn, hf⟩ := ih hh
          exact ⟨n, .tail _ hn, hf⟩

theorem the_weight_is_zero_at_the_door {A : Type u} (beq : A → A → Bool) (room : List A) :
    ∀ needs : List A, lacking beq room needs = 0 ↔ backed beq room needs = true := by
  intro needs
  induction needs with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons n' needs ih =>
      cases he : enrolled beq room n' with
      | true =>
          constructor
          · intro h0
            have hh : cond (enrolled beq room n')
                (lacking beq room needs) (lacking beq room needs + 1) = 0 := h0
            rw [he] at hh
            have hb := ih.mp hh
            show (enrolled beq room n' && backed beq room needs) = true
            rw [he, hb]
            exact rfl
          · intro hb
            have hh : (enrolled beq room n' && backed beq room needs) = true := hb
            rw [he] at hh
            show cond (enrolled beq room n')
                (lacking beq room needs) (lacking beq room needs + 1) = 0
            rw [he]
            exact ih.mpr hh
      | false =>
          constructor
          · intro h0
            have hh : cond (enrolled beq room n')
                (lacking beq room needs) (lacking beq room needs + 1) = 0 := h0
            rw [he] at hh
            exact nomatch hh
          · intro hb
            have hh : (enrolled beq room n' && backed beq room needs) = true := hb
            rw [he] at hh
            exact nomatch hh

theorem bool_three_collide : ∀ x y z : Bool, x = y ∨ y = z ∨ x = z := sorry

theorem and_congr_first {a b c : Prop} (h : a ↔ b) : (a ∧ c) ↔ (b ∧ c) :=
  ⟨fun x => ⟨h.mp x.1, x.2⟩, fun x => ⟨h.mpr x.1, x.2⟩⟩

theorem and_congr_second {a b c : Prop} (h : b ↔ c) : (a ∧ b) ↔ (a ∧ c) :=
  ⟨fun x => ⟨x.1, h.mp x.2⟩, fun x => ⟨x.1, h.mpr x.2⟩⟩

theorem and_regroups {a b c : Prop} : ((a ∧ b) ∧ c) ↔ (a ∧ (b ∧ c)) :=
  ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩⟩

theorem the_still_map_carries {S : Type u} {P : Type v} {A : Type w} (f : S → P → A) :
    carries f f (fun s => s) :=
  fun _ _ => rfl

theorem zero_add : ∀ n : Nat, 0 + n = n :=
  by
    (intro x; induction x;
      all_goals
        (first
          | (intros; rfl)
          | (rename_i ih; intros; exact congrArg _ ih)))

theorem add_regroups : ∀ a b c : Nat, (a + b) + c = a + (b + c) :=
  by
    (intro _ _ z; induction z;
      all_goals
        (first
          | (intros; rfl)
          | (rename_i ih; intros; exact congrArg _ ih)))

theorem click_slides : ∀ a b : Nat, (a + b) + 1 = (a + 1) + b :=
  by
    (intro _ y; induction y;
      all_goals
        (first
          | (intros; rfl)
          | (rename_i ih; intros; exact congrArg _ ih)))

theorem the_append_rests {A : Type u} : ∀ l : List A, l ++ [] = l := sorry

theorem the_appends_regroup {A : Type u} : ∀ l m t : List A, (l ++ m) ++ t = l ++ (m ++ t) :=
  by
    (intro x; induction x;
      all_goals
        (first
          | (intros; rfl)
          | (rename_i ih; intros; exact congrArg _ (ih _ _))))

theorem map_crosses_append {A : Type u} {B : Type v} (f : A → B) :
    ∀ l m : List A, (l ++ m).map f = l.map f ++ m.map f :=
  by
    (intro x; induction x;
      all_goals
        (first
          | (intros; rfl)
          | (rename_i ih; intros; exact congrArg _ (ih _))))

theorem the_unencumbered_are_welcome {A : Type u} (beq : A → A → Bool) (room : List A) :
    backed beq room [] = true := sorry

theorem true_or_reads (b : Bool) : (true || b) = true := sorry

theorem or_swallows : ∀ b : Bool, (b || true) = true := sorry

theorem len_map {A : Type u} {B : Type v} (f : A → B) :
    ∀ l : List A, (l.map f).length = l.length := sorry

theorem ble_refl : ∀ n : Nat, Nat.ble n n = true :=
  by
    (intro x; induction x;
      all_goals
        (first
          | (intros; rfl)
          | (intros; assumption)))

theorem ble_le_succ : ∀ n : Nat, Nat.ble n (n + 1) = true := sorry

theorem beq_self : ∀ n : Nat, Nat.beq n n = true := sorry

theorem perm_refl {A : Type u} : ∀ l : List A, l.Perm l := sorry

theorem not_not : ∀ b : Bool, (!(!b)) = b := sorry

theorem one_scales : ∀ n : Nat, 1 * n = n := sorry

theorem inc_inc : ∀ (b : Bool) (bs : List Bool),
    inc (inc (b :: bs)) = b :: inc bs := sorry

theorem the_zeros_span_the_width : ∀ n : Nat, (zeros n).length = n := sorry

theorem the_again_steps_first {α : Sort u} (Φ : α → α) :
    ∀ (n : Nat) (a : α), again Φ (n + 1) a = again Φ n (Φ a) := sorry

theorem the_home_wheel_turns : again collatzStep 3 1 = 1 := sorry

theorem len_replicate {A : Type u} (a : A) :
    ∀ n : Nat, (List.replicate n a).length = n := sorry

theorem the_unit_word_is_its_count :
    ∀ w : List Unit, List.replicate w.length () = w := sorry

theorem ble_le_add_left : ∀ a b : Nat, Nat.ble b (a + b) = true :=
  by
    (intro _ y; induction y;
      all_goals
        (first
          | (intros; rfl)
          | (intros; assumption)))

theorem the_rest_reads {A : Type w} {a b : A} {l m : List A} (h : a :: l = b :: m) : l = m :=
  congrArg (fun x => x.tail) h

theorem a_member_is_enrolled {A : Type u} (beq : A → A → Bool) (hrefl : ∀ x, beq x x = true) :
    ∀ (s : List A) (p : A), p ∈ s → enrolled beq s p = true
  | [], _, h => nomatch h
  | q :: s, p, h => by
      cases h with
      | head =>
          show (beq q q || enrolled beq s q) = true
          rw [hrefl]
          rfl
      | tail _ h' =>
          show (beq q p || enrolled beq s p) = true
          rw [a_member_is_enrolled beq hrefl s p h']
          cases beq q p <;> rfl

theorem an_enrolled_name_stays_enrolled_down_the_hall {A : Type u} (beq : A → A → Bool)
    (l : List A) (n : A) :
    ∀ room : List A, enrolled beq room n = true → enrolled beq (room ++ l) n = true
  | [], h => nomatch h
  | y :: room, h => by
      show (beq y n || enrolled beq (room ++ l) n) = true
      have h1 : (beq y n || enrolled beq room n) = true := h
      cases hy : beq y n with
      | true => rfl
      | false =>
          rw [hy] at h1
          exact an_enrolled_name_stays_enrolled_down_the_hall beq l n room h1

theorem a_merging_map_has_no_section {S : Type u} {T : Type u'} (h : S → T)
    {s s' : S} (hs : s ≠ s') (hm : h s = h s')
    (r : T → S) (hr : ∀ x, r (h x) = x) : False := sorry

theorem mul_spreads : ∀ a b c : Nat, a * (b + c) = a * b + a * c
  | _, _, 0 => rfl
  | a, b, c + 1 =>
      (congrArg (fun x => x + a) (mul_spreads a b c)).trans
        (add_regroups (a * b) (a * c) a)

theorem lengths_add {A : Type u} : ∀ l m : List A, (l ++ m).length = l.length + m.length
  | [], m => (zero_add m.length).symm
  | _ :: l, m =>
      (congrArg (fun n => n + 1) (lengths_add l m)).trans
        (click_slides l.length m.length)

theorem the_enrolled_stay_enrolled {A : Type u} (beq : A → A → Bool)
    (st : List A × List (A × List A)) (arr : A × List A) (x : A)
    (h : enrolled beq st.1 x = true) :
    enrolled beq (welcome beq st arr).1 x = true := by
  cases hb : backed beq st.1 arr.2 with
  | false =>
      rw [the_unbacked_wait beq st arr hb]
      exact h
  | true =>
      rw [the_backed_are_seated beq st arr hb]
      show (beq arr.1 x || enrolled beq st.1 x) = true
      rw [h]
      exact or_swallows (beq arr.1 x)

theorem the_seat_is_load_bearing_in_the_same_click {A : Type u} (beq : A → A → Bool)
    (hrefl : ∀ y : A, beq y y = true)
    (st : List A × List (A × List A)) (arr : A × List A)
    (hb : backed beq st.1 arr.2 = true) :
    enrolled beq (welcome beq st arr).1 arr.1 = true := sorry

theorem the_insertions_count {A : Type u} (x : A) :
    ∀ l : List A, (inserts x l).length = l.length + 1
  | [] => rfl
  | y :: l => by
      show ((inserts x l).map (y :: ·)).length + 1 = (l.length + 1) + 1
      rw [len_map, the_insertions_count x l]

theorem mem_joinMap_back {A : Type u} {B : Type v} {f : A → List B} {q : B} :
    ∀ as : List A, q ∈ joinMap f as → ∃ a, a ∈ as ∧ q ∈ f a
  | [], h => nomatch h
  | a :: as, h => by
      cases mem_append_split (f a) h with
      | inl hfa => exact ⟨a, List.Mem.head as, hfa⟩
      | inr hrest =>
          obtain ⟨b, hb, hq⟩ := mem_joinMap_back as hrest
          exact ⟨b, List.Mem.tail a hb, hq⟩

theorem the_insertion_grows_one {A : Type u} (x : A) :
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

theorem succ_adds (a b : Nat) : (a + 1) + b = (a + b) + 1 := sorry

theorem ble_le_add : ∀ a b : Nat, Nat.ble a (a + b) = true :=
  by
    (intro _ y; induction y;
      all_goals
        (first
          | (intros; (apply ble_trans <;> (apply ble_refl <;> fail)))
          |
            (intros;
              (apply ble_trans <;>
                  first
                  | assumption
                  | (apply ble_le_succ <;> fail)))))

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

theorem perm_middle {A : Type u} (x : A) :
    ∀ (u v : List A), (u ++ x :: v).Perm (x :: (u ++ v))
  | [], v => perm_refl (x :: v)
  | y :: u, v =>
      List.Perm.trans (List.Perm.cons y (perm_middle x u v))
        (List.Perm.swap x y (u ++ v))

theorem mem_joinMap_intro {A : Type u} {B : Type v} {f : A → List B} {a : A}
    {q : B} : ∀ {as : List A}, a ∈ as → q ∈ f a → q ∈ joinMap f as
  | _ :: as, List.Mem.head _, hq => mem_append_left (joinMap f as) hq
  | b :: _, List.Mem.tail _ h, hq =>
      mem_append_right (f b) (mem_joinMap_intro h hq)

theorem the_wedge_fits_anywhere {A : Type u} (x : A) :
    ∀ (u v : List A), (u ++ x :: v) ∈ inserts x (u ++ v)
  | [], v => by
      cases v with
      | nil => exact List.Mem.head _
      | cons y t => exact List.Mem.head _
  | y :: u, v =>
      List.Mem.tail _
        (mem_map_intro (y :: ·) (the_wedge_fits_anywhere x u v))

theorem the_trade_swaps_the_pair {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) :
    trade beq a b a = b ∧ trade beq a b b = a := by
  constructor
  · show cond (beq a a) b (cond (beq a b) a a) = b
    rw [hR a]
    exact rfl
  · show cond (beq b a) b (cond (beq b b) a b) = a
    rw [beq_no hE (fun h => hab h.symm), hR b]
    exact rfl

theorem the_trade_spares_the_stranger {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y) {a b x : A}
    (hxa : x ≠ a) (hxb : x ≠ b) : trade beq a b x = x := by
  show cond (beq x a) b (cond (beq x b) a x) = x
  rw [beq_no hE hxa, beq_no hE hxb]
  exact rfl

theorem apart_across {A : Type u} :
    ∀ (u w : List A), Apart (u ++ w) →
      ∀ x, x ∈ u → ∀ y, y ∈ w → x ≠ y
  | [], _, _, _, hx, _, _ => nomatch hx
  | z :: u, w, h, x, hx, y, hy => by
      cases h with
      | cons hz hrest =>
          cases hx with
          | head => exact hz y (mem_append_right u hy)
          | tail _ hx' => exact apart_across u w hrest x hx' y hy

theorem apart_removes_the_mark {A : Type u} :
    ∀ (v1 : List A) {x : A} {v2 : List A},
      Apart (v1 ++ x :: v2) → Apart (v1 ++ v2)
  | [], _, _, h => by
      cases h with
      | cons _ hrest => exact hrest
  | _ :: v1, _, _, h => by
      cases h with
      | cons hz hrest =>
          exact Apart.cons
            (fun y hy => hz y (mem_insert_middle v1 hy))
            (apart_removes_the_mark v1 hrest)

theorem the_first_voice_decides {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) :
    ∀ p : List A, a ∈ p →
      firstOf beq a b p = !(firstOf beq b a p)
  | [], ha => nomatch ha
  | x :: p, ha => by
      cases hxa : beq x a with
      | true =>
          have hx : x = a := hE x a hxa
          show cond (beq x a) true
              (cond (beq x b) false (firstOf beq a b p))
            = !(cond (beq x b) true
                (cond (beq x a) false (firstOf beq b a p)))
          rw [hxa, hx, beq_no hE hab]
          exact rfl
      | false =>
          have hxa' := ne_of_beq_no hR hxa
          have ha' : a ∈ p := by
            cases ha with
            | head => exact absurd rfl hxa'
            | tail _ h => exact h
          cases hxb : beq x b with
          | true =>
              show cond (beq x a) true
                  (cond (beq x b) false (firstOf beq a b p))
                = !(cond (beq x b) true
                    (cond (beq x a) false (firstOf beq b a p)))
              rw [hxa, hxb]
              exact rfl
          | false =>
              show cond (beq x a) true
                  (cond (beq x b) false (firstOf beq a b p))
                = !(cond (beq x b) true
                    (cond (beq x a) false (firstOf beq b a p)))
              rw [hxa, hxb, the_first_voice_decides hE hR hab p ha']
              exact rfl

theorem mul_two_reads_double (n : Nat) : n * 2 = n + n :=
  by
    (intros; (try dsimp only [] at *); intros;
      (apply ((add_regroups _ _ _)).trans (by (apply zero_add <;> fail)) <;> fail))

theorem every_word_fits :
    ∀ (n : Nat) (w : List Bool), w ∈ words n → w.length = n
  | 0, _, hw => by
      cases hw with
      | head => rfl
      | tail _ h' => exact nomatch h'
  | n + 1, w, hw => by
      cases mem_append_split ((words n).map (true :: ·)) hw with
      | inl h1 =>
          obtain ⟨u, hu, he⟩ := mem_map_back (words n) h1
          rw [← he]
          show u.length + 1 = n + 1
          rw [every_word_fits n u hu]
      | inr h2 =>
          obtain ⟨u, hu, he⟩ := mem_map_back (words n) h2
          rw [← he]
          show u.length + 1 = n + 1
          rw [every_word_fits n u hu]

theorem the_book_holds_every_word :
    ∀ w : List Bool, w ∈ words w.length
  | [] => List.Mem.head _
  | true :: t =>
      mem_append_left ((words t.length).map (false :: ·))
        (mem_map_intro (true :: ·) (the_book_holds_every_word t))
  | false :: t =>
      mem_append_right ((words t.length).map (true :: ·))
        (mem_map_intro (false :: ·) (the_book_holds_every_word t))

theorem the_retrace_comes_home :
    ∀ (n : Nat) (s : List Bool), again dec n (again inc n s) = s
  | 0, _ => rfl
  | n + 1, s => by
      rw [the_again_steps_first dec n]
      show again dec n (dec (inc (again inc n s))) = s
      rw [the_tick_unwinds]
      exact the_retrace_comes_home n s

theorem enrolled_grows {A : Type u} (beq : A → A → Bool) (room : List A) (y x : A)
    (h : enrolled beq room x = true) : enrolled beq (y :: room) x = true := sorry

theorem the_backing_reaches_each_need {A : Type u} (beq : A → A → Bool) (room : List A) :
    ∀ needs : List A, backed beq room needs = true →
      ∀ n, n ∈ needs → enrolled beq room n = true := by
  intro needs
  induction needs with
  | nil => intro _ n hn; cases hn
  | cons n' needs ih =>
      intro h n hn
      have hh : (enrolled beq room n' && backed beq room needs) = true := h
      have hp := and_reads _ _ hh
      cases hn with
      | head => exact hp.1
      | tail _ hm => exact ih hp.2 n hm

theorem mul_one_reads (a : Nat) : a * 1 = a := sorry

theorem the_hallway_is_too_small {S : Type u} (r : S → Bool) (a b c : S) :
    r a = r b ∨ r b = r c ∨ r a = r c := sorry

theorem the_unenrolled_are_no_member {A : Type u} (beq : A → A → Bool) (hrefl : ∀ x, beq x x = true)
    (s : List A) (p : A) (h : enrolled beq s p = false) : ¬ p ∈ s :=
  fun hp => nomatch (h.symm.trans (a_member_is_enrolled beq hrefl s p hp))

theorem the_backing_survives_the_hall {A : Type u} (beq : A → A → Bool) (room l : List A) :
    ∀ needs : List A, backed beq room needs = true → backed beq (room ++ l) needs = true
  | [], _ => rfl
  | n :: needs, h => by
      show (enrolled beq (room ++ l) n && backed beq (room ++ l) needs) = true
      have h1 : (enrolled beq room n && backed beq room needs) = true := h
      cases he : enrolled beq room n with
      | false => rw [he] at h1; exact nomatch h1
      | true =>
          rw [he] at h1
          rw [an_enrolled_name_stays_enrolled_down_the_hall beq l n room he,
            the_backing_survives_the_hall beq room l needs h1]
          exact rfl

theorem the_join_counts_evenly {A : Type u} {B : Type v} (f : A → List B) (n : Nat) :
    ∀ as : List A, (∀ a, a ∈ as → (f a).length = n) →
      (joinMap f as).length = n * as.length
  | [], _ => rfl
  | a :: as, h => by
      show (f a ++ joinMap f as).length = n * (as.length + 1)
      rw [lengths_add, h a (List.Mem.head as),
          the_join_counts_evenly f n as
            (fun b hb => h b (List.Mem.tail a hb))]
      exact Nat.add_comm n (n * as.length)

theorem the_orders_keep_the_length {A : Type u} :
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

theorem two_splits_perm {A : Type u} (x : A) :
    ∀ (u v w z : List A), u ++ x :: v = w ++ x :: z →
      (u ++ v).Perm (w ++ z)
  | [], v, [], z, h => by
      rw [(List.cons.inj h).2]
  | [], v, w₀ :: w', z, h => by
      obtain ⟨h₁, h₂⟩ := List.cons.inj h
      rw [h₂, ← h₁]
      exact perm_middle x w' z
  | u₀ :: u', v, [], z, h => by
      obtain ⟨h₁, h₂⟩ := List.cons.inj h
      rw [← h₂, h₁]
      exact perm_symm (perm_middle x u' v)
  | u₀ :: u', v, w₀ :: w', z, h => by
      obtain ⟨h₁, h₂⟩ := List.cons.inj h
      rw [h₁]
      exact List.Perm.cons w₀ (two_splits_perm x u' v w' z h₂)

theorem the_trade_undoes_itself {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) (x : A) :
    trade beq a b (trade beq a b x) = x := by
  cases hxa : beq x a with
  | true =>
      have hx : x = a := hE x a hxa
      rw [hx, (the_trade_swaps_the_pair hE hR hab).1,
          (the_trade_swaps_the_pair hE hR hab).2]
  | false =>
      cases hxb : beq x b with
      | true =>
          have hx : x = b := hE x b hxb
          rw [hx, (the_trade_swaps_the_pair hE hR hab).2,
              (the_trade_swaps_the_pair hE hR hab).1]
      | false =>
          have hfix : trade beq a b x = x := by
            show cond (beq x a) b (cond (beq x b) a x) = x
            rw [hxa, hxb]
            exact rfl
          rw [hfix, hfix]

theorem the_trade_hears_no_order {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) (x : A) :
    trade beq a b x = trade beq b a x := by
  cases hxa : beq x a with
  | true =>
      have hx : x = a := hE x a hxa
      rw [hx, (the_trade_swaps_the_pair hE hR hab).1]
      exact ((the_trade_swaps_the_pair hE hR
        (fun h => hab h.symm)).2).symm
  | false =>
      cases hxb : beq x b with
      | true =>
          have hx : x = b := hE x b hxb
          rw [hx, (the_trade_swaps_the_pair hE hR hab).2]
          exact ((the_trade_swaps_the_pair hE hR
            (fun h => hab h.symm)).1).symm
      | false =>
          have hxa' := ne_of_beq_no hR hxa
          have hxb' := ne_of_beq_no hR hxb
          rw [the_trade_spares_the_stranger hE hxa' hxb',
              the_trade_spares_the_stranger hE hxb' hxa']

theorem the_trade_spares_the_word {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y) {a b : A} :
    ∀ w : List A, (∀ x, x ∈ w → x ≠ a) → (∀ x, x ∈ w → x ≠ b) →
      w.map (trade beq a b) = w
  | [], _, _ => rfl
  | x :: w, hA, hB => by
      show trade beq a b x :: w.map (trade beq a b) = x :: w
      rw [the_trade_spares_the_stranger hE (hA x (List.Mem.head w))
            (hB x (List.Mem.head w)),
          the_trade_spares_the_word hE w
            (fun y hy => hA y (List.Mem.tail x hy))
            (fun y hy => hB y (List.Mem.tail x hy))]

theorem the_apart_mark_sits_once {A : Type u} (v1 : List A) {x : A}
    (v2 : List A) (h : Apart (v1 ++ x :: v2)) : ¬ x ∈ v1 ++ v2 := by
  intro hx
  cases mem_append_split v1 hx with
  | inl h1 =>
      exact apart_across v1 (x :: v2) h x h1 x (List.Mem.head v2) rfl
  | inr h2 =>
      have hs := apart_drop v1 (x :: v2) h
      cases hs with
      | cons hxf _ => exact hxf x h2 rfl

theorem the_traded_word_reverses_the_verdict {A : Type u}
    {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) :
    ∀ p : List A,
      firstOf beq a b (p.map (trade beq a b)) = firstOf beq b a p
  | [] => rfl
  | x :: p => by
      cases hxa : beq x a with
      | true =>
          have hx : x = a := hE x a hxa
          rw [hx]
          show firstOf beq a b
              (trade beq a b a :: p.map (trade beq a b))
            = firstOf beq b a (a :: p)
          rw [(the_trade_swaps_the_pair hE hR hab).1]
          show cond (beq b a) true
              (cond (beq b b) false
                (firstOf beq a b (p.map (trade beq a b))))
            = cond (beq a b) true
              (cond (beq a a) false (firstOf beq b a p))
          rw [beq_no hE (fun h => hab h.symm), beq_no hE hab, hR a, hR b]
          exact rfl
      | false =>
          cases hxb : beq x b with
          | true =>
              have hx : x = b := hE x b hxb
              rw [hx]
              show firstOf beq a b
                  (trade beq a b b :: p.map (trade beq a b))
                = firstOf beq b a (b :: p)
              rw [(the_trade_swaps_the_pair hE hR hab).2]
              show cond (beq a a) true
                  (cond (beq a b) false
                    (firstOf beq a b (p.map (trade beq a b))))
                = cond (beq b b) true
                  (cond (beq b a) false (firstOf beq b a p))
              rw [hR a, hR b]
              exact rfl
          | false =>
              have hxa' := ne_of_beq_no hR hxa
              have hxb' := ne_of_beq_no hR hxb
              show firstOf beq a b
                  (trade beq a b x :: p.map (trade beq a b))
                = firstOf beq b a (x :: p)
              rw [the_trade_spares_the_stranger hE hxa' hxb']
              show cond (beq x a) true
                  (cond (beq x b) false
                    (firstOf beq a b (p.map (trade beq a b))))
                = cond (beq x b) true
                  (cond (beq x a) false (firstOf beq b a p))
              rw [hxa, hxb,
                  the_traded_word_reverses_the_verdict hE hR hab p]

theorem the_filter_splits_the_room {A : Type u} (q : A → Bool) :
    ∀ L : List A,
      (L.filter q).length + (L.filter (fun x => !(q x))).length
        = L.length
  | [] => rfl
  | x :: L => by
      cases hq : q x with
      | true =>
          have hnot : (fun y => !(q y)) x = false := by
            show (!(q x)) = false
            rw [hq]
            exact rfl
          rw [List.filter_cons_of_pos hq,
              List.filter_cons_of_neg (p := fun y => !(q y))
                (ne_true_of_eq_false hnot)]
          show ((L.filter q).length + 1)
              + (L.filter (fun y => !(q y))).length
            = L.length + 1
          rw [succ_adds, the_filter_splits_the_room q L]
      | false =>
          have hnot : (fun y => !(q y)) x = true := by
            show (!(q x)) = true
            rw [hq]
            exact rfl
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq),
              List.filter_cons_of_pos (p := fun y => !(q y)) hnot]
          show ((L.filter q).length
              + (L.filter (fun y => !(q y))).length) + 1
            = L.length + 1
          rw [the_filter_splits_the_room q L]

theorem the_book_counts_the_cap :
    ∀ n : Nat, (words n).length = roomCap n
  | 0 => rfl
  | n + 1 => by
      show ((words n).map (true :: ·) ++ (words n).map (false :: ·)).length
          = roomCap n + roomCap n
      rw [lengths_add, len_map, len_map, the_book_counts_the_cap n]

theorem the_book_repeats_no_word : ∀ n : Nat, Apart (words n)
  | 0 => Apart.cons (fun _ hb => nomatch hb) Apart.nil
  | n + 1 =>
      apart_append ((words n).map (false :: ·))
        (apart_map (fun _ _ h => (List.cons.inj h).2)
          (the_book_repeats_no_word n))
        (apart_map (fun _ _ h => (List.cons.inj h).2)
          (the_book_repeats_no_word n))
        (fun _ hx _ hy he =>
          match mem_map_back (words n) hx, mem_map_back (words n) hy with
          | ⟨_, _, hex⟩, ⟨_, _, hey⟩ =>
              nomatch (List.cons.inj ((hex.trans he).trans hey.symm)).1)

theorem the_doubling_passes_the_tick_inward :
    ∀ (c : Nat) (b : Bool) (bs : List Bool),
      again inc (c + c) (b :: bs) = b :: again inc c bs
  | 0, _, _ => rfl
  | c + 1, b, bs => by
      rw [show (c + 1) + (c + 1) = ((c + c) + 1) + 1 from
            congrArg (· + 1) (succ_adds c c)]
      show inc (inc (again inc (c + c) (b :: bs)))
          = b :: again inc (c + 1) bs
      rw [the_doubling_passes_the_tick_inward c b bs, inc_inc]
      exact rfl

theorem the_wear_is_a_reading (n : Nat) (s : List Bool) :
    again dec n (again inc n s) = s
      ∧ (∀ p q : List Bool, inc p = inc q → p = q)
      ∧ again collatzStep 3 1 = 1
      ∧ collatzStep 1 = collatzStep 8
      ∧ (1 : Nat) ≠ 8
      ∧ ¬ ∃ g : Nat → Nat, ∀ m, g (collatzStep m) = m :=
  ⟨the_retrace_comes_home n s,
   (fun p q h =>
     (the_tick_unwinds p).symm.trans ((congrArg dec h).trans (the_tick_unwinds q))),
   the_home_wheel_turns,
   the_step_merges_the_riders.1,
   the_step_merges_the_riders.2,
   no_inverse_unsteps_the_collatz⟩

theorem the_backing_survives_the_seating {A : Type u} (beq : A → A → Bool)
    (room : List A) (y : A) :
    ∀ needs : List A, backed beq room needs = true →
      backed beq (y :: room) needs = true := by
  intro needs
  induction needs with
  | nil => intro _; rfl
  | cons n' needs ih =>
      intro h
      have hh : (enrolled beq room n' && backed beq room needs) = true := h
      have hp := and_reads _ _ hh
      show (enrolled beq (y :: room) n' && backed beq (y :: room) needs) = true
      rw [enrolled_grows beq room y n' hp.1, ih hp.2]
      exact rfl

theorem the_click_spares_the_dark {A : Type u} (beq : A → A → Bool)
    (st : List A × List (A × List A)) (arr : A × List A) (x : A)
    (hdark : enrolled beq st.1 x = false)
    (hcite : beq arr.1 x = true → ∃ z, z ∈ arr.2 ∧ enrolled beq st.1 z = false) :
    enrolled beq (welcome beq st arr).1 x = false := by
  cases hb : backed beq st.1 arr.2 with
  | false =>
      rw [the_unbacked_wait beq st arr hb]
      exact hdark
  | true =>
      rw [the_backed_are_seated beq st arr hb]
      show (beq arr.1 x || enrolled beq st.1 x) = false
      cases ha : beq arr.1 x with
      | false => exact hdark
      | true =>
          obtain ⟨z, hz, hzd⟩ := hcite ha
          have hze := the_backing_reaches_each_need beq st.1 arr.2 hb z hz
          rw [hze] at hzd
          exact nomatch hzd

theorem everyone_means_each (beq : Nat → Nat → Bool) (members confirmed : List Nat)
    (h : everyone beq members confirmed = true) :
    ∀ m, m ∈ members → enrolled beq confirmed m = true := sorry

theorem the_orders_count_to_the_factorial {A : Type u} :
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

theorem the_shuffle_cancels_the_mark {A : Type u} {L M : List A}
    (h : L.Perm M) :
    ∀ (x : A) (u v w z : List A), L = u ++ x :: v → M = w ++ x :: z →
      (u ++ v).Perm (w ++ z) := by
  induction h with
  | nil =>
      intro x u v w z hL _
      cases u with
      | nil => exact nomatch hL
      | cons _ _ => exact nomatch hL
  | cons y h' ih =>
      intro x u v w z hL hM
      cases u with
      | nil =>
          obtain ⟨hyx, hv⟩ := List.cons.inj hL
          cases w with
          | nil =>
              obtain ⟨_, hz⟩ := List.cons.inj hM
              rw [← hv, ← hz]
              exact h'
          | cons w₀ w' =>
              obtain ⟨hyw, ht₂⟩ := List.cons.inj hM
              rw [← hv, ← hyw, hyx]
              exact (ht₂ ▸ h').trans (perm_middle x w' z)
      | cons u₀ u' =>
          obtain ⟨hyu, ht₁⟩ := List.cons.inj hL
          cases w with
          | nil =>
              obtain ⟨hyx, hz⟩ := List.cons.inj hM
              rw [← hz, ← hyu, hyx]
              exact (perm_symm (perm_middle x u' v)).trans
                (by
                  rw [show u' ++ x :: v = u'.append (x :: v) from rfl,
                      ← ht₁]
                  exact h')
          | cons w₀ w' =>
              obtain ⟨hyu2, ht₁2⟩ := List.cons.inj hL
              obtain ⟨hyw, ht₂⟩ := List.cons.inj hM
              rw [← hyu, ← hyw]
              exact List.Perm.cons y (ih x u' v w' z ht₁ ht₂)
  | swap a b l =>
      intro x u v w z hL hM
      cases u with
      | nil =>
          obtain ⟨hbx, hv⟩ := List.cons.inj hL
          cases w with
          | nil =>
              obtain ⟨hax, hz⟩ := List.cons.inj hM
              rw [← hv, ← hz, hax, hbx]
          | cons w₀ w' =>
              obtain ⟨haw, hM2⟩ := List.cons.inj hM
              cases w' with
              | nil =>
                  obtain ⟨_, hlz⟩ := List.cons.inj hM2
                  rw [← hv, ← haw, ← hlz]
                  exact perm_refl (a :: l)
              | cons w₁ w'' =>
                  obtain ⟨hbw, hl⟩ := List.cons.inj hM2
                  rw [← hv, ← haw, ← hbw, hl, hbx]
                  exact List.Perm.cons a (perm_middle x w'' z)
      | cons u₀ u' =>
          obtain ⟨hbu, hL2⟩ := List.cons.inj hL
          cases u' with
          | nil =>
              obtain ⟨hax, hlv⟩ := List.cons.inj hL2
              cases w with
              | nil =>
                  obtain ⟨_, hz⟩ := List.cons.inj hM
                  rw [← hbu, ← hlv, ← hz]
                  exact perm_refl (b :: l)
              | cons w₀ w' =>
                  obtain ⟨haw, hM2⟩ := List.cons.inj hM
                  cases w' with
                  | nil =>
                      obtain ⟨hbx2, hlz⟩ := List.cons.inj hM2
                      rw [← hbu, ← haw, ← hlv, hbx2, hax, hlz]
                  | cons w₁ w'' =>
                      obtain ⟨hbw, hl2⟩ := List.cons.inj hM2
                      rw [← hbu, ← hlv, hl2, ← haw, ← hbw, hax]
                      exact List.Perm.trans
                        (List.Perm.cons b (perm_middle x w'' z))
                        (List.Perm.swap x b (w'' ++ z))
          | cons u₁ u'' =>
              obtain ⟨hau, hl⟩ := List.cons.inj hL2
              cases w with
              | nil =>
                  obtain ⟨hax, hz⟩ := List.cons.inj hM
                  rw [← hbu, ← hau, ← hz, hl, hax]
                  exact List.Perm.cons b (perm_symm (perm_middle x u'' v))
              | cons w₀ w' =>
                  obtain ⟨haw, hM2⟩ := List.cons.inj hM
                  cases w' with
                  | nil =>
                      obtain ⟨hbx2, hlz⟩ := List.cons.inj hM2
                      rw [← hbu, ← hau, ← haw, ← hlz, hl, hbx2]
                      exact List.Perm.trans
                        (List.Perm.swap a x (u'' ++ v))
                        (List.Perm.cons a
                          (perm_symm (perm_middle x u'' v)))
                  | cons w₁ w'' =>
                      obtain ⟨hbw, hl2⟩ := List.cons.inj hM2
                      rw [← hbu, ← hau, ← haw, ← hbw]
                      exact List.Perm.trans
                        (List.Perm.swap a b (u'' ++ v))
                        (List.Perm.cons a (List.Perm.cons b
                          (two_splits_perm x u'' v w'' z
                            (hl.symm.trans hl2))))
  | trans h₁ _ ih₁ ih₂ =>
      intro x u v w z hL hM
      have hxL : x ∈ _ := perm_mem h₁ x
        (by rw [hL]; exact mem_append_right u (List.Mem.head v))
      obtain ⟨u₀, v₀, hmid⟩ := mem_splits hxL
      exact (ih₁ x u v u₀ v₀ hL hmid).trans (ih₂ x u₀ v₀ w z hmid hM)

theorem the_traded_word_trades_home {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) :
    ∀ p : List A, (p.map (trade beq a b)).map (trade beq a b) = p
  | [] => rfl
  | x :: p => by
      show trade beq a b (trade beq a b x)
            :: (p.map (trade beq a b)).map (trade beq a b) = x :: p
      rw [the_trade_undoes_itself hE hR hab x,
          the_traded_word_trades_home hE hR hab p]

theorem the_wedged_trade_is_a_shuffle {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    (u v1 v2 : List A)
    (hl : Apart (u ++ a :: (v1 ++ b :: v2))) :
    ((u ++ a :: (v1 ++ b :: v2)).map (trade beq a b)).Perm
      (u ++ a :: (v1 ++ b :: v2)) := by
  have hua : ∀ x, x ∈ u → x ≠ a := fun x hx =>
    apart_across u (a :: (v1 ++ b :: v2)) hl x hx a
      (List.Mem.head (v1 ++ b :: v2))
  have hub : ∀ x, x ∈ u → x ≠ b := fun x hx =>
    apart_across u (a :: (v1 ++ b :: v2)) hl x hx b
      (List.Mem.tail a (mem_append_right v1 (List.Mem.head v2)))
  have hcons : Apart (a :: (v1 ++ b :: v2)) :=
    apart_drop u (a :: (v1 ++ b :: v2)) hl
  cases hcons with
  | cons hafresh hvrest =>
      have hv1a : ∀ x, x ∈ v1 → x ≠ a := fun x hx he =>
        hafresh x (mem_append_left (b :: v2) hx) he.symm
      have hv1b : ∀ x, x ∈ v1 → x ≠ b := fun x hx =>
        apart_across v1 (b :: v2) hvrest x hx b (List.Mem.head v2)
      have hbfresh : Apart (b :: v2) := apart_drop v1 (b :: v2) hvrest
      cases hbfresh with
      | cons hbf _ =>
          have hv2a : ∀ x, x ∈ v2 → x ≠ a := fun x hx he =>
            hafresh x (mem_append_right v1 (List.Mem.tail b hx)) he.symm
          have hv2b : ∀ x, x ∈ v2 → x ≠ b := fun x hx he =>
            hbf x hx he.symm
          have hmap : (u ++ a :: (v1 ++ b :: v2)).map (trade beq a b)
              = u ++ b :: (v1 ++ a :: v2) := by
            rw [map_crosses_append (trade beq a b) u (a :: (v1 ++ b :: v2))]
            show u.map (trade beq a b)
                ++ trade beq a b a :: (v1 ++ b :: v2).map (trade beq a b)
              = u ++ b :: (v1 ++ a :: v2)
            rw [the_trade_spares_the_word hE u hua hub,
                (the_trade_swaps_the_pair hE hR hab).1,
                map_crosses_append (trade beq a b) v1 (b :: v2)]
            show u ++ b :: (v1.map (trade beq a b)
                ++ trade beq a b b :: v2.map (trade beq a b))
              = u ++ b :: (v1 ++ a :: v2)
            rw [the_trade_spares_the_word hE v1 hv1a hv1b,
                (the_trade_swaps_the_pair hE hR hab).2,
                the_trade_spares_the_word hE v2 hv2a hv2b]
          rw [hmap]
          refine perm_append_left ?_ u
          exact ((List.Perm.cons b (perm_middle a v1 v2)).trans
            (List.Perm.swap a b (v1 ++ v2))).trans
            (List.Perm.cons a (perm_symm (perm_middle b v1 v2)))

theorem the_matching_rooms_are_shuffles {A : Type u} :
    ∀ (u v : List A), Apart u → Apart v → (∀ x, x ∈ u ↔ x ∈ v) →
      u.Perm v
  | [], [], _, _, _ => .nil
  | [], y :: v, _, _, hmem => nomatch (hmem y).mpr (List.Mem.head v)
  | x :: u, v, hu, hv, hmem => by
      have hxv : x ∈ v := (hmem x).mp (List.Mem.head u)
      obtain ⟨v1, v2, hsplit⟩ := mem_splits hxv
      subst hsplit
      cases hu with
      | cons hx hurest =>
          have hmem' : ∀ y, y ∈ u ↔ y ∈ v1 ++ v2 := by
            intro y
            constructor
            · intro hy
              have hyx : y ≠ x := fun he => hx y hy he.symm
              have hyv : y ∈ v1 ++ x :: v2 :=
                (hmem y).mp (List.Mem.tail x hy)
              cases mem_append_split v1 hyv with
              | inl h1 => exact mem_append_left v2 h1
              | inr h2 =>
                  cases h2 with
                  | head => exact absurd rfl hyx
                  | tail _ h2' => exact mem_append_right v1 h2'
            · intro hy
              have hyv : y ∈ v1 ++ x :: v2 := mem_insert_middle v1 hy
              have hyu : y ∈ x :: u := (hmem y).mpr hyv
              cases hyu with
              | head => exact absurd hy (the_apart_mark_sits_once v1 v2 hv)
              | tail _ h' => exact h'
          exact (List.Perm.cons x
            (the_matching_rooms_are_shuffles u (v1 ++ v2) hurest
              (apart_removes_the_mark v1 hv) hmem')).trans
            (perm_symm (perm_middle x v1 v2))

theorem the_verdicts_split_the_room {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (ha : a ∈ l) :
    ((perms l).filter (firstOf beq a b)).length
      + ((perms l).filter (firstOf beq b a)).length
      = (perms l).length := by
  have hcompl : ∀ p, p ∈ perms l →
      firstOf beq b a p = !(firstOf beq a b p) := by
    intro p hp
    have hap : a ∈ p :=
      perm_mem (perm_symm (every_order_is_a_shuffle l p hp)) a ha
    rw [the_first_voice_decides hE hR hab p hap, not_not]
  rw [filter_congr_mem (firstOf beq b a)
        (fun p => !(firstOf beq a b p)) (perms l) hcompl]
  exact the_filter_splits_the_room (firstOf beq a b) (perms l)

theorem the_odometer_comes_home_at_the_cap :
    ∀ s : List Bool, again inc (roomCap s.length) s = s
  | [] => rfl
  | b :: bs => by
      show again inc (roomCap bs.length + roomCap bs.length) (b :: bs)
          = b :: bs
      rw [the_doubling_passes_the_tick_inward (roomCap bs.length) b bs,
          the_odometer_comes_home_at_the_cap bs]

theorem the_clock_reaches_every_word :
    ∀ w : List Bool, clockAt w.length (val w) = w
  | [] => rfl
  | false :: t => by
      show again inc ((0 : Nat) + (val t + val t))
          (false :: zeros t.length) = false :: t
      rw [zero_add,
          the_doubling_passes_the_tick_inward (val t) false
            (zeros t.length)]
      show false :: clockAt t.length (val t) = false :: t
      rw [the_clock_reaches_every_word t]
  | true :: t => by
      show again inc ((1 : Nat) + (val t + val t))
          (false :: zeros t.length) = true :: t
      rw [Nat.add_comm 1 (val t + val t)]
      show inc (again inc (val t + val t) (false :: zeros t.length))
          = true :: t
      rw [the_doubling_passes_the_tick_inward (val t) false
            (zeros t.length)]
      show inc (false :: clockAt t.length (val t)) = true :: t
      rw [the_clock_reaches_every_word t]
      exact rfl

theorem no_mark_lights_itself {A : Type u} (beq : A → A → Bool) (x : A) :
    ∀ (w : List (A × List A)) (st : List A × List (A × List A)),
      enrolled beq st.1 x = false →
      (∀ arr, arr ∈ w → beq arr.1 x = true → x ∈ arr.2) →
      enrolled beq (intake beq st w).1 x = false := by
  intro w
  induction w with
  | nil => intro st hdark _; exact hdark
  | cons arr w ih =>
      intro st hdark hself
      show enrolled beq (intake beq (welcome beq st arr) w).1 x = false
      exact ih (welcome beq st arr)
        (the_click_spares_the_dark beq st arr x hdark
          (fun ha => ⟨x, hself arr (.head _) ha, hdark⟩))
        (fun a ha hb => hself a (.tail _ ha) hb)

theorem the_circle_stays_dark {A : Type u} (beq : A → A → Bool) (x y : A) :
    ∀ (w : List (A × List A)) (st : List A × List (A × List A)),
      enrolled beq st.1 x = false → enrolled beq st.1 y = false →
      (∀ arr, arr ∈ w → beq arr.1 x = true → y ∈ arr.2) →
      (∀ arr, arr ∈ w → beq arr.1 y = true → x ∈ arr.2) →
      enrolled beq (intake beq st w).1 x = false
        ∧ enrolled beq (intake beq st w).1 y = false := by
  intro w
  induction w with
  | nil => intro st hdx hdy _ _; exact ⟨hdx, hdy⟩
  | cons arr w ih =>
      intro st hdx hdy hcx hcy
      have hdx' := the_click_spares_the_dark beq st arr x hdx
        (fun ha => ⟨y, hcx arr (.head _) ha, hdy⟩)
      have hdy' := the_click_spares_the_dark beq st arr y hdy
        (fun ha => ⟨x, hcy arr (.head _) ha, hdx⟩)
      show enrolled beq (intake beq (welcome beq st arr) w).1 x = false
        ∧ enrolled beq (intake beq (welcome beq st arr) w).1 y = false
      exact ih (welcome beq st arr) hdx' hdy'
        (fun a ha hb => hcx a (.tail _ ha) hb)
        (fun a ha hb => hcy a (.tail _ ha) hb)

theorem the_key_is_cut_from_the_room {A : Type u} (beq : A → A → Bool)
    (hrefl : ∀ y : A, beq y y = true) (room : List A) :
    ∀ needs : List A, lacking beq room needs = 1 →
      ∃ k, k ∈ needs ∧ enrolled beq room k = false ∧
        backed beq (k :: room) needs = true := by
  intro needs
  induction needs with
  | nil =>
      intro h
      have h' : (0 : Nat) = 1 := h
      exact nomatch h'
  | cons n' needs ih =>
      intro h
      cases he : enrolled beq room n' with
      | true =>
          have hh : cond (enrolled beq room n')
              (lacking beq room needs) (lacking beq room needs + 1) = 1 := h
          rw [he] at hh
          obtain ⟨k, hk, hkd, hkb⟩ := ih hh
          refine ⟨k, .tail _ hk, hkd, ?_⟩
          show (enrolled beq (k :: room) n' && backed beq (k :: room) needs) = true
          rw [enrolled_grows beq room k n' he, hkb]
          exact rfl
      | false =>
          have hh : cond (enrolled beq room n')
              (lacking beq room needs) (lacking beq room needs + 1) = 1 := h
          rw [he] at hh
          have h0 : lacking beq room needs = 0 := Nat.succ.inj hh
          have hb := (the_weight_is_zero_at_the_door beq room needs).mp h0
          refine ⟨n', .head _, he, ?_⟩
          show (enrolled beq (n' :: room) n' && backed beq (n' :: room) needs) = true
          have h1 : enrolled beq (n' :: room) n' = true := by
            show (beq n' n' || enrolled beq room n') = true
            rw [hrefl n']
            exact rfl
          rw [h1, the_backing_survives_the_seating beq room n' needs hb]
          exact rfl

theorem the_book_is_the_answer_space (n : Nat) :
    (words n).length = roomCap n
      ∧ Apart (words n)
      ∧ (∀ w : List Bool, w ∈ words n → w.length = n)
      ∧ (∀ w : List Bool, w ∈ words w.length)
      ∧ (words 3).length = 8 :=
  by
    (intros; (repeat' constructor);
      all_goals
        (intros;
          first
          | (apply the_book_counts_the_cap <;> fail)
          | (apply the_book_repeats_no_word <;> fail)
          | (apply every_word_fits <;> assumption)
          | (apply the_book_holds_every_word <;> fail)))

theorem every_shuffle_is_an_order {A : Type u} :
    ∀ (l p : List A), p.Perm l → p ∈ perms l
  | [], p, h => by
      have hlen : p.length = 0 := perm_length h
      cases p with
      | nil => exact List.Mem.head _
      | cons _ _ => exact nomatch hlen
  | x :: l, p, h => by
      have hx : x ∈ p := perm_mem (perm_symm h) x (List.Mem.head l)
      obtain ⟨u, v, hp⟩ := mem_splits hx
      have h₂ : (u ++ v).Perm l :=
        the_shuffle_cancels_the_mark h x u v [] l hp rfl
      have h₃ : (u ++ v) ∈ perms l :=
        every_shuffle_is_an_order l (u ++ v) h₂
      have h₄ : p ∈ inserts x (u ++ v) := by
        rw [hp]
        exact the_wedge_fits_anywhere x u v
      show p ∈ joinMap (inserts x) (perms l)
      exact mem_joinMap_intro h₃ h₄

theorem the_trade_is_a_shuffle {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (hl : Apart l) (ha : a ∈ l) (hb : b ∈ l) :
    (l.map (trade beq a b)).Perm l := by
  obtain ⟨u, v, huv⟩ := mem_splits ha
  subst huv
  cases mem_append_split u hb with
  | inr hbv =>
      cases hbv with
      | head => exact absurd rfl hab
      | tail _ hbv' =>
          obtain ⟨v1, v2, hv⟩ := mem_splits hbv'
          subst hv
          exact the_wedged_trade_is_a_shuffle hE hR hab u v1 v2 hl
  | inl hbu =>
      obtain ⟨u1, u2, hu⟩ := mem_splits hbu
      subst hu
      rw [the_appends_regroup u1 (b :: u2) (a :: v)] at hl ⊢
      show ((u1 ++ b :: (u2 ++ a :: v)).map (trade beq a b)).Perm
          (u1 ++ b :: (u2 ++ a :: v))
      rw [map_congr_mem (trade beq a b) (trade beq b a)
            (u1 ++ b :: (u2 ++ a :: v))
            (fun x _ => the_trade_hears_no_order hE hR hab x)]
      exact the_wedged_trade_is_a_shuffle hE hR (fun h => hab h.symm)
        u1 u2 v hl

theorem the_value_tells_the_words_apart {n : Nat} {p q : List Bool}
    (hp : p ∈ words n) (hq : q ∈ words n) (he : val p = val q) :
    p = q := by
  have h1 : again inc (val p) (zeros n) = p := by
    rw [← every_word_fits n p hp]
    exact the_clock_reaches_every_word p
  have h2 : again inc (val q) (zeros n) = q := by
    rw [← every_word_fits n q hq]
    exact the_clock_reaches_every_word q
  rw [← h1, ← h2, he]

theorem the_trade_keeps_the_room {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (hl : Apart l) (ha : a ∈ l) (hb : b ∈ l)
    {p : List A} (hp : p ∈ perms l) :
    p.map (trade beq a b) ∈ perms l :=
  every_shuffle_is_an_order l (p.map (trade beq a b))
    ((perm_map (trade beq a b) (every_order_is_a_shuffle l p hp)).trans
      (the_trade_is_a_shuffle hE hR hab hl ha hb))

theorem the_orbit_is_the_book (n : Nat) (w : List Bool) (s : List Bool) :
    (words n).length = roomCap n
      ∧ (zeros n).length = n
      ∧ again inc (roomCap (zeros n).length) (zeros n) = zeros n
      ∧ (w ∈ words n → again inc (val w) (zeros n) = w)
      ∧ (∀ p q : List Bool, p ∈ words n → q ∈ words n → val p = val q → p = q)
      ∧ dec (inc s) = s ∧ inc (dec s) = s :=
  ⟨the_book_counts_the_cap n,
   the_zeros_span_the_width n,
   the_odometer_comes_home_at_the_cap (zeros n),
   (fun hw => by
     rw [← every_word_fits n w hw]
     exact the_clock_reaches_every_word w),
   (fun _ _ hp hq he => the_value_tells_the_words_apart hp hq he),
   the_tick_unwinds s,
   the_unwind_ticks s⟩

theorem the_census_of_orders_is_exact {A : Type u} (l p : List A)
    (hl : Apart l) :
    (p.Perm l ↔ p ∈ perms l)
      ∧ Apart (perms l)
      ∧ (perms l).length = fact l.length := sorry

theorem the_trade_shuffles_the_room {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (hl : Apart l) (ha : a ∈ l) (hb : b ∈ l) :
    ((perms l).map (fun p => p.map (trade beq a b))).Perm (perms l) := by
  refine the_matching_rooms_are_shuffles _ _ ?_
    (the_orders_repeat_never l hl) ?_
  · refine apart_map ?_ (the_orders_repeat_never l hl)
    intro p q hpq
    exact (the_traded_word_trades_home hE hR hab p).symm.trans
      ((congrArg (List.map (trade beq a b)) hpq).trans
        (the_traded_word_trades_home hE hR hab q))
  · intro x
    constructor
    · intro hx
      obtain ⟨p, hp, he⟩ := mem_map_back (perms l) hx
      rw [← he]
      exact the_trade_keeps_the_room hE hR hab hl ha hb hp
    · intro hx
      have h1 : x.map (trade beq a b) ∈ perms l :=
        the_trade_keeps_the_room hE hR hab hl ha hb hx
      have h2 := mem_map_intro (fun p => p.map (trade beq a b)) h1
      rw [the_traded_word_trades_home hE hR hab x] at h2
      exact h2

theorem the_two_directions_count_alike {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (hl : Apart l) (ha : a ∈ l) (hb : b ∈ l) :
    ((perms l).filter (firstOf beq a b)).length
      = ((perms l).filter (firstOf beq b a)).length := by
  have h1 : (((perms l).map (fun p => p.map (trade beq a b))).filter
      (firstOf beq a b)).length
      = ((perms l).filter (firstOf beq a b)).length :=
    perm_length (perm_filter (firstOf beq a b)
      (the_trade_shuffles_the_room hE hR hab hl ha hb))
  have h2 : ((perms l).map (fun p => p.map (trade beq a b))).filter
      (firstOf beq a b)
      = ((perms l).filter
          (fun p => firstOf beq a b (p.map (trade beq a b)))).map
          (fun p => p.map (trade beq a b)) :=
    filter_map_commutes (fun p => p.map (trade beq a b))
      (firstOf beq a b) (perms l)
  have h3 : (perms l).filter
      (fun p => firstOf beq a b (p.map (trade beq a b)))
      = (perms l).filter (firstOf beq b a) :=
    filter_congr_mem _ _ (perms l)
      (fun p _ => the_traded_word_reverses_the_verdict hE hR hab p)
  rw [← h1, h2, h3, len_map]

theorem the_direction_is_even_money {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (hl : Apart l) (ha : a ∈ l) (hb : b ∈ l) :
    ((perms l).filter (firstOf beq a b)).length
        = ((perms l).filter (firstOf beq b a)).length
      ∧ ((perms l).filter (firstOf beq a b)).length
          + ((perms l).filter (firstOf beq b a)).length = fact l.length
      ∧ sameRatio ((perms l).filter (firstOf beq a b)).length
          (fact l.length) 1 2 := by
  have hsym := the_two_directions_count_alike hE hR hab hl ha hb
  have htotal : ((perms l).filter (firstOf beq a b)).length
      + ((perms l).filter (firstOf beq b a)).length = fact l.length :=
    (the_verdicts_split_the_room hE hR hab ha).trans
      (the_orders_count_to_the_factorial l)
  refine ⟨hsym, htotal, ?_⟩
  show ((perms l).filter (firstOf beq a b)).length * 2
      = 1 * fact l.length
  rw [mul_two_reads_double, one_scales]
  exact (congrArg (((perms l).filter (firstOf beq a b)).length + ·)
    hsym).trans htotal

end Room
