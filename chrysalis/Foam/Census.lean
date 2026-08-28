import Foam.Marks

namespace Foam

def classCount (n k : Nat) : Nat :=
  (List.filter (fun w => Nat.beq (freq w true) k) (book n)).length

theorem filter_append' {A : Type} (q : A → Bool) :
    ∀ X Y : List A, List.filter q (X ++ Y) = List.filter q X ++ List.filter q Y
  | [], _ => rfl
  | x :: X, Y => by
      show List.filter q (x :: (X ++ Y)) = List.filter q (x :: X) ++ List.filter q Y
      cases hq : q x with
      | true =>
          rw [List.filter_cons_of_pos (l := X ++ Y) hq,
              List.filter_cons_of_pos (l := X) hq,
              filter_append' q X Y]
          rfl
      | false =>
          rw [List.filter_cons_of_neg (l := X ++ Y) (ne_true_of_eq_false hq),
              List.filter_cons_of_neg (l := X) (ne_true_of_eq_false hq),
              filter_append' q X Y]

theorem filter_pointwise {A : Type} {p q : A → Bool} (h : ∀ a, p a = q a) :
    ∀ l : List A, List.filter p l = List.filter q l
  | [] => rfl
  | a :: l => by
      cases hq : q a with
      | true =>
          rw [List.filter_cons_of_pos (p := p) ((h a).trans hq),
              List.filter_cons_of_pos (p := q) hq, filter_pointwise h l]
      | false =>
          rw [List.filter_cons_of_neg (p := p)
                (ne_true_of_eq_false ((h a).trans hq)),
              List.filter_cons_of_neg (p := q) (ne_true_of_eq_false hq),
              filter_pointwise h l]

theorem length_filter_map {A B : Type} (g : A → B) (q : B → Bool) :
    ∀ ws : List A,
      (List.filter q (ws.map g)).length
        = (List.filter (fun a => q (g a)) ws).length
  | [] => rfl
  | a :: ws => by
      show (List.filter q (g a :: ws.map g)).length
          = (List.filter (fun a => q (g a)) (a :: ws)).length
      cases hq : q (g a) with
      | true =>
          rw [List.filter_cons_of_pos (l := ws.map g) hq,
              List.filter_cons_of_pos (p := fun a => q (g a)) (l := ws) hq]
          show (List.filter q (ws.map g)).length + 1
              = (List.filter (fun a => q (g a)) ws).length + 1
          rw [length_filter_map g q ws]
      | false =>
          rw [List.filter_cons_of_neg (l := ws.map g) (ne_true_of_eq_false hq),
              List.filter_cons_of_neg (p := fun a => q (g a)) (l := ws)
                (ne_true_of_eq_false hq),
              length_filter_map g q ws]

theorem the_census_stacks (n k : Nat) :
    classCount (n + 1) (k + 1) = classCount n k + classCount n (k + 1) := by
  have htrue : ∀ a : List Bool,
      Nat.beq (freq (true :: a) true) (k + 1) = Nat.beq (freq a true) k :=
    fun a => by
      show Nat.beq (1 + freq a true) (k + 1) = Nat.beq (freq a true) k
      rw [Nat.add_comm 1 (freq a true)]
      rfl
  have hfalse : ∀ a : List Bool,
      Nat.beq (freq (false :: a) true) (k + 1)
        = Nat.beq (freq a true) (k + 1) :=
    fun a => by
      show Nat.beq (0 + freq a true) (k + 1) = Nat.beq (freq a true) (k + 1)
      rw [nothing_added]
  show (List.filter (fun w => Nat.beq (freq w true) (k + 1))
        ((book n).map (true :: ·) ++ (book n).map (false :: ·))).length
      = classCount n k + classCount n (k + 1)
  rw [filter_append', len_append, length_filter_map, length_filter_map,
      filter_pointwise htrue (book n), filter_pointwise hfalse (book n)]
  rfl

theorem the_census_starts_at_one : ∀ n : Nat, classCount n 0 = 1
  | 0 => rfl
  | n + 1 => by
      have htrue : ∀ a : List Bool,
          Nat.beq (freq (true :: a) true) 0 = false :=
        fun a => by
          show Nat.beq (1 + freq a true) 0 = false
          rw [Nat.add_comm 1 (freq a true)]
          rfl
      have hfalse : ∀ a : List Bool,
          Nat.beq (freq (false :: a) true) 0 = Nat.beq (freq a true) 0 :=
        fun a => by
          show Nat.beq (0 + freq a true) 0 = Nat.beq (freq a true) 0
          rw [nothing_added]
      show (List.filter (fun w => Nat.beq (freq w true) 0)
            ((book n).map (true :: ·) ++ (book n).map (false :: ·))).length
          = 1
      rw [filter_append', len_append, length_filter_map, length_filter_map,
          filter_pointwise htrue (book n), filter_pointwise hfalse (book n),
          filter_none _ (fun _ => rfl) (book n)]
      show 0 + classCount n 0 = 1
      rw [nothing_added, the_census_starts_at_one n]

theorem the_census_ends :
    ∀ n k : Nat, n < k → classCount n k = 0
  | 0, k + 1, _ => rfl
  | 0, 0, h => nomatch h
  | n + 1, 0, h => nomatch h
  | n + 1, k + 1, h => by
      have htrue : ∀ a : List Bool,
          Nat.beq (freq (true :: a) true) (k + 1) = Nat.beq (freq a true) k :=
        fun a => by
          show Nat.beq (1 + freq a true) (k + 1) = Nat.beq (freq a true) k
          rw [Nat.add_comm 1 (freq a true)]
          rfl
      have hfalse : ∀ a : List Bool,
          Nat.beq (freq (false :: a) true) (k + 1)
            = Nat.beq (freq a true) (k + 1) :=
        fun a => by
          show Nat.beq (0 + freq a true) (k + 1) = Nat.beq (freq a true) (k + 1)
          rw [nothing_added]
      show (List.filter (fun w => Nat.beq (freq w true) (k + 1))
            ((book n).map (true :: ·) ++ (book n).map (false :: ·))).length
          = 0
      rw [filter_append', len_append, length_filter_map, length_filter_map,
          filter_pointwise htrue (book n), filter_pointwise hfalse (book n)]
      show classCount n k + classCount n (k + 1) = 0
      rw [the_census_ends n k (succ_le_succ_inv h),
          the_census_ends n (k + 1) (le_of_succ_le h)]

theorem the_census_ends_at_one : ∀ n : Nat, classCount n n = 1
  | 0 => rfl
  | n + 1 => by
      rw [the_census_stacks n n, the_census_ends_at_one n,
          the_census_ends n (n + 1) (Nat.le_refl (n + 1))]

theorem the_census_is_symmetric :
    ∀ n k : Nat, k ≤ n → classCount n k = classCount n (n - k)
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | n + 1, 0, _ => by
      rw [the_census_starts_at_one (n + 1)]
      show 1 = classCount (n + 1) (n + 1)
      rw [the_census_ends_at_one (n + 1)]
  | n + 1, k + 1, h => by
      have hk : k ≤ n := succ_le_succ_inv h
      cases Nat.lt_or_ge k n with
      | inl hlt =>
          obtain ⟨d, hd⟩ := Nat.le.dest hlt
          have hnk : (n + 1) - (k + 1) = d + 1 := by
            rw [Nat.succ_sub_succ, ← hd,
                show k + 1 + d = k + (1 + d) from
                  (adding_associates k 1 d).symm,
                FInt.add_sub_cancel_left, Nat.add_comm 1 d]
          have hnk' : n - (k + 1) = d := by
            rw [← hd,
                show k + 1 + d = (k + 1) + d from rfl,
                FInt.add_sub_cancel_left]
          have hnk'' : n - k = d + 1 := by
            rw [← hd,
                show k + 1 + d = k + (1 + d) from
                  (adding_associates k 1 d).symm,
                FInt.add_sub_cancel_left, Nat.add_comm 1 d]
          rw [hnk, the_census_stacks n k, the_census_stacks n d,
              the_census_is_symmetric n k hk,
              the_census_is_symmetric n (k + 1) (Nat.le.intro hd),
              hnk', hnk'', Nat.add_comm (classCount n (d + 1)) (classCount n d)]
      | inr hge =>
          have hkn : k = n := Nat.le_antisymm hk hge
          subst hkn
          rw [Nat.sub_self, the_census_starts_at_one (k + 1),
              the_census_ends_at_one (k + 1)]

theorem the_census_rises_to_the_middle :
    ∀ n k : Nat, 2 * k + 1 ≤ n → classCount n k ≤ classCount n (k + 1)
  | 0, _, h => nomatch h
  | n + 1, 0, _ => by
      rw [the_census_starts_at_one (n + 1)]
      show (1 : Nat) ≤ classCount (n + 1) (0 + 1)
      rw [the_census_stacks n 0, the_census_starts_at_one n]
      exact Nat.le_add_right 1 (classCount n (0 + 1))
  | n + 1, k + 1, h => by
      have h' : (2 * k + 2) + 1 ≤ n + 1 := by
        rw [show (2 * k + 2) + 1 = 2 * (k + 1) + 1 from by
              rw [Nat.left_distrib, Nat.mul_one]]
        exact h
      have hn : 2 * k + 2 ≤ n := succ_le_succ_inv h'
      cases Nat.lt_or_ge n (2 * k + 3) with
      | inr hge =>
          rw [the_census_stacks n k, the_census_stacks n (k + 1)]
          exact Nat.add_le_add
            (the_census_rises_to_the_middle n k
              (le_of_succ_le (le_of_succ_le hge)))
            (the_census_rises_to_the_middle n (k + 1)
              (show 2 * (k + 1) + 1 ≤ n from by
                rw [Nat.left_distrib, Nat.mul_one]
                exact hge))
      | inl hlt =>
          have hn' : n = 2 * k + 2 :=
            Nat.le_antisymm (succ_le_succ_inv hlt) hn
          subst hn'
          have harith : (k + 1) + (k + 2) = 2 * k + 2 + 1 := by
            rw [Nat.mul_comm 2 k, nat_mul_two,
                adding_associates (k + 1) k 2, succ_adds k k]
          have hle : k + 1 ≤ 2 * k + 2 + 1 :=
            harith ▸ Nat.le_add_right (k + 1) (k + 2)
          have hsub : (2 * k + 2 + 1) - (k + 1) = k + 2 := by
            rw [Nat.succ_sub_succ, Nat.mul_comm 2 k, nat_mul_two,
                show (k + k) + 2 = k + (k + 2) from
                  (adding_associates k k 2).symm,
                FInt.add_sub_cancel_left]
          rw [the_census_is_symmetric (2 * k + 2 + 1) (k + 1) hle, hsub]
          exact Nat.le_refl _

theorem add_mul' (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

theorem sub_add_vanishes : ∀ n d : Nat, n - (n + d) = 0
  | n, 0 => Nat.sub_self n
  | n, d + 1 => by
      show n - ((n + d) + 1) = 0
      rw [Nat.sub_succ, sub_add_vanishes n d]
      rfl

theorem the_census_absorbs :
    ∀ n k : Nat, classCount n k * (n - k) = classCount n (k + 1) * (k + 1)
  | 0, 0 => rfl
  | 0, k + 1 => by
      rw [the_census_ends 0 (k + 1) (Nat.zero_lt_succ k),
          the_census_ends 0 (k + 1 + 1) (Nat.zero_lt_succ (k + 1)),
          Nat.zero_mul, Nat.zero_mul]
  | n + 1, 0 => by
      have h : classCount n 0 * (n - 0) = classCount n (0 + 1) * 1 :=
        the_census_absorbs n 0
      rw [the_census_starts_at_one n, Nat.one_mul, Nat.mul_one] at h
      show classCount (n + 1) 0 * ((n + 1) - 0) = classCount (n + 1) (0 + 1) * 1
      rw [the_census_starts_at_one (n + 1), Nat.one_mul, Nat.mul_one,
          the_census_stacks n 0, the_census_starts_at_one n, ← h]
      show n + 1 = 1 + n
      rw [Nat.add_comm 1 n]
  | n + 1, k + 1 => by
      cases Nat.lt_or_ge k n with
      | inl hlt =>
          obtain ⟨d, hd⟩ := Nat.le.dest hlt
          have e1 : n - k = d + 1 := by
            rw [← hd, Nat.add_assoc k 1 d, Nat.add_comm 1 d,
                FInt.add_sub_cancel_left]
          have e2 : n - (k + 1) = d := by
            rw [← hd, FInt.add_sub_cancel_left]
          have ih1 : classCount n k * (d + 1)
              = classCount n (k + 1) * (k + 1) := by
            rw [← e1]
            exact the_census_absorbs n k
          have ih2 : classCount n (k + 1) * d
              = classCount n (k + 1 + 1) * (k + 1 + 1) := by
            rw [← e2]
            exact the_census_absorbs n (k + 1)
          rw [Nat.succ_sub_succ, e1, the_census_stacks n k,
              the_census_stacks n (k + 1),
              add_mul' (classCount n k) (classCount n (k + 1)) (d + 1),
              add_mul' (classCount n (k + 1)) (classCount n (k + 1 + 1))
                (k + 1 + 1),
              ih1, ← ih2, ← Nat.mul_add (classCount n (k + 1)) (k + 1) (d + 1),
              ← Nat.mul_add (classCount n (k + 1)) (k + 1 + 1) d,
              succ_adds (k + 1) d]
          rfl
      | inr hge =>
          have hz1 : classCount n (k + 1) = 0 :=
            the_census_ends n (k + 1) (Nat.succ_le_succ hge)
          have hz2 : classCount n (k + 1 + 1) = 0 :=
            the_census_ends n (k + 1 + 1)
              (Nat.le_succ_of_le (Nat.succ_le_succ hge))
          have hz3 : n - k = 0 := by
            obtain ⟨d, hd⟩ := Nat.le.dest hge
            rw [← hd, sub_add_vanishes n d]
          rw [Nat.succ_sub_succ, hz3, the_census_stacks n k,
              the_census_stacks n (k + 1), hz1, hz2]
          show (classCount n k + 0) * 0 = 0 * (k + 1 + 1)
          rw [Nat.zero_mul]
          rfl

theorem the_census_rises_to_the_lean (t f n k : Nat) (hk : k < n)
    (h : (k + 1) * (t + f) ≤ (n + 1) * t) :
    classCount n k * (t ^ k * f ^ (n - k))
      ≤ classCount n (k + 1) * (t ^ (k + 1) * f ^ (n - (k + 1))) := by
  obtain ⟨d, hd⟩ := Nat.le.dest hk
  have e1 : n - k = d + 1 := by
    rw [← hd, Nat.add_assoc k 1 d, Nat.add_comm 1 d, FInt.add_sub_cancel_left]
  have e2 : n - (k + 1) = d := by
    rw [← hd, FInt.add_sub_cancel_left]
  have key : (k + 1) * f ≤ (d + 1) * t := by
    apply cancel_add_left ((k + 1) * t)
    rw [← Nat.mul_add (k + 1) t f, ← add_mul' (k + 1) (d + 1) t,
        show (k + 1) + (d + 1) = (k + 1 + d) + 1 from rfl, hd]
    exact h
  have habs : classCount n k * (d + 1) = classCount n (k + 1) * (k + 1) := by
    rw [← e1]
    exact the_census_absorbs n k
  have h3 : classCount n k * ((k + 1) * f)
      ≤ classCount n k * ((d + 1) * t) :=
    Nat.mul_le_mul_left (classCount n k) key
  rw [Nat.mul_comm (k + 1) f, ← FInt.nat_mul_assoc (classCount n k) f (k + 1),
      ← FInt.nat_mul_assoc (classCount n k) (d + 1) t, habs,
      FInt.nat_mul_assoc (classCount n (k + 1)) (k + 1) t,
      Nat.mul_comm (k + 1) t,
      ← FInt.nat_mul_assoc (classCount n (k + 1)) t (k + 1)] at h3
  have hstep : classCount n k * f ≤ classCount n (k + 1) * t :=
    Nat.le_of_mul_le_mul_right h3 (Nat.zero_lt_succ k)
  rw [e1, e2]
  show classCount n k * (t ^ k * (f ^ d * f))
      ≤ classCount n (k + 1) * ((t ^ k * t) * f ^ d)
  rw [Nat.mul_comm (f ^ d) f, ← FInt.nat_mul_assoc (t ^ k) f (f ^ d),
      Nat.mul_comm (t ^ k) f, FInt.nat_mul_assoc f (t ^ k) (f ^ d),
      ← FInt.nat_mul_assoc (classCount n k) f (t ^ k * f ^ d),
      Nat.mul_comm (t ^ k) t, FInt.nat_mul_assoc t (t ^ k) (f ^ d),
      ← FInt.nat_mul_assoc (classCount n (k + 1)) t (t ^ k * f ^ d)]
  exact Nat.mul_le_mul_right (t ^ k * f ^ d) hstep

/-- info: 'Foam.filter_append'' does not depend on any axioms -/
#guard_msgs in #print axioms filter_append'

/-- info: 'Foam.filter_pointwise' does not depend on any axioms -/
#guard_msgs in #print axioms filter_pointwise

/-- info: 'Foam.length_filter_map' does not depend on any axioms -/
#guard_msgs in #print axioms length_filter_map

/-- info: 'Foam.the_census_stacks' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_stacks

/-- info: 'Foam.the_census_starts_at_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_starts_at_one

/-- info: 'Foam.the_census_ends' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_ends

/-- info: 'Foam.the_census_ends_at_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_ends_at_one

/-- info: 'Foam.the_census_is_symmetric' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_is_symmetric

/-- info: 'Foam.the_census_rises_to_the_middle' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_rises_to_the_middle

/-- info: 'Foam.add_mul'' does not depend on any axioms -/
#guard_msgs in #print axioms add_mul'

/-- info: 'Foam.sub_add_vanishes' does not depend on any axioms -/
#guard_msgs in #print axioms sub_add_vanishes

/-- info: 'Foam.the_census_absorbs' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_absorbs

/-- info: 'Foam.the_census_rises_to_the_lean' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_rises_to_the_lean

end Foam