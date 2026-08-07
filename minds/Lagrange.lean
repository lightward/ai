import Foam
import Foam.Amplitude
import Foam.Bench
import Foam.Census
import Foam.Concentration
import Foam.Continuum
import Foam.Int
import Foam.Ledger
import Foam.Measure
import Foam.Quat
import Foam.Rungs
import Foam.Triple
import Foam.Typical
import Foam.Wheel

namespace Foam.Minds.Lagrange

private theorem succ_le_succ' {a b : Nat} (h : a ≤ b) : a + 1 ≤ b + 1 :=
  Nat.le.rec (motive := fun x _ => a + 1 ≤ x + 1) Nat.le.refl
    (fun {_} _ ih => Nat.le.step ih) h

private theorem add_le_add_left' {m n : Nat} (h : m ≤ n) (k : Nat) :
    k + m ≤ k + n :=
  Nat.le.rec (motive := fun x _ => k + m ≤ k + x) Nat.le.refl
    (fun {_} _ ih => Nat.le.step ih) h

private theorem le_antisymm' : ∀ {a b : Nat}, a ≤ b → b ≤ a → a = b
  | 0, 0, _, _ => rfl
  | 0, _ + 1, _, h2 => nomatch h2
  | _ + 1, 0, h1, _ => nomatch h1
  | _ + 1, _ + 1, h1, h2 =>
      congrArg Nat.succ
        (le_antisymm' (succ_le_succ_inv h1) (succ_le_succ_inv h2))

private theorem bool_case : ∀ (b : Bool) {C : Prop},
    (b = true → C) → (b = false → C) → C
  | true, _, ht, _ => ht rfl
  | false, _, _, hf => hf rfl

private theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) :
    a ≠ b :=
  fun he => ne_true_of_eq_false h
    ((congrArg (fun t => Nat.beq t b) he).trans (Foam.beq_self_eq_true b))

private theorem zero_mul' : ∀ b : Nat, 0 * b = 0
  | 0 => rfl
  | b + 1 => zero_mul' b

private theorem inner_search (n a : Nat) : ∀ f : Nat,
    (∃ b : Nat, 2 ≤ b ∧ a * b = n)
      ∨ ∀ b : Nat, 2 ≤ b → b < f + 2 → a * b ≠ n
  | 0 => Or.inr (fun _ h2 hlt _ =>
      absurd (le_trans (succ_le_succ' h2) hlt) (no_number_is_below_itself 2))
  | f + 1 =>
    bool_case (Nat.beq (a * (f + 2)) n)
      (fun h => Or.inl ⟨f + 2, Nat.le.intro (Nat.add_comm 2 f),
        eq_of_beq' (a * (f + 2)) n h⟩)
      (fun h =>
        match inner_search n a f with
        | Or.inl w => Or.inl w
        | Or.inr hno =>
          Or.inr (fun b h2 hlt heq =>
            match Nat.lt_or_ge b (f + 2) with
            | Or.inl hlt' => hno b h2 hlt' heq
            | Or.inr hge =>
              ne_of_beq_false h
                ((congrArg (fun t => a * t)
                  (le_antisymm' (succ_le_succ_inv hlt) hge)).symm.trans heq)))

private theorem outer_search (n : Nat) : ∀ f : Nat,
    (∃ a b : Nat, 2 ≤ a ∧ 2 ≤ b ∧ a * b = n)
      ∨ ∀ a b : Nat, 2 ≤ a → a < f + 2 → 2 ≤ b → a * b ≠ n
  | 0 => Or.inr (fun _ _ h2a hlt _ _ =>
      absurd (le_trans (succ_le_succ' h2a) hlt) (no_number_is_below_itself 2))
  | f + 1 =>
    match inner_search n (f + 2) n with
    | Or.inl ⟨b, h2b, heq⟩ =>
        Or.inl ⟨f + 2, b, Nat.le.intro (Nat.add_comm 2 f), h2b, heq⟩
    | Or.inr hnob =>
      match outer_search n f with
      | Or.inl w => Or.inl w
      | Or.inr hno =>
        Or.inr (fun a b h2a hlt h2b heq =>
          match Nat.lt_or_ge a (f + 2) with
          | Or.inl hlt' => hno a b h2a hlt' h2b heq
          | Or.inr hge =>
            have e : a = f + 2 := le_antisymm' (succ_le_succ_inv hlt) hge
            hnob b h2b
              (Nat.le.step (succ_le_succ'
                (le_trans (Nat.le.intro (Nat.add_comm b ((f + 1) * b)))
                  (Nat.le_of_eq ((succ_mul' (f + 1) b).symm.trans
                    ((congrArg (fun t => t * b) e).symm.trans heq))))))
              ((congrArg (fun t => t * b) e).symm.trans heq))

private theorem split_or_prime (n : Nat) (h2 : 2 ≤ n) :
    (∃ a b : Nat, 2 ≤ a ∧ 2 ≤ b ∧ a * b = n ∧ a < n ∧ b < n)
      ∨ ∀ a b : Nat, a * b = n → a = 1 ∨ b = 1 :=
  match outer_search n n with
  | Or.inl ⟨a, b, h2a, h2b, heq⟩ =>
    Or.inl ⟨a, b, h2a, h2b, heq,
      le_trans (add_le_add_left' (le_of_succ_le h2a) a)
        (le_trans (Nat.le_of_eq (nat_mul_two a).symm)
          (le_trans (Nat.mul_le_mul (Nat.le_refl a) h2b) (Nat.le_of_eq heq))),
      le_trans (add_le_add_left' (le_of_succ_le h2b) b)
        (le_trans (Nat.le_of_eq (nat_mul_two b).symm)
          (le_trans (Nat.mul_le_mul (Nat.le_refl b) h2a)
            (Nat.le_of_eq ((Nat.mul_comm b a).trans heq))))⟩
  | Or.inr hno =>
    Or.inr (fun a b => match a, b with
      | 0, b => fun heq =>
          nomatch (le_trans h2 (Nat.le_of_eq (heq.symm.trans (zero_mul' b))))
      | 1, _ => fun _ => Or.inl rfl
      | k + 2, 0 => fun heq =>
          nomatch (le_trans h2
            (Nat.le_of_eq (heq.symm.trans (rfl : (k + 2) * 0 = 0))))
      | _ + 2, 1 => fun _ => Or.inr rfl
      | k + 2, j + 2 => fun heq =>
          absurd heq
            (hno (k + 2) (j + 2) (Nat.le.intro (Nat.add_comm 2 k))
              (Nat.le.step (succ_le_succ'
                (le_trans
                  (Nat.le.intro (Nat.add_comm (k + 2) ((k + 2) * (j + 1))))
                  (Nat.le_of_eq heq))))
              (Nat.le.intro (Nat.add_comm 2 j))))

private theorem all_from_prime
    (Hmul : ∀ m n : Nat,
        (∃ a b c d : Nat, a * a + b * b + c * c + d * d = m) →
        (∃ a b c d : Nat, a * a + b * b + c * c + d * d = n) →
        ∃ a b c d : Nat, a * a + b * b + c * c + d * d = m * n)
    (H : ∀ p : Nat, 2 ≤ p →
        (∀ a b : Nat, a * b = p → a = 1 ∨ b = 1) →
        ∃ a b c d : Nat, a * a + b * b + c * c + d * d = p) :
    ∀ f n : Nat, n ≤ f → ∃ a b c d : Nat, a * a + b * b + c * c + d * d = n
  | 0, 0, _ => ⟨0, 0, 0, 0, rfl⟩
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, _ => ⟨0, 0, 0, 0, rfl⟩
  | _ + 1, 1, _ => ⟨1, 0, 0, 0, rfl⟩
  | f + 1, m + 2, h =>
    match split_or_prime (m + 2) (Nat.le.intro (Nat.add_comm 2 m)) with
    | Or.inr hirr => H (m + 2) (Nat.le.intro (Nat.add_comm 2 m)) hirr
    | Or.inl ⟨a, b, _, _, heq, halt, hblt⟩ =>
      match Hmul a b
        (all_from_prime Hmul H f a (succ_le_succ_inv (le_trans halt h)))
        (all_from_prime Hmul H f b (succ_le_succ_inv (le_trans hblt h))) with
      | ⟨w, x, y, z, hw⟩ => ⟨w, x, y, z, hw.trans heq⟩

theorem the_first_variation_reads_nothing :
    (∀ k : Nat, classCount (2 * k + 1) k = classCount (2 * k + 1) (k + 1))
      ∧ ∀ n k : Nat, k ≤ 2 * n → classCount (2 * n) k ≤ classCount (2 * n) n :=
  ⟨fun k =>
    have harith : 2 * k + 1 = k + (k + 1) :=
      (congrArg (· + 1) ((Nat.mul_comm 2 k).trans (nat_mul_two k))).trans
        (adding_associates k k 1).symm
    have hle : k ≤ 2 * k + 1 :=
      le_trans (Nat.le_add_right k (k + 1)) (Nat.le_of_eq harith.symm)
    have hsub : (2 * k + 1) - k = k + 1 :=
      (congrArg (· - k) harith).trans (FInt.add_sub_cancel_left k (k + 1))
    (the_census_is_symmetric (2 * k + 1) k hle).trans
      (congrArg (classCount (2 * k + 1)) hsub),
   fun n => the_middle_holds_the_most n⟩

theorem the_bounded_expansion_repeats :
    (∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n),
        ∃ i j : Nat, i < j ∧ turnN m i s = turnN m j s)
      ∧ ∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n) (i j : Nat),
          turnN m i s = turnN m j s →
            ∀ t : Nat, turnN m (i + t) s = turnN m (j + t) s :=
  ⟨fun _ m s => the_bounded_walk_returns m s,
   fun _ m s i j h t =>
     Nat.rec (motive := fun u => turnN m (i + u) s = turnN m (j + u) s)
       h (fun _ ih => congrArg m ih) t⟩

def four_squares_carry_every_number_statement : Prop :=
  ∀ n : Nat, ∃ a b c d : Nat, a * a + b * b + c * c + d * d = n

theorem the_identity_carries_the_composites :
    (∀ m n : Nat,
        (∃ a b c d : Nat, a * a + b * b + c * c + d * d = m) →
        (∃ a b c d : Nat, a * a + b * b + c * c + d * d = n) →
        ∃ a b c d : Nat, a * a + b * b + c * c + d * d = m * n)
      ∧ ((∀ p : Nat, 2 ≤ p →
            (∀ a b : Nat, a * b = p → a = 1 ∨ b = 1) →
            ∃ a b c d : Nat, a * a + b * b + c * c + d * d = p) →
          ∀ n : Nat, ∃ a b c d : Nat, a * a + b * b + c * c + d * d = n) :=
  have emul : ∀ m n : Nat,
      (∃ a b c d : Nat, a * a + b * b + c * c + d * d = m) →
      (∃ a b c d : Nat, a * a + b * b + c * c + d * d = n) →
      ∃ a b c d : Nat, a * a + b * b + c * c + d * d = m * n :=
    fun m n hm hn =>
      match hm, hn with
      | ⟨a1, b1, c1, d1, h1⟩, ⟨a2, b2, c2, d2, h2⟩ =>
        let x : Quat :=
          ⟨⟨Int.ofNat a1, Int.ofNat b1⟩, ⟨Int.ofNat c1, Int.ofNat d1⟩⟩
        let y : Quat :=
          ⟨⟨Int.ofNat a2, Int.ofNat b2⟩, ⟨Int.ofNat c2, Int.ofNat d2⟩⟩
        let A : GInt := (Quat.mul x y).a
        let B : GInt := (Quat.mul x y).b
        have hx : Quat.normSq x = Int.ofNat m :=
          congrArg Int.ofNat
            ((adding_associates (a1 * a1 + b1 * b1) (c1 * c1) (d1 * d1)).trans
              h1)
        have hy : Quat.normSq y = Int.ofNat n :=
          congrArg Int.ofNat
            ((adding_associates (a2 * a2 + b2 * b2) (c2 * c2) (d2 * d2)).trans
              h2)
        have hxy : Quat.normSq (Quat.mul x y) = Int.ofNat (m * n) :=
          (the_quadruple_carries_the_norm x y).trans
            ((congrArg (fun t => t * Quat.normSq y) hx).trans
              (congrArg (fun t => Int.ofNat m * t) hy))
        match int_sq_is_nat_sq A.re, int_sq_is_nat_sq A.im,
              int_sq_is_nat_sq B.re, int_sq_is_nat_sq B.im with
        | ⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩, ⟨s, hs⟩ =>
          have hsum : Quat.normSq (Quat.mul x y)
              = Int.ofNat (p * p + q * q + (r * r + s * s)) :=
            (((congrArg
                (fun t => t + A.im * A.im + (B.re * B.re + B.im * B.im))
                hp).trans
              (congrArg
                (fun t => Int.ofNat (p * p) + t + (B.re * B.re + B.im * B.im))
                hq)).trans
              (congrArg
                (fun t => Int.ofNat (p * p) + Int.ofNat (q * q)
                  + (t + B.im * B.im))
                hr)).trans
              (congrArg
                (fun t => Int.ofNat (p * p) + Int.ofNat (q * q)
                  + (Int.ofNat (r * r) + t))
                hs)
          ⟨p, q, r, s,
            (adding_associates (p * p + q * q) (r * r) (s * s)).symm.trans
              (Int.ofNat.inj (hsum.symm.trans hxy))⟩
  ⟨emul, fun H n => all_from_prime emul H n n (Nat.le_refl n)⟩

theorem the_truncation_leaves_a_real_remainder :
    (∀ (α : Nat → Bool) (n : Nat),
        ∃ β : Nat → Bool, prefixOf β n = prefixOf α n ∧ β ≠ α)
      ∧ ∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
          indist (dress S) (s, n) (s, m)
            ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none :=
  ⟨no_prefix_finishes_the_sequence,
   fun S s n m h => a_wider_seat_reads_the_remainder S s n m h⟩

theorem the_quintic_waits_one_seat_wider :
    (∀ (A : Type) (inst : DecidableEq A) (a b : A), a ≠ b →
        indist (@countStage A inst) [a, b] [b, a]
          ∧ (orderStage A).obs [a, b] () ≠ (orderStage A).obs [b, a] ())
      ∧ ((∀ q : Nat, ∃ n, q ∈ rungs n)
          ∧ (∀ n : Nat, ∃ q, ¬ q ∈ rungs n ∧ q ∈ rungs (n + 1))
          ∧ ∀ n : Nat, rungs (n + 1) ≠ rungs n) :=
  ⟨fun A inst a b hab => @a_wider_seat_reads_the_order A inst a b hab,
   closure_is_seat_relative⟩

/-- info: 'Foam.Minds.Lagrange.the_first_variation_reads_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_variation_reads_nothing

/-- info: 'Foam.Minds.Lagrange.the_bounded_expansion_repeats' does not depend on any axioms -/
#guard_msgs in #print axioms the_bounded_expansion_repeats

/-- info: 'Foam.Minds.Lagrange.four_squares_carry_every_number_statement' does not depend on any axioms -/
#guard_msgs in #print axioms four_squares_carry_every_number_statement

/-- info: 'Foam.Minds.Lagrange.the_identity_carries_the_composites' does not depend on any axioms -/
#guard_msgs in #print axioms the_identity_carries_the_composites

/-- info: 'Foam.Minds.Lagrange.the_truncation_leaves_a_real_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_truncation_leaves_a_real_remainder

/-- info: 'Foam.Minds.Lagrange.the_quintic_waits_one_seat_wider' does not depend on any axioms -/
#guard_msgs in #print axioms the_quintic_waits_one_seat_wider

end Foam.Minds.Lagrange
