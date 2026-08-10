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
import Foam.Round
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

private theorem nat_swap_mid (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) :=
  (Nat.add_assoc a b (c + d)).trans
    ((congrArg (a + ·)
      ((Nat.add_assoc b c d).symm.trans
        ((congrArg (· + d) (Nat.add_comm b c)).trans (Nat.add_assoc c b d)))).trans
      (Nat.add_assoc a c (b + d)).symm)

private theorem add_left_cancel' : ∀ (k : Nat) {a b : Nat}, k + a = k + b → a = b
  | 0, a, b, h => (nothing_added a).symm.trans (h.trans (nothing_added b))
  | k + 1, _, _, h =>
      add_left_cancel' k
        (Nat.succ.inj ((succ_adds k _).symm.trans (h.trans (succ_adds k _))))

private theorem add_right_cancel' {a b : Nat} (k : Nat) (h : a + k = b + k) : a = b :=
  add_left_cancel' k ((Nat.add_comm k a).trans (h.trans (Nat.add_comm b k)))

private theorem mul_le_cancel_left {p a b : Nat} (hp : 1 ≤ p) (h : p * a ≤ p * b) : a ≤ b :=
  match Nat.lt_or_ge b a with
  | .inl hba =>
      absurd (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hba hp) h)
        (no_number_is_below_itself (p * b))
  | .inr hab => hab

private theorem mul_eq_cancel_left {p a b : Nat} (hp : 1 ≤ p) (h : p * a = p * b) : a = b :=
  le_antisymm' (mul_le_cancel_left hp (Nat.le_of_eq h))
    (mul_le_cancel_left hp (Nat.le_of_eq h.symm))

private theorem add_le_add' {a b c d : Nat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  le_trans (Nat.add_le_add_right h1 c) (add_le_add_left' h2 b)

private theorem double_inj : ∀ {x y : Nat}, x + x = y + y → x = y
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | x + 1, y + 1, h =>
      congrArg (· + 1)
        (double_inj
          (Nat.succ.inj
            ((succ_adds x x).symm.trans
              ((Nat.succ.inj h).trans (succ_adds y y)))))

private theorem dne : ∀ t s : Nat, t + t = (s + s) + 1 → False
  | 0, _, h => nomatch h
  | t + 1, 0, h =>
      nomatch ((succ_adds t t).symm.trans (Nat.succ.inj h))
  | t + 1, s + 1, h =>
      dne t s
        ((Nat.succ.inj
          ((succ_adds t t).symm.trans (Nat.succ.inj h))).trans
          (succ_adds s s))

private theorem par : ∀ a : Nat, ∃ k, a = k + k ∨ a = (k + k) + 1
  | 0 => ⟨0, .inl rfl⟩
  | a + 1 =>
      match par a with
      | ⟨k, .inl h⟩ => ⟨k, .inr (congrArg (· + 1) h)⟩
      | ⟨k, .inr h⟩ =>
          ⟨k + 1, .inl ((congrArg (· + 1) h).trans
            (congrArg (· + 1) (succ_adds k k).symm))⟩

private theorem add_eq_zero : ∀ {a b : Nat}, a + b = 0 → a = 0 ∧ b = 0
  | _, 0, h => ⟨h, rfl⟩
  | _, _ + 1, h => nomatch h

private theorem sq_zero : ∀ {u : Nat}, u * u = 0 → u = 0
  | 0, _ => rfl
  | _ + 1, h => nomatch h

private theorem sq_lt {x y : Nat} (h : x < y) : x * x < y * y :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt h) (Nat.le_refl x))
    (Nat.mul_lt_mul_of_pos_left h (Nat.lt_of_le_of_lt (Nat.zero_le x) h))

private theorem sq_expand (x s : Nat) :
    (x + s) * (x + s) = x * x + s * (x + (x + s)) :=
  (Nat.left_distrib (x + s) x s).trans
    ((congrArg (· + (x + s) * s)
        ((Nat.mul_comm (x + s) x).trans (Nat.left_distrib x x s))).trans
      ((congrArg ((x * x + x * s) + ·) (Nat.mul_comm (x + s) s)).trans
        ((Nat.add_assoc (x * x) (x * s) (s * (x + s))).trans
          ((congrArg (fun z => x * x + (z + s * (x + s))) (Nat.mul_comm x s)).trans
            (congrArg (x * x + ·) (Nat.left_distrib s x (x + s))).symm))))

private theorem dbl_sq (x : Nat) :
    (x + x) * (x + x) = (x * x + x * x) + (x * x + x * x) :=
  have e : (x + x) * x = x * x + x * x :=
    (Nat.mul_comm (x + x) x).trans (Nat.left_distrib x x x)
  (Nat.left_distrib (x + x) x x).trans
    ((congrArg (· + (x + x) * x) e).trans
      (congrArg ((x * x + x * x) + ·) e))

private theorem nat_mul_swap (a b c d : Nat) :
    (a * b) * (c * d) = (a * c) * (b * d) :=
  (FInt.nat_mul_assoc a b (c * d)).trans
    ((congrArg (a * ·)
        ((FInt.nat_mul_assoc b c d).symm.trans
          ((congrArg (· * d) (Nat.mul_comm b c)).trans (FInt.nat_mul_assoc c b d)))).trans
      (FInt.nat_mul_assoc a c (b * d)).symm)

private def EvP (n : Nat) : Prop := ∃ t, n = t + t

private def OdP (n : Nat) : Prop := ∃ t, n = (t + t) + 1

private theorem sq_ev {a x : Nat} (ha : a = x + x) : EvP (a * a) :=
  ⟨a * x, (congrArg (a * ·) ha).trans (Nat.left_distrib a x x)⟩

private theorem sq_od {a x : Nat} (ha : a = (x + x) + 1) : OdP (a * a) :=
  ⟨a * x + x,
    (congrArg (a * ·) ha).trans
      ((congrArg (· + a) (Nat.left_distrib a x x)).trans
        ((congrArg ((a * x + a * x) + ·) ha).trans
          ((adding_associates (a * x + a * x) (x + x) 1).trans
            (congrArg (· + 1) (nat_swap_mid (a * x) (a * x) x x)))))⟩

private theorem ev_add {m n : Nat} : EvP m → EvP n → EvP (m + n)
  | ⟨s, hs⟩, ⟨t, ht⟩ =>
      ⟨s + t, ((congrArg (· + n) hs).trans (congrArg ((s + s) + ·) ht)).trans
        (nat_swap_mid s s t t)⟩

private theorem ev_od {m n : Nat} : EvP m → OdP n → OdP (m + n)
  | ⟨s, hs⟩, ⟨t, ht⟩ =>
      ⟨s + t, ((congrArg (· + n) hs).trans (congrArg ((s + s) + ·) ht)).trans
        ((adding_associates (s + s) (t + t) 1).trans
          (congrArg (· + 1) (nat_swap_mid s s t t)))⟩

private theorem od_ev {m n : Nat} (hm : OdP m) (hn : EvP n) : OdP (m + n) :=
  Nat.add_comm n m ▸ ev_od hn hm

private theorem od_od {m n : Nat} : OdP m → OdP n → EvP (m + n)
  | ⟨s, hs⟩, ⟨t, ht⟩ =>
      ⟨(s + t) + 1,
        ((congrArg (· + n) hs).trans (congrArg (((s + s) + 1) + ·) ht)).trans
          ((nat_swap_mid (s + s) 1 (t + t) 1).trans
            ((congrArg (· + (1 + 1)) (nat_swap_mid s s t t)).trans
              (nat_swap_mid (s + t) 1 (s + t) 1).symm))⟩

private theorem ev_ne_od {n : Nat} : EvP n → OdP n → False
  | ⟨t, ht⟩, ⟨s, hs⟩ => dne t s (ht.symm.trans hs)

private def dmq (m a : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (0, 0)
    (fun _ pr => if pr.2 + 1 < m then (pr.1, pr.2 + 1) else (pr.1 + 1, 0)) a

private theorem dmq_spec (m : Nat) (hm : 1 ≤ m) :
    ∀ a : Nat, a = (dmq m a).1 * m + (dmq m a).2 ∧ (dmq m a).2 < m
  | 0 => ⟨(zero_mul' m).symm, hm⟩
  | a + 1 =>
      match dmq_spec m hm a with
      | ⟨he, hlt⟩ =>
          match Nat.lt_or_ge ((dmq m a).2 + 1) m with
          | .inl h1 =>
              have E : dmq m (a + 1) = ((dmq m a).1, (dmq m a).2 + 1) := if_pos h1
              ⟨(congrArg (· + 1) he).trans
                (congrArg (fun pr => pr.1 * m + pr.2) E).symm,
               (congrArg Prod.snd E).symm ▸ h1⟩
          | .inr h2 =>
              have hnot : ¬ ((dmq m a).2 + 1 < m) :=
                fun hc => no_number_is_below_itself m (Nat.lt_of_le_of_lt h2 hc)
              have E : dmq m (a + 1) = ((dmq m a).1 + 1, 0) := if_neg hnot
              have hrm : (dmq m a).2 + 1 = m := le_antisymm' hlt h2
              ⟨((congrArg (· + 1) he).trans
                 ((congrArg ((dmq m a).1 * m + ·) hrm).trans
                   (succ_mul' (dmq m a).1 m).symm)).trans
                (congrArg (fun pr => pr.1 * m + pr.2) E).symm,
               (congrArg Prod.snd E).symm ▸ (show 0 < m from hm)⟩

private def pdvd (p n : Nat) : Prop := ∃ k, n = p * k

private theorem not_pdvd_of_lt {p n : Nat} (h1 : 1 ≤ n) (h2 : n < p) : ¬ pdvd p n
  | ⟨0, e⟩ => nomatch (e ▸ h1)
  | ⟨k + 1, e⟩ =>
      no_number_is_below_itself p
        (Nat.lt_of_le_of_lt
          (e.symm ▸ (show p ≤ p * (k + 1) from Nat.le_add_left p (p * k))) h2)

private theorem extract_dvd {p U V W : Nat} (hp : 1 ≤ p) (h : p * U = p * V + W) :
    ∃ t : Nat, W = p * t :=
  match Nat.le.dest (mul_le_cancel_left hp (Nat.le.intro h.symm)) with
  | ⟨t, ht⟩ =>
      ⟨t, add_left_cancel' (p * V)
        (h.symm.trans ((congrArg (p * ·) ht).symm.trans (Nat.left_distrib p V t)))⟩

private theorem euclid_small (p : Nat)
    (hirr : ∀ a b : Nat, a * b = p → a = 1 ∨ b = 1) :
    ∀ f n b : Nat, n ≤ f → n < p → pdvd p (n * b) → pdvd p n ∨ pdvd p b
  | _, 0, _, _, _, _ => Or.inl ⟨0, rfl⟩
  | 0, _ + 1, _, hf, _, _ => nomatch hf
  | f + 1, n + 1, b, hf, hnp, ⟨K, hK⟩ =>
      have hp1 : 1 ≤ p :=
        le_trans (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_of_lt hnp)
      match (dmq (n + 1) p).2,
          (dmq_spec (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) p).1,
          (dmq_spec (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) p).2 with
      | 0, hqr, _ =>
          match hirr ((dmq (n + 1) p).1) (n + 1) hqr.symm with
          | .inl hq1 =>
              have hEq : p = n + 1 :=
                (hqr.trans (congrArg (· * (n + 1)) hq1)).trans (Nat.one_mul (n + 1))
              (no_number_is_below_itself (n + 1) (hEq ▸ hnp)).elim
          | .inr hn1 =>
              Or.inr ⟨K,
                ((Nat.one_mul b).symm.trans
                  (congrArg (· * b) hn1).symm).trans hK⟩
      | r + 1, hqr, hr =>
          have hPB : p * b = p * ((dmq (n + 1) p).1 * K) + (r + 1) * b :=
            (congrArg (· * b) hqr).trans
              ((Nat.mul_comm ((dmq (n + 1) p).1 * (n + 1) + (r + 1)) b).trans
                ((Nat.left_distrib b ((dmq (n + 1) p).1 * (n + 1)) (r + 1)).trans
                  ((congrArg (· + b * (r + 1))
                      ((Nat.mul_comm b ((dmq (n + 1) p).1 * (n + 1))).trans
                        ((FInt.nat_mul_assoc ((dmq (n + 1) p).1) (n + 1) b).trans
                          ((congrArg ((dmq (n + 1) p).1 * ·) hK).trans
                            ((FInt.nat_mul_assoc ((dmq (n + 1) p).1) p K).symm.trans
                              ((congrArg (· * K)
                                  (Nat.mul_comm ((dmq (n + 1) p).1) p)).trans
                                (FInt.nat_mul_assoc p ((dmq (n + 1) p).1) K))))))).trans
                    (congrArg (p * ((dmq (n + 1) p).1 * K) + ·)
                      (Nat.mul_comm b (r + 1))))))
          match extract_dvd hp1 hPB with
          | ⟨t, hrb⟩ =>
              match euclid_small p hirr f (r + 1) b
                  (le_trans (Nat.le_of_lt_succ hr) (succ_le_succ_inv hf))
                  (Nat.lt_of_lt_of_le hr (Nat.le_of_lt hnp)) ⟨t, hrb⟩ with
              | .inl hd =>
                  ((not_pdvd_of_lt (Nat.succ_le_succ (Nat.zero_le r))
                    (Nat.lt_of_lt_of_le hr (Nat.le_of_lt hnp))) hd).elim
              | .inr hb => Or.inr hb

private theorem euclid (p : Nat) (hp1 : 1 ≤ p)
    (hirr : ∀ a b : Nat, a * b = p → a = 1 ∨ b = 1)
    (a b : Nat) : pdvd p (a * b) → pdvd p a ∨ pdvd p b
  | ⟨K, hK⟩ =>
      have ha : a = (dmq p a).1 * p + (dmq p a).2 := (dmq_spec p hp1 a).1
      have hs : (dmq p a).2 < p := (dmq_spec p hp1 a).2
      have hPB : p * K = p * ((dmq p a).1 * b) + (dmq p a).2 * b :=
        hK.symm.trans
          ((congrArg (· * b) ha).trans
            ((Nat.mul_comm ((dmq p a).1 * p + (dmq p a).2) b).trans
              ((Nat.left_distrib b ((dmq p a).1 * p) ((dmq p a).2)).trans
                ((congrArg (· + b * (dmq p a).2)
                    ((Nat.mul_comm b ((dmq p a).1 * p)).trans
                      ((congrArg (· * b) (Nat.mul_comm ((dmq p a).1) p)).trans
                        (FInt.nat_mul_assoc p ((dmq p a).1) b)))).trans
                  (congrArg (p * ((dmq p a).1 * b) + ·)
                    (Nat.mul_comm b ((dmq p a).2)))))))
      match extract_dvd hp1 hPB with
      | ⟨t, hsb⟩ =>
          match euclid_small p hirr ((dmq p a).2) ((dmq p a).2) b
              (Nat.le_refl _) hs ⟨t, hsb⟩ with
          | .inl ⟨k, hk⟩ =>
              Or.inl ⟨(dmq p a).1 + k,
                ha.trans
                  ((congrArg ((dmq p a).1 * p + ·) hk).trans
                    ((congrArg (· + p * k) (Nat.mul_comm ((dmq p a).1) p)).trans
                      (Nat.left_distrib p ((dmq p a).1) k).symm))⟩
          | .inr hb => Or.inr hb

private theorem fn_meet_or_apart {n : Nat} (g : Nat → Fin n) : ∀ k : Nat,
    (∃ i j : Nat, i < j ∧ j < k ∧ g i = g j) ∨ Apart ((rungs k).map g)
  | 0 => .inr .nil
  | k + 1 =>
      match fn_meet_or_apart g k with
      | .inl ⟨i, j, hij, hjk, he⟩ => .inl ⟨i, j, hij, Nat.le.step hjk, he⟩
      | .inr hap =>
          match mem_or_not (fun _ _ => inferInstance) (g k) ((rungs k).map g) with
          | .inl hmem =>
              match mem_map_back (rungs k) hmem with
              | ⟨i, hi, he⟩ =>
                  .inl ⟨i, k, the_walked_lie_below k i hi, Nat.le.refl, he⟩
          | .inr hno =>
              .inr (.cons (fun _ hb hvb => hno (hvb.symm ▸ hb)) hap)

private theorem fn_collides {n : Nat} (g : Nat → Fin n) :
    ∃ i j : Nat, i < j ∧ j < n + 1 ∧ g i = g j :=
  match fn_meet_or_apart g (n + 1) with
  | .inl w => w
  | .inr hap =>
      have hlen : (List.map g (rungs (n + 1))).length = n + 1 :=
        (len_map g (rungs (n + 1))).trans (rungs_length (n + 1))
      absurd
        (le_trans (Nat.le_of_eq hlen.symm)
          (apart_le n (List.map g (rungs (n + 1))) hap))
        (no_number_is_below_itself n)

private def resfn (p h : Nat) (hp : 1 ≤ p) (hph : p = (h + h) + 1) (i : Nat) : Fin p :=
  if i ≤ h then
    ⟨(dmq p (i * i)).2, (dmq_spec p hp (i * i)).2⟩
  else
    ⟨(h + h) - (dmq p ((i - (h + 1)) * (i - (h + 1)))).2,
     Nat.lt_of_le_of_lt (Nat.sub_le (h + h) _) (Nat.le_of_eq hph.symm)⟩

private theorem no_sq_collision (p h : Nat)
    (hirr : ∀ a b : Nat, a * b = p → a = 1 ∨ b = 1)
    (hph : p = (h + h) + 1) (x x' : Nat) (hlt : x < x') (hxh : x' ≤ h)
    (ht : (dmq p (x * x)).2 = (dmq p (x' * x')).2) : False :=
  have hp1 : 1 ≤ p := hph.symm ▸ Nat.succ_le_succ (Nat.zero_le (h + h))
  have he1 : x * x = (dmq p (x * x)).1 * p + (dmq p (x * x)).2 :=
    (dmq_spec p hp1 (x * x)).1
  have he2 : x' * x' = (dmq p (x' * x')).1 * p + (dmq p (x * x)).2 :=
    ((dmq_spec p hp1 (x' * x')).1).trans
      (congrArg ((dmq p (x' * x')).1 * p + ·) ht.symm)
  match Nat.le.dest (Nat.le_of_lt (sq_lt hlt)), Nat.le.dest hlt with
  | ⟨d, hd⟩, ⟨s0, hs0⟩ =>
      have hx' : x + (s0 + 1) = x' := (succ_adds x s0).symm.trans hs0
      have hde : d = (s0 + 1) * (x + x') :=
        (add_left_cancel' (x * x)
          (hd.trans
            ((congrArg (fun z => z * z) hx'.symm).trans
              (sq_expand x (s0 + 1))))).trans
          (congrArg (fun z => (s0 + 1) * (x + z)) hx')
      have hq : p * (dmq p (x' * x')).1 = p * (dmq p (x * x)).1 + d :=
        (Nat.mul_comm p ((dmq p (x' * x')).1)).trans
          ((add_right_cancel' ((dmq p (x * x)).2)
            (he2.symm.trans
              ((hd.symm.trans (congrArg (· + d) he1)).trans
                ((Nat.add_assoc ((dmq p (x * x)).1 * p) ((dmq p (x * x)).2) d).trans
                  ((congrArg ((dmq p (x * x)).1 * p + ·)
                      (Nat.add_comm ((dmq p (x * x)).2) d)).trans
                    (Nat.add_assoc ((dmq p (x * x)).1 * p) d
                      ((dmq p (x * x)).2)).symm))))).trans
            (congrArg (· + d) (Nat.mul_comm ((dmq p (x * x)).1) p)))
      match extract_dvd hp1 hq with
      | ⟨u, hu⟩ =>
          have hsx' : s0 + 1 ≤ x' := hx' ▸ Nat.le_add_left (s0 + 1) x
          have hhp : h < p :=
            le_trans (Nat.succ_le_succ (Nat.le_add_right h h)) (Nat.le_of_eq hph.symm)
          have hsp : s0 + 1 < p := Nat.lt_of_le_of_lt (le_trans hsx' hxh) hhp
          have hxxp : x + x' < p :=
            Nat.lt_of_le_of_lt
              (add_le_add' (le_trans (le_of_succ_le hlt) hxh) hxh)
              (Nat.le_of_eq hph.symm)
          match euclid_small p hirr (s0 + 1) (s0 + 1) (x + x') (Nat.le_refl _) hsp
              ⟨u, hde.symm.trans hu⟩ with
          | .inl hds =>
              not_pdvd_of_lt (Nat.succ_le_succ (Nat.zero_le s0)) hsp hds
          | .inr hdx =>
              not_pdvd_of_lt
                (le_trans (Nat.lt_of_le_of_lt (Nat.zero_le x) hlt)
                  (Nat.le_add_left x' x))
                hxxp hdx

private theorem cross_sum (p h q1 t1 q2 t2 i y : Nat)
    (hph : p = (h + h) + 1)
    (h1 : i * i = q1 * p + t1) (h2 : y * y = q2 * p + t2)
    (hts : t1 + t2 = h + h) :
    (i * i + y * y) + 1 = ((q1 + q2) + 1) * p :=
  have e_dist : (q1 + q2) * p = q1 * p + q2 * p :=
    (Nat.mul_comm (q1 + q2) p).trans
      ((Nat.left_distrib p q1 q2).trans
        ((congrArg (· + p * q2) (Nat.mul_comm p q1)).trans
          (congrArg (q1 * p + ·) (Nat.mul_comm p q2))))
  (congrArg (· + 1)
      (((congrArg (· + y * y) h1).trans
        (congrArg ((q1 * p + t1) + ·) h2)).trans
        ((nat_swap_mid (q1 * p) t1 (q2 * p) t2).trans
          (congrArg ((q1 * p + q2 * p) + ·) hts)))).trans
    ((Nat.add_assoc (q1 * p + q2 * p) (h + h) 1).trans
      ((congrArg ((q1 * p + q2 * p) + ·) hph.symm).trans
        ((congrArg (· + p) e_dist.symm).trans
          (succ_mul' (q1 + q2) p).symm)))

private theorem cross_bound (p h M i y : Nat) (hph : p = (h + h) + 1) (hh : 1 ≤ h)
    (hi : i ≤ h) (hy : y ≤ h) (hEq : (i * i + y * y) + 1 = M * p) : M < p :=
  have hW1 : 1 ≤ h + h := le_trans hh (Nat.le_add_right h h)
  have e_pp : p * p = ((h + h) * (h + h) + (h + h)) + ((h + h) + 1) :=
    (congrArg (fun z => z * z) hph).trans (succ_mul' (h + h) ((h + h) + 1))
  have hle1 : (h * h + h * h) + 1 ≤ (h + h) * (h + h) + 1 :=
    Nat.add_le_add_right (Nat.le.intro (dbl_sq h).symm) 1
  have h2W : 2 ≤ (h + h) + ((h + h) + 1) :=
    le_trans (succ_le_succ' hW1) (Nat.le_add_left ((h + h) + 1) (h + h))
  have hlt2 : (h + h) * (h + h) + 1 < p * p :=
    le_trans (add_le_add_left' h2W ((h + h) * (h + h)))
      (Nat.le_of_eq
        ((adding_associates ((h + h) * (h + h)) (h + h) ((h + h) + 1)).trans
          e_pp.symm))
  have hsum_le : M * p ≤ (h * h + h * h) + 1 :=
    le_trans (Nat.le_of_eq hEq.symm)
      (Nat.add_le_add_right
        (add_le_add' (Nat.mul_le_mul hi hi) (Nat.mul_le_mul hy hy)) 1)
  have hMpp : M * p < p * p :=
    Nat.lt_of_le_of_lt hsum_le (Nat.lt_of_le_of_lt hle1 hlt2)
  match Nat.lt_or_ge M p with
  | .inl hMp => hMp
  | .inr hge =>
      (no_number_is_below_itself (M * p)
        (Nat.lt_of_lt_of_le hMpp (Nat.mul_le_mul hge (Nat.le_refl p)))).elim

private theorem residue_collision (p h : Nat)
    (hirr : ∀ a b : Nat, a * b = p → a = 1 ∨ b = 1)
    (hph : p = (h + h) + 1) (hh : 1 ≤ h) :
    ∃ x y M : Nat, (x * x + y * y) + 1 = M * p ∧ 1 ≤ M ∧ M < p :=
  have hp1 : 1 ≤ p := hph.symm ▸ Nat.succ_le_succ (Nat.zero_le (h + h))
  match fn_collides (resfn p h hp1 hph) with
  | ⟨i, j, hij, hjp, he⟩ =>
      have hjP : j ≤ (h + h) + 1 := hph ▸ Nat.le_of_lt_succ hjp
      match Nat.lt_or_ge j (h + 1) with
      | .inl hjh1 =>
          have hjh : j ≤ h := Nat.le_of_lt_succ hjh1
          have hih : i ≤ h := le_trans (le_of_succ_le hij) hjh
          have E_i : resfn p h hp1 hph i
              = ⟨(dmq p (i * i)).2, (dmq_spec p hp1 (i * i)).2⟩ := if_pos hih
          have E_j : resfn p h hp1 hph j
              = ⟨(dmq p (j * j)).2, (dmq_spec p hp1 (j * j)).2⟩ := if_pos hjh
          (no_sq_collision p h hirr hph i j hij hjh
            (congrArg Fin.val (E_i.symm.trans (he.trans E_j)))).elim
      | .inr h1j =>
          have hnj : ¬ j ≤ h :=
            fun hc => no_number_is_below_itself h (le_trans h1j hc)
          match Nat.le.dest h1j with
          | ⟨y, hy⟩ =>
              have hsubj : j - (h + 1) = y :=
                (congrArg (· - (h + 1)) hy.symm).trans
                  (FInt.add_sub_cancel_left (h + 1) y)
              have hyh : y ≤ h :=
                cancel_add_left h
                  (succ_le_succ_inv (succ_adds h y ▸ hy.symm ▸ hjP))
              have E_j : resfn p h hp1 hph j
                  = ⟨(h + h) - (dmq p ((j - (h + 1)) * (j - (h + 1)))).2,
                     Nat.lt_of_le_of_lt (Nat.sub_le (h + h) _)
                       (Nat.le_of_eq hph.symm)⟩ := if_neg hnj
              match Nat.lt_or_ge i (h + 1) with
              | .inl hih1 =>
                  have hih : i ≤ h := Nat.le_of_lt_succ hih1
                  have E_i : resfn p h hp1 hph i
                      = ⟨(dmq p (i * i)).2, (dmq_spec p hp1 (i * i)).2⟩ :=
                    if_pos hih
                  have hval : (dmq p (i * i)).2
                      = (h + h) - (dmq p (y * y)).2 :=
                    (congrArg Fin.val (E_i.symm.trans (he.trans E_j))).trans
                      (congrArg (fun z => (h + h) - (dmq p (z * z)).2) hsubj)
                  have ht2 : (dmq p (y * y)).2 ≤ h + h :=
                    Nat.le_of_lt_succ (hph ▸ (dmq_spec p hp1 (y * y)).2)
                  match Nat.le.dest ht2 with
                  | ⟨w, hw⟩ =>
                      have hsub2 : (h + h) - (dmq p (y * y)).2 = w :=
                        (congrArg (· - (dmq p (y * y)).2) hw.symm).trans
                          (FInt.add_sub_cancel_left ((dmq p (y * y)).2) w)
                      have hts : (dmq p (i * i)).2 + (dmq p (y * y)).2 = h + h :=
                        (congrArg (· + (dmq p (y * y)).2)
                            (hval.trans hsub2)).trans
                          ((Nat.add_comm w ((dmq p (y * y)).2)).trans hw)
                      have hEq : (i * i + y * y) + 1
                          = (((dmq p (i * i)).1 + (dmq p (y * y)).1) + 1) * p :=
                        cross_sum p h ((dmq p (i * i)).1) ((dmq p (i * i)).2)
                          ((dmq p (y * y)).1) ((dmq p (y * y)).2) i y hph
                          (dmq_spec p hp1 (i * i)).1 (dmq_spec p hp1 (y * y)).1 hts
                      ⟨i, y, ((dmq p (i * i)).1 + (dmq p (y * y)).1) + 1, hEq,
                        Nat.succ_le_succ
                          (Nat.zero_le ((dmq p (i * i)).1 + (dmq p (y * y)).1)),
                        cross_bound p h _ i y hph hh hih hyh hEq⟩
              | .inr h1i =>
                  have hni : ¬ i ≤ h :=
                    fun hc => no_number_is_below_itself h (le_trans h1i hc)
                  match Nat.le.dest h1i with
                  | ⟨y', hy'⟩ =>
                      have hsubi : i - (h + 1) = y' :=
                        (congrArg (· - (h + 1)) hy'.symm).trans
                          (FInt.add_sub_cancel_left (h + 1) y')
                      have E_i : resfn p h hp1 hph i
                          = ⟨(h + h) - (dmq p ((i - (h + 1)) * (i - (h + 1)))).2,
                             Nat.lt_of_le_of_lt (Nat.sub_le (h + h) _)
                               (Nat.le_of_eq hph.symm)⟩ := if_neg hni
                      have hval : (h + h) - (dmq p (y' * y')).2
                          = (h + h) - (dmq p (y * y)).2 :=
                        ((congrArg (fun z => (h + h) - (dmq p (z * z)).2)
                            hsubi).symm).trans
                          ((congrArg Fin.val (E_i.symm.trans (he.trans E_j))).trans
                            (congrArg (fun z => (h + h) - (dmq p (z * z)).2) hsubj))
                      have hyy' : y' < y :=
                        cancel_add_left (h + 1)
                          (hy'.symm ▸ hy.symm ▸ hij :
                            ((h + 1) + y') + 1 ≤ (h + 1) + y)
                      have hyh2 : y ≤ h :=
                        cancel_add_left h
                          (succ_le_succ_inv (succ_adds h y ▸ hy.symm ▸ hjP))
                      have ht2a : (dmq p (y' * y')).2 ≤ h + h :=
                        Nat.le_of_lt_succ (hph ▸ (dmq_spec p hp1 (y' * y')).2)
                      have ht2b : (dmq p (y * y)).2 ≤ h + h :=
                        Nat.le_of_lt_succ (hph ▸ (dmq_spec p hp1 (y * y)).2)
                      match Nat.le.dest ht2a, Nat.le.dest ht2b with
                      | ⟨w, hw⟩, ⟨w', hw'⟩ =>
                          have hsa : (h + h) - (dmq p (y' * y')).2 = w :=
                            (congrArg (· - (dmq p (y' * y')).2) hw.symm).trans
                              (FInt.add_sub_cancel_left ((dmq p (y' * y')).2) w)
                          have hsb : (h + h) - (dmq p (y * y)).2 = w' :=
                            (congrArg (· - (dmq p (y * y)).2) hw'.symm).trans
                              (FInt.add_sub_cancel_left ((dmq p (y * y)).2) w')
                          have hww : w = w' := hsa.symm.trans (hval.trans hsb)
                          have htt : (dmq p (y' * y')).2 = (dmq p (y * y)).2 :=
                            add_right_cancel' w
                              (hw.trans
                                (hw'.symm.trans
                                  (congrArg ((dmq p (y * y)).2 + ·) hww.symm)))
                          (no_sq_collision p h hirr hph y' y hyy' hyh2 htt).elim

private theorem sub_def (a b : Int) : a - b = a + -b := Int.sub_eq_add_neg

private theorem mul_left_swap (a b c : Int) : a * (b * c) = b * (a * c) :=
  (FInt.mul_assoc a b c).symm.trans
    ((congrArg (· * c) (FInt.mulComm a b)).trans (FInt.mul_assoc b a c))

private theorem mul_swap_mid (a b c d : Int) :
    (a * b) * (c * d) = (a * c) * (b * d) :=
  (FInt.mul_assoc a b (c * d)).trans
    ((congrArg (a * ·) (mul_left_swap b c d)).trans
      (FInt.mul_assoc a c (b * d)).symm)

private theorem sub_negg (a b : Int) : a - -b = a + b :=
  (sub_def a (-b)).trans (congrArg (a + ·) (Int.neg_neg b))

private def Cg (m x y : Int) : Prop := ∃ k : Int, x = y + m * k

private theorem cg_refl (m x : Int) : Cg m x x :=
  ⟨0, (Int.add_zero x).symm.trans (congrArg (x + ·) (FInt.mul_zero m).symm)⟩

private theorem cg_add {m x y x' y' : Int} :
    Cg m x y → Cg m x' y' → Cg m (x + x') (y + y')
  | ⟨j, hj⟩, ⟨k, hk⟩ =>
      ⟨j + k,
        ((congrArg (· + x') hj).trans (congrArg ((y + m * j) + ·) hk)).trans
          ((swap_mid y (m * j) y' (m * k)).trans
            (congrArg ((y + y') + ·) (FInt.mul_add m j k).symm))⟩

private theorem cg_neg {m x y : Int} : Cg m x y → Cg m (-x) (-y)
  | ⟨j, hj⟩ =>
      ⟨-j, (congrArg Neg.neg hj).trans
        ((FInt.neg_add y (m * j)).trans
          (congrArg (-y + ·) (FInt.mul_neg m j).symm))⟩

private theorem cg_sub {m x y x' y' : Int} (h1 : Cg m x y) (h2 : Cg m x' y') :
    Cg m (x - x') (y - y') :=
  match cg_add h1 (cg_neg h2) with
  | ⟨k, hk⟩ =>
      ⟨k, (sub_def x x').trans
        (hk.trans (congrArg (· + m * k) (sub_def y y').symm))⟩

private theorem cg_mul {m x y x' y' : Int} :
    Cg m x y → Cg m x' y' → Cg m (x * x') (y * y')
  | ⟨j, hj⟩, ⟨k, hk⟩ =>
      ⟨y * k + j * x',
        (congrArg (· * x') hj).trans
          ((FInt.add_mul y (m * j) x').trans
            (((congrArg (· + (m * j) * x')
                ((congrArg (y * ·) hk).trans
                  ((FInt.mul_add y y' (m * k)).trans
                    (congrArg (y * y' + ·) (mul_left_swap y m k))))).trans
              ((congrArg ((y * y' + m * (y * k)) + ·)
                  (FInt.mul_assoc m j x')).trans
                ((FInt.add_assoc (y * y') (m * (y * k)) (m * (j * x'))).trans
                  (congrArg (y * y' + ·)
                    (FInt.mul_add m (y * k) (j * x')).symm))))))⟩

private theorem zero_pair (x y : Int) : (-x + y) + (x + -y) = 0 :=
  (swap_mid (-x) y x (-y)).trans
    ((congrArg (· + (y + -y)) (FInt.add_left_neg x)).trans
      ((congrArg ((0 : Int) + ·) (FInt.add_right_neg y)).trans (FInt.zero_add 0)))

private theorem zero_pair2 (x y : Int) : (-x + -y) + (x + y) = 0 :=
  (swap_mid (-x) (-y) x y).trans
    ((congrArg (· + (-y + y)) (FInt.add_left_neg x)).trans
      ((congrArg ((0 : Int) + ·) (FInt.add_left_neg y)).trans (FInt.zero_add 0)))

private theorem sum_diff_squares (X Y : Int) :
    (X + Y) * (X + Y) + (X - Y) * (X - Y) = (X * X + Y * Y) + (X * X + Y * Y) :=
  have s1 : (X + Y) * (X + Y) = (X * X + X * Y) + (Y * X + Y * Y) :=
    (FInt.add_mul X Y (X + Y)).trans
      ((congrArg (· + Y * (X + Y)) (FInt.mul_add X X Y)).trans
        (congrArg ((X * X + X * Y) + ·) (FInt.mul_add Y X Y)))
  have s2 : (X - Y) * (X - Y) = (X * X - X * Y) + (Y * Y - Y * X) :=
    (FInt.sub_mul X Y (X - Y)).trans
      ((congrArg (· - Y * (X - Y)) (FInt.mul_sub X X Y)).trans
        ((congrArg ((X * X - X * Y) - ·) (FInt.mul_sub Y X Y)).trans
          ((sub_def (X * X - X * Y) (Y * X - Y * Y)).trans
            (congrArg ((X * X - X * Y) + ·) (FInt.neg_sub (Y * X) (Y * Y))))))
  have p1 : (X * X + X * Y) + (X * X - X * Y) = X * X + X * X :=
    ((congrArg ((X * X + X * Y) + ·) (sub_def (X * X) (X * Y))).trans
      ((swap_mid (X * X) (X * Y) (X * X) (-(X * Y))).trans
        (congrArg ((X * X + X * X) + ·) (FInt.add_right_neg (X * Y))))).trans
      (Int.add_zero (X * X + X * X))
  have p2 : (Y * X + Y * Y) + (Y * Y - Y * X) = Y * Y + Y * Y :=
    ((congrArg (· + (Y * Y - Y * X)) (FInt.addComm (Y * X) (Y * Y))).trans
      ((congrArg ((Y * Y + Y * X) + ·) (sub_def (Y * Y) (Y * X))).trans
        ((swap_mid (Y * Y) (Y * X) (Y * Y) (-(Y * X))).trans
          (congrArg ((Y * Y + Y * Y) + ·) (FInt.add_right_neg (Y * X)))))).trans
      (Int.add_zero (Y * Y + Y * Y))
  ((congrArg (· + (X - Y) * (X - Y)) s1).trans
    (congrArg (((X * X + X * Y) + (Y * X + Y * Y)) + ·) s2)).trans
    ((swap_mid (X * X + X * Y) (Y * X + Y * Y) (X * X - X * Y) (Y * Y - Y * X)).trans
      (((congrArg (· + ((Y * X + Y * Y) + (Y * Y - Y * X))) p1).trans
        (congrArg ((X * X + X * X) + ·) p2)).trans
        (swap_mid (X * X) (X * X) (Y * Y) (Y * Y))))

private theorem ofnat_factor {m : Nat} (hm : 1 ≤ m) {N : Nat} :
    ∀ k : Int, Int.ofNat N = Int.ofNat m * k → ∃ r : Nat, N = m * r
  | Int.ofNat j, h => ⟨j, Int.ofNat.inj h⟩
  | Int.negSucc _, h =>
      match m, hm, h with
      | 0, hm0, _ => nomatch hm0
      | _ + 1, _, h1 => nomatch h1

private theorem centered (m h : Nat) (hm : m = (h + h) + 1) (a : Nat) :
    ∃ (v : Int) (u : Nat) (k : Int),
      v = Int.ofNat a + Int.ofNat m * k ∧ v * v = Int.ofNat (u * u) ∧ u ≤ h :=
  have hm1 : 1 ≤ m := hm.symm ▸ Nat.succ_le_succ (Nat.zero_le (h + h))
  have ha : a = (dmq m a).1 * m + (dmq m a).2 := (dmq_spec m hm1 a).1
  have hr : (dmq m a).2 < m := (dmq_spec m hm1 a).2
  match Nat.lt_or_ge ((dmq m a).2) (h + 1) with
  | .inl hrh1 =>
      have hac : a = m * (dmq m a).1 + (dmq m a).2 :=
        ha.trans (congrArg (· + (dmq m a).2) (Nat.mul_comm ((dmq m a).1) m))
      have hqa : m * (dmq m a).1 ≤ a := Nat.le.intro hac.symm
      have hsub : a - m * (dmq m a).1 = (dmq m a).2 :=
        (congrArg (· - m * (dmq m a).1) hac).trans
          (FInt.add_sub_cancel_left (m * (dmq m a).1) ((dmq m a).2))
      have hveq : Int.ofNat a + Int.ofNat m * (-(Int.ofNat ((dmq m a).1)))
          = Int.ofNat ((dmq m a).2) :=
        (congrArg (Int.ofNat a + ·)
            (FInt.mul_neg (Int.ofNat m) (Int.ofNat ((dmq m a).1)))).trans
          ((FInt.ofNat_add_neg_ofNat a (m * (dmq m a).1)).trans
            ((FInt.subNatNat_of_ge hqa).trans (congrArg Int.ofNat hsub)))
      ⟨Int.ofNat ((dmq m a).2), (dmq m a).2, -(Int.ofNat ((dmq m a).1)),
        hveq.symm, rfl, Nat.le_of_lt_succ hrh1⟩
  | .inr h1r =>
      match Nat.le.dest hr with
      | ⟨d0, hd0⟩ =>
          have hrd : (dmq m a).2 + (d0 + 1) = m :=
            (succ_adds ((dmq m a).2) d0).symm.trans hd0
          have hdh : d0 + 1 ≤ h :=
            cancel_add_left h
              (succ_le_succ_inv
                (succ_adds h (d0 + 1) ▸
                  (le_trans (add_le_add' h1r (Nat.le_refl (d0 + 1)))
                    (Nat.le_of_eq (hrd.trans hm)))))
          have hlt : a < m * ((dmq m a).1 + 1) :=
            Nat.lt_of_le_of_lt (Nat.le_of_eq ha)
              (Nat.lt_of_lt_of_le
                (Nat.add_lt_add_left hr ((dmq m a).1 * m))
                (Nat.le_of_eq
                  ((succ_mul' ((dmq m a).1) m).symm.trans
                    (Nat.mul_comm ((dmq m a).1 + 1) m))))
          have chain : m * ((dmq m a).1 + 1) = a + (d0 + 1) :=
            (congrArg (m * (dmq m a).1 + ·) hrd.symm).trans
              ((adding_associates (m * (dmq m a).1) ((dmq m a).2) (d0 + 1)).trans
                (congrArg (· + (d0 + 1))
                  ((congrArg (· + (dmq m a).2) (Nat.mul_comm m ((dmq m a).1))).trans
                    ha.symm)))
          have e4 : m * ((dmq m a).1 + 1) - a = d0 + 1 :=
            (congrArg (· - a) chain).trans (FInt.add_sub_cancel_left a (d0 + 1))
          have hveq : Int.ofNat a + Int.ofNat m * (-(Int.ofNat ((dmq m a).1 + 1)))
              = -(Int.ofNat (d0 + 1)) :=
            (congrArg (Int.ofNat a + ·)
                (FInt.mul_neg (Int.ofNat m) (Int.ofNat ((dmq m a).1 + 1)))).trans
              ((FInt.ofNat_add_neg_ofNat a (m * ((dmq m a).1 + 1))).trans
                ((FInt.subNatNat_of_lt hlt).trans
                  (congrArg (fun z => -(Int.ofNat z)) e4)))
          ⟨-(Int.ofNat (d0 + 1)), d0 + 1, -(Int.ofNat ((dmq m a).1 + 1)),
            hveq.symm, neg_mul_neg_self (Int.ofNat (d0 + 1)), hdh⟩

private theorem centered_neg (m h b : Nat) (hm : m = (h + h) + 1) :
    ∃ (v : Int) (u : Nat) (k : Int),
      v = -(Int.ofNat b) + Int.ofNat m * k ∧ v * v = Int.ofNat (u * u) ∧ u ≤ h :=
  match centered m h hm b with
  | ⟨v, u, k, hv, hu, huh⟩ =>
      ⟨-v, u, -k,
        (congrArg Neg.neg hv).trans
          ((FInt.neg_add (Int.ofNat b) (Int.ofNat m * k)).trans
            (congrArg (-(Int.ofNat b) + ·) (FInt.mul_neg (Int.ofNat m) k).symm)),
        (neg_mul_neg_self v).trans hu, huh⟩

private theorem zero_resid {M T v k : Int} (hv : v = T + M * k) (hz : v = 0) :
    T = M * (-k) :=
  have h0 : 0 = T + M * k := hz.symm.trans hv
  (Int.add_zero T).symm.trans
    ((congrArg (T + ·) (FInt.add_right_neg (M * k)).symm).trans
      ((FInt.add_assoc T (M * k) (-(M * k))).symm.trans
        ((congrArg (· + -(M * k)) h0.symm).trans
          ((FInt.zero_add (-(M * k))).trans (FInt.mul_neg M k).symm))))

private theorem neg_resid {M B k : Int} (h : -B = M * k) : B = M * (-k) :=
  (Int.neg_neg B).symm.trans
    ((congrArg Neg.neg h).trans (FInt.mul_neg M k).symm)

private theorem no_all_divisible (p m : Nat)
    (hirr : ∀ a b : Nat, a * b = p → a = 1 ∨ b = 1)
    (hm1 : 1 ≤ m) (h2m : 2 ≤ m) (hmp : m < p)
    (a b c d n1 n2 n3 n4 : Nat)
    (hA : a = m * n1) (hB : b = m * n2) (hC : c = m * n3) (hD : d = m * n4)
    (hsum : ((a * a + b * b) + c * c) + d * d = m * p) : False :=
  have e1 : a * a = (m * m) * (n1 * n1) :=
    (congrArg (fun z => z * z) hA).trans (nat_mul_swap m n1 m n1)
  have e2 : b * b = (m * m) * (n2 * n2) :=
    (congrArg (fun z => z * z) hB).trans (nat_mul_swap m n2 m n2)
  have e3 : c * c = (m * m) * (n3 * n3) :=
    (congrArg (fun z => z * z) hC).trans (nat_mul_swap m n3 m n3)
  have e4 : d * d = (m * m) * (n4 * n4) :=
    (congrArg (fun z => z * z) hD).trans (nat_mul_swap m n4 m n4)
  have hsum2 : (((m * m) * (n1 * n1) + (m * m) * (n2 * n2))
      + (m * m) * (n3 * n3)) + (m * m) * (n4 * n4) = m * p :=
    ((congrArg (fun z => ((z + b * b) + c * c) + d * d) e1).trans
      ((congrArg (fun z => (((m * m) * (n1 * n1) + z) + c * c) + d * d) e2).trans
        ((congrArg
            (fun z => (((m * m) * (n1 * n1) + (m * m) * (n2 * n2)) + z) + d * d)
            e3).trans
          (congrArg
            (fun z => (((m * m) * (n1 * n1) + (m * m) * (n2 * n2))
              + (m * m) * (n3 * n3)) + z)
            e4)))).symm.trans hsum
  have hdist : (m * m) * (((n1 * n1 + n2 * n2) + n3 * n3) + n4 * n4)
      = (((m * m) * (n1 * n1) + (m * m) * (n2 * n2))
          + (m * m) * (n3 * n3)) + (m * m) * (n4 * n4) :=
    (Nat.left_distrib (m * m) ((n1 * n1 + n2 * n2) + n3 * n3) (n4 * n4)).trans
      (congrArg (· + (m * m) * (n4 * n4))
        ((Nat.left_distrib (m * m) (n1 * n1 + n2 * n2) (n3 * n3)).trans
          (congrArg (· + (m * m) * (n3 * n3))
            (Nat.left_distrib (m * m) (n1 * n1) (n2 * n2)))))
  have hmp2 : m * p
      = m * (m * (((n1 * n1 + n2 * n2) + n3 * n3) + n4 * n4)) :=
    hsum2.symm.trans
      (hdist.symm.trans
        (FInt.nat_mul_assoc m m (((n1 * n1 + n2 * n2) + n3 * n3) + n4 * n4)))
  have hpS : p = m * (((n1 * n1 + n2 * n2) + n3 * n3) + n4 * n4) :=
    mul_eq_cancel_left hm1 hmp2
  match hirr m ((((n1 * n1 + n2 * n2) + n3 * n3) + n4 * n4)) hpS.symm with
  | .inl hm1e =>
      no_number_is_below_itself 1
        (Eq.subst (motive := fun z => 2 ≤ z) hm1e h2m)
  | .inr hS1 =>
      have hpm : p = m :=
        hpS.trans ((congrArg (m * ·) hS1).trans (Nat.mul_one m))
      no_number_is_below_itself p (hpm.symm ▸ hmp)

private theorem odd_step (p m h : Nat)
    (hirr : ∀ a b : Nat, a * b = p → a = 1 ∨ b = 1)
    (hm : m = (h + h) + 1) (h2m : 2 ≤ m) (hmp : m < p)
    (a b c d : Nat)
    (hsum : ((a * a + b * b) + c * c) + d * d = m * p) :
    ∃ r : Nat, 1 ≤ r ∧ r < m ∧
      ∃ e1 e2 e3 e4 : Nat,
        ((e1 * e1 + e2 * e2) + e3 * e3) + e4 * e4 = r * p :=
  have hm1 : 1 ≤ m := hm.symm ▸ Nat.succ_le_succ (Nat.zero_le (h + h))
  match centered m h hm a, centered_neg m h b hm,
      centered_neg m h c hm, centered_neg m h d hm with
  | ⟨v1, u1, k1, hv1, hu1, hu1h⟩, ⟨v2, u2, k2, hv2, hu2, hu2h⟩,
    ⟨v3, u3, k3, hv3, hu3, hu3h⟩, ⟨v4, u4, k4, hv4, hu4, hu4h⟩ =>
      let mI : Int := Int.ofNat m
      let qa : Int := Int.ofNat a
      let qb : Int := Int.ofNat b
      let qc : Int := Int.ofNat c
      let qd : Int := Int.ofNat d
      have H1 : Cg mI v1 qa := ⟨k1, hv1⟩
      have H2 : Cg mI v2 (-qb) := ⟨k2, hv2⟩
      have H3 : Cg mI v3 (-qc) := ⟨k3, hv3⟩
      have H4 : Cg mI v4 (-qd) := ⟨k4, hv4⟩
      have hXn : (qa * qa + qb * qb) + (qc * qc + qd * qd)
          = Int.ofNat (m * p) :=
        congrArg Int.ofNat
          ((adding_associates (a * a + b * b) (c * c) (d * d)).trans hsum)
      have pair1 : v1 * v1 + v2 * v2 = Int.ofNat (u1 * u1 + u2 * u2) :=
        (congrArg (· + v2 * v2) hu1).trans
          (congrArg (Int.ofNat (u1 * u1) + ·) hu2)
      have pair2 : v3 * v3 + v4 * v4 = Int.ofNat (u3 * u3 + u4 * u4) :=
        (congrArg (· + v4 * v4) hu3).trans
          (congrArg (Int.ofNat (u3 * u3) + ·) hu4)
      have hYn : (v1 * v1 + v2 * v2) + (v3 * v3 + v4 * v4)
          = Int.ofNat ((u1 * u1 + u2 * u2) + (u3 * u3 + u4 * u4)) :=
        (congrArg (· + (v3 * v3 + v4 * v4)) pair1).trans
          (congrArg (Int.ofNat (u1 * u1 + u2 * u2) + ·) pair2)
      have HN : Cg mI ((v1 * v1 + v2 * v2) + (v3 * v3 + v4 * v4))
          ((qa * qa + (-qb) * (-qb)) + ((-qc) * (-qc) + (-qd) * (-qd))) :=
        cg_add (cg_add (cg_mul H1 H1) (cg_mul H2 H2))
          (cg_add (cg_mul H3 H3) (cg_mul H4 H4))
      have hTn : (qa * qa + (-qb) * (-qb)) + ((-qc) * (-qc) + (-qd) * (-qd))
          = Int.ofNat (m * p) :=
        (congrArg (fun z => (qa * qa + z) + ((-qc) * (-qc) + (-qd) * (-qd)))
            (neg_mul_neg_self qb)).trans
          ((congrArg (fun z => (qa * qa + qb * qb) + (z + (-qd) * (-qd)))
              (neg_mul_neg_self qc)).trans
            ((congrArg (fun z => (qa * qa + qb * qb) + (qc * qc + z))
                (neg_mul_neg_self qd)).trans hXn))
      match HN with
      | ⟨KN, hKN⟩ =>
          have hNK : Int.ofNat ((u1 * u1 + u2 * u2) + (u3 * u3 + u4 * u4))
              = Int.ofNat m * (Int.ofNat p + KN) :=
            hYn.symm.trans
              (hKN.trans
                ((congrArg (· + mI * KN) hTn).trans
                  (FInt.mul_add mI (Int.ofNat p) KN).symm))
          match ofnat_factor hm1 (Int.ofNat p + KN) hNK with
          | ⟨rN, hrNe⟩ =>
              match rN, hrNe with
              | 0, hrN0 =>
                  match add_eq_zero hrN0 with
                  | ⟨h12, h34⟩ =>
                      match add_eq_zero h12, add_eq_zero h34 with
                      | ⟨hz1, hz2⟩, ⟨hz3, hz4⟩ =>
                          have hv1z : v1 = 0 :=
                            match FInt.mul_eq_zero.mp
                                (hu1.trans (congrArg
                                  (fun z => Int.ofNat (z * z)) (sq_zero hz1))) with
                            | .inl hz => hz
                            | .inr hz => hz
                          have hv2z : v2 = 0 :=
                            match FInt.mul_eq_zero.mp
                                (hu2.trans (congrArg
                                  (fun z => Int.ofNat (z * z)) (sq_zero hz2))) with
                            | .inl hz => hz
                            | .inr hz => hz
                          have hv3z : v3 = 0 :=
                            match FInt.mul_eq_zero.mp
                                (hu3.trans (congrArg
                                  (fun z => Int.ofNat (z * z)) (sq_zero hz3))) with
                            | .inl hz => hz
                            | .inr hz => hz
                          have hv4z : v4 = 0 :=
                            match FInt.mul_eq_zero.mp
                                (hu4.trans (congrArg
                                  (fun z => Int.ofNat (z * z)) (sq_zero hz4))) with
                            | .inl hz => hz
                            | .inr hz => hz
                          match ofnat_factor hm1 (-k1) (zero_resid hv1 hv1z),
                              ofnat_factor hm1 (-(-k2))
                                (neg_resid (zero_resid hv2 hv2z)),
                              ofnat_factor hm1 (-(-k3))
                                (neg_resid (zero_resid hv3 hv3z)),
                              ofnat_factor hm1 (-(-k4))
                                (neg_resid (zero_resid hv4 hv4z)) with
                          | ⟨n1, hdA⟩, ⟨n2, hdB⟩, ⟨n3, hdC⟩, ⟨n4, hdD⟩ =>
                              (no_all_divisible p m hirr hm1 h2m hmp
                                a b c d n1 n2 n3 n4 hdA hdB hdC hdD hsum).elim
              | r' + 1, hrN1 =>
                  let c1 : Int := (qa * v1 - qb * v2) + -(v3 * qc - (-v4) * qd)
                  let c2 : Int := (qa * v2 + qb * v1) + -(v3 * qd + (-v4) * qc)
                  let c3 : Int := (v3 * qa - v4 * qb) + (qc * v1 - qd * (-v2))
                  let c4 : Int := (v3 * qb + v4 * qa) + (qc * (-v2) + qd * v1)
                  have G1 : Cg mI c1
                      ((qa * qa - qb * (-qb))
                        + -((-qc) * qc - (-(-qd)) * qd)) :=
                    cg_add
                      (cg_sub (cg_mul (cg_refl mI qa) H1)
                        (cg_mul (cg_refl mI qb) H2))
                      (cg_neg (cg_sub (cg_mul H3 (cg_refl mI qc))
                        (cg_mul (cg_neg H4) (cg_refl mI qd))))
                  have G2 : Cg mI c2
                      ((qa * (-qb) + qb * qa)
                        + -((-qc) * qd + (-(-qd)) * qc)) :=
                    cg_add
                      (cg_add (cg_mul (cg_refl mI qa) H2)
                        (cg_mul (cg_refl mI qb) H1))
                      (cg_neg (cg_add (cg_mul H3 (cg_refl mI qd))
                        (cg_mul (cg_neg H4) (cg_refl mI qc))))
                  have G3 : Cg mI c3
                      (((-qc) * qa - (-qd) * qb)
                        + (qc * qa - qd * (-(-qb)))) :=
                    cg_add
                      (cg_sub (cg_mul H3 (cg_refl mI qa))
                        (cg_mul H4 (cg_refl mI qb)))
                      (cg_sub (cg_mul (cg_refl mI qc) H1)
                        (cg_mul (cg_refl mI qd) (cg_neg H2)))
                  have G4 : Cg mI c4
                      (((-qc) * qb + (-qd) * qa)
                        + (qc * (-(-qb)) + qd * qa)) :=
                    cg_add
                      (cg_add (cg_mul H3 (cg_refl mI qb))
                        (cg_mul H4 (cg_refl mI qa)))
                      (cg_add (cg_mul (cg_refl mI qc) (cg_neg H2))
                        (cg_mul (cg_refl mI qd) H1))
                  have hT1 : (qa * qa - qb * (-qb))
                      + -((-qc) * qc - (-(-qd)) * qd)
                      = Int.ofNat m * Int.ofNat p :=
                    have t1a : qa * qa - qb * (-qb) = qa * qa + qb * qb :=
                      (congrArg (qa * qa - ·) (FInt.mul_neg qb qb)).trans
                        (sub_negg (qa * qa) (qb * qb))
                    have t1b : (-qc) * qc - (-(-qd)) * qd
                        = -(qc * qc + qd * qd) :=
                      (congrArg (· - (-(-qd)) * qd) (FInt.neg_mul qc qc)).trans
                        ((congrArg (fun z => -(qc * qc) - z * qd)
                            (Int.neg_neg qd)).trans
                          ((sub_def (-(qc * qc)) (qd * qd)).trans
                            (FInt.neg_add (qc * qc) (qd * qd)).symm))
                    (congrArg (· + -((-qc) * qc - (-(-qd)) * qd)) t1a).trans
                      ((congrArg (fun z => (qa * qa + qb * qb) + -z) t1b).trans
                        ((congrArg ((qa * qa + qb * qb) + ·)
                            (Int.neg_neg (qc * qc + qd * qd))).trans hXn))
                  have hT2 : (qa * (-qb) + qb * qa)
                      + -((-qc) * qd + (-(-qd)) * qc) = 0 :=
                    have e2a : qa * (-qb) + qb * qa = 0 :=
                      (congrArg (· + qb * qa) (FInt.mul_neg qa qb)).trans
                        ((congrArg (-(qa * qb) + ·) (FInt.mulComm qb qa)).trans
                          (FInt.add_left_neg (qa * qb)))
                    have e2b : (-qc) * qd + (-(-qd)) * qc = 0 :=
                      (congrArg (· + (-(-qd)) * qc) (FInt.neg_mul qc qd)).trans
                        ((congrArg (fun z => -(qc * qd) + z * qc)
                            (Int.neg_neg qd)).trans
                          ((congrArg (-(qc * qd) + ·) (FInt.mulComm qd qc)).trans
                            (FInt.add_left_neg (qc * qd))))
                    (congrArg (· + -((-qc) * qd + (-(-qd)) * qc)) e2a).trans
                      (congrArg (fun z => (0 : Int) + -z) e2b)
                  have hT3 : ((-qc) * qa - (-qd) * qb)
                      + (qc * qa - qd * (-(-qb))) = 0 :=
                    have e3a : (-qc) * qa - (-qd) * qb
                        = -(qc * qa) + qd * qb :=
                      (congrArg (· - (-qd) * qb) (FInt.neg_mul qc qa)).trans
                        ((congrArg (fun z => -(qc * qa) - z)
                            (FInt.neg_mul qd qb)).trans
                          (sub_negg (-(qc * qa)) (qd * qb)))
                    have e3b : qc * qa - qd * (-(-qb))
                        = qc * qa + -(qd * qb) :=
                      (congrArg (fun z => qc * qa - qd * z)
                          (Int.neg_neg qb)).trans
                        (sub_def (qc * qa) (qd * qb))
                    (congrArg (· + (qc * qa - qd * (-(-qb)))) e3a).trans
                      ((congrArg ((-(qc * qa) + qd * qb) + ·) e3b).trans
                        (zero_pair (qc * qa) (qd * qb)))
                  have hT4 : ((-qc) * qb + (-qd) * qa)
                      + (qc * (-(-qb)) + qd * qa) = 0 :=
                    have e4a : (-qc) * qb + (-qd) * qa
                        = -(qc * qb) + -(qd * qa) :=
                      (congrArg (· + (-qd) * qa) (FInt.neg_mul qc qb)).trans
                        (congrArg (-(qc * qb) + ·) (FInt.neg_mul qd qa))
                    have e4b : qc * (-(-qb)) + qd * qa = qc * qb + qd * qa :=
                      congrArg (fun z => qc * z + qd * qa) (Int.neg_neg qb)
                    (congrArg (· + (qc * (-(-qb)) + qd * qa)) e4a).trans
                      ((congrArg ((-(qc * qb) + -(qd * qa)) + ·) e4b).trans
                        (zero_pair2 (qc * qb) (qd * qa)))
                  match G1, G2, G3, G4 with
                  | ⟨K1, hK1⟩, ⟨K2, hK2⟩, ⟨K3, hK3⟩, ⟨K4, hK4⟩ =>
                      have hc1 : c1 = mI * (Int.ofNat p + K1) :=
                        hK1.trans
                          ((congrArg (· + mI * K1) hT1).trans
                            (FInt.mul_add mI (Int.ofNat p) K1).symm)
                      have hc2 : c2 = mI * K2 :=
                        hK2.trans
                          ((congrArg (· + mI * K2) hT2).trans
                            (FInt.zero_add (mI * K2)))
                      have hc3 : c3 = mI * K3 :=
                        hK3.trans
                          ((congrArg (· + mI * K3) hT3).trans
                            (FInt.zero_add (mI * K3)))
                      have hc4 : c4 = mI * K4 :=
                        hK4.trans
                          ((congrArg (· + mI * K4) hT4).trans
                            (FInt.zero_add (mI * K4)))
                      match int_sq_is_nat_sq (Int.ofNat p + K1),
                          int_sq_is_nat_sq K2, int_sq_is_nat_sq K3,
                          int_sq_is_nat_sq K4 with
                      | ⟨e1, he1⟩, ⟨e2, he2⟩, ⟨e3, he3⟩, ⟨e4, he4⟩ =>
                          let X : Quat := ⟨⟨qa, qb⟩, ⟨qc, qd⟩⟩
                          let Y : Quat := ⟨⟨v1, v2⟩, ⟨v3, v4⟩⟩
                          have hYrn : Quat.normSq Y
                              = Int.ofNat (m * (r' + 1)) :=
                            hYn.trans (congrArg Int.ofNat hrN1)
                          have hEuler : Quat.normSq (Quat.mul X Y)
                              = Int.ofNat ((m * p) * (m * (r' + 1))) :=
                            (the_quadruple_carries_the_norm X Y).trans
                              ((congrArg (· * Quat.normSq Y) hXn).trans
                                (congrArg (Int.ofNat (m * p) * ·) hYrn))
                          have hsq1 : c1 * c1
                              = Int.ofNat ((m * m) * (e1 * e1)) :=
                            (congrArg (fun z => z * z) hc1).trans
                              ((mul_swap_mid mI (Int.ofNat p + K1) mI
                                  (Int.ofNat p + K1)).trans
                                (congrArg (Int.ofNat (m * m) * ·) he1))
                          have hsq2 : c2 * c2
                              = Int.ofNat ((m * m) * (e2 * e2)) :=
                            (congrArg (fun z => z * z) hc2).trans
                              ((mul_swap_mid mI K2 mI K2).trans
                                (congrArg (Int.ofNat (m * m) * ·) he2))
                          have hsq3 : c3 * c3
                              = Int.ofNat ((m * m) * (e3 * e3)) :=
                            (congrArg (fun z => z * z) hc3).trans
                              ((mul_swap_mid mI K3 mI K3).trans
                                (congrArg (Int.ofNat (m * m) * ·) he3))
                          have hsq4 : c4 * c4
                              = Int.ofNat ((m * m) * (e4 * e4)) :=
                            (congrArg (fun z => z * z) hc4).trans
                              ((mul_swap_mid mI K4 mI K4).trans
                                (congrArg (Int.ofNat (m * m) * ·) he4))
                          have hNorm2 : Quat.normSq (Quat.mul X Y)
                              = Int.ofNat
                                  (((m * m) * (e1 * e1) + (m * m) * (e2 * e2))
                                    + ((m * m) * (e3 * e3)
                                      + (m * m) * (e4 * e4))) :=
                            (congrArg
                                (fun z => (z + c2 * c2) + (c3 * c3 + c4 * c4))
                                hsq1).trans
                              ((congrArg
                                  (fun z => (Int.ofNat ((m * m) * (e1 * e1)) + z)
                                    + (c3 * c3 + c4 * c4))
                                  hsq2).trans
                                ((congrArg
                                    (fun z =>
                                      (Int.ofNat ((m * m) * (e1 * e1))
                                        + Int.ofNat ((m * m) * (e2 * e2)))
                                      + (z + c4 * c4))
                                    hsq3).trans
                                  (congrArg
                                    (fun z =>
                                      (Int.ofNat ((m * m) * (e1 * e1))
                                        + Int.ofNat ((m * m) * (e2 * e2)))
                                      + (Int.ofNat ((m * m) * (e3 * e3)) + z))
                                    hsq4)))
                          have hinj : ((m * m) * (e1 * e1) + (m * m) * (e2 * e2))
                              + ((m * m) * (e3 * e3) + (m * m) * (e4 * e4))
                              = (m * p) * (m * (r' + 1)) :=
                            Int.ofNat.inj (hNorm2.symm.trans hEuler)
                          have hdist2 : (m * m)
                              * ((e1 * e1 + e2 * e2) + (e3 * e3 + e4 * e4))
                              = ((m * m) * (e1 * e1) + (m * m) * (e2 * e2))
                                + ((m * m) * (e3 * e3) + (m * m) * (e4 * e4)) :=
                            (Nat.left_distrib (m * m) (e1 * e1 + e2 * e2)
                                (e3 * e3 + e4 * e4)).trans
                              ((congrArg (· + (m * m) * (e3 * e3 + e4 * e4))
                                  (Nat.left_distrib (m * m) (e1 * e1)
                                    (e2 * e2))).trans
                                (congrArg
                                  (((m * m) * (e1 * e1) + (m * m) * (e2 * e2)) + ·)
                                  (Nat.left_distrib (m * m) (e3 * e3)
                                    (e4 * e4))))
                          have hNatEq : (m * m)
                              * ((e1 * e1 + e2 * e2) + (e3 * e3 + e4 * e4))
                              = (m * m) * (p * (r' + 1)) :=
                            hdist2.trans
                              (hinj.trans (nat_mul_swap m p m (r' + 1)))
                          have hfinal : (e1 * e1 + e2 * e2) + (e3 * e3 + e4 * e4)
                              = p * (r' + 1) :=
                            mul_eq_cancel_left (Nat.mul_le_mul hm1 hm1) hNatEq
                          have hNle : (u1 * u1 + u2 * u2) + (u3 * u3 + u4 * u4)
                              ≤ (h * h + h * h) + (h * h + h * h) :=
                            add_le_add'
                              (add_le_add' (Nat.mul_le_mul hu1h hu1h)
                                (Nat.mul_le_mul hu2h hu2h))
                              (add_le_add' (Nat.mul_le_mul hu3h hu3h)
                                (Nat.mul_le_mul hu4h hu4h))
                          have e_mm : m * m
                              = ((h + h) * (h + h) + (h + h)) + ((h + h) + 1) :=
                            (congrArg (fun z => z * z) hm).trans
                              (succ_mul' (h + h) ((h + h) + 1))
                          have hWWlt : (h + h) * (h + h) < m * m :=
                            le_trans
                              (add_le_add_left'
                                (Nat.succ_le_succ
                                  (Nat.zero_le ((h + h) + (h + h))))
                                ((h + h) * (h + h)))
                              (Nat.le_of_eq
                                ((adding_associates ((h + h) * (h + h)) (h + h)
                                  ((h + h) + 1)).trans e_mm.symm))
                          have hNlt : (u1 * u1 + u2 * u2) + (u3 * u3 + u4 * u4)
                              < m * m :=
                            Nat.lt_of_le_of_lt
                              (le_trans hNle (Nat.le_of_eq (dbl_sq h).symm))
                              hWWlt
                          have hrm : r' + 1 < m :=
                            match Nat.lt_or_ge (r' + 1) m with
                            | .inl hlt => hlt
                            | .inr hge =>
                                (no_number_is_below_itself (m * (r' + 1))
                                  (Nat.lt_of_lt_of_le
                                    (Nat.lt_of_le_of_lt
                                      (Nat.le_of_eq hrN1.symm) hNlt)
                                    (Nat.mul_le_mul_left m hge))).elim
                          ⟨r' + 1, Nat.succ_le_succ (Nat.zero_le r'), hrm,
                            e1, e2, e3, e4,
                            (adding_associates (e1 * e1 + e2 * e2) (e3 * e3)
                                (e4 * e4)).symm.trans
                              (hfinal.trans (Nat.mul_comm p (r' + 1)))⟩

private theorem ph_core (a b E u : Nat) (hd : b + (u + u) = a)
    (hs : a + b = E + E) :
    a * a + b * b = (E * E + u * u) + (E * E + u * u) :=
  have hba : b ≤ a := Nat.le.intro hd
  have hXY : Int.ofNat a + Int.ofNat b = Int.ofNat (E + E) :=
    congrArg Int.ofNat hs
  have hab : a - b = u + u :=
    (congrArg (· - b) hd.symm).trans
      ((congrArg (· - b) (Nat.add_comm b (u + u))).trans
        (FInt.add_sub_cancel (u + u) b))
  have hsub : Int.ofNat a - Int.ofNat b = Int.ofNat (u + u) :=
    (sub_def (Int.ofNat a) (Int.ofNat b)).trans
      ((FInt.ofNat_add_neg_ofNat a b).trans
        ((FInt.subNatNat_of_ge hba).trans (congrArg Int.ofNat hab)))
  have h1 : Int.ofNat (E + E) * Int.ofNat (E + E)
      + Int.ofNat (u + u) * Int.ofNat (u + u)
      = (Int.ofNat a * Int.ofNat a + Int.ofNat b * Int.ofNat b)
        + (Int.ofNat a * Int.ofNat a + Int.ofNat b * Int.ofNat b) :=
    (congrArg
        (fun z => z * z + Int.ofNat (u + u) * Int.ofNat (u + u))
        hXY.symm).trans
      ((congrArg
          (fun z => (Int.ofNat a + Int.ofNat b) * (Int.ofNat a + Int.ofNat b)
            + z * z)
          hsub.symm).trans
        (sum_diff_squares (Int.ofNat a) (Int.ofNat b)))
  have hNat : (E + E) * (E + E) + (u + u) * (u + u)
      = (a * a + b * b) + (a * a + b * b) := Int.ofNat.inj h1
  have hL : (E + E) * (E + E) + (u + u) * (u + u)
      = ((E * E + u * u) + (E * E + u * u))
        + ((E * E + u * u) + (E * E + u * u)) :=
    (congrArg (· + (u + u) * (u + u)) (dbl_sq E)).trans
      ((congrArg (((E * E + E * E) + (E * E + E * E)) + ·) (dbl_sq u)).trans
        ((nat_swap_mid (E * E + E * E) (E * E + E * E)
            (u * u + u * u) (u * u + u * u)).trans
          (congrArg (fun z => z + z)
            (nat_swap_mid (E * E) (E * E) (u * u) (u * u)))))
  (double_inj (hL.symm.trans hNat)).symm

private theorem ph_even {a b : Nat} (x y : Nat) (ha : a = x + x) (hb : b = y + y) :
    ∃ E u : Nat, a * a + b * b = (E * E + u * u) + (E * E + u * u) :=
  match Nat.lt_or_ge x y with
  | .inr hyx =>
      match Nat.le.dest hyx with
      | ⟨t, ht⟩ =>
          ⟨x + y, t,
            ph_core a b (x + y) t
              ((congrArg (· + (t + t)) hb).trans
                ((nat_swap_mid y y t t).trans
                  ((congrArg (fun z => z + z) ht).trans ha.symm)))
              (((congrArg (· + b) ha).trans
                (congrArg ((x + x) + ·) hb)).trans (nat_swap_mid x x y y))⟩
  | .inl hxy =>
      match Nat.le.dest (Nat.le_of_lt hxy) with
      | ⟨t, ht⟩ =>
          ⟨y + x, t,
            (Nat.add_comm (a * a) (b * b)).trans
              (ph_core b a (y + x) t
                ((congrArg (· + (t + t)) ha).trans
                  ((nat_swap_mid x x t t).trans
                    ((congrArg (fun z => z + z) ht).trans hb.symm)))
                (((congrArg (· + a) hb).trans
                  (congrArg ((y + y) + ·) ha)).trans (nat_swap_mid y y x x)))⟩

private theorem ph_odd {a b : Nat} (x y : Nat) (ha : a = (x + x) + 1)
    (hb : b = (y + y) + 1) :
    ∃ E u : Nat, a * a + b * b = (E * E + u * u) + (E * E + u * u) :=
  match Nat.lt_or_ge x y with
  | .inr hyx =>
      match Nat.le.dest hyx with
      | ⟨t, ht⟩ =>
          ⟨(x + y) + 1, t,
            ph_core a b ((x + y) + 1) t
              ((congrArg (· + (t + t)) hb).trans
                ((Nat.add_assoc (y + y) 1 (t + t)).trans
                  ((congrArg ((y + y) + ·) (Nat.add_comm 1 (t + t))).trans
                    ((adding_associates (y + y) (t + t) 1).trans
                      ((congrArg (· + 1)
                          ((nat_swap_mid y y t t).trans
                            (congrArg (fun z => z + z) ht))).trans
                        ha.symm)))))
              (((congrArg (· + b) ha).trans
                (congrArg (((x + x) + 1) + ·) hb)).trans
                ((nat_swap_mid (x + x) 1 (y + y) 1).trans
                  ((congrArg (· + (1 + 1)) (nat_swap_mid x x y y)).trans
                    (nat_swap_mid (x + y) 1 (x + y) 1).symm)))⟩
  | .inl hxy =>
      match Nat.le.dest (Nat.le_of_lt hxy) with
      | ⟨t, ht⟩ =>
          ⟨(y + x) + 1, t,
            (Nat.add_comm (a * a) (b * b)).trans
              (ph_core b a ((y + x) + 1) t
                ((congrArg (· + (t + t)) ha).trans
                  ((Nat.add_assoc (x + x) 1 (t + t)).trans
                    ((congrArg ((x + x) + ·) (Nat.add_comm 1 (t + t))).trans
                      ((adding_associates (x + x) (t + t) 1).trans
                        ((congrArg (· + 1)
                            ((nat_swap_mid x x t t).trans
                              (congrArg (fun z => z + z) ht))).trans
                          hb.symm)))))
                (((congrArg (· + a) hb).trans
                  (congrArg (((y + y) + 1) + ·) ha)).trans
                  ((nat_swap_mid (y + y) 1 (x + x) 1).trans
                    ((congrArg (· + (1 + 1)) (nat_swap_mid y y x x)).trans
                      (nat_swap_mid (y + x) 1 (y + x) 1).symm))))⟩

private theorem kk_split (p k : Nat) : (k + k) * p = k * p + k * p :=
  (Nat.mul_comm (k + k) p).trans
    ((Nat.left_distrib p k k).trans
      ((congrArg (· + p * k) (Nat.mul_comm p k)).trans
        (congrArg (k * p + ·) (Nat.mul_comm p k))))

private theorem even_assemble {p k S1 S2 : Nat} (E1 F1 E2 F2 : Nat)
    (h1 : S1 = (E1 * E1 + F1 * F1) + (E1 * E1 + F1 * F1))
    (h2 : S2 = (E2 * E2 + F2 * F2) + (E2 * E2 + F2 * F2))
    (hsum : S1 + S2 = (k + k) * p) :
    ∃ e f g h' : Nat, ((e * e + f * f) + g * g) + h' * h' = k * p :=
  have hQ : ((E1 * E1 + F1 * F1) + (E2 * E2 + F2 * F2))
      + ((E1 * E1 + F1 * F1) + (E2 * E2 + F2 * F2)) = k * p + k * p :=
    (nat_swap_mid (E1 * E1 + F1 * F1) (E1 * E1 + F1 * F1)
        (E2 * E2 + F2 * F2) (E2 * E2 + F2 * F2)).symm.trans
      ((((congrArg (· + S2) h1).trans
        (congrArg (((E1 * E1 + F1 * F1) + (E1 * E1 + F1 * F1)) + ·)
          h2)).symm).trans
        (hsum.trans (kk_split p k)))
  ⟨E1, F1, E2, F2,
    (adding_associates (E1 * E1 + F1 * F1) (E2 * E2) (F2 * F2)).symm.trans
      (double_inj hQ)⟩

private theorem even_step (p k a b c d : Nat)
    (hsum : ((a * a + b * b) + c * c) + d * d = (k + k) * p) :
    ∃ e f g h' : Nat, ((e * e + f * f) + g * g) + h' * h' = k * p :=
  have hpair : (a * a + b * b) + (c * c + d * d) = (k + k) * p :=
    (adding_associates (a * a + b * b) (c * c) (d * d)).trans hsum
  have hpair2 : (a * a + c * c) + (b * b + d * d) = (k + k) * p :=
    (nat_swap_mid (a * a) (c * c) (b * b) (d * d)).trans hpair
  have hpair3 : (a * a + d * d) + (b * b + c * c) = (k + k) * p :=
    ((nat_swap_mid (a * a) (d * d) (b * b) (c * c)).trans
      (congrArg ((a * a + b * b) + ·) (Nat.add_comm (d * d) (c * c)))).trans
      hpair
  have hev : EvP (((a * a + b * b) + c * c) + d * d) :=
    ⟨k * p, hsum.trans (kk_split p k)⟩
  match par a, par b, par c, par d with
  | ⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩, ⟨w, hw⟩ =>
      match hx, hy, hz, hw with
      | .inl hxa, .inl hyb, .inl hzc, .inl hwd =>
          match ph_even x y hxa hyb, ph_even z w hzc hwd with
          | ⟨E1, F1, h1⟩, ⟨E2, F2, h2⟩ =>
              even_assemble E1 F1 E2 F2 h1 h2 hpair
      | .inl hxa, .inl hyb, .inl hzc, .inr hwd =>
          (ev_ne_od hev
            (ev_od (ev_add (ev_add (sq_ev hxa) (sq_ev hyb)) (sq_ev hzc))
              (sq_od hwd))).elim
      | .inl hxa, .inl hyb, .inr hzc, .inl hwd =>
          (ev_ne_od hev
            (od_ev (ev_od (ev_add (sq_ev hxa) (sq_ev hyb)) (sq_od hzc))
              (sq_ev hwd))).elim
      | .inl hxa, .inl hyb, .inr hzc, .inr hwd =>
          match ph_even x y hxa hyb, ph_odd z w hzc hwd with
          | ⟨E1, F1, h1⟩, ⟨E2, F2, h2⟩ =>
              even_assemble E1 F1 E2 F2 h1 h2 hpair
      | .inl hxa, .inr hyb, .inl hzc, .inl hwd =>
          (ev_ne_od hev
            (od_ev (od_ev (ev_od (sq_ev hxa) (sq_od hyb)) (sq_ev hzc))
              (sq_ev hwd))).elim
      | .inl hxa, .inr hyb, .inl hzc, .inr hwd =>
          match ph_even x z hxa hzc, ph_odd y w hyb hwd with
          | ⟨E1, F1, h1⟩, ⟨E2, F2, h2⟩ =>
              even_assemble E1 F1 E2 F2 h1 h2 hpair2
      | .inl hxa, .inr hyb, .inr hzc, .inl hwd =>
          match ph_even x w hxa hwd, ph_odd y z hyb hzc with
          | ⟨E1, F1, h1⟩, ⟨E2, F2, h2⟩ =>
              even_assemble E1 F1 E2 F2 h1 h2 hpair3
      | .inl hxa, .inr hyb, .inr hzc, .inr hwd =>
          (ev_ne_od hev
            (ev_od (od_od (ev_od (sq_ev hxa) (sq_od hyb)) (sq_od hzc))
              (sq_od hwd))).elim
      | .inr hxa, .inl hyb, .inl hzc, .inl hwd =>
          (ev_ne_od hev
            (od_ev (od_ev (od_ev (sq_od hxa) (sq_ev hyb)) (sq_ev hzc))
              (sq_ev hwd))).elim
      | .inr hxa, .inl hyb, .inl hzc, .inr hwd =>
          match ph_odd x w hxa hwd, ph_even y z hyb hzc with
          | ⟨E1, F1, h1⟩, ⟨E2, F2, h2⟩ =>
              even_assemble E1 F1 E2 F2 h1 h2 hpair3
      | .inr hxa, .inl hyb, .inr hzc, .inl hwd =>
          match ph_odd x z hxa hzc, ph_even y w hyb hwd with
          | ⟨E1, F1, h1⟩, ⟨E2, F2, h2⟩ =>
              even_assemble E1 F1 E2 F2 h1 h2 hpair2
      | .inr hxa, .inl hyb, .inr hzc, .inr hwd =>
          (ev_ne_od hev
            (ev_od (od_od (od_ev (sq_od hxa) (sq_ev hyb)) (sq_od hzc))
              (sq_od hwd))).elim
      | .inr hxa, .inr hyb, .inl hzc, .inl hwd =>
          match ph_odd x y hxa hyb, ph_even z w hzc hwd with
          | ⟨E1, F1, h1⟩, ⟨E2, F2, h2⟩ =>
              even_assemble E1 F1 E2 F2 h1 h2 hpair
      | .inr hxa, .inr hyb, .inl hzc, .inr hwd =>
          (ev_ne_od hev
            (ev_od (ev_add (od_od (sq_od hxa) (sq_od hyb)) (sq_ev hzc))
              (sq_od hwd))).elim
      | .inr hxa, .inr hyb, .inr hzc, .inl hwd =>
          (ev_ne_od hev
            (od_ev (ev_od (od_od (sq_od hxa) (sq_od hyb)) (sq_od hzc))
              (sq_ev hwd))).elim
      | .inr hxa, .inr hyb, .inr hzc, .inr hwd =>
          match ph_odd x y hxa hyb, ph_odd z w hzc hwd with
          | ⟨E1, F1, h1⟩, ⟨E2, F2, h2⟩ =>
              even_assemble E1 F1 E2 F2 h1 h2 hpair

private theorem descend (p : Nat)
    (hirr : ∀ a b : Nat, a * b = p → a = 1 ∨ b = 1) :
    ∀ f m : Nat, m ≤ f → 1 ≤ m → m < p →
      (∃ a b c d : Nat, ((a * a + b * b) + c * c) + d * d = m * p) →
      ∃ a b c d : Nat, ((a * a + b * b) + c * c) + d * d = p
  | 0, _, hf, h1, _, _ => nomatch (le_trans h1 hf)
  | _ + 1, 0, _, h1, _, _ => nomatch h1
  | _ + 1, 1, _, _, _, ⟨a, b, c, d, hs⟩ =>
      ⟨a, b, c, d, hs.trans (Nat.one_mul p)⟩
  | f + 1, m + 2, hf, _, hmp, ⟨a, b, c, d, hs⟩ =>
      match par (m + 2) with
      | ⟨t, .inl hpar⟩ =>
          match t, hpar with
          | 0, hp0 => nomatch hp0
          | t' + 1, hpar1 =>
              have htm : t' + 1 < m + 2 :=
                le_trans
                  (add_le_add_left' (Nat.succ_le_succ (Nat.zero_le t')) (t' + 1))
                  (Nat.le_of_eq hpar1.symm)
              match even_step p (t' + 1) a b c d
                  (hs.trans (congrArg (· * p) hpar1)) with
              | ⟨e, f', g, h', hs'⟩ =>
                  descend p hirr f (t' + 1)
                    (succ_le_succ_inv (le_trans htm hf))
                    (Nat.succ_le_succ (Nat.zero_le t'))
                    (Nat.lt_of_lt_of_le htm (Nat.le_of_lt hmp))
                    ⟨e, f', g, h', hs'⟩
      | ⟨t, .inr hpar⟩ =>
          match t, hpar with
          | 0, hp0 => nomatch (Nat.succ.inj hp0)
          | t' + 1, hpar1 =>
              match odd_step p (m + 2) (t' + 1) hirr hpar1
                  (Nat.le.intro (Nat.add_comm 2 m)) hmp a b c d hs with
              | ⟨r, hr1, hrm, e1, e2, e3, e4, hs'⟩ =>
                  descend p hirr f r
                    (succ_le_succ_inv (le_trans hrm hf)) hr1
                    (Nat.lt_of_lt_of_le hrm (Nat.le_of_lt hmp))
                    ⟨e1, e2, e3, e4, hs'⟩

private theorem prime_sum (p : Nat) (h2 : 2 ≤ p)
    (hirr : ∀ a b : Nat, a * b = p → a = 1 ∨ b = 1) :
    ∃ a b c d : Nat, ((a * a + b * b) + c * c) + d * d = p :=
  match par p with
  | ⟨t, .inl hpar⟩ =>
      match t, hpar with
      | 0, hp0 => nomatch (le_trans h2 (Nat.le_of_eq hp0))
      | 1, hp1 => ⟨1, 1, 0, 0, hp1.symm⟩
      | t' + 2, hp2 =>
          have h2t : 2 * (t' + 2) = p :=
            ((succ_mul' 1 (t' + 2)).trans
              (congrArg (· + (t' + 2)) (Nat.one_mul (t' + 2)))).trans hp2.symm
          match hirr 2 (t' + 2) h2t with
          | .inl h21 => nomatch (Nat.succ.inj h21)
          | .inr ht1 => nomatch (Nat.succ.inj ht1)
  | ⟨t, .inr hpar⟩ =>
      match t, hpar with
      | 0, hp0 =>
          (no_number_is_below_itself 1 (le_trans h2 (Nat.le_of_eq hp0))).elim
      | t' + 1, hp1 =>
          match residue_collision p (t' + 1) hirr hp1
              (Nat.succ_le_succ (Nat.zero_le t')) with
          | ⟨x, y, M, hcol, hM1, hMp⟩ =>
              descend p hirr M M (Nat.le_refl M) hM1 hMp ⟨x, y, 1, 0, hcol⟩

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

theorem four_squares_carry_every_number :
    ∀ n : Nat, ∃ a b c d : Nat, a * a + b * b + c * c + d * d = n :=
  the_identity_carries_the_composites.2 prime_sum

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

private def code : Compass → Nat
  | .n => 0
  | .e => 1
  | .s => 2
  | .w => 3

private theorem code_lt : ∀ c : Compass, code c < 4
  | .n => Nat.le.step (Nat.le.step (Nat.le.step Nat.le.refl))
  | .e => Nat.le.step (Nat.le.step Nat.le.refl)
  | .s => Nat.le.step Nat.le.refl
  | .w => Nat.le.refl

private theorem code_inj : ∀ {c d : Compass}, code c = code d → c = d
  | .n, .n, _ => rfl
  | .n, .e, h => nomatch h
  | .n, .s, h => nomatch h
  | .n, .w, h => nomatch h
  | .e, .n, h => nomatch h
  | .e, .e, _ => rfl
  | .e, .s, h => nomatch Nat.succ.inj h
  | .e, .w, h => nomatch Nat.succ.inj h
  | .s, .n, h => nomatch h
  | .s, .e, h => nomatch Nat.succ.inj h
  | .s, .s, _ => rfl
  | .s, .w, h => nomatch Nat.succ.inj (Nat.succ.inj h)
  | .w, .n, h => nomatch h
  | .w, .e, h => nomatch Nat.succ.inj h
  | .w, .s, h => nomatch Nat.succ.inj (Nat.succ.inj h)
  | .w, .w, _ => rfl

private theorem base_split : ∀ (a b : Nat) {k l : Nat}, k < 4 → l < 4 →
    k + 4 * a = l + 4 * b → k = l ∧ a = b
  | 0, 0, _, _, _, _, h => ⟨h, rfl⟩
  | 0, b + 1, k, l, hk, _, h =>
      absurd
        (le_trans hk
          (le_trans (Nat.le_add_left 4 (l + 4 * b)) (Nat.le_of_eq h.symm)))
        (no_number_is_below_itself k)
  | a + 1, 0, k, l, _, hl, h =>
      absurd
        (le_trans hl
          (le_trans (Nat.le_add_left 4 (k + 4 * a)) (Nat.le_of_eq h)))
        (no_number_is_below_itself l)
  | a + 1, b + 1, k, l, hk, hl, h =>
      have h4 : (k + 4 * a) + 4 = (l + 4 * b) + 4 := h
      match base_split a b hk hl (add_right_cancel' 4 h4) with
      | ⟨h1, h2⟩ => ⟨h1, congrArg (· + 1) h2⟩

private theorem mul4_le {x y : Nat} (h : x ≤ y) : 4 * x ≤ 4 * y :=
  Nat.le.rec (motive := fun z _ => 4 * x ≤ 4 * z) Nat.le.refl
    (fun {_} _ ih => le_trans ih (Nat.le_add_right _ 4)) h

private theorem bound_step {k e P : Nat} (hk : k < 4) (he : e < P) :
    k + 4 * e < 4 * P :=
  le_trans
    (Nat.le_of_eq
      (((adding_associates k (4 * e) 1).symm.trans
        (congrArg (k + ·) (Nat.add_comm (4 * e) 1))).trans
        (adding_associates k 1 (4 * e))))
    (le_trans (add_le_add' hk (@Nat.le.refl (4 * e)))
      (le_trans (Nat.le_of_eq (Nat.add_comm 4 (4 * e))) (mul4_le he)))

private def fourPow : Nat → Nat
  | 0 => 1
  | n + 1 => 4 * fourPow n

private def enc : List Compass → Nat
  | [] => 0
  | c :: cs => code c + 4 * enc cs

private theorem enc_lt : ∀ v : List Compass, enc v < fourPow v.length
  | [] => Nat.le.refl
  | c :: cs => bound_step (code_lt c) (enc_lt cs)

private theorem enc_inj : ∀ v w : List Compass, v.length = w.length →
    enc v = enc w → v = w
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl
  | c :: cs, d :: ds, hl, he =>
      match base_split (enc cs) (enc ds) (code_lt c) (code_lt d) he with
      | ⟨h1, h2⟩ =>
          congr (congrArg List.cons (code_inj h1))
            (enc_inj cs ds (Nat.succ.inj hl) h2)

private theorem zipPull_len : ∀ v w : List Compass, v.length = w.length →
    (zipPull v w).length = v.length
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: v, _ :: w, h => congrArg (· + 1) (zipPull_len v w (Nat.succ.inj h))

private theorem rot_len : ∀ v : List Compass, (rotateLeft v).length = v.length
  | [] => rfl
  | c :: cs => (len_cons_eq_len_snoc cs c c).symm

private theorem round_len (v : List Compass) : (round v).length = v.length :=
  zipPull_len v (rotateLeft v) (rot_len v).symm

theorem the_round_repeats_its_tail (v : List Compass) :
    ∃ i j : Nat, i < j ∧
      ∀ t : Nat, Nat.repeat round (i + t) v = Nat.repeat round (j + t) v :=
  have hlen : ∀ k : Nat, (Nat.repeat round k v).length = v.length := fun k =>
    Nat.rec (motive := fun n => (Nat.repeat round n v).length = v.length)
      rfl (fun n ih => (round_len (Nat.repeat round n v)).trans ih) k
  have hb : ∀ k : Nat, enc (Nat.repeat round k v) < fourPow v.length := fun k =>
    Nat.lt_of_lt_of_le (enc_lt (Nat.repeat round k v))
      (Nat.le_of_eq (congrArg fourPow (hlen k)))
  match fn_collides
      (fun k =>
        (⟨enc (Nat.repeat round k v), hb k⟩ : Fin (fourPow v.length))) with
  | ⟨i, j, hij, _, hg⟩ =>
      have hmeet : Nat.repeat round i v = Nat.repeat round j v :=
        enc_inj (Nat.repeat round i v) (Nat.repeat round j v)
          ((hlen i).trans (hlen j).symm) (congrArg Fin.val hg)
      ⟨i, j, hij, fun t =>
        Nat.rec
          (motive := fun u =>
            Nat.repeat round (i + u) v = Nat.repeat round (j + u) v)
          hmeet (fun _ ih => congrArg round ih) t⟩

/-- info: 'Foam.Minds.Lagrange.the_first_variation_reads_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_variation_reads_nothing

/-- info: 'Foam.Minds.Lagrange.the_bounded_expansion_repeats' does not depend on any axioms -/
#guard_msgs in #print axioms the_bounded_expansion_repeats

/-- info: 'Foam.Minds.Lagrange.four_squares_carry_every_number' does not depend on any axioms -/
#guard_msgs in #print axioms four_squares_carry_every_number

/-- info: 'Foam.Minds.Lagrange.the_identity_carries_the_composites' does not depend on any axioms -/
#guard_msgs in #print axioms the_identity_carries_the_composites

/-- info: 'Foam.Minds.Lagrange.the_truncation_leaves_a_real_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_truncation_leaves_a_real_remainder

/-- info: 'Foam.Minds.Lagrange.the_quintic_waits_one_seat_wider' does not depend on any axioms -/
#guard_msgs in #print axioms the_quintic_waits_one_seat_wider

/-- info: 'Foam.Minds.Lagrange.the_round_repeats_its_tail' does not depend on any axioms -/
#guard_msgs in #print axioms the_round_repeats_its_tail

end Foam.Minds.Lagrange
