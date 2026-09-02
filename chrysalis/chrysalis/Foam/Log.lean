import Foam.Typical

namespace Foam

def logSearch : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, w => if 2 ^ (fuel + 1) ≤ w then fuel + 1 else logSearch fuel w

def logTwo (w : Nat) : Nat := logSearch w w

theorem logSearch_finds : ∀ (fuel w n : Nat), 2 ^ n ≤ w →
    (∀ s, n < s → ¬ 2 ^ s ≤ w) → n ≤ fuel → logSearch fuel w = n
  | 0, _, n, _, _, hn => by
      cases n with
      | zero => rfl
      | succ m => exact nomatch hn
  | fuel + 1, w, n, hpow, hbig, hn => by
      cases Nat.lt_or_ge fuel n with
      | inl hlt =>
          have he : n = fuel + 1 := Nat.le_antisymm hn hlt
          subst he
          show (if 2 ^ (fuel + 1) ≤ w then fuel + 1 else logSearch fuel w)
              = fuel + 1
          rw [if_pos hpow]
      | inr hge =>
          have hno : ¬ 2 ^ (fuel + 1) ≤ w :=
            hbig (fuel + 1) (Nat.succ_le_succ hge)
          show (if 2 ^ (fuel + 1) ≤ w then fuel + 1 else logSearch fuel w) = n
          rw [if_neg hno]
          exact logSearch_finds fuel w n hpow hbig hge

theorem two_pow_lt_two_pow {n s : Nat} (h : n < s) : 2 ^ n < 2 ^ s := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  rw [← hd, pow_splits (n + 1) d]
  have h1 : 2 ^ n < 2 ^ (n + 1) := by
    show 2 ^ n < 2 ^ n * 2
    rw [nat_mul_two]
    exact Nat.add_lt_add_left (two_pow_pos n) (2 ^ n)
  have h2 : 2 ^ (n + 1) ≤ 2 ^ (n + 1) * 2 ^ d := by
    rw [← Nat.mul_one (2 ^ (n + 1))]
    rw [FInt.nat_mul_assoc (2 ^ (n + 1)) 1 (2 ^ d)]
    rw [Nat.one_mul (2 ^ d)]
    exact Nat.mul_le_mul_left (2 ^ (n + 1)) (two_pow_pos d)
  exact le_trans h1 h2

theorem logTwo_pow (n : Nat) : logTwo (2 ^ n) = n :=
  logSearch_finds (2 ^ n) (2 ^ n) n (Nat.le_refl _)
    (fun _ hs h2 =>
      no_number_is_below_itself (2 ^ n)
        (le_trans (two_pow_lt_two_pow hs) h2))
    (le_of_succ_le (two_pow_clears_the_line n))

theorem the_book_logs_to_its_depth (n : Nat) :
    logTwo ((book n).length) = n := by
  rw [the_book_has_two_to_the_n]
  exact logTwo_pow n

theorem natSumOver_congr_mem {v u : List Bool → Nat} :
    ∀ L : List (List Bool), (∀ w, w ∈ L → v w = u w) →
      natSumOver v L = natSumOver u L
  | [], _ => rfl
  | w :: L, h => by
      show v w + natSumOver v L = u w + natSumOver u L
      rw [h w (.head L),
          natSumOver_congr_mem L (fun x hx => h x (.tail w hx))]

theorem the_price_is_the_log (n : Nat) :
    natSumOver List.length (book n)
      = (book n).length * logTwo ((book n).length) := by
  rw [natSumOver_congr_mem (book n)
        (fun w hw => book_words_have_length n w hw),
      natSumOver_const n (book n),
      the_book_logs_to_its_depth]

theorem S_eq_k_log_W (k n S W : Nat)
    (hW : W = (book n).length) (hS : S = k * n) :
    S = k * logTwo W := by
  rw [hS, hW, the_book_logs_to_its_depth]

/-- info: 'Foam.logSearch_finds' does not depend on any axioms -/
#guard_msgs in #print axioms logSearch_finds

/-- info: 'Foam.two_pow_lt_two_pow' does not depend on any axioms -/
#guard_msgs in #print axioms two_pow_lt_two_pow

/-- info: 'Foam.logTwo_pow' does not depend on any axioms -/
#guard_msgs in #print axioms logTwo_pow

/-- info: 'Foam.the_book_logs_to_its_depth' does not depend on any axioms -/
#guard_msgs in #print axioms the_book_logs_to_its_depth

/-- info: 'Foam.natSumOver_congr_mem' does not depend on any axioms -/
#guard_msgs in #print axioms natSumOver_congr_mem

/-- info: 'Foam.the_price_is_the_log' does not depend on any axioms -/
#guard_msgs in #print axioms the_price_is_the_log

/-- info: 'Foam.S_eq_k_log_W' does not depend on any axioms -/
#guard_msgs in #print axioms S_eq_k_log_W

end Foam
