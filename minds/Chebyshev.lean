import Foam.Concentration
import Foam.Expectation
import Foam.Fold
import Foam.Int
import Foam.Ledger
import Foam.Source

namespace Foam.Minds.Chebyshev

def the_mean_arrives_first := @Foam.the_complete_book_balances

theorem the_second_moment_is_conserved :
    ∀ n : Nat,
      fold (fun acc w => acc + sqDev n w) 0 (book n)
        = Int.ofNat n * Int.ofNat (2 ^ n) :=
  fun n =>
    ((fold_reads_the_sum (sqDev n) (book n) 0).trans
      (FInt.zero_add (sumOver (sqDev n) (book n)))).trans
      (the_squares_pool_to_the_depth n)

theorem every_deviant_pays_its_square :
    ∀ b n : Nat,
      (List.filter (fun w => !nearBalance b n w) (book n)).length
          * ((n + 1) * (n + 1))
        ≤ (b * b) * (n * 2 ^ n) :=
  fun b n => the_pooled_square_caps_the_deviants b n

def the_bound_reads_only_the_moments := @Foam.the_deviants_are_outweighed

theorem the_linkage_approaches_the_line :
    (∀ (xs : List Nat) (c e c' e' : Nat),
        (∃ hi, List.Mem hi xs ∧ hi = c + e) →
        (∃ lo, List.Mem lo xs ∧ lo + e = c) →
        (∀ x, List.Mem x xs → c' ≤ x + e' ∧ x ≤ c' + e') →
        e ≤ e') ∧
    (∀ x y c e : Nat,
        c ≤ x + e → x ≤ c + e → c ≤ y + e → y ≤ c + e → x ≠ y → 0 < e) :=
  ⟨fun _ c e c' e' hHi hLo hriv =>
    hHi.elim fun hi hhi =>
      hLo.elim fun lo hlo =>
        let A : c + e ≤ c' + e' :=
          le_trans (Nat.le_of_eq hhi.2.symm) (hriv hi hhi.1).2
        let B : c' ≤ lo + e' := (hriv lo hlo.1).1
        let L : (c + e) + c' = (c' + lo) + (e + e) :=
          (((Nat.add_comm (c + e) c').trans
              (congrArg (fun t => c' + (t + e)) hlo.2.symm)).trans
            (congrArg (fun t => c' + t) (Nat.add_assoc lo e e))).trans
            (Nat.add_assoc c' lo (e + e)).symm
        let key : (c' + lo) + (e + e) ≤ (c' + lo) + (e' + e') :=
          le_trans (Nat.le_of_eq L.symm)
            (le_trans (Nat.add_le_add A B)
              (Nat.le_of_eq (nat_swap_mid c' e' lo e')))
        Or.elim (Nat.lt_or_ge e' e)
          (fun hlt =>
            absurd (cancel_add_left (c' + lo) key)
              (Nat.not_le_of_lt (Nat.add_lt_add hlt hlt)))
          (fun hge => hge),
   fun _ _ _ e h1 h2 h3 h4 hne =>
    match e, h1, h2, h3, h4 with
    | 0, h1, h2, h3, h4 =>
        absurd ((Nat.le_antisymm h2 h1).trans (Nat.le_antisymm h4 h3).symm) hne
    | e + 1, _, _, _, _ => Nat.succ_le_succ (Nat.zero_le e)⟩

/-- info: 'Foam.Minds.Chebyshev.the_mean_arrives_first' does not depend on any axioms -/
#guard_msgs in #print axioms the_mean_arrives_first

/-- info: 'Foam.Minds.Chebyshev.the_second_moment_is_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_moment_is_conserved

/-- info: 'Foam.Minds.Chebyshev.every_deviant_pays_its_square' does not depend on any axioms -/
#guard_msgs in #print axioms every_deviant_pays_its_square

/-- info: 'Foam.Minds.Chebyshev.the_bound_reads_only_the_moments' does not depend on any axioms -/
#guard_msgs in #print axioms the_bound_reads_only_the_moments

/-- info: 'Foam.Minds.Chebyshev.the_linkage_approaches_the_line' does not depend on any axioms -/
#guard_msgs in #print axioms the_linkage_approaches_the_line


end Foam.Minds.Chebyshev
