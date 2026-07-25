import Foam.Exhibits.Hall
import Foam.Log
import Foam.Minds.Boltzmann
import Foam.Minds.Shannon
import Foam.Minds.Landauer

namespace Foam.Exhibits

def entropy : Exhibit where
  Claim := ∀ (k n S W : Nat),
    W = (book n).length → S = k * n → S = k * logTwo W
  receipt := S_eq_k_log_W
  Love := ∀ (k n S W : Nat),
    W = (book n).length → S = k * n →
      S = k * logTwo W
        ∧ natSumOver List.length (book n)
            = (book n).length * logTwo (book n).length
        ∧ ∀ (L : Nat) (ms : List (List Bool)), AllDiff ms →
            (∀ m, m ∈ ms → m ∈ book L) → ms.length ≤ 2 ^ L
  love := Minds.Boltzmann.entropy_is_the_price_of_the_name
  Fame := ((∀ (n : Nat) (f : List Bool → List Bool),
        (∀ w1 w2, w1 ∈ book n → w2 ∈ book n → w1 ≠ w2 →
          ¬ ∃ t, f w1 ++ t = f w2) →
        n * (book n).length ≤ (pool ((book n).map f)).length)
      ∧ (∀ (n : Nat) (f : List Bool → List Bool),
          (pool ((book n).map f)).length
            = (massStage Bool).obs (pool ((book n).map f)) ())
      ∧ ∀ (A : Type) (xs ys : List A),
          (massStage A).obs (xs ++ ys) ()
            = (massStage A).obs xs () + (massStage A).obs ys ())
    ∧ ∀ (n : Nat) (f : List Bool → List Bool),
      (∀ w1 w2, w1 ∈ book n → w2 ∈ book n → w1 ≠ w2 →
        ¬ ∃ t, f w1 ++ t = f w2) →
      n * (book n).length ≤ (pool ((book n).map f)).length
  fame := And.intro Minds.Shannon.entropy_of_the_source
    Minds.Landauer.no_machine_undercuts_the_bill
  Dark := ∀ n : Nat, 0 < n →
    ∃ w₁ w₂ : List Bool, w₁ ∈ book n ∧ w₂ ∈ book n
      ∧ freq w₁ true ≠ freq w₂ true
  dark := no_run_reads_its_own_ratio
  keyword := "Entropy"
  inscription := "S = k log W"

/-- info: 'Foam.Exhibits.entropy' does not depend on any axioms -/
#guard_msgs in #print axioms entropy

end Foam.Exhibits
