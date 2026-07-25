import Foam.Log
import Foam.Serving
import Foam.Minds.Boltzmann
import Foam.Minds.Shannon
import Foam.Minds.Landauer

namespace Foam.Exhibits.Entropy

def keyword : String := "Entropy"

def inscription : String := "S = k log W"

def dressReader : Beholder (Nat × String) :=
  ⟨Unit, String, fun s _ => s.2⟩

def groundReader : Beholder (Nat × String) :=
  ⟨Unit, Nat × Nat, fun s _ => ((book s.1).length, logTwo (book s.1).length)⟩

theorem the_ground_cannot_hear_the_inscription
    (n : Nat) (s s' : String) (p : Unit) :
    groundReader.obs (n, s) p = groundReader.obs (n, s') p := rfl

theorem the_street_cannot_hear_the_proof
    (n n' : Nat) (s : String) (p : Unit) :
    dressReader.obs (n, s) p = dressReader.obs (n', s) p := rfl

theorem the_stand_reads_true (st : Nat × String) :
    (groundReader.obs st ()).2 = st.1 :=
  the_book_logs_to_its_depth st.1

theorem the_stand_is_a_seat {R : Type}
    (g : dressReader.Ans → groundReader.Ans → R) :
    ∃ c : Beholder (Nat × String), ∃ post : c.Ans → R,
      ∃ enc : dressReader.Probe × groundReader.Probe → c.Probe,
        ∀ st p q,
          compare dressReader groundReader g st p q
            = post (c.obs st (enc (p, q))) :=
  the_comparison_is_a_seat dressReader groundReader g

def the_claim := @Foam.S_eq_k_log_W

def the_love := @Foam.Minds.Boltzmann.entropy_is_the_price_of_the_name

def the_fame :=
  And.intro @Foam.Minds.Shannon.entropy_of_the_source
    @Foam.Minds.Landauer.no_machine_undercuts_the_bill

def the_dark := @Foam.no_run_reads_its_own_ratio

/-- info: 'Foam.Exhibits.Entropy.the_ground_cannot_hear_the_inscription' does not depend on any axioms -/
#guard_msgs in #print axioms the_ground_cannot_hear_the_inscription

/-- info: 'Foam.Exhibits.Entropy.the_street_cannot_hear_the_proof' does not depend on any axioms -/
#guard_msgs in #print axioms the_street_cannot_hear_the_proof

/-- info: 'Foam.Exhibits.Entropy.the_stand_reads_true' does not depend on any axioms -/
#guard_msgs in #print axioms the_stand_reads_true

/-- info: 'Foam.Exhibits.Entropy.the_stand_is_a_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_stand_is_a_seat

/-- info: 'Foam.Exhibits.Entropy.the_claim' does not depend on any axioms -/
#guard_msgs in #print axioms the_claim

/-- info: 'Foam.Exhibits.Entropy.the_love' does not depend on any axioms -/
#guard_msgs in #print axioms the_love

/-- info: 'Foam.Exhibits.Entropy.the_fame' does not depend on any axioms -/
#guard_msgs in #print axioms the_fame

/-- info: 'Foam.Exhibits.Entropy.the_dark' does not depend on any axioms -/
#guard_msgs in #print axioms the_dark

end Foam.Exhibits.Entropy
