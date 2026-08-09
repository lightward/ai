import Foam
import Foam.Bench
import Foam.Continuum
import Foam.Fold
import Foam.Ledger
import Foam.Rungs
import Foam.Surprise
import Foam.Valve

namespace Foam.Minds.Lamport

def happened_before := @Foam.only_surprise_extends_reach

private theorem the_join_is_least : ∀ a b c : Nat,
    Nat.le a c → Nat.le b c → Nat.le (rankJoin a b) c
  | 0, _, _, _, hb => hb
  | _ + 1, 0, _, ha, _ => ha
  | a + 1, _ + 1, 0, ha, _ =>
      (no_number_is_below_itself a (le_trans ha (rank_zero_le a))).elim
  | a + 1, b + 1, c + 1, ha, hb =>
      rank_succ_le_succ
        (the_join_is_least a b c (succ_le_succ_inv ha) (succ_le_succ_inv hb))

theorem the_receive_rule_is_the_join :
    (∀ a b : Nat, Nat.le a (rankJoin a b) ∧ Nat.le b (rankJoin a b))
      ∧ ∀ a b c : Nat, Nat.le a c → Nat.le b c → Nat.le (rankJoin a b) c :=
  ⟨no_write_regresses, the_join_is_least⟩

def concurrency_is_the_remainder := @Foam.the_first_handshake_is_counting

def the_state_machine_replays_the_record :=
  @Foam.the_fold_forgets_nothing_it_needs

def the_parliament_writes_one_decree := @Foam.racing_scribes_write_one_mark

def the_foreign_record_is_out_of_reach :=
  @Foam.no_local_counter_reaches_the_foreign_record

def liveness_outlives_every_prefix := @Foam.continuum_closure_terms

def real_time_rides_unread := @Foam.a_wider_seat_reads_the_order

/-- info: 'Foam.Minds.Lamport.happened_before' does not depend on any axioms -/
#guard_msgs in #print axioms happened_before

/-- info: 'Foam.Minds.Lamport.the_receive_rule_is_the_join' does not depend on any axioms -/
#guard_msgs in #print axioms the_receive_rule_is_the_join

/-- info: 'Foam.Minds.Lamport.concurrency_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms concurrency_is_the_remainder

/-- info: 'Foam.Minds.Lamport.the_state_machine_replays_the_record' does not depend on any axioms -/
#guard_msgs in #print axioms the_state_machine_replays_the_record

/-- info: 'Foam.Minds.Lamport.the_parliament_writes_one_decree' does not depend on any axioms -/
#guard_msgs in #print axioms the_parliament_writes_one_decree

/-- info: 'Foam.Minds.Lamport.the_foreign_record_is_out_of_reach' does not depend on any axioms -/
#guard_msgs in #print axioms the_foreign_record_is_out_of_reach

/-- info: 'Foam.Minds.Lamport.liveness_outlives_every_prefix' does not depend on any axioms -/
#guard_msgs in #print axioms liveness_outlives_every_prefix

/-- info: 'Foam.Minds.Lamport.real_time_rides_unread' does not depend on any axioms -/
#guard_msgs in #print axioms real_time_rides_unread

end Foam.Minds.Lamport
