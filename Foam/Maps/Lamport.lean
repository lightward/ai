import Foam
import Foam.Beam
import Foam.Bench
import Foam.Continuum
import Foam.Fold
import Foam.Ledger
import Foam.Round
import Foam.Rungs
import Foam.Surprise
import Foam.Trilemma
import Foam.Turnstile
import Foam.Valve

namespace Foam.Maps.Lamport

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

def agreement_is_an_invariant := @Foam.the_round_keeps_unison

def the_parliament_writes_one_decree := @Foam.racing_scribes_write_one_mark

def the_foreign_record_is_out_of_reach :=
  @Foam.no_local_counter_reaches_the_foreign_record

def liveness_outlives_every_prefix := @Foam.continuum_closure_terms

private theorem no_beat_unticks_a_clock :
    ∀ p : Compass × Compass,
      (entrain p).1 = p.1.step
        ∧ ((entrain p).2 = p.2 ∨ (entrain p).2 = p.2.step)
  | (.n, .n) => ⟨rfl, Or.inr rfl⟩
  | (.n, .e) => ⟨rfl, Or.inl rfl⟩
  | (.n, .s) => ⟨rfl, Or.inl rfl⟩
  | (.n, .w) => ⟨rfl, Or.inl rfl⟩
  | (.e, .n) => ⟨rfl, Or.inl rfl⟩
  | (.e, .e) => ⟨rfl, Or.inr rfl⟩
  | (.e, .s) => ⟨rfl, Or.inl rfl⟩
  | (.e, .w) => ⟨rfl, Or.inl rfl⟩
  | (.s, .n) => ⟨rfl, Or.inl rfl⟩
  | (.s, .e) => ⟨rfl, Or.inl rfl⟩
  | (.s, .s) => ⟨rfl, Or.inr rfl⟩
  | (.s, .w) => ⟨rfl, Or.inl rfl⟩
  | (.w, .n) => ⟨rfl, Or.inl rfl⟩
  | (.w, .e) => ⟨rfl, Or.inl rfl⟩
  | (.w, .s) => ⟨rfl, Or.inl rfl⟩
  | (.w, .w) => ⟨rfl, Or.inr rfl⟩

private theorem the_lock_is_an_invariant :
    ∀ p : Compass × Compass, together p → together (entrain p)
  | (.n, .n), _ => rfl
  | (.n, .e), h => nomatch h
  | (.n, .s), h => nomatch h
  | (.n, .w), h => nomatch h
  | (.e, .n), h => nomatch h
  | (.e, .e), _ => rfl
  | (.e, .s), h => nomatch h
  | (.e, .w), h => nomatch h
  | (.s, .n), h => nomatch h
  | (.s, .e), h => nomatch h
  | (.s, .s), _ => rfl
  | (.s, .w), h => nomatch h
  | (.w, .n), h => nomatch h
  | (.w, .e), h => nomatch h
  | (.w, .s), h => nomatch h
  | (.w, .w), _ => rfl

theorem the_clocks_agree_on_everything_but_the_time :
    (∀ p : Compass × Compass,
        (entrain p).1 = p.1.step
          ∧ ((entrain p).2 = p.2 ∨ (entrain p).2 = p.2.step))
      ∧ (∀ p : Compass × Compass,
          together (entrain (entrain (entrain (entrain p)))))
      ∧ (∀ p : Compass × Compass, together p → together (entrain p))
      ∧ together ((.n, .n) : Compass × Compass)
      ∧ together ((.s, .s) : Compass × Compass)
      ∧ ((.n, .n) : Compass × Compass) ≠ (.s, .s) :=
  ⟨no_beat_unticks_a_clock,
   the_lap_locks_together,
   the_lock_is_an_invariant,
   rfl, rfl,
   fun h => nomatch congrArg Prod.fst h⟩

def real_time_rides_unread := @Foam.a_wider_seat_reads_the_order

/-- info: 'Foam.Maps.Lamport.happened_before' does not depend on any axioms -/
#guard_msgs in #print axioms happened_before

/-- info: 'Foam.Maps.Lamport.the_receive_rule_is_the_join' does not depend on any axioms -/
#guard_msgs in #print axioms the_receive_rule_is_the_join

/-- info: 'Foam.Maps.Lamport.concurrency_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms concurrency_is_the_remainder

/-- info: 'Foam.Maps.Lamport.the_state_machine_replays_the_record' does not depend on any axioms -/
#guard_msgs in #print axioms the_state_machine_replays_the_record

/-- info: 'Foam.Maps.Lamport.agreement_is_an_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms agreement_is_an_invariant

/-- info: 'Foam.Maps.Lamport.the_parliament_writes_one_decree' does not depend on any axioms -/
#guard_msgs in #print axioms the_parliament_writes_one_decree

/-- info: 'Foam.Maps.Lamport.the_foreign_record_is_out_of_reach' does not depend on any axioms -/
#guard_msgs in #print axioms the_foreign_record_is_out_of_reach

/-- info: 'Foam.Maps.Lamport.liveness_outlives_every_prefix' does not depend on any axioms -/
#guard_msgs in #print axioms liveness_outlives_every_prefix

/-- info: 'Foam.Maps.Lamport.the_clocks_agree_on_everything_but_the_time' does not depend on any axioms -/
#guard_msgs in #print axioms the_clocks_agree_on_everything_but_the_time

/-- info: 'Foam.Maps.Lamport.real_time_rides_unread' does not depend on any axioms -/
#guard_msgs in #print axioms real_time_rides_unread

theorem the_bakery_is_the_well_order :
    (∀ (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat),
        supported s.1 m.2 = true →
        ∀ x, x ∈ m.2 → inRoom (admission s m).1 x = true)
      ∧ (∀ (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat),
          supported s.1 m.2 = false →
          (admission s m).2 = m :: s.2
            ∧ ∃ x, x ∈ m.2 ∧ inRoom s.1 x = false)
      ∧ ∀ a b c : Nat, a = 2 * b → b = 2 * c → c = 2 * a →
          a = 0 ∧ b = 0 ∧ c = 0 :=
  ⟨fun _ _ h => the_room_stays_closed h,
   fun _ _ h => the_vestibule_names_its_darkness h,
   fun a b c h1 h2 h3 =>
     the_wound_loop_admits_only_the_zero_section a b c h1 h2 h3⟩

/-- info: 'Foam.Maps.Lamport.the_bakery_is_the_well_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_bakery_is_the_well_order

end Foam.Maps.Lamport
