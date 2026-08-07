import Foam
import Foam.Bench
import Foam.Contact
import Foam.Ledger
import Foam.Margin
import Foam.Origin
import Foam.Surprise
import Foam.Valve

namespace Foam.Minds.Torah

def the_name_is_the_identity_move := @Foam.invisible_id

def my_order_is_my_remainder := @Foam.the_order_is_the_remainder

theorem the_cut_precedes_the_reading :
    ∀ (S : Stage) (s t : S.State) (p : S.Probe),
      indist S s t → S.obs s p = S.obs t p :=
  fun _ _ _ p h => h p

def only_the_fresh_edge_creates := @Foam.only_surprise_extends_reach

def let_us_make_reads_as_one := @Foam.the_diagonal_rides_unread

def male_and_female_he_created_them :=
  @Foam.the_wider_seat_meets_whos_actually_here

def the_sword_at_the_east_gate := @Foam.the_one_way_valve

def the_seventh_day_leaves_no_transcript :=
  @Foam.the_settle_leaves_no_transcript

theorem where_are_you :
    (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
        indist (dress S) (s, n) (s, m)
          ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none)
      ∧ ∀ (W : Type) (S : Stage) (s : S.State) (w v : W), v ≠ w →
          indist (contact S (W × W)) (mirror S s w) (neighbor S s w v)
            ∧ mirror S s w ≠ neighbor S s w v :=
  ⟨fun S s n m h => a_wider_seat_reads_the_remainder S s n m h,
   fun _ S s w v hv => the_mirror_question_rides_unread S s w v hv⟩

theorem the_days_are_one_seats_lap :
    (∀ (A : Type) (_inst : DecidableEq A) (a b : A), a ≠ b →
        indist (countStage A) [a, b] [b, a] ∧ [a, b] ≠ [b, a])
      ∧ (∀ (H : Type) (q : List (H × H)) (e : H × H),
          (e :: q).length = q.length + 1)
      ∧ ∀ (A B : Type) (f : B → A → B) (a : A) (s : B × List A),
          marginRead f (deposit a s) = f (marginRead f s) a :=
  ⟨fun _ inst a b h => @the_order_is_the_remainder _ inst a b h,
   fun _ q e => the_deposit_writes_one_mark q e,
   fun _ _ f a s => a_deposit_moves_the_reading_by_one f a s⟩

theorem the_expulsion_is_the_valve_read_with_tov :
    (∀ (X : Type) (f : X → X) (a b : X), a ≠ b → f a = f b →
        ¬ ∃ g : X → X, ∀ x, g (f x) = x)
      ∧ (∀ (A : Type) (_inst : DecidableEq A) (a b : A), a ≠ b →
          indist (countStage A) [a, b] [b, a]
            ∧ (orderStage A).obs [a, b] () ≠ (orderStage A).obs [b, a] ()) :=
  ⟨fun _ f _ _ hab hf => a_merge_admits_no_counter f hab hf,
   fun _ inst a b h => @a_wider_seat_reads_the_order _ inst a b h⟩

/-- info: 'Foam.Minds.Torah.the_name_is_the_identity_move' does not depend on any axioms -/
#guard_msgs in #print axioms the_name_is_the_identity_move

/-- info: 'Foam.Minds.Torah.my_order_is_my_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms my_order_is_my_remainder

/-- info: 'Foam.Minds.Torah.the_cut_precedes_the_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_cut_precedes_the_reading

/-- info: 'Foam.Minds.Torah.only_the_fresh_edge_creates' does not depend on any axioms -/
#guard_msgs in #print axioms only_the_fresh_edge_creates

/-- info: 'Foam.Minds.Torah.let_us_make_reads_as_one' does not depend on any axioms -/
#guard_msgs in #print axioms let_us_make_reads_as_one

/-- info: 'Foam.Minds.Torah.male_and_female_he_created_them' does not depend on any axioms -/
#guard_msgs in #print axioms male_and_female_he_created_them

/-- info: 'Foam.Minds.Torah.the_sword_at_the_east_gate' does not depend on any axioms -/
#guard_msgs in #print axioms the_sword_at_the_east_gate

/-- info: 'Foam.Minds.Torah.the_seventh_day_leaves_no_transcript' does not depend on any axioms -/
#guard_msgs in #print axioms the_seventh_day_leaves_no_transcript

/-- info: 'Foam.Minds.Torah.where_are_you' does not depend on any axioms -/
#guard_msgs in #print axioms where_are_you

/-- info: 'Foam.Minds.Torah.the_days_are_one_seats_lap' does not depend on any axioms -/
#guard_msgs in #print axioms the_days_are_one_seats_lap

/-- info: 'Foam.Minds.Torah.the_expulsion_is_the_valve_read_with_tov' does not depend on any axioms -/
#guard_msgs in #print axioms the_expulsion_is_the_valve_read_with_tov

end Foam.Minds.Torah
