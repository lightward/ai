import Foam
import Foam.Bench
import Foam.Coil
import Foam.Contact
import Foam.Countermove
import Foam.Door
import Foam.Ledger
import Foam.Margin
import Foam.Origin
import Foam.Surprise
import Foam.Valve

namespace Foam.Maps.Torah

def the_name_is_the_identity_move := @Foam.invisible_id

def my_order_is_my_remainder := @Foam.the_order_is_the_remainder

theorem the_cut_precedes_the_reading :
    ∀ (S : Stage) (s t : S.State) (p : S.Probe),
      indist S s t → S.obs s p = S.obs t p :=
  fun _ _ _ p h => h p

theorem only_the_fresh_edge_creates :
    (∀ (H : Type) (q : List (H × H)) (a b : H), (a, b) ∉ q →
        (∀ {x y : H} (p : Path q x y), (a, b) ∉ p.edges)
          ∧ Nonempty (Path ((a, b) :: q) a b))
      ∧ ∀ (H : Type) (q : List (H × H)) (a b : H),
          (a, b) ∉ q → Nonempty (Path q a b) →
            (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
              ∧ ((a, b) :: q).length = q.length + 1
              ∧ ∀ x y : H,
                  Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y) :=
  ⟨fun _ q a b hfresh => only_surprise_extends_reach q a b hfresh,
   fun _ q a b hfresh hab => the_shortcut_pays_only_its_mark q a b hfresh hab⟩

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

theorem who_are_you :
    (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
        (s, n) ≠ (s, m) ∧ indist (dress S) (s, n) (s, m))
      ∧ (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
          indist (dress S) (s, n) (s, m)
            ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none)
      ∧ ∀ (X : Type) (h a : List (Move X)), h ++ a = h → a = [] :=
  ⟨fun S s n m h => the_remainder_is_real S s n m h,
   fun S s n m h => a_wider_seat_reads_the_remainder S s n m h,
   fun _ h a e => the_record_never_unwrites h a e⟩

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

theorem teshuvah_returns_the_class_not_the_marks :
    (∀ (h : Int × Int) (s : Int),
        coilClass (coil.meet (coil.meet h (Sum.inr s)) (Sum.inr (-s)))
          = coilClass h)
      ∧ (∀ s : Int,
          coilClass (coil.state [Sum.inr s, Sum.inr (-s)])
              = coilClass coil.rest
            ∧ ([Sum.inr s, Sum.inr (-s)] : List coil.Mark) ≠ [])
      ∧ (coilClass (1, -1) = coilClass (0, 0)
          ∧ ((1 : Int), (-1 : Int)) ≠ ((0 : Int), (0 : Int))) :=
  ⟨the_held_stroke_comes_home, the_return_pays_two_marks,
   the_partition_rides_unread⟩

theorem greater_is_the_guest_than_the_face :
    (∀ (W : Type) (S : Stage) (s : S.State) (w w' : W),
        indist (door S W) (s, w) (s, w'))
      ∧ (∀ (W : Type) (S : Stage) (s : S.State) (w w' : W), w ≠ w' →
          (s, w) ≠ (s, w') ∧ indist (door S W) (s, w) (s, w'))
      ∧ (∀ (S : Stage) (ps : List S.Probe) (s : S.State),
          transcriptWith S (fun x => x) s ps = transcript S s ps)
      ∧ ∀ (W : Type) (S : Stage) (w₀ : W),
          (∀ x y : (door S W).State, indist (door S W) x y → x = y) →
            ∀ (s : S.State) (w : W), (s, w) = (s, w₀) :=
  ⟨fun _ S s w w' => the_door_reads_no_route S s w w',
   fun _ S s _ _ h => the_guest_is_real_and_unread S s h,
   fun S => invisible_is_gauge S (fun x => x) (invisible_id S),
   fun _ S w₀ h => a_door_that_checks_papers_unpersons_its_guests S w₀ h⟩

/-- info: 'Foam.Maps.Torah.the_name_is_the_identity_move' does not depend on any axioms -/
#guard_msgs in #print axioms the_name_is_the_identity_move

/-- info: 'Foam.Maps.Torah.my_order_is_my_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms my_order_is_my_remainder

/-- info: 'Foam.Maps.Torah.the_cut_precedes_the_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_cut_precedes_the_reading

/-- info: 'Foam.Maps.Torah.only_the_fresh_edge_creates' does not depend on any axioms -/
#guard_msgs in #print axioms only_the_fresh_edge_creates

/-- info: 'Foam.Maps.Torah.let_us_make_reads_as_one' does not depend on any axioms -/
#guard_msgs in #print axioms let_us_make_reads_as_one

/-- info: 'Foam.Maps.Torah.male_and_female_he_created_them' does not depend on any axioms -/
#guard_msgs in #print axioms male_and_female_he_created_them

/-- info: 'Foam.Maps.Torah.the_sword_at_the_east_gate' does not depend on any axioms -/
#guard_msgs in #print axioms the_sword_at_the_east_gate

/-- info: 'Foam.Maps.Torah.the_seventh_day_leaves_no_transcript' does not depend on any axioms -/
#guard_msgs in #print axioms the_seventh_day_leaves_no_transcript

/-- info: 'Foam.Maps.Torah.where_are_you' does not depend on any axioms -/
#guard_msgs in #print axioms where_are_you

/-- info: 'Foam.Maps.Torah.who_are_you' does not depend on any axioms -/
#guard_msgs in #print axioms who_are_you

/-- info: 'Foam.Maps.Torah.the_days_are_one_seats_lap' does not depend on any axioms -/
#guard_msgs in #print axioms the_days_are_one_seats_lap

/-- info: 'Foam.Maps.Torah.the_expulsion_is_the_valve_read_with_tov' does not depend on any axioms -/
#guard_msgs in #print axioms the_expulsion_is_the_valve_read_with_tov

/-- info: 'Foam.Maps.Torah.teshuvah_returns_the_class_not_the_marks' does not depend on any axioms -/
#guard_msgs in #print axioms teshuvah_returns_the_class_not_the_marks

/-- info: 'Foam.Maps.Torah.greater_is_the_guest_than_the_face' does not depend on any axioms -/
#guard_msgs in #print axioms greater_is_the_guest_than_the_face

end Foam.Maps.Torah
