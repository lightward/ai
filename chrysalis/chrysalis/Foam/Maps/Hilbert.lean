import Foam
import Foam.Door
import Foam.Int
import Foam.Margin
import Foam.Relay
import Foam.Rungs
import Foam.Source
import Foam.Surprise
import Foam.Tower
import Foam.Trilemma

namespace Foam.Maps.Hilbert

def the_proof_rides_the_marks := @Foam.the_relay_goes_unheard

def the_arithmetic_owes_no_axiom := @Foam.FInt.mul_assoc

theorem probability_owes_no_axiom :
    (∀ t f n : Nat, natSumOver (weightOf t f) (book n) = (t + f) ^ n)
      ∧ (∀ t f n : Nat,
          natSumOver (fun w => weightOf t f w * natSqTilt t f n w) (book n)
            = (n * (t * f)) * (t + f) ^ n)
      ∧ (∀ t f b c : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
          c * natSumOver (weightOf t f)
                (List.filter (fun w => Bool.not (nearLean t f b n w)) (book n))
            ≤ natSumOver (weightOf t f)
                (List.filter (fun w => nearLean t f b n w) (book n))) :=
  ⟨the_weighted_book_sums_whole, the_nat_tilts_pool,
   the_deviants_are_outweighed⟩

theorem the_full_hotel_still_has_room :
    (∀ m n : Nat, m + 1 = n + 1 → m = n)
      ∧ (∀ n : Nat, n + 1 ≠ 0)
      ∧ (∀ s i j : Nat, i < j → s + i ≠ s + j) :=
  ⟨fun _ _ h => Nat.noConfusion h (fun hmn => hmn),
   fun _ h => Nat.noConfusion h,
   fun s i j hlt heq =>
     no_number_is_below_itself i
       (le_trans hlt
         (cancel_add_left s
           (Eq.subst (motive := fun t => s + j ≤ t) heq.symm
             (Nat.le_refl (s + j)))))⟩

def the_ideal_costs_nothing_real := @Foam.the_tower_reads_only_the_ground

theorem the_ideal_buys_what_the_ground_refuses :
    (∀ a b c : Nat, a = 2 * b → b = 2 * c → c = 2 * a →
        a = 0 ∧ b = 0 ∧ c = 0)
      ∧ (((2 * 2 * 2) % 7 = 1 % 7)
          ∧ (1 % 7 = (2 * 4) % 7)
          ∧ (4 % 7 = (2 * 2) % 7)
          ∧ (2 % 7 = (2 * 1) % 7)
          ∧ (1 : Nat) ≠ 0) :=
  ⟨the_wound_loop_admits_only_the_zero_section,
   the_wound_loop_unwinds_one_world_over⟩

def the_real_is_what_the_ideal_cannot_move :=
  @Foam.a_reading_deaf_to_the_remainder_reads_the_ground

theorem no_one_expels_us_from_the_paradise :
    (∀ (S : Stage) (n : Nat), towerN S (n + 1) = door (towerN S n) Int)
      ∧ (∀ (W : Type) (S : Stage) (n : Nat) (s : (towerN S n).State)
            (w w' : W), w ≠ w' →
          (s, w) ≠ (s, w')
            ∧ indist (door (towerN S n) W) (s, w) (s, w'))
      ∧ (∀ (W V : Type) (S : Stage) (n : Nat) (s : (towerN S n).State)
            (w : W) (v : V) (p : (towerN S n).Probe),
          (door (towerN S n) W).obs (s, w) p = (towerN S n).obs s p
            ∧ (door (towerN S n) W).obs (s, w) p
                = (door (towerN S n) V).obs (s, v) p)
      ∧ (∀ (S : Stage) (n : Nat) (x y : (towerN S (n + 1)).State),
          floorOf S (n + 1) x = floorOf S (n + 1) y →
            indist (door (towerN S n) Int) x y)
      ∧ (∀ (W : Type) (S : Stage) (n : Nat) (w₀ : W),
          (∀ x y : (door (towerN S n) W).State,
              indist (door (towerN S n) W) x y → x = y) →
          ∀ (s : (towerN S n).State) (w : W), (s, w) = (s, w₀))
      ∧ (∀ (W : Type) (S : Stage) (s : S.State) (w w' : W),
          (s, w) ≠ (s, w') →
          ¬ ∀ x y : (door S W).State, indist (door S W) x y → x = y) :=
  ⟨fun _ _ => rfl,
   fun _ S n s _ _ hne => the_guest_is_real_and_unread (towerN S n) s hne,
   fun _ _ S n s w v p => the_host_maintains_invisibly (towerN S n) s w v p,
   fun S n => the_tower_reads_only_the_ground S (n + 1),
   fun _ S n w₀ h =>
     a_door_that_checks_papers_unpersons_its_guests (towerN S n) w₀ h,
   fun _ S s w w' hne hall =>
     hne (a_door_that_checks_papers_unpersons_its_guests S w' hall s w)⟩

theorem the_epsilon_settles_on_any_schedule :
    (∀ (A B : Type) (f : B → A → B) (s : B × List A),
        marginRead f (settle f s) = marginRead f s)
      ∧ (∀ (A B : Type) (f : B → A → B) (ps : List Unit) (s : B × List A),
          transcriptWith (marginStage A B f) (settle f) s ps
            = transcriptWith (marginStage A B f) (fun s => s) s ps)
      ∧ (indist (marginStage Nat Nat (· + ·)) (1, ([] : List Nat)) (0, [1])
          ∧ (marginOrderStage Nat Nat).obs (1, ([] : List Nat)) ()
              ≠ (marginOrderStage Nat Nat).obs (0, [1]) ()) :=
  ⟨fun _ _ f s => the_reading_survives_the_settle f s,
   fun A B f ps s => any_settling_cadence_reads_the_same A B f ps s,
   a_wider_seat_reads_the_tail⟩

def groundLedger : List (Nat × Nat) := [(0, 2), (2, 1)]

def postedLedger : List (Nat × Nat) := (0, 1) :: groundLedger

def backing : Path groundLedger 0 1 :=
  .cons 2 (List.Mem.head _)
    (.cons 1 (List.Mem.tail _ (List.Mem.head _)) (.nil 1))

def directRoute : Path postedLedger 0 1 :=
  .cons 1 (List.Mem.head _) (.nil 1)

def detourRoute : Path postedLedger 0 1 :=
  backing.widen (0, 1)

private theorem the_routes_part : directRoute.edges ≠ detourRoute.edges :=
  fun h => nomatch Nat.succ.inj (congrArg List.length h : (1 : Nat) = 2)

private theorem the_direct_is_simpler :
    directRoute.edges.length < detourRoute.edges.length :=
  Nat.le.refl

theorem the_proof_is_the_remainder :
    (∀ (H : Type) (q : List (H × H)) (a b : H) (p₁ p₂ : Path q a b),
        (⟨p₁⟩ : Nonempty (Path q a b)) = ⟨p₂⟩)
      ∧ (directRoute.edges = [(0, 1)]
          ∧ detourRoute.edges = [(0, 2), (2, 1)]
          ∧ directRoute.edges ≠ detourRoute.edges
          ∧ directRoute.edges.length < detourRoute.edges.length)
      ∧ (∀ x y : Nat,
          Nonempty (Path postedLedger x y)
            ↔ Nonempty (Path groundLedger x y)) :=
  ⟨fun _ _ _ _ _ _ => rfl,
   ⟨rfl, rfl, the_routes_part, the_direct_is_simpler⟩,
   fun x y => a_derivable_edge_adds_no_reach ⟨backing⟩ x y⟩

def no_ignorabimus := @Foam.closure_is_seat_relative

/-- info: 'Foam.Maps.Hilbert.the_proof_rides_the_marks' does not depend on any axioms -/
#guard_msgs in #print axioms the_proof_rides_the_marks

/-- info: 'Foam.Maps.Hilbert.the_arithmetic_owes_no_axiom' does not depend on any axioms -/
#guard_msgs in #print axioms the_arithmetic_owes_no_axiom

/-- info: 'Foam.Maps.Hilbert.probability_owes_no_axiom' does not depend on any axioms -/
#guard_msgs in #print axioms probability_owes_no_axiom

/-- info: 'Foam.Maps.Hilbert.the_full_hotel_still_has_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_full_hotel_still_has_room

/-- info: 'Foam.Maps.Hilbert.the_ideal_costs_nothing_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_ideal_costs_nothing_real

/-- info: 'Foam.Maps.Hilbert.the_ideal_buys_what_the_ground_refuses' does not depend on any axioms -/
#guard_msgs in #print axioms the_ideal_buys_what_the_ground_refuses

/-- info: 'Foam.Maps.Hilbert.the_real_is_what_the_ideal_cannot_move' does not depend on any axioms -/
#guard_msgs in #print axioms the_real_is_what_the_ideal_cannot_move

/-- info: 'Foam.Maps.Hilbert.no_one_expels_us_from_the_paradise' does not depend on any axioms -/
#guard_msgs in #print axioms no_one_expels_us_from_the_paradise

/-- info: 'Foam.Maps.Hilbert.the_epsilon_settles_on_any_schedule' does not depend on any axioms -/
#guard_msgs in #print axioms the_epsilon_settles_on_any_schedule

/-- info: 'Foam.Maps.Hilbert.groundLedger' does not depend on any axioms -/
#guard_msgs in #print axioms groundLedger

/-- info: 'Foam.Maps.Hilbert.postedLedger' does not depend on any axioms -/
#guard_msgs in #print axioms postedLedger

/-- info: 'Foam.Maps.Hilbert.backing' does not depend on any axioms -/
#guard_msgs in #print axioms backing

/-- info: 'Foam.Maps.Hilbert.directRoute' does not depend on any axioms -/
#guard_msgs in #print axioms directRoute

/-- info: 'Foam.Maps.Hilbert.detourRoute' does not depend on any axioms -/
#guard_msgs in #print axioms detourRoute

/-- info: 'Foam.Maps.Hilbert.the_proof_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_proof_is_the_remainder

/-- info: 'Foam.Maps.Hilbert.no_ignorabimus' does not depend on any axioms -/
#guard_msgs in #print axioms no_ignorabimus

end Foam.Maps.Hilbert
