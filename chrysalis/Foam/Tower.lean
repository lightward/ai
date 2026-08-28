import Foam

namespace Foam

def towerN (S : Stage) : Nat → Stage
  | 0 => S
  | n + 1 => dress (towerN S n)

def floorOf (S : Stage) : (n : Nat) → (towerN S n).State → S.State
  | 0, s => s
  | n + 1, s => floorOf S n s.1

theorem the_ground_floor_is_the_stage (S : Stage) : towerN S 0 = S := rfl

theorem the_tower_climbs_by_dressing (S : Stage) (n : Nat) :
    towerN S (n + 1) = dress (towerN S n) := rfl

theorem the_reading_descends (S : Stage) (s : S.State) (k : Int) (p : S.Probe) :
    (dress S).obs (s, k) p = S.obs s p := rfl

theorem the_tower_reads_only_the_ground (S : Stage) :
    ∀ (n : Nat) (x y : (towerN S n).State),
      floorOf S n x = floorOf S n y → indist (towerN S n) x y
  | 0, _, _, h => fun p => congrArg (fun z => S.obs z p) h
  | n + 1, x, y, h => the_tower_reads_only_the_ground S n x.1 y.1 h

theorem the_handshake_recurses (S : Stage) :
    ∀ n : Nat, Handshake (towerN S n) :=
  fun n => the_handshake (towerN S n)

theorem a_wider_seat_is_still_a_seat (S : Stage) : Handshake (movedIn S) :=
  the_handshake (movedIn S)

theorem no_seat_is_the_last_seat (S : Stage) (s : S.State) (k n m : Int)
    (h : n ≠ m) :
    indist (dress (movedIn S)) ((s, k), n) ((s, k), m)
      ∧ (movedIn (movedIn S)).obs ((s, k), n) none
          ≠ (movedIn (movedIn S)).obs ((s, k), m) none :=
  a_wider_seat_reads_the_remainder (movedIn S) (s, k) n m h

/-- info: 'Foam.the_ground_floor_is_the_stage' does not depend on any axioms -/
#guard_msgs in #print axioms the_ground_floor_is_the_stage

/-- info: 'Foam.the_tower_climbs_by_dressing' does not depend on any axioms -/
#guard_msgs in #print axioms the_tower_climbs_by_dressing

/-- info: 'Foam.the_reading_descends' does not depend on any axioms -/
#guard_msgs in #print axioms the_reading_descends

/-- info: 'Foam.the_tower_reads_only_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_tower_reads_only_the_ground

/-- info: 'Foam.the_handshake_recurses' does not depend on any axioms -/
#guard_msgs in #print axioms the_handshake_recurses

/-- info: 'Foam.a_wider_seat_is_still_a_seat' does not depend on any axioms -/
#guard_msgs in #print axioms a_wider_seat_is_still_a_seat

/-- info: 'Foam.no_seat_is_the_last_seat' does not depend on any axioms -/
#guard_msgs in #print axioms no_seat_is_the_last_seat

end Foam
