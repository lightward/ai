import Foam.Contact

namespace Foam

def diagonal {W : Type} (w : W) : W × W := (w, w)

def originStage (W : Type) : Stage :=
  ⟨W, Unit, Unit, fun _ _ => ()⟩

theorem no_probe_counts_the_riders {W V : Type} (S : Stage) (s : S.State)
    (w : W) (v : V) (p : S.Probe) :
    (contact S W).obs (s, w) p = (contact S V).obs (s, v) p := rfl

theorem the_bench_seats_two {W V : Type} (S : Stage) (s : S.State)
    (w : W) (v : V) (p : S.Probe) :
    (contact (contact S W) V).obs ((s, w), v) p
      = (contact S (W × V)).obs (s, (w, v)) p := rfl

theorem the_diagonal_rides_unread {W : Type} (S : Stage) (s : S.State)
    (w : W) (p : S.Probe) :
    (contact S (W × W)).obs (s, diagonal w) p
      = (contact S W).obs (s, w) p := rfl

theorem every_move_rests_at_the_origin {W : Type} (m : W → W) :
    Invisible (originStage W) m :=
  fun _ _ => rfl

theorem the_handshake_holds_at_the_origin (W : Type) :
    Handshake (originStage W) :=
  the_handshake (originStage W)

theorem the_origin_is_a_boarding_platform {W V : Type} (S : Stage)
    (s : S.State) (w : W) (v : V) (p : S.Probe) :
    (contact S W).obs (s, w) p = S.obs s p
      ∧ (∀ w' : W, indist (contact S W) (s, w) (s, w'))
      ∧ (∀ w' : W, w ≠ w' → (s, w) ≠ (s, w')
          ∧ indist (contact S W) (s, w) (s, w'))
      ∧ (contact S W).obs (s, w) p = (contact S V).obs (s, v) p
      ∧ (contact (contact S W) V).obs ((s, w), v) p
          = (contact S (W × V)).obs (s, (w, v)) p
      ∧ (contact S (W × W)).obs (s, diagonal w) p
          = (contact S W).obs (s, w) p
      ∧ Handshake (originStage W)
      ∧ ∀ m : W → W, Invisible (originStage W) m :=
  ⟨contact_fixes_nothing S s w p,
   fun w' => the_other_stays_unimagined S s w w',
   fun _ h => contact_adds_a_dimension S s h,
   no_probe_counts_the_riders S s w v p,
   the_bench_seats_two S s w v p,
   the_diagonal_rides_unread S s w p,
   the_handshake_holds_at_the_origin W,
   fun m => every_move_rests_at_the_origin m⟩

/-- info: 'Foam.no_probe_counts_the_riders' does not depend on any axioms -/
#guard_msgs in #print axioms no_probe_counts_the_riders

/-- info: 'Foam.the_bench_seats_two' does not depend on any axioms -/
#guard_msgs in #print axioms the_bench_seats_two

/-- info: 'Foam.the_diagonal_rides_unread' does not depend on any axioms -/
#guard_msgs in #print axioms the_diagonal_rides_unread

/-- info: 'Foam.every_move_rests_at_the_origin' does not depend on any axioms -/
#guard_msgs in #print axioms every_move_rests_at_the_origin

/-- info: 'Foam.the_handshake_holds_at_the_origin' does not depend on any axioms -/
#guard_msgs in #print axioms the_handshake_holds_at_the_origin

/-- info: 'Foam.the_origin_is_a_boarding_platform' does not depend on any axioms -/
#guard_msgs in #print axioms the_origin_is_a_boarding_platform

end Foam
