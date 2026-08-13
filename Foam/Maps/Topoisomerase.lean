import Foam.Beam
import Foam.Coil
import Foam.Door
import Foam.Seat
import Foam.Trilemma

namespace Foam.Maps.Topoisomerase

theorem the_relaxed_state :
    coilClass coil.rest = 0 ∧ coil.rest = ((0 : Int), (0 : Int)) :=
  ⟨Foam.the_relaxed_state, rfl⟩

theorem the_held_cut :
    (∀ (h : Int × Int) (s : Int),
        coilClass (coil.meet h (Sum.inr s)) = coilClass h + s)
      ∧ ∀ (h : Int × Int) (s : Int),
          coilClass (coil.meet (coil.meet h (Sum.inr s)) (Sum.inr (-s)))
            = coilClass h :=
  ⟨the_stroke_moves_the_class_by_its_size, the_held_stroke_comes_home⟩

theorem the_strand_passage :
    (∀ h : Int × Int, coilClass (coil.meet h (Sum.inr 1)) = coilClass h + 1)
      ∧ (∀ h : Int × Int, coilClass (coil.meet h (Sum.inr 2)) = coilClass h + 2)
      ∧ ∀ s : Int,
          coilClass (coil.state [Sum.inr s, Sum.inr (-s)])
              = coilClass coil.rest
            ∧ ([Sum.inr s, Sum.inr (-s)] : List coil.Mark) ≠ [] :=
  ⟨fun h => the_stroke_moves_the_class_by_its_size h 1,
   fun h => the_stroke_moves_the_class_by_its_size h 2,
   the_return_pays_two_marks⟩

theorem the_two_sectors :
    (∀ (h : Int × Int) (d : Int),
        coilClass (coil.meet h (Sum.inl d)) = coilClass h)
      ∧ (∀ k1 k2 k3 k1' k2' k3' u v w : Nat, 0 < u → 0 < v → 0 < w →
          k1' * u = k1 * v → k2' * v = k2 * w → k3' * w = k3 * u →
          k1' * (k2' * k3') = k1 * (k2 * k3))
      ∧ ∀ k1 k1' k2 k3 : Nat, k1 ≠ k1' → 0 < k2 * k3 →
          k1 * (k2 * k3) ≠ k1' * (k2 * k3) :=
  ⟨the_shuffle_conserves_the_class,
   fun k1 k2 k3 k1' k2' k3' u v w hu hv hw h1 h2 h3 =>
     the_holonomy_ignores_the_regauging k1 k2 k3 k1' k2' k3' u v w
       hu hv hw h1 h2 h3,
   fun k1 k1' k2 k3 h hp => the_cut_moves_the_class k1 k1' k2 k3 h hp⟩

theorem the_wrap_decides_the_sign :
    (∀ p : Compass × Compass,
        together (entrain (entrain (entrain (entrain p)))))
      ∧ (∀ p : Compass × Compass,
          opposed (conjugated (conjugated (conjugated (conjugated p)))))
      ∧ (∀ p : Compass × Compass,
          window (conjugated (window p)) = entrain p)
      ∧ ∀ h : Int × Int,
          coilClass (coil.meet h (Sum.inr (-2))) = coilClass h + (-2) :=
  ⟨the_lap_locks_together, the_conjugate_locks_opposed,
   two_windows_read_direct,
   fun h => the_stroke_moves_the_class_by_its_size h (-2)⟩

theorem the_coil :
    (∀ xs ys : List coil.Mark,
        coil.state (xs ++ ys) = fold coil.meet (coil.state xs) ys)
      ∧ (coilClass (1, -1) = coilClass (0, 0)
          ∧ ((1 : Int), (-1 : Int)) ≠ ((0 : Int), (0 : Int))) :=
  ⟨fun xs ys => a_seat_resumes coil xs ys, the_partition_rides_unread⟩

theorem below_equilibrium :
    (∀ (W : Type) (s : coil.stage.State) (w w' : W), w ≠ w' →
        (s, w) ≠ (s, w') ∧ indist (door coil.stage W) (s, w) (s, w'))
      ∧ (∀ (W V : Type) (s : coil.stage.State) (w : W) (v : V)
            (p : coil.stage.Probe),
          (door coil.stage W).obs (s, w) p = coil.stage.obs s p
            ∧ (door coil.stage W).obs (s, w) p
                = (door coil.stage V).obs (s, v) p)
      ∧ (∀ (X : Type) (f : (dress coil.stage).State → X),
          (∀ (s : coil.stage.State) (n m : Int), f (s, n) = f (s, m))
            ↔ ∃ g : coil.stage.State → X,
                ∀ (s : coil.stage.State) (n : Int), f (s, n) = g s)
      ∧ (∀ (W : Type)
            (m m' : (door coil.stage W).State → (door coil.stage W).State),
          Invisible (door coil.stage W) m → Invisible (door coil.stage W) m' →
            ∀ (ps : List (door coil.stage W).Probe)
              (s : (door coil.stage W).State),
              transcriptWith (door coil.stage W) m s ps
                = transcriptWith (door coil.stage W) m' s ps)
      ∧ ∀ (s : coil.stage.State) (n m : Int), n ≠ m →
          indist (dress coil.stage) (s, n) (s, m)
            ∧ (movedIn coil.stage).obs (s, n) none
                ≠ (movedIn coil.stage).obs (s, m) none :=
  ⟨fun _ s _ _ hw => the_guest_is_real_and_unread coil.stage s hw,
   fun _ _ s w v p => the_host_maintains_invisibly coil.stage s w v p,
   fun _ f => a_reading_deaf_to_the_remainder_reads_the_ground coil.stage f,
   fun W m m' hm hm' ps s =>
     correct_maintenance_has_no_signature (door coil.stage W) m m' hm hm' ps s,
   fun s n m h => a_wider_seat_reads_the_remainder coil.stage s n m h⟩

/-- info: 'Foam.Maps.Topoisomerase.the_relaxed_state' does not depend on any axioms -/
#guard_msgs in #print axioms the_relaxed_state

/-- info: 'Foam.Maps.Topoisomerase.the_held_cut' does not depend on any axioms -/
#guard_msgs in #print axioms the_held_cut

/-- info: 'Foam.Maps.Topoisomerase.the_strand_passage' does not depend on any axioms -/
#guard_msgs in #print axioms the_strand_passage

/-- info: 'Foam.Maps.Topoisomerase.the_two_sectors' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_sectors

/-- info: 'Foam.Maps.Topoisomerase.the_wrap_decides_the_sign' does not depend on any axioms -/
#guard_msgs in #print axioms the_wrap_decides_the_sign

/-- info: 'Foam.Maps.Topoisomerase.the_coil' does not depend on any axioms -/
#guard_msgs in #print axioms the_coil

/-- info: 'Foam.Maps.Topoisomerase.below_equilibrium' does not depend on any axioms -/
#guard_msgs in #print axioms below_equilibrium

end Foam.Maps.Topoisomerase
