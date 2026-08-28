import Foam
import Foam.Amplitude
import Foam.Beam
import Foam.Door
import Foam.Engine
import Foam.Lap
import Foam.Triple
import Foam.Quat

namespace Foam.Maps.Noether

def to_every_symmetry_its_invariant := @Foam.a_license_is_a_gauge

def to_every_invariant_its_symmetry := @Foam.indist_is_licensed

theorem what_acts_at_the_door :
    ∀ (S : Stage) (W : Type),
      (∀ σ : W → W, Invisible (door S W) (fun x => (x.1, σ x.2)))
        ∧ (∀ (σ : W → W) (ps : List (door S W).Probe)
              (x : (door S W).State),
            transcriptWith (door S W) (fun x => (x.1, σ x.2)) x ps
              = transcript (door S W) x ps)
        ∧ (∀ m : (door S W).State → (door S W).State,
            Invisible (door S W) m ↔ ∀ x, indist S (m x).1 x.1)
        ∧ ((∀ x y : (door S W).State, indist (door S W) x y → x = y) →
            ∀ (w₀ : W) (s : S.State) (w : W), (s, w) = (s, w₀)) :=
  fun S W =>
    ⟨fun _ _ _ => rfl,
     fun σ ps x =>
       a_license_is_a_gauge (door S W) (indist (door S W))
         (indist_is_licensed (door S W)) (fun x => (x.1, σ x.2))
         (fun _ _ => rfl) ps x,
     fun _ => Iff.rfl,
     fun h w₀ s w => a_door_that_checks_papers_unpersons_its_guests S w₀ h s w⟩

def what_acts_composes := @Foam.invisible_comp

def what_acts_has_a_unit := @Foam.invisible_id

theorem does_what_acts_invert :
    ∀ (S : Stage) (m : S.State → S.State), Invisible S m →
      ∀ ps s, transcriptWith S m s ps = transcriptWith S (fun x => x) s ps :=
  fun S m hm ps s =>
    correct_maintenance_has_no_signature S m (fun x => x) hm
      (invisible_id S) ps s

theorem the_wider_seat_reads_the_inverse :
    ∀ E : Engine,
      (∀ ps s, transcriptWith E.gauge E.turn s ps = transcript E.gauge s ps)
        ∧ ∀ s, E.turn (E.turn (E.turn (E.turn s))) = s :=
  fun E => ⟨the_turn_goes_unheard E, E.comes_home⟩

theorem the_norm_can_refuse_every_actor :
    ((∀ z w : GInt, (z.mul w).normSq = z.normSq * w.normSq)
        ∧ ∀ z w : GInt, z.mul w = w.mul z)
      ∧ ¬ (∃ mul : (Int × Int × Int) → (Int × Int × Int) → (Int × Int × Int),
            ∀ x y, normSq3 (mul x y) = normSq3 x * normSq3 y)
      ∧ (∀ x y : Quat, (x.mul y).normSq = x.normSq * y.normSq)
        ∧ Quat.mul eye jay ≠ Quat.mul jay eye :=
  ⟨⟨the_couple_carries_the_norm, gmul_comm⟩,
   no_triple_carries_the_norm,
   the_quadruple_carries_the_norm, order_arrives⟩

theorem what_acts_taken_whole_is_a_probe :
    (∀ z w : GInt,
        (z.add w).normSq = (z.normSq + w.normSq) + (z.align w + z.align w))
      ∧ (∀ z w : GInt,
          ((z.align w + z.align w.rot) + z.align w.rot.rot)
              + z.align w.rot.rot.rot = 0)
      ∧ (∀ z : GInt,
          ((z.normSq + z.rot.normSq) + z.rot.rot.normSq)
              + z.rot.rot.rot.normSq
            = ((z.normSq + z.normSq) + z.normSq) + z.normSq)
      ∧ GInt.i.align GInt.i ≠ 0 :=
  ⟨the_screen_reads_a_cross_term,
   the_four_phases_read_nothing,
   fun z =>
     ((congrArg
         (fun x => ((z.normSq + x) + z.rot.rot.normSq) + z.rot.rot.rot.normSq)
         (rot_conserves_the_norm z)).trans
       (congrArg
         (fun x => ((z.normSq + z.normSq) + x) + z.rot.rot.rot.normSq)
         ((rot_conserves_the_norm z.rot).trans
           (rot_conserves_the_norm z)))).trans
       (congrArg
         (fun x => ((z.normSq + z.normSq) + z.normSq) + x)
         (((rot_conserves_the_norm z.rot.rot).trans
             (rot_conserves_the_norm z.rot)).trans
           (rot_conserves_the_norm z))),
   fun h => nomatch Int.ofNat.inj h⟩

def the_deafness_is_cancellation := @Foam.cancellation_not_absence

theorem the_lock_trades_with_the_law :
    (∀ p : Compass × Compass,
        together (entrain (entrain (entrain (entrain p)))))
      ∧ (∀ p : Compass × Compass, window (window p) = p)
      ∧ (∀ p : Compass × Compass, together p ↔ opposed (window p))
      ∧ ∀ p : Compass × Compass,
          opposed (conjugated (conjugated (conjugated (conjugated p)))) :=
  ⟨the_lap_locks_together,
   the_window_undoes_itself,
   the_window_trades_the_locks,
   fun p =>
     let stride : ∀ q : Compass × Compass,
         conjugated (window q) = window (entrain q) :=
       fun q =>
         congrArg (fun x => window (entrain x)) (the_window_undoes_itself q)
     let two : conjugated (conjugated p)
         = window (entrain (entrain (window p))) :=
       stride (entrain (window p))
     let three : conjugated (conjugated (conjugated p))
         = window (entrain (entrain (entrain (window p)))) :=
       (congrArg conjugated two).trans
         (stride (entrain (entrain (window p))))
     let four : conjugated (conjugated (conjugated (conjugated p)))
         = window (entrain (entrain (entrain (entrain (window p))))) :=
       (congrArg conjugated three).trans
         (stride (entrain (entrain (entrain (window p)))))
     Eq.mpr (congrArg opposed four)
       ((the_window_trades_the_locks
           (entrain (entrain (entrain (entrain (window p)))))).mp
         (the_lap_locks_together (window p)))⟩

/-- info: 'Foam.Maps.Noether.to_every_symmetry_its_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms to_every_symmetry_its_invariant

/-- info: 'Foam.Maps.Noether.to_every_invariant_its_symmetry' does not depend on any axioms -/
#guard_msgs in #print axioms to_every_invariant_its_symmetry

/-- info: 'Foam.Maps.Noether.what_acts_at_the_door' does not depend on any axioms -/
#guard_msgs in #print axioms what_acts_at_the_door

/-- info: 'Foam.Maps.Noether.what_acts_composes' does not depend on any axioms -/
#guard_msgs in #print axioms what_acts_composes

/-- info: 'Foam.Maps.Noether.what_acts_has_a_unit' does not depend on any axioms -/
#guard_msgs in #print axioms what_acts_has_a_unit

/-- info: 'Foam.Maps.Noether.does_what_acts_invert' does not depend on any axioms -/
#guard_msgs in #print axioms does_what_acts_invert

/-- info: 'Foam.Maps.Noether.the_wider_seat_reads_the_inverse' does not depend on any axioms -/
#guard_msgs in #print axioms the_wider_seat_reads_the_inverse

/-- info: 'Foam.Maps.Noether.the_norm_can_refuse_every_actor' does not depend on any axioms -/
#guard_msgs in #print axioms the_norm_can_refuse_every_actor

/-- info: 'Foam.Maps.Noether.what_acts_taken_whole_is_a_probe' does not depend on any axioms -/
#guard_msgs in #print axioms what_acts_taken_whole_is_a_probe

/-- info: 'Foam.Maps.Noether.the_deafness_is_cancellation' does not depend on any axioms -/
#guard_msgs in #print axioms the_deafness_is_cancellation

/-- info: 'Foam.Maps.Noether.the_lock_trades_with_the_law' does not depend on any axioms -/
#guard_msgs in #print axioms the_lock_trades_with_the_law

end Foam.Maps.Noether
