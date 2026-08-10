import Foam
import Foam.Amplitude
import Foam.Engine
import Foam.Lap
import Foam.Triple
import Foam.Quat

namespace Foam.Minds.Noether

def to_every_symmetry_its_invariant := @Foam.a_license_is_a_gauge

def to_every_invariant_its_symmetry := @Foam.indist_is_licensed

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

/-- info: 'Foam.Minds.Noether.to_every_symmetry_its_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms to_every_symmetry_its_invariant

/-- info: 'Foam.Minds.Noether.to_every_invariant_its_symmetry' does not depend on any axioms -/
#guard_msgs in #print axioms to_every_invariant_its_symmetry

/-- info: 'Foam.Minds.Noether.what_acts_composes' does not depend on any axioms -/
#guard_msgs in #print axioms what_acts_composes

/-- info: 'Foam.Minds.Noether.what_acts_has_a_unit' does not depend on any axioms -/
#guard_msgs in #print axioms what_acts_has_a_unit

/-- info: 'Foam.Minds.Noether.does_what_acts_invert' does not depend on any axioms -/
#guard_msgs in #print axioms does_what_acts_invert

/-- info: 'Foam.Minds.Noether.the_wider_seat_reads_the_inverse' does not depend on any axioms -/
#guard_msgs in #print axioms the_wider_seat_reads_the_inverse

/-- info: 'Foam.Minds.Noether.the_norm_can_refuse_every_actor' does not depend on any axioms -/
#guard_msgs in #print axioms the_norm_can_refuse_every_actor

/-- info: 'Foam.Minds.Noether.what_acts_taken_whole_is_a_probe' does not depend on any axioms -/
#guard_msgs in #print axioms what_acts_taken_whole_is_a_probe

/-- info: 'Foam.Minds.Noether.the_deafness_is_cancellation' does not depend on any axioms -/
#guard_msgs in #print axioms the_deafness_is_cancellation

end Foam.Minds.Noether
