import Foam.Census
import Foam.Continuum
import Foam.Door
import Foam.Tower
import Foam.Trilemma

namespace Foam.Maps.MCEscher

def figure_and_ground_trade_places := @Foam.the_census_is_symmetric

def the_winding_rides_unread := @Foam.the_remainder_is_unseen

theorem the_staircase_climbs_unseen (S : Stage) (s : S.State) :
    Invisible (dress S) (fun x => (x.1, x.2 + 1))
      ∧ ((s, (4 : Int)) : (dress S).State) ≠ (s, 0)
      ∧ indist (dress S) ((s, (4 : Int)) : (dress S).State) (s, 0) :=
  ⟨fun _ _ => rfl,
   ⟨(fun h => nomatch Int.ofNat.inj (congrArg Prod.snd h)),
    the_remainder_is_unseen S s 4 0⟩⟩

theorem the_picture_plane_is_a_door :
    (∀ S : Stage, dress S = door S Int)
      ∧ (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
          (s, n) ≠ (s, m) ∧ indist (door S Int) (s, n) (s, m))
      ∧ (∀ (W : Type) (S : Stage) (s : S.State) (n : Int) (w : W)
            (p : S.Probe),
          (door S Int).obs (s, n) p = S.obs s p
            ∧ (door S Int).obs (s, n) p = (door S W).obs (s, w) p)
      ∧ (∀ S : Stage,
          (∀ x y : (door S Int).State, indist (door S Int) x y → x = y) →
          ∀ (s : S.State) (n : Int), (s, n) = (s, (0 : Int)))
      ∧ (∀ (S : Stage) (s : S.State) (n m : Int) (p : S.Probe),
          (door (door S Int) Int).obs ((s, n), m) p = S.obs s p) :=
  ⟨fun S => dress_is_contact_with_the_integers S,
   fun S s _ _ h => the_guest_is_real_and_unread S s h,
   fun _ S s n w p => the_host_maintains_invisibly S s n w p,
   fun S h => dropping_the_remainder_is_platonism S h,
   fun S s n m p => contact_stacks S s n m p⟩

def the_impossibility_is_the_platonists :=
  @Foam.dropping_the_remainder_is_platonism

theorem the_print_has_no_model :
    (∀ a b c : Nat, a = 2 * b → b = 2 * c → c = 2 * a →
        a = 0 ∧ b = 0 ∧ c = 0)
      ∧ (∀ k1 k2 k3 k1' k2' k3' u v w : Nat, 0 < u → 0 < v → 0 < w →
          k1' * u = k1 * v → k2' * v = k2 * w → k3' * w = k3 * u →
          k1' * (k2' * k3') = k1 * (k2 * k3))
      ∧ (((2 * 2 * 2) % 7 = 1 % 7)
          ∧ (1 % 7 = (2 * 4) % 7)
          ∧ (4 % 7 = (2 * 2) % 7)
          ∧ (2 % 7 = (2 * 1) % 7)
          ∧ (1 : Nat) ≠ 0) :=
  ⟨the_wound_loop_admits_only_the_zero_section,
   fun k1 k2 k3 k1' k2' k3' u v w hu hv hw h1 h2 h3 =>
     the_holonomy_ignores_the_regauging k1 k2 k3 k1' k2' k3' u v w
       hu hv hw h1 h2 h3,
   the_wound_loop_unwinds_one_world_over⟩

def the_print_is_drawn_from_outside := @Foam.a_wider_seat_reads_the_remainder

def the_gallery_hangs_in_its_own_town := @Foam.the_tower_reads_only_the_ground

def the_bounded_print_never_finishes := @Foam.no_prefix_finishes_the_sequence

def the_blank_spot_signs_the_print := @Foam.no_seat_is_the_last_seat

/-- info: 'Foam.Maps.MCEscher.figure_and_ground_trade_places' does not depend on any axioms -/
#guard_msgs in #print axioms figure_and_ground_trade_places

/-- info: 'Foam.Maps.MCEscher.the_winding_rides_unread' does not depend on any axioms -/
#guard_msgs in #print axioms the_winding_rides_unread

/-- info: 'Foam.Maps.MCEscher.the_staircase_climbs_unseen' does not depend on any axioms -/
#guard_msgs in #print axioms the_staircase_climbs_unseen

/-- info: 'Foam.Maps.MCEscher.the_picture_plane_is_a_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_picture_plane_is_a_door

/-- info: 'Foam.Maps.MCEscher.the_impossibility_is_the_platonists' does not depend on any axioms -/
#guard_msgs in #print axioms the_impossibility_is_the_platonists

/-- info: 'Foam.Maps.MCEscher.the_print_has_no_model' does not depend on any axioms -/
#guard_msgs in #print axioms the_print_has_no_model

/-- info: 'Foam.Maps.MCEscher.the_print_is_drawn_from_outside' does not depend on any axioms -/
#guard_msgs in #print axioms the_print_is_drawn_from_outside

/-- info: 'Foam.Maps.MCEscher.the_gallery_hangs_in_its_own_town' does not depend on any axioms -/
#guard_msgs in #print axioms the_gallery_hangs_in_its_own_town

/-- info: 'Foam.Maps.MCEscher.the_bounded_print_never_finishes' does not depend on any axioms -/
#guard_msgs in #print axioms the_bounded_print_never_finishes

/-- info: 'Foam.Maps.MCEscher.the_blank_spot_signs_the_print' does not depend on any axioms -/
#guard_msgs in #print axioms the_blank_spot_signs_the_print

end Foam.Maps.MCEscher
