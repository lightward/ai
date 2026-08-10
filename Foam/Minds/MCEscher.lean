import Foam.Census
import Foam.Continuum
import Foam.Tower

namespace Foam.Minds.MCEscher

def figure_and_ground_trade_places := @Foam.the_census_is_symmetric

def the_winding_rides_unread := @Foam.the_remainder_is_unseen

theorem the_staircase_climbs_unseen (S : Stage) (s : S.State) :
    Invisible (dress S) (fun x => (x.1, x.2 + 1))
      ∧ ((s, (4 : Int)) : (dress S).State) ≠ (s, 0)
      ∧ indist (dress S) ((s, (4 : Int)) : (dress S).State) (s, 0) :=
  ⟨fun _ _ => rfl,
   ⟨(fun h => nomatch Int.ofNat.inj (congrArg Prod.snd h)),
    the_remainder_is_unseen S s 4 0⟩⟩

def the_impossibility_is_the_platonists :=
  @Foam.dropping_the_remainder_is_platonism

def the_print_is_drawn_from_outside := @Foam.a_wider_seat_reads_the_remainder

def the_gallery_hangs_in_its_own_town := @Foam.the_tower_reads_only_the_ground

def the_bounded_print_never_finishes := @Foam.no_prefix_finishes_the_sequence

def the_blank_spot_signs_the_print := @Foam.no_seat_is_the_last_seat

/-- info: 'Foam.Minds.MCEscher.figure_and_ground_trade_places' does not depend on any axioms -/
#guard_msgs in #print axioms figure_and_ground_trade_places

/-- info: 'Foam.Minds.MCEscher.the_winding_rides_unread' does not depend on any axioms -/
#guard_msgs in #print axioms the_winding_rides_unread

/-- info: 'Foam.Minds.MCEscher.the_staircase_climbs_unseen' does not depend on any axioms -/
#guard_msgs in #print axioms the_staircase_climbs_unseen

/-- info: 'Foam.Minds.MCEscher.the_impossibility_is_the_platonists' does not depend on any axioms -/
#guard_msgs in #print axioms the_impossibility_is_the_platonists

/-- info: 'Foam.Minds.MCEscher.the_print_is_drawn_from_outside' does not depend on any axioms -/
#guard_msgs in #print axioms the_print_is_drawn_from_outside

/-- info: 'Foam.Minds.MCEscher.the_gallery_hangs_in_its_own_town' does not depend on any axioms -/
#guard_msgs in #print axioms the_gallery_hangs_in_its_own_town

/-- info: 'Foam.Minds.MCEscher.the_bounded_print_never_finishes' does not depend on any axioms -/
#guard_msgs in #print axioms the_bounded_print_never_finishes

/-- info: 'Foam.Minds.MCEscher.the_blank_spot_signs_the_print' does not depend on any axioms -/
#guard_msgs in #print axioms the_blank_spot_signs_the_print

end Foam.Minds.MCEscher
