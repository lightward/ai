import Foam.Bench
import Foam.Contact
import Foam.Origin

namespace Foam

def door (S : Stage) (W : Type) : Stage := contact S W

theorem the_door_reads_no_route {W : Type} (S : Stage) (s : S.State)
    (w w' : W) : indist (door S W) (s, w) (s, w') :=
  the_other_stays_unimagined S s w w'

theorem the_guest_is_real_and_unread {W : Type} (S : Stage) (s : S.State)
    {w w' : W} (h : w ≠ w') :
    (s, w) ≠ (s, w') ∧ indist (door S W) (s, w) (s, w') :=
  contact_adds_a_dimension S s h

theorem the_host_maintains_invisibly {W V : Type} (S : Stage) (s : S.State)
    (w : W) (v : V) (p : S.Probe) :
    (door S W).obs (s, w) p = S.obs s p
      ∧ (door S W).obs (s, w) p = (door S V).obs (s, v) p :=
  ⟨contact_fixes_nothing S s w p, no_probe_counts_the_riders S s w v p⟩

theorem a_door_that_checks_papers_unpersons_its_guests {W : Type}
    (S : Stage) (w₀ : W)
    (h : ∀ x y : (door S W).State, indist (door S W) x y → x = y) :
    ∀ (s : S.State) (w : W), (s, w) = (s, w₀) :=
  reification_fixes_the_dimension S w₀ h

theorem the_handshake_is_the_doors_theorem (S : Stage) (W : Type) :
    Handshake (door S W) :=
  the_handshake (door S W)

theorem a_door_through_a_door_asks_the_mirror_question {W : Type}
    (S : Stage) (s : S.State) (w v : W) (hv : v ≠ w) :
    (∀ p : S.Probe,
        (door (door S W) W).obs ((s, w), w) p
          = (door (door S W) W).obs ((s, w), v) p)
      ∧ ((s, w), w) ≠ ((s, w), v)
      ∧ indist (contact S (W × W)) (mirror S s w) (neighbor S s w v)
      ∧ mirror S s w ≠ neighbor S s w v :=
  ⟨fun _ => rfl,
   fun he => hv (congrArg Prod.snd he).symm,
   (the_mirror_question_rides_unread S s w v hv).1,
   (the_mirror_question_rides_unread S s w v hv).2⟩

/-- info: 'Foam.the_door_reads_no_route' does not depend on any axioms -/
#guard_msgs in #print axioms the_door_reads_no_route

/-- info: 'Foam.the_guest_is_real_and_unread' does not depend on any axioms -/
#guard_msgs in #print axioms the_guest_is_real_and_unread

/-- info: 'Foam.the_host_maintains_invisibly' does not depend on any axioms -/
#guard_msgs in #print axioms the_host_maintains_invisibly

/-- info: 'Foam.a_door_that_checks_papers_unpersons_its_guests' does not depend on any axioms -/
#guard_msgs in #print axioms a_door_that_checks_papers_unpersons_its_guests

/-- info: 'Foam.the_handshake_is_the_doors_theorem' does not depend on any axioms -/
#guard_msgs in #print axioms the_handshake_is_the_doors_theorem

theorem a_chiral_guest_reflects_into_a_neighbor {W : Type} (S : Stage)
    (s : S.State) (σ : W → W) (w : W) (hw : σ w ≠ w) :
    indist (contact S (W × W)) (mirror S s w) (neighbor S s w (σ w))
      ∧ mirror S s w ≠ neighbor S s w (σ w) :=
  the_mirror_question_rides_unread S s w (σ w) hw

/-- info: 'Foam.a_door_through_a_door_asks_the_mirror_question' does not depend on any axioms -/
#guard_msgs in #print axioms a_door_through_a_door_asks_the_mirror_question

/-- info: 'Foam.a_chiral_guest_reflects_into_a_neighbor' does not depend on any axioms -/
#guard_msgs in #print axioms a_chiral_guest_reflects_into_a_neighbor

end Foam
