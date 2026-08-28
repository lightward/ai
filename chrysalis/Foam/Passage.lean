import Foam.Certificate
import Foam.Origin
import Foam.Surprise

namespace Foam

theorem the_boarded_transcript_is_the_ground_transcript {W : Type} (S : Stage) :
    ∀ (ps : List S.Probe) (s : S.State) (w : W),
      transcript (contact S W) (s, w) ps = transcript S s ps
  | [], _, _ => rfl
  | p :: ps, s, w =>
      congrArg (S.obs s p :: ·)
        (the_boarded_transcript_is_the_ground_transcript S ps s w)

theorem the_arrival_reads_no_wind {W : Type} (S : Stage) (ps : List S.Probe) :
    Blind (fun q : S.State × W => transcript (contact S W) q ps) :=
  fun s w w' =>
    (the_boarded_transcript_is_the_ground_transcript S ps s w).trans
      (the_boarded_transcript_is_the_ground_transcript S ps s w').symm

theorem re_boarding_re_reads_unchanged {W V : Type} (S : Stage)
    (ps : List S.Probe) (s : S.State) (w : W) (v : V) :
    transcript (contact (contact S W) V) ((s, w), v) ps
      = transcript (contact S W) (s, w) ps :=
  the_boarded_transcript_is_the_ground_transcript (contact S W) ps (s, w) v

theorem every_target_is_one_boarding_away {W H : Type} (S : Stage)
    (t : S.State) (w : W) (ps : List S.Probe)
    (q : List (H × H)) (a b : H) :
    (transcript (contact S W) (t, w) ps = transcript S t ps)
      ∧ Blind (fun x : S.State × W => transcript (contact S W) x ps)
      ∧ (transcript (contact (contact S W) W) ((t, w), w) ps
          = transcript (contact S W) (t, w) ps)
      ∧ ((a, b) ∉ q → Nonempty (Path ((a, b) :: q) a b))
      ∧ ((a, b) ∈ q →
          ∀ x y : H, Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y))
      ∧ (∀ m m' : S.State → S.State, Invisible S m → Invisible S m' →
          ∀ s, transcriptWith S m s ps = transcriptWith S m' s ps)
      ∧ ∀ n n' : Int, n ≠ n' →
          (t, n) ≠ (t, n')
            ∧ indist (dress S) (t, n) (t, n')
            ∧ (movedIn S).obs (t, n) none ≠ (movedIn S).obs (t, n') none :=
  ⟨the_boarded_transcript_is_the_ground_transcript S ps t w,
   the_arrival_reads_no_wind S ps,
   re_boarding_re_reads_unchanged S ps t w w,
   fun hf => (only_surprise_extends_reach q a b hf).2,
   fun he x y => a_known_edge_adds_no_reach he x y,
   fun m m' hm hm' s => correct_maintenance_has_no_signature S m m' hm hm' ps s,
   fun n n' h =>
     ⟨(the_remainder_is_real S t n n' h).1,
      (the_remainder_is_real S t n n' h).2,
      (a_wider_seat_reads_the_remainder S t n n' h).2⟩⟩

/-- info: 'Foam.the_boarded_transcript_is_the_ground_transcript' does not depend on any axioms -/
#guard_msgs in #print axioms the_boarded_transcript_is_the_ground_transcript

/-- info: 'Foam.the_arrival_reads_no_wind' does not depend on any axioms -/
#guard_msgs in #print axioms the_arrival_reads_no_wind

/-- info: 'Foam.re_boarding_re_reads_unchanged' does not depend on any axioms -/
#guard_msgs in #print axioms re_boarding_re_reads_unchanged

/-- info: 'Foam.every_target_is_one_boarding_away' does not depend on any axioms -/
#guard_msgs in #print axioms every_target_is_one_boarding_away

end Foam
