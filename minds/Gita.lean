import Foam
import Foam.Discovery
import Foam.Expectation
import Foam.Joint
import Foam.Ledger
import Foam.Mind
import Foam.Origin
import Foam.Surprise
import Foam.Valve
import Foam.Width

namespace Foam.Minds.Gita

def senayor_ubhayor_madhye := @Foam.the_comparison_is_a_seat

def arjuna_visada := @Foam.the_cut_mints_the_seat

def na_jayate_mriyate := @Foam.every_move_rests_at_the_origin

def vasamsi_jirnani := @Foam.the_arrival_sheds_its_route

theorem karmany_evadhikaras_te :
    (∀ (A B : Type) (send : A × B → A × B) (p : A × B),
        (send p).2 ≠ p.2 → ¬ ∃ ms : List (A → A), runLocal ms (send p) = p)
      ∧ ∀ n : Nat, 0 < n →
          ∃ w₁ w₂ : List Bool, w₁ ∈ book n ∧ w₂ ∈ book n
            ∧ freq w₁ true ≠ freq w₂ true :=
  ⟨fun _ _ send p hs => no_local_counter_reaches_the_foreign_record send p hs,
   fun n hn => no_run_reads_its_own_ratio n hn⟩

theorem mrtyu_never_hides (S : Stage) (z : S.State) {s t : S.State}
    {p : S.Probe} (hdist : S.obs s p ≠ S.obs t p) :
    ¬ Invisible S (fun _ => z) :=
  fun hinv => hdist ((hinv s p).symm.trans (hinv t p))

def udbhava_extends_reach := @Foam.only_surprise_extends_reach

def death_files_among_the_graces := @Foam.a_wider_seat_reads_the_order

private theorem transcript_maps (S : Stage) (s : S.State) :
    ∀ ps : List S.Probe, transcript S s ps = ps.map (S.obs s)
  | [] => rfl
  | p :: ps => congrArg (List.cons (S.obs s p)) (transcript_maps S s ps)

private theorem transcript_len (S : Stage) (s : S.State) :
    ∀ ps : List S.Probe, (transcript S s ps).length = ps.length
  | [] => rfl
  | _ :: ps => congrArg (· + 1) (transcript_len S s ps)

theorem vibhuti_streams_the_totality (S : Stage) (s : S.State)
    (ps : List S.Probe) :
    transcript S s ps = ps.map (S.obs s)
      ∧ (transcript S s ps).length = ps.length :=
  ⟨transcript_maps S s ps, transcript_len S s ps⟩

theorem the_roll_call_reads_the_seated {State : Type}
    (bs : List (Beholder State)) (d : ∀ b, b ∈ bs → b.Probe) (s t : State) :
    ((∀ b, b ∈ bs → indist b.toStage s t) → indist (gather bs).toStage s t)
      ∧ (indist (gather bs).toStage s t →
          ∀ b, b ∈ bs → indist b.toStage s t) :=
  ⟨fun h => the_gathering_invents_no_reading bs s t h,
   fun hg b hb => the_gathering_loses_no_reading bs d s t hg b hb⟩

private def Elsewhen {State : Type} (here : Beholder State)
    (m : State → State) (there : Beholder State) : Prop :=
  Invisible here.toStage m ∧ ¬ Invisible there.toStage m

theorem na_sva_caksusa {State : Type} (a : Beholder State)
    (m : State → State) :
    ¬ Elsewhen a m a :=
  fun h => h.2 h.1

private def plenum (State : Type) : Beholder State :=
  ⟨Unit, State, fun s _ => s⟩

theorem divyam_caksuh {State : Type} (a : Beholder State) (s : State)
    (p : a.Probe) :
    ((a.pair (plenum State)).obs s (p, ())).1 = a.obs s p
      ∧ ((a.pair (plenum State)).obs s (p, ())).2 = s :=
  ⟨rfl, rfl⟩

def mam_tu_veda_na_kascana := @Foam.a_wider_seat_reads_the_remainder

def yathecchasi_tatha_kuru := @Foam.the_approach_is_yours

/-- info: 'Foam.Minds.Gita.senayor_ubhayor_madhye' does not depend on any axioms -/
#guard_msgs in #print axioms senayor_ubhayor_madhye

/-- info: 'Foam.Minds.Gita.arjuna_visada' does not depend on any axioms -/
#guard_msgs in #print axioms arjuna_visada

/-- info: 'Foam.Minds.Gita.na_jayate_mriyate' does not depend on any axioms -/
#guard_msgs in #print axioms na_jayate_mriyate

/-- info: 'Foam.Minds.Gita.vasamsi_jirnani' does not depend on any axioms -/
#guard_msgs in #print axioms vasamsi_jirnani

/-- info: 'Foam.Minds.Gita.karmany_evadhikaras_te' does not depend on any axioms -/
#guard_msgs in #print axioms karmany_evadhikaras_te

/-- info: 'Foam.Minds.Gita.mrtyu_never_hides' does not depend on any axioms -/
#guard_msgs in #print axioms mrtyu_never_hides

/-- info: 'Foam.Minds.Gita.udbhava_extends_reach' does not depend on any axioms -/
#guard_msgs in #print axioms udbhava_extends_reach

/-- info: 'Foam.Minds.Gita.death_files_among_the_graces' does not depend on any axioms -/
#guard_msgs in #print axioms death_files_among_the_graces

/-- info: 'Foam.Minds.Gita.vibhuti_streams_the_totality' does not depend on any axioms -/
#guard_msgs in #print axioms vibhuti_streams_the_totality

/-- info: 'Foam.Minds.Gita.the_roll_call_reads_the_seated' does not depend on any axioms -/
#guard_msgs in #print axioms the_roll_call_reads_the_seated

/-- info: 'Foam.Minds.Gita.na_sva_caksusa' does not depend on any axioms -/
#guard_msgs in #print axioms na_sva_caksusa

/-- info: 'Foam.Minds.Gita.divyam_caksuh' does not depend on any axioms -/
#guard_msgs in #print axioms divyam_caksuh

/-- info: 'Foam.Minds.Gita.mam_tu_veda_na_kascana' does not depend on any axioms -/
#guard_msgs in #print axioms mam_tu_veda_na_kascana

/-- info: 'Foam.Minds.Gita.yathecchasi_tatha_kuru' does not depend on any axioms -/
#guard_msgs in #print axioms yathecchasi_tatha_kuru

end Foam.Minds.Gita
