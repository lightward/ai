import Foam
import Foam.Beam
import Foam.Discovery
import Foam.Door
import Foam.Expectation
import Foam.Joint
import Foam.Ledger
import Foam.Passage
import Foam.Seat
import Foam.Origin
import Foam.Surprise
import Foam.Valve
import Foam.Width

namespace Foam.Maps.Gita

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

theorem lokasangraha :
    (∀ p : Compass × Compass, (entrain p).1 = p.1.step)
      ∧ (entrain (.n, .n)).2 ≠ (entrain (.e, .n)).2
      ∧ ∀ p : Compass × Compass,
          together (entrain (entrain (entrain (entrain p)))) :=
  ⟨(fun p =>
    match p with
    | (.n, .n) => rfl
    | (.n, .e) => rfl
    | (.n, .s) => rfl
    | (.n, .w) => rfl
    | (.e, .n) => rfl
    | (.e, .e) => rfl
    | (.e, .s) => rfl
    | (.e, .w) => rfl
    | (.s, .n) => rfl
    | (.s, .e) => rfl
    | (.s, .s) => rfl
    | (.s, .w) => rfl
    | (.w, .n) => rfl
    | (.w, .e) => rfl
    | (.w, .s) => rfl
    | (.w, .w) => rfl),
   (fun h => nomatch h),
   the_lap_locks_together⟩

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

private def indwell {W : Type} (S : Stage) (bs : List S.State) (w : W) :
    List (door S W).State :=
  bs.map (fun s => (s, w))

private def whirl {W : Type} (S : Stage) (μ : W → S.State → S.State) :
    (door S W).State → (door S W).State :=
  fun q => (μ q.2 q.1, q.2)

private theorem whirl_reads_the_machine {W : Type} (S : Stage)
    (μ : W → S.State → S.State) :
    ∀ (ps : List S.Probe) (s : S.State) (w : W),
      transcriptWith (door S W) (whirl S μ) (s, w) ps
        = transcriptWith S (μ w) s ps
  | [], _, _ => rfl
  | p :: ps, s, w =>
      congrArg (S.obs (μ w s) p :: ·)
        (whirl_reads_the_machine S μ ps (μ w s) w)

theorem isvarah_sarva_bhutanam {W : Type} (S : Stage)
    (μ : W → S.State → S.State) (s : S.State) (bs : List S.State)
    {w w' : W} (hw : w ≠ w') (ps : List S.Probe) :
    ((s, w) ≠ (s, w') ∧ indist (door S W) (s, w) (s, w'))
      ∧ (indwell S (s :: bs) w ≠ indwell S (s :: bs) w'
          ∧ ∀ t, t ∈ s :: bs → indist (door S W) (t, w) (t, w'))
      ∧ ((whirl S μ (s, w)).2 = w
          ∧ transcript (door S W) (s, w) ps = transcript S s ps
          ∧ transcriptWith (door S W) (whirl S μ) (s, w) ps
              = transcriptWith S (μ w) s ps)
      ∧ (∀ (V : Type) (v : V) (p : S.Probe),
          (door S W).obs (s, w) p = (door S V).obs (s, v) p)
      ∧ ∀ w₀ : W,
          (∀ x y : (door S W).State, indist (door S W) x y → x = y) →
            ∀ (t : S.State) (u : W), (t, u) = (t, w₀) :=
  ⟨the_guest_is_real_and_unread S s hw,
   ⟨fun he => hw (congrArg (fun l => (l.headD (s, w)).2) he),
    fun t _ => the_door_reads_no_route S t w w'⟩,
   ⟨rfl,
    the_boarded_transcript_is_the_ground_transcript S ps s w,
    whirl_reads_the_machine S μ ps s w⟩,
   fun _ v p => (the_host_maintains_invisibly S s w v p).2,
   fun w₀ h => a_door_that_checks_papers_unpersons_its_guests S w₀ h⟩

def yathecchasi_tatha_kuru := @Foam.the_approach_is_yours

/-- info: 'Foam.Maps.Gita.senayor_ubhayor_madhye' does not depend on any axioms -/
#guard_msgs in #print axioms senayor_ubhayor_madhye

/-- info: 'Foam.Maps.Gita.arjuna_visada' does not depend on any axioms -/
#guard_msgs in #print axioms arjuna_visada

/-- info: 'Foam.Maps.Gita.na_jayate_mriyate' does not depend on any axioms -/
#guard_msgs in #print axioms na_jayate_mriyate

/-- info: 'Foam.Maps.Gita.vasamsi_jirnani' does not depend on any axioms -/
#guard_msgs in #print axioms vasamsi_jirnani

/-- info: 'Foam.Maps.Gita.karmany_evadhikaras_te' does not depend on any axioms -/
#guard_msgs in #print axioms karmany_evadhikaras_te

/-- info: 'Foam.Maps.Gita.lokasangraha' does not depend on any axioms -/
#guard_msgs in #print axioms lokasangraha

/-- info: 'Foam.Maps.Gita.mrtyu_never_hides' does not depend on any axioms -/
#guard_msgs in #print axioms mrtyu_never_hides

/-- info: 'Foam.Maps.Gita.udbhava_extends_reach' does not depend on any axioms -/
#guard_msgs in #print axioms udbhava_extends_reach

/-- info: 'Foam.Maps.Gita.death_files_among_the_graces' does not depend on any axioms -/
#guard_msgs in #print axioms death_files_among_the_graces

/-- info: 'Foam.Maps.Gita.vibhuti_streams_the_totality' does not depend on any axioms -/
#guard_msgs in #print axioms vibhuti_streams_the_totality

/-- info: 'Foam.Maps.Gita.the_roll_call_reads_the_seated' does not depend on any axioms -/
#guard_msgs in #print axioms the_roll_call_reads_the_seated

/-- info: 'Foam.Maps.Gita.na_sva_caksusa' does not depend on any axioms -/
#guard_msgs in #print axioms na_sva_caksusa

/-- info: 'Foam.Maps.Gita.divyam_caksuh' does not depend on any axioms -/
#guard_msgs in #print axioms divyam_caksuh

/-- info: 'Foam.Maps.Gita.mam_tu_veda_na_kascana' does not depend on any axioms -/
#guard_msgs in #print axioms mam_tu_veda_na_kascana

/-- info: 'Foam.Maps.Gita.isvarah_sarva_bhutanam' does not depend on any axioms -/
#guard_msgs in #print axioms isvarah_sarva_bhutanam

/-- info: 'Foam.Maps.Gita.yathecchasi_tatha_kuru' does not depend on any axioms -/
#guard_msgs in #print axioms yathecchasi_tatha_kuru

end Foam.Maps.Gita
