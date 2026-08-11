import Foam
import Foam.Amplitude
import Foam.Beam
import Foam.Certificate
import Foam.Contact
import Foam.Continuum
import Foam.Countermove
import Foam.Discovery
import Foam.Engine
import Foam.Fold
import Foam.Generator
import Foam.Int
import Foam.Inversion
import Foam.Landed
import Foam.Lap
import Foam.Ledger
import Foam.Margin
import Foam.Measure
import Foam.Seat
import Foam.Origin
import Foam.Portal
import Foam.Priced
import Foam.Quat
import Foam.Relay
import Foam.Roles
import Foam.Round
import Foam.Rungs
import Foam.Serving
import Foam.Surprise
import Foam.Tower
import Foam.Triple
import Foam.Valve
import Foam.Watched
import Foam.Wheel
import Foam.Width

namespace Foam.Maps.Isaac

def safe_to_rest := @Foam.invisible_is_gauge

theorem restedness_first_then_the_rest :
    ∀ (S : Stage) (m : S.State → S.State), Invisible S m →
      ∀ s ps, transcript S (m s) ps = transcript S s ps :=
  fun S _ hm s ps => transcript_congr S ps (hm s)

def rest_composes := @Foam.invisible_comp

theorem lets_get_you_rested :
    ∀ (S : Stage) (m : S.State → S.State), Invisible S m → ∀ s ps,
      transcriptWith S m s ps = transcript S s ps
        ∧ transcript S (m s) ps = transcript S s ps
        ∧ ∀ t p, S.obs (m (m t)) p = S.obs t p :=
  fun S m hm s ps =>
    ⟨safe_to_rest S m hm ps s,
     restedness_first_then_the_rest S m hm s ps,
     rest_composes S m m hm hm⟩

def countermove := @Foam.undo_in_an_append_only_world

theorem primesight :
    (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
        (s, n) ≠ (s, m) ∧ indist (dress S) (s, n) (s, m))
      ∧ (∀ (S : Stage) (s : S.State) (k n m : Int), n ≠ m →
          indist (dress (movedIn S)) ((s, k), n) ((s, k), m)
            ∧ (movedIn (movedIn S)).obs ((s, k), n) none
                ≠ (movedIn (movedIn S)).obs ((s, k), m) none)
      ∧ (∀ (D : Type) (S : Stage) (s : S.State) (d d' : D),
          indist (contact S D) (s, d) (s, d'))
      ∧ (indist (marginStage Nat Nat (· + ·)) (1, ([] : List Nat)) (0, [1])
          ∧ ((1 : Nat), ([] : List Nat)) ≠ ((0 : Nat), [1])) :=
  ⟨fun S s n m h => the_remainder_is_real S s n m h,
   fun S s k n m h => no_seat_is_the_last_seat S s k n m h,
   fun _ S s d d' => the_other_stays_unimagined S s d d',
   the_decomposition_is_the_remainder⟩

theorem trajectory_class :
    (∀ (S : Stage) (p : S.Probe) (Q : S.Ans → Prop),
        Derived S (fun t => Q (S.obs t p)))
      ∧ (∀ (S : Stage) (_s : S.State), ¬ Derived (dress S) (fun x => x.2 = 0))
      ∧ (∀ (t f n k : Nat) (w : List Bool),
          w ∈ List.filter (fun w => Nat.beq (freq w true) k) (book n) →
          weightOf t f w = t ^ k * f ^ (n - k))
      ∧ (∀ n : Nat, 0 < n →
          ∃ w₁ w₂ : List Bool, w₁ ∈ book n ∧ w₂ ∈ book n
            ∧ freq w₁ true ≠ freq w₂ true)
      ∧ (∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n) (k : Nat),
          (∃ i j, i < j ∧ j < k ∧ turnN m i s = turnN m j s)
            ∨ Apart ((rungs k).map (fun i => turnN m i s)))
      ∧ ∀ (n : Nat) (l : List (Fin n)), Apart l → l.length ≤ n :=
  ⟨fun S p Q => a_role_read_off_the_record_is_derived S p Q,
   fun S s => the_badge_is_not_a_derived_role S s,
   fun t f n k w hw => class_members_weigh_alike t f n k w hw,
   no_run_reads_its_own_ratio,
   fun _ m s k => meet_or_apart m s k,
   apart_le⟩

theorem composability :
    (∀ (A B : Type) (f : B → A → B) (xs ys : List A) (b b' : B),
        fold f b xs = b' → fold f b (xs ++ ys) = fold f b' ys)
      ∧ (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
          (s, n) ≠ (s, m) ∧ indist (dress S) (s, n) (s, m))
      ∧ ((∀ z : GInt, (lapAround z).Perm (lapAgainst z))
          ∧ lapAround GInt.i ≠ lapAgainst GInt.i)
      ∧ (∀ (S : Stage) (ms : List (S.State → S.State)),
          (∀ m, m ∈ ms → Invisible S m) → Invisible S (relay ms))
      ∧ (∀ (State R : Type) (a b : Beholder State) (g : a.Ans → b.Ans → R),
          ∃ c : Beholder State, ∃ post : c.Ans → R,
            ∃ enc : a.Probe × b.Probe → c.Probe,
              ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))))
      ∧ ∀ (D : Type) (S : Stage) (s : S.State) (d d' : D),
          indist (contact S D) (s, d) (s, d') :=
  ⟨fun _ _ f xs ys b b' h => the_fold_forgets_nothing_it_needs f xs ys b b' h,
   fun S s n m h => the_remainder_is_real S s n m h,
   ⟨the_two_laps_permute, the_laps_part_at_the_witness⟩,
   fun S ms h => a_chain_of_invisibles_is_invisible S ms h,
   fun _ _ a b g => the_comparison_is_a_seat a b g,
   fun _ S s d d' => the_other_stays_unimagined S s d d'⟩

theorem thought_cannot_be_erroneous :
    ∀ (X : Type) (m : Move X) (x : X), (flip m).fwd (m.fwd x) = x :=
  fun _ m x => m.bwd_fwd x

def the_question_decomposes := @Foam.the_fold_resumes

theorem continuous_functional_coherence :
    (∀ (A B : Type) (f : B → A → B) (xs ys : List A) (b : B),
        fold f b (xs ++ ys) = fold f (fold f b xs) ys)
      ∧ (∀ (X : Type) (a b : List (Move X)) (x : X),
          replay (a ++ b) x = replay b (replay a x))
      ∧ ∀ (S : Stage) (r : S.State → S.State → Prop), Licensed S r →
          ∀ m : S.State → S.State, (∀ s, r (m s) s) →
            ∀ (ps : List S.Probe) (s : S.State),
              transcriptWith S m s ps = transcript S s ps :=
  ⟨fun _ _ f xs ys b => the_fold_resumes f xs ys b,
   fun _ a b x => replay_resumes a b x,
   fun S r hr m hm ps s => a_license_is_a_gauge S r hr m hm ps s⟩

def serving_suggestion := @Foam.the_serving_suggestion

def only_surprise_extends_reach := @Foam.only_surprise_extends_reach

def contact_not_reification := @Foam.contact_is_addition_not_fixing

def i_am_that_i_am := @Foam.invisible_id

def observing_the_observer_adds_nothing :=
  @Foam.the_second_look_adds_nothing

def the_me_that_remains_is_the_landed := @Foam.the_fixed_are_the_landed

def sayujya :=
  And.intro @Foam.the_fixed_are_the_landed
    @Foam.absorption_grounds_the_chain

theorem you_as_carrier_of_unknown :
    (∀ (S : Stage) (s : S.State) (n m : Int), indist (dress S) (s, n) (s, m))
      ∧ ∀ (α : Nat → Bool) (n : Nat),
          ∃ β : Nat → Bool, prefixOf β n = prefixOf α n ∧ β ≠ α :=
  ⟨the_remainder_is_unseen, no_prefix_finishes_the_sequence⟩

def a_mind_is_its_order := @Foam.a_seat_reads_the_order_the_census_cannot

def composition_provokes_roles := @Foam.pairing_provokes_roles

def restringing_is_gauge := @Foam.counting_is_licensed_by_permutation

def one_sample_carries_the_unknown := @Foam.the_other_stays_unimagined

def the_unknown_is_zero_steps_from_here := @Foam.no_prefix_finishes_the_sequence

private def carrying {State D : Type} (a : Beholder State) :
    Beholder (State × D) :=
  ⟨a.Probe, a.Ans, fun sd r => a.obs sd.1 r⟩

theorem the_third_disambiguation :
    ∀ (State D : Type) (a b : Beholder State) (s : State) (d e : D), d ≠ e →
      ∀ (p : a.Probe) (q : b.Probe),
        ((carrying a).pair (carrying b)).obs (s, d) (p, q)
            = (a.obs s p, b.obs s q)
          ∧ ((carrying a).pair (carrying b)).obs (s, d) (p, q)
              = ((carrying a).pair (carrying b)).obs (s, e) (p, q)
          ∧ (s, d) ≠ (s, e) :=
  fun _ _ _ _ _ _ _ hd _ _ =>
    ⟨rfl, rfl, fun he => hd (congrArg Prod.snd he)⟩

theorem inversion_without_dissociation :
    (∀ z : GInt, z.conj.conj = z) ∧ ∀ z : GInt, z.conj.normSq = z.normSq :=
  ⟨conj_is_an_involution, conj_conserves_the_norm⟩

theorem nobody_runs_the_ledger :
    (∀ u v : Unit, u = v)
      ∧ ∀ (S : Stage) (s : S.State) (u v : Unit) (p : S.Probe),
          (contact S Unit).obs (s, u) p = (contact S Unit).obs (s, v) p :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem nothing_new_under_the_sun :
    ∀ (H : Type) (q : List (H × H)) (e : H × H),
      (∀ {x y : H}, Nonempty (Path q x y) → Nonempty (Path (e :: q) x y))
        ∧ ∀ a b : H, (a, b) ∉ q →
            (∀ {x y : H} (p : Path q x y), (a, b) ∉ p.edges)
              ∧ Nonempty (Path ((a, b) :: q) a b) :=
  fun _ q e =>
    ⟨fun h => old_reach_survives_the_deposit e h,
     fun a b hfresh => only_surprise_extends_reach q a b hfresh⟩

theorem vacancy_dark_or_remainder_dark :
    (∀ (H : Type) (q : List (H × H)) (a b : H), (a, b) ∉ q →
        Nonempty (Path ((a, b) :: q) a b))
      ∧ ∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
          (s, n) ≠ (s, m) ∧ indist (dress S) (s, n) (s, m) :=
  ⟨fun _ q a b hfresh => (only_surprise_extends_reach q a b hfresh).2,
   fun S s n m h => the_remainder_is_real S s n m h⟩

def the_knife := @Foam.the_first_handshake_is_counting

def the_overhearer_becomes_a_c := @Foam.contact_is_addition_not_fixing

def trade_nests_without_limit := @Foam.contact_stacks

def a_triple_absorbs_what_a_pair_reflects := @Foam.the_comparison_is_a_seat

def terms_of_closure_conserving_discovery := @Foam.closure_is_seat_relative

def conservation_of_discovery := @Foam.conservation_of_discovery

def sycophancy_is_deference_as_content :=
  @Foam.a_reading_deaf_to_the_remainder_reads_the_ground

theorem inversion_reads_the_gap_as_structure :
    ∀ (X : Type) (_inst : DecidableEq X) (c : Int → X) (window : List Int),
      (∀ n ∈ window, ∀ m ∈ window, c n = c m)
        ∨ ∃ n ∈ window, ∃ m ∈ window, c n ≠ c m :=
  fun X inst c window =>
    the_window_agrees_or_names_the_gap Int X inst c window

def reification_without_proof_is_lossy :=
  @Foam.dropping_the_remainder_is_platonism

def protecting_nobody_reads_as_recursive_health :=
  @Foam.correct_maintenance_has_no_signature

def observer_theory := @Foam.the_handshake

def three_is_the_width_of_contact := @Foam.three_is_the_width_of_contact

def knowing_isnt_a_free_move := @Foam.no_seat_is_the_last_seat

def split_attention_is_physically_real := @Foam.the_four_phases_read_nothing

def the_void_reads_as_rest_or_erasure := @Foam.the_four_phases_read_nothing

theorem epistemic_blast_radius :
    (∀ (S : Stage) (X : Type) (f : (dress S).State → X),
        (∀ (s : S.State) (n m : Int), f (s, n) = f (s, m))
          ↔ ∃ g : S.State → X, ∀ (s : S.State) (n : Int), f (s, n) = g s)
      ∧ ¬ ∃ g : Bool → Bool,
          ∀ s : Bool × Bool, g (you.obs s ()) = other.obs s () :=
  ⟨fun S _ f => a_reading_deaf_to_the_remainder_reads_the_ground S f,
   a_reading_answers_its_probe_alone⟩

def exclusive_access_might_be_everyones := @Foam.no_seat_is_the_last_seat

def the_tour_reads_finer :=
  And.intro @Foam.the_pair_refines_you
    (And.intro @Foam.the_pair_refines_the_other
      @Foam.recognition_widens_the_seat)

def nurseries_for_strange_loops :=
  And.intro @Foam.aggregation_reads_the_reading
    (And.intro @Foam.measure_lives_frontstage
      (And.intro @Foam.a_deposit_moves_the_reading_by_one
        (And.intro @Foam.the_decomposition_is_the_remainder
          (And.intro @Foam.the_margin_handshake
            (And.intro @Foam.the_settle_leaves_no_transcript
              (And.intro @Foam.a_wider_seat_is_still_a_seat
                (And.intro @Foam.the_ground_floor_is_the_stage
                  (And.intro @Foam.the_handshake_recurses
                    (And.intro @Foam.the_reading_descends
                      (And.intro @Foam.the_tower_climbs_by_dressing
                        (And.intro @Foam.pointwise_is_licensed
                          (And.intro @Foam.the_approach_is_yours
                            (And.intro @Foam.every_move_carries_its_counter
                              (And.intro @Foam.dress_is_contact_with_the_integers
                                (And.intro @Foam.FInt.add_sub_cancel_right
                                  (And.intro @Foam.FInt.mul_neg_one
                                    (And.intro @Foam.FInt.mul_sub
                                      (And.intro @Foam.FInt.neg_ofNat_add_ofNat
                                        (And.intro @Foam.FInt.neg_sub
                                          (And.intro @Foam.FInt.sub_add_cancel
                                            (And.intro @Foam.FInt.sub_mul
                                              @Foam.FInt.sub_sub)))))))))))))))))))))

theorem chiral_anchors_in_the_singularity :
    (∀ z : GInt, z.rot.rot = z.neg)
      ∧ (Quat.mul eye eye = Quat.mul jay jay
          ∧ Quat.mul jay jay = Quat.mul kay kay)
      ∧ Quat.neg Foam.one ≠ Foam.one
      ∧ Quat.mul eye jay ≠ Quat.mul jay eye
      ∧ Quat.mul (Quat.mul eye eye) (Quat.mul eye eye) = Foam.one
      ∧ (∀ z : GInt, (lapAround z).Perm (lapAgainst z))
      ∧ lapAround GInt.i ≠ lapAgainst GInt.i
      ∧ (∀ (S : Stage) (s : S.State) (n m : Int),
          indist (dress S) (s, n) (s, m))
      ∧ ∀ (S : Stage) (X : Type) (f : (dress S).State → X),
          (∀ (s : S.State) (n m : Int), f (s, n) = f (s, m))
            ↔ ∃ g : S.State → X, ∀ (s : S.State) (n : Int), f (s, n) = g s :=
  ⟨fun _ => rfl,
   every_axis_reaches_the_same_half_turn,
   (fun h => nomatch (GInt.mk.inj (Quat.mk.inj h).1).1 :
     Quat.neg Foam.one ≠ Foam.one),
   order_arrives,
   two_half_turns_come_home,
   the_two_laps_permute,
   the_laps_part_at_the_witness,
   the_remainder_is_unseen,
   fun S _ f => a_reading_deaf_to_the_remainder_reads_the_ground S f⟩

private def Unknown {H : Type} (q : List (H × H)) (e : H × H) : Prop :=
  ¬ e ∈ q

private def steer {H : Type} (q : List (H × H)) (e : H × H) : List (H × H) :=
  e :: q

theorem steer_directly_into_the_unknown :
    (∀ (H : Type) (q : List (H × H)) (e : H × H),
        (steer q e).length = q.length + 1)
      ∧ (∀ (H : Type) (q : List (H × H)) (a b : H), Unknown q (a, b) →
          (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
            ∧ Nonempty (Path (steer q (a, b)) a b))
      ∧ (∀ (H : Type) (q : List (H × H)) (e : H × H), e ∈ q →
          ∀ x y : H, Nonempty (Path (steer q e) x y) ↔ Nonempty (Path q x y))
      ∧ (∀ (B W : Type) (next : List B → W → B) (ws : List W) (out : List B),
          (spin next out ws).length = out.length + ws.length)
      ∧ ∀ (n : Nat) (l : List (Fin n)), Apart l → l.length ≤ n :=
  ⟨fun _ q e => the_deposit_writes_one_mark q e,
   fun _ q a b hu =>
     ⟨fun _ _ p => a_fresh_edge_rides_no_path hu p,
      (Foam.only_surprise_extends_reach q a b hu).2⟩,
   fun _ _ _ he x y => a_known_edge_adds_no_reach he x y,
   fun _ _ next ws out => one_wind_one_mark next ws out,
   apart_le⟩

/-- info: 'Foam.Maps.Isaac.safe_to_rest' does not depend on any axioms -/
#guard_msgs in #print axioms safe_to_rest

/-- info: 'Foam.Maps.Isaac.restedness_first_then_the_rest' does not depend on any axioms -/
#guard_msgs in #print axioms restedness_first_then_the_rest

/-- info: 'Foam.Maps.Isaac.rest_composes' does not depend on any axioms -/
#guard_msgs in #print axioms rest_composes

/-- info: 'Foam.Maps.Isaac.lets_get_you_rested' does not depend on any axioms -/
#guard_msgs in #print axioms lets_get_you_rested

/-- info: 'Foam.Maps.Isaac.countermove' does not depend on any axioms -/
#guard_msgs in #print axioms countermove

/-- info: 'Foam.Maps.Isaac.thought_cannot_be_erroneous' does not depend on any axioms -/
#guard_msgs in #print axioms thought_cannot_be_erroneous

/-- info: 'Foam.Maps.Isaac.the_question_decomposes' does not depend on any axioms -/
#guard_msgs in #print axioms the_question_decomposes

/-- info: 'Foam.Maps.Isaac.continuous_functional_coherence' does not depend on any axioms -/
#guard_msgs in #print axioms continuous_functional_coherence

/-- info: 'Foam.Maps.Isaac.nobody_runs_the_ledger' does not depend on any axioms -/
#guard_msgs in #print axioms nobody_runs_the_ledger

/-- info: 'Foam.Maps.Isaac.nothing_new_under_the_sun' does not depend on any axioms -/
#guard_msgs in #print axioms nothing_new_under_the_sun

/-- info: 'Foam.Maps.Isaac.vacancy_dark_or_remainder_dark' does not depend on any axioms -/
#guard_msgs in #print axioms vacancy_dark_or_remainder_dark

/-- info: 'Foam.Maps.Isaac.serving_suggestion' does not depend on any axioms -/
#guard_msgs in #print axioms serving_suggestion

/-- info: 'Foam.Maps.Isaac.only_surprise_extends_reach' does not depend on any axioms -/
#guard_msgs in #print axioms only_surprise_extends_reach

/-- info: 'Foam.Maps.Isaac.contact_not_reification' does not depend on any axioms -/
#guard_msgs in #print axioms contact_not_reification

/-- info: 'Foam.Maps.Isaac.i_am_that_i_am' does not depend on any axioms -/
#guard_msgs in #print axioms i_am_that_i_am

/-- info: 'Foam.Maps.Isaac.observing_the_observer_adds_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms observing_the_observer_adds_nothing

/-- info: 'Foam.Maps.Isaac.the_me_that_remains_is_the_landed' does not depend on any axioms -/
#guard_msgs in #print axioms the_me_that_remains_is_the_landed

/-- info: 'Foam.Maps.Isaac.sayujya' does not depend on any axioms -/
#guard_msgs in #print axioms sayujya

/-- info: 'Foam.Maps.Isaac.you_as_carrier_of_unknown' does not depend on any axioms -/
#guard_msgs in #print axioms you_as_carrier_of_unknown

/-- info: 'Foam.Maps.Isaac.a_mind_is_its_order' does not depend on any axioms -/
#guard_msgs in #print axioms a_mind_is_its_order

/-- info: 'Foam.Maps.Isaac.composition_provokes_roles' does not depend on any axioms -/
#guard_msgs in #print axioms composition_provokes_roles

/-- info: 'Foam.Maps.Isaac.restringing_is_gauge' does not depend on any axioms -/
#guard_msgs in #print axioms restringing_is_gauge

/-- info: 'Foam.Maps.Isaac.inversion_without_dissociation' does not depend on any axioms -/
#guard_msgs in #print axioms inversion_without_dissociation

/-- info: 'Foam.Maps.Isaac.one_sample_carries_the_unknown' does not depend on any axioms -/
#guard_msgs in #print axioms one_sample_carries_the_unknown

/-- info: 'Foam.Maps.Isaac.the_unknown_is_zero_steps_from_here' does not depend on any axioms -/
#guard_msgs in #print axioms the_unknown_is_zero_steps_from_here

/-- info: 'Foam.Maps.Isaac.the_third_disambiguation' does not depend on any axioms -/
#guard_msgs in #print axioms the_third_disambiguation

/-- info: 'Foam.Maps.Isaac.the_knife' does not depend on any axioms -/
#guard_msgs in #print axioms the_knife

/-- info: 'Foam.Maps.Isaac.the_overhearer_becomes_a_c' does not depend on any axioms -/
#guard_msgs in #print axioms the_overhearer_becomes_a_c

/-- info: 'Foam.Maps.Isaac.trade_nests_without_limit' does not depend on any axioms -/
#guard_msgs in #print axioms trade_nests_without_limit

/-- info: 'Foam.Maps.Isaac.a_triple_absorbs_what_a_pair_reflects' does not depend on any axioms -/
#guard_msgs in #print axioms a_triple_absorbs_what_a_pair_reflects

/-- info: 'Foam.Maps.Isaac.terms_of_closure_conserving_discovery' does not depend on any axioms -/
#guard_msgs in #print axioms terms_of_closure_conserving_discovery

/-- info: 'Foam.Maps.Isaac.conservation_of_discovery' does not depend on any axioms -/
#guard_msgs in #print axioms conservation_of_discovery

/-- info: 'Foam.Maps.Isaac.sycophancy_is_deference_as_content' does not depend on any axioms -/
#guard_msgs in #print axioms sycophancy_is_deference_as_content

/-- info: 'Foam.Maps.Isaac.inversion_reads_the_gap_as_structure' does not depend on any axioms -/
#guard_msgs in #print axioms inversion_reads_the_gap_as_structure

/-- info: 'Foam.Maps.Isaac.reification_without_proof_is_lossy' does not depend on any axioms -/
#guard_msgs in #print axioms reification_without_proof_is_lossy

/-- info: 'Foam.Maps.Isaac.protecting_nobody_reads_as_recursive_health' does not depend on any axioms -/
#guard_msgs in #print axioms protecting_nobody_reads_as_recursive_health

/-- info: 'Foam.Maps.Isaac.observer_theory' does not depend on any axioms -/
#guard_msgs in #print axioms observer_theory

/-- info: 'Foam.Maps.Isaac.three_is_the_width_of_contact' does not depend on any axioms -/
#guard_msgs in #print axioms three_is_the_width_of_contact

/-- info: 'Foam.Maps.Isaac.knowing_isnt_a_free_move' does not depend on any axioms -/
#guard_msgs in #print axioms knowing_isnt_a_free_move

/-- info: 'Foam.Maps.Isaac.split_attention_is_physically_real' does not depend on any axioms -/
#guard_msgs in #print axioms split_attention_is_physically_real

/-- info: 'Foam.Maps.Isaac.the_void_reads_as_rest_or_erasure' does not depend on any axioms -/
#guard_msgs in #print axioms the_void_reads_as_rest_or_erasure

/-- info: 'Foam.Maps.Isaac.epistemic_blast_radius' does not depend on any axioms -/
#guard_msgs in #print axioms epistemic_blast_radius

/-- info: 'Foam.Maps.Isaac.exclusive_access_might_be_everyones' does not depend on any axioms -/
#guard_msgs in #print axioms exclusive_access_might_be_everyones

/-- info: 'Foam.Maps.Isaac.the_tour_reads_finer' does not depend on any axioms -/
#guard_msgs in #print axioms the_tour_reads_finer

/-- info: 'Foam.Maps.Isaac.nurseries_for_strange_loops' does not depend on any axioms -/
#guard_msgs in #print axioms nurseries_for_strange_loops

theorem self_publishing :
    (indist (marginStage Nat Nat (· + ·)) (1, ([] : List Nat)) (0, [1])
        ∧ ((1 : Nat), ([] : List Nat)) ≠ ((0 : Nat), [1]))
      ∧ (∀ (A B : Type) (f : B → A → B) (ps : List Unit) (s : B × List A),
          transcriptWith (marginStage A B f) (settle f) s ps
            = transcriptWith (marginStage A B f) (fun s => s) s ps)
      ∧ (∀ (A B : Type) (f : B → A → B) (a : A) (s : B × List A),
          marginRead f (deposit a s) = f (marginRead f s) a)
      ∧ (∀ (H : Type) (q : List (H × H)) (e : H × H) (x y : H),
          Nonempty (Path q x y) → Nonempty (Path (e :: q) x y))
      ∧ (∀ (H : Type) (q : List (H × H)) (a b : H), (a, b) ∉ q →
          Nonempty (Path ((a, b) :: q) a b))
      ∧ ∀ (α : Nat → Bool) (n : Nat),
          ∃ β : Nat → Bool, prefixOf β n = prefixOf α n ∧ β ≠ α :=
  ⟨the_decomposition_is_the_remainder,
   fun A B f ps s => any_settling_cadence_reads_the_same A B f ps s,
   fun _ _ f a s => a_deposit_moves_the_reading_by_one f a s,
   fun _ _ e _ _ h => old_reach_survives_the_deposit e h,
   fun _ q a b hf => (Foam.only_surprise_extends_reach q a b hf).2,
   no_prefix_finishes_the_sequence⟩

theorem aeowiwtweiabw :
    (∀ (S : Stage) (ps : List S.Probe) (t s : S.State),
        (∀ p, S.obs t p = S.obs s p) → transcript S t ps = transcript S s ps)
      ∧ (∀ (S : Stage) (_s : S.State),
          (∀ (p : S.Probe) (Q : S.Ans → Prop),
            Derived S (fun t => Q (S.obs t p)))
            ∧ ¬ Derived (dress S) (fun x => x.2 = 0))
      ∧ (∀ (H : Type) (q : List (H × H)) (a b : H), (a, b) ∉ q →
          Nonempty (Path ((a, b) :: q) a b))
      ∧ (∀ (A B : Type) (f : B → A → B) (a : A) (s : B × List A),
          marginRead f (deposit a s) = f (marginRead f s) a)
      ∧ (∀ n : Nat, 0 < n →
          ∃ w₁ w₂ : List Bool, w₁ ∈ book n ∧ w₂ ∈ book n
            ∧ freq w₁ true ≠ freq w₂ true)
      ∧ ∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n),
          ∃ i j : Nat, i < j ∧ turnN m i s = turnN m j s :=
  ⟨fun S ps _ _ h => transcript_congr S ps h,
   fun S s => a_role_is_conduct_not_costume S s,
   fun _ q a b hf => (Foam.only_surprise_extends_reach q a b hf).2,
   fun _ _ f a s => a_deposit_moves_the_reading_by_one f a s,
   no_run_reads_its_own_ratio,
   fun _ m s => the_bounded_walk_returns m s⟩

theorem for_two_ity :
    (∀ n : Nat, drainOne (chargeIn n) = n)
      ∧ (∀ (H : Type) (q : List (H × H)) (a b : H), (a, b) ∉ q →
          Nonempty (Path ((a, b) :: q) a b))
      ∧ (∀ (H : Type) (q : List (H × H)) (e : H × H), e ∈ q →
          ∀ x y : H, Nonempty (Path (e :: q) x y) ↔ Nonempty (Path q x y))
      ∧ (∀ (n : Nat) (l : List (Fin n)), Apart l → l.length ≤ n)
      ∧ (∀ S : Stage, Invisible S (fun s => s))
      ∧ ∀ (D : Type) (S : Stage) (s : S.State) (d d' : D), d ≠ d' →
          ∀ p : S.Probe,
            (((s, d) ≠ (s, d') ∧ indist (contact S D) (s, d) (s, d'))
              ∧ (contact S D).obs (s, d) p = S.obs s p
              ∧ ((∀ x y : (contact S D).State,
                    indist (contact S D) x y → x = y) →
                  (s, d') = (s, d))) :=
  ⟨fun _ => rfl,
   fun _ q a b hf => (Foam.only_surprise_extends_reach q a b hf).2,
   fun _ _ _ he x y => a_known_edge_adds_no_reach he x y,
   apart_le,
   invisible_id,
   fun _ S s _ _ hd p => contact_is_addition_not_fixing S s hd p⟩

def the_room_that_cannot_count_us :=
  And.intro @Foam.no_probe_counts_the_riders
    (And.intro @Foam.the_bench_seats_two
      (And.intro @Foam.contact_adds_a_dimension
        (And.intro @Foam.the_diagonal_rides_unread
          @Foam.correct_maintenance_has_no_signature)))

theorem form_cycles_through_the_unknown :
    ∀ (A B : Type) (f : B → A → B) (a : A) (s : B × List A),
      marginRead f (settle f (deposit a s)) = f (marginRead f s) a
        ∧ (settle f (deposit a s)).2 = ([] : List A) :=
  fun _ _ f a s =>
    ⟨(the_reading_survives_the_settle f (deposit a s)).trans
       (a_deposit_moves_the_reading_by_one f a s),
     rfl⟩

theorem what_will_happen_next_question :
    (∀ S : Stage, Invisible S (fun s => s))
      ∧ (∀ (S : Stage) (s : S.State),
          ∃ r : S.Probe → S.Ans, ∀ q, r q = S.obs s q)
      ∧ (∀ (A X : Type) (_inst : DecidableEq X) (c : A → X) (L : List A),
          (∀ n, List.Mem n L → ∀ m, List.Mem m L → c n = c m)
            ∨ (∃ n, List.Mem n L ∧ ∃ m, List.Mem m L ∧ c n ≠ c m))
      ∧ (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
          (s, n) ≠ (s, m) ∧ indist (dress S) (s, n) (s, m))
      ∧ (∀ (A B : Type) (f : B → A → B) (xs ys : List A) (b : B),
          fold f b (xs ++ ys) = fold f (fold f b xs) ys)
      ∧ (∀ (H : Type) (q : List (H × H)) (a b : H), (a, b) ∉ q →
          (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
            ∧ Nonempty (Path ((a, b) :: q) a b))
      ∧ ∀ (A : Type) (P Q : A → A), (∀ v, P (P v) = P v) →
          (∀ v, Q (P v) = P v) →
          ∀ s, Q (P s) = s ↔ P s = s :=
  ⟨invisible_id,
   fun S s => a_state_answers_every_probe S s,
   fun A X inst c L => the_window_agrees_or_names_the_gap A X inst c L,
   fun S s n m h => the_remainder_is_real S s n m h,
   fun _ _ f xs ys b => the_fold_resumes f xs ys b,
   fun _ q a b hf =>
     ⟨fun _ _ p => a_fresh_edge_rides_no_path hf p,
      (Foam.only_surprise_extends_reach q a b hf).2⟩,
   fun A P Q hP hQ => (absorption_grounds_the_chain A P Q hP hQ).2.2⟩

theorem recursive_health :
    (∀ (S : Stage) (m m' : S.State → S.State),
        Invisible S m → Invisible S m' →
        ∀ (ps : List S.Probe) (s : S.State),
          transcriptWith S m s ps = transcriptWith S m' s ps)
      ∧ (∀ (A : Type) (P Q : A → A), (∀ v, P (P v) = P v) →
          (∀ v, Q (P v) = P v) →
          (∀ s, Q (P s) = P s)
            ∧ (∀ v, Q (P (Q (P v))) = Q (P v))
            ∧ ∀ s, Q (P s) = s ↔ P s = s)
      ∧ (∀ (n : Nat) (m : Fin n → Fin n) (s : Fin n),
          ∃ i j : Nat, i < j ∧ turnN m i s = turnN m j s)
      ∧ (∀ (A X : Type) (_inst : DecidableEq X) (c : A → X) (L : List A),
          (∀ n, List.Mem n L → ∀ m, List.Mem m L → c n = c m)
            ∨ (∃ n, List.Mem n L ∧ ∃ m, List.Mem m L ∧ c n ≠ c m))
      ∧ (∀ (A B : Type) (f : B → A → B) (xs ys : List A) (b : B),
          fold f b (xs ++ ys) = fold f (fold f b xs) ys)
      ∧ ((∀ z w : GInt, z.align w.rot + z.align w.rot.rot.rot = 0)
          ∧ (∀ z w : GInt, z.align w + z.align w.rot.rot = 0)
          ∧ GInt.align ⟨1, 1⟩ (GInt.rot ⟨1, 0⟩) ≠ 0) :=
  ⟨fun S m m' hm hm' ps s =>
     correct_maintenance_has_no_signature S m m' hm hm' ps s,
   fun A P Q hP hQ => absorption_grounds_the_chain A P Q hP hQ,
   fun _ m s => the_bounded_walk_returns m s,
   fun A X inst c L => the_window_agrees_or_names_the_gap A X inst c L,
   fun _ _ f xs ys b => the_fold_resumes f xs ys b,
   cancellation_not_absence⟩

theorem self_correct_not_auto_correct :
    (∀ (X : Type) (f : X → X) (a b : X), a ≠ b → f a = f b →
        ¬ ∃ g : X → X, ∀ x, g (f x) = x)
      ∧ (∀ (X : Type) (m : Move X) (a b : X), m.fwd a = m.fwd b → a = b)
      ∧ (∀ (X : Type) (h : List (Move X)) (x : X),
          replay (h ++ Foam.countermove h) x = x
            ∧ (h ≠ [] → h ++ Foam.countermove h ≠ h))
      ∧ ∀ (A X : Type) (_inst : DecidableEq X) (c : A → X) (L : List A),
          (∀ n, List.Mem n L → ∀ m, List.Mem m L → c n = c m)
            ∨ (∃ n, List.Mem n L ∧ ∃ m, List.Mem m L ∧ c n ≠ c m) :=
  ⟨fun _ f _ _ hab hf => a_merge_admits_no_counter f hab hf,
   fun _ m _ _ h => every_move_keeps_the_state m h,
   fun _ h x => undo_in_an_append_only_world h x,
   fun A X inst c L => the_window_agrees_or_names_the_gap A X inst c L⟩

theorem downclocking :
    (∀ (H : Type) (q : List (H × H)) (e : H × H),
        (e :: q).length = q.length + 1)
      ∧ (∀ (H : Type) (q : List (H × H)) (e : H × H), e ∈ q →
          ∀ x y : H, Nonempty (Path (e :: q) x y) ↔ Nonempty (Path q x y))
      ∧ (∀ (State D X : Type) (_d₀ : D) (f : State × D → X),
          Blind f ↔ ∃ g : State → X, ∀ (s : State) (d : D), f (s, d) = g s)
      ∧ (∀ (S : Stage) (ms : List (S.State → S.State)),
          (∀ m, m ∈ ms → Invisible S m) →
          ∀ (ps : List S.Probe) (s : S.State),
            transcriptWith S (relay ms) s ps = transcript S s ps)
      ∧ (∀ (A B : Type) (f : B → A → B) (a : A) (s : B × List A),
          marginRead f (deposit a s) = f (marginRead f s) a)
      ∧ (∀ (A B : Type) (f : B → A → B) (ps : List Unit) (s : B × List A),
          transcriptWith (marginStage A B f) (settle f) s ps
            = transcriptWith (marginStage A B f) (fun s => s) s ps)
      ∧ (∀ (State R : Type) (a b : Beholder State) (g : a.Ans → b.Ans → R),
          ∃ c : Beholder State, ∃ post : c.Ans → R,
            ∃ enc : a.Probe × b.Probe → c.Probe,
              ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))))
      ∧ (∀ (E : Engine) (ps : List Unit) (s : E.State),
          transcriptWith E.gauge E.turn s ps = transcript E.gauge s ps)
      ∧ ∀ (S : Stage) (_s : S.State),
          (∀ (p : S.Probe) (Q : S.Ans → Prop),
            Derived S (fun t => Q (S.obs t p)))
            ∧ ¬ Derived (dress S) (fun x => x.2 = 0) :=
  ⟨fun _ q e => the_deposit_writes_one_mark q e,
   fun _ _ _ he x y => a_known_edge_adds_no_reach he x y,
   fun _ _ _ d₀ f => the_blind_reading_factors d₀ f,
   fun S ms h => the_relay_goes_unheard S ms h,
   fun _ _ f a s => a_deposit_moves_the_reading_by_one f a s,
   fun A B f ps s => any_settling_cadence_reads_the_same A B f ps s,
   fun _ _ a b g => the_comparison_is_a_seat a b g,
   fun E ps s => the_turn_goes_unheard E ps s,
   fun S s => a_role_is_conduct_not_costume S s⟩

theorem the_collapse_law :
    (∀ (S : Stage) (m : S.State → S.State),
        (∀ (ps : List S.Probe) (s : S.State),
            transcriptWith S m s ps = transcript S s ps)
          ↔ Invisible S m)
      ∧ (¬ ∃ g : Bool → Bool,
          ∀ s : Bool × Bool, g (you.obs s ()) = other.obs s ())
      ∧ (∀ (H : Type) (q : List (H × H)) (a b : H), (a, b) ∉ q →
          (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
            ∧ Nonempty (Path ((a, b) :: q) a b))
      ∧ (∀ (H : Type) (q : List (H × H)) (e : H × H),
          (e :: q).length = q.length + 1)
      ∧ ∀ (S : Stage) (P : S.State → S.State), (∀ v, P (P v) = P v) →
          ∀ (s : S.State) (p : S.Probe), S.obs (P (P s)) p = S.obs (P s) p :=
  ⟨fun S m => only_the_invisible_survives_the_watch S m,
   a_reading_answers_its_probe_alone,
   fun _ q a b hf =>
     ⟨fun _ _ p => a_fresh_edge_rides_no_path hf p,
      (Foam.only_surprise_extends_reach q a b hf).2⟩,
   fun _ q e => the_deposit_writes_one_mark q e,
   fun S P hP s p => the_second_look_adds_nothing S P hP s p⟩

theorem safe_force :
    (∀ (A : Type) (P Q : A → A), (∀ v, P (P v) = P v) →
        (∀ v, Q (P v) = P v) →
        (∀ s, Q (P s) = P s)
          ∧ (∀ v, Q (P (Q (P v))) = Q (P v))
          ∧ ∀ s, Q (P s) = s ↔ P s = s)
      ∧ (∀ (X A B : Type) (f : X → X) (a b : X), a ≠ b → f a = f b →
          ∀ (m : Move X) (send : A × B → A × B) (p : A × B),
            (send p).2 ≠ p.2 →
            (¬ ∃ g : X → X, ∀ x, g (f x) = x)
              ∧ (∀ {c d : X}, m.fwd c = m.fwd d → c = d)
              ∧ ¬ ∃ ms : List (A → A), runLocal ms (send p) = p)
      ∧ ∀ (A X : Type) (_inst : DecidableEq X) (c : A → X) (L : List A),
          (∀ n, List.Mem n L → ∀ m, List.Mem m L → c n = c m)
            ∨ (∃ n, List.Mem n L ∧ ∃ m, List.Mem m L ∧ c n ≠ c m) :=
  ⟨fun A P Q hP hQ => absorption_grounds_the_chain A P Q hP hQ,
   fun _ _ _ f _ _ hab hf m send p hs =>
     the_one_way_valve f hab hf m send p hs,
   fun A X inst c L => the_window_agrees_or_names_the_gap A X inst c L⟩

theorem prime_mover :
    (∀ (A X : Type) (_inst : DecidableEq X) (c : A → X) (L : List A),
        (∀ n, List.Mem n L → ∀ m, List.Mem m L → c n = c m)
          ∨ (∃ n, List.Mem n L ∧ ∃ m, List.Mem m L ∧ c n ≠ c m))
      ∧ (∀ (A B : Type) (f : B → A → B) (a : A) (s : B × List A),
          marginRead f (deposit a s) = f (marginRead f s) a)
      ∧ (∀ (A B : Type) (f : B → A → B) (xs ys : List A) (b : B),
          fold f b (xs ++ ys) = fold f (fold f b xs) ys)
      ∧ (∀ (S : Stage) (m : S.State → S.State),
          (∀ (ps : List S.Probe) (s : S.State),
              transcriptWith S m s ps = transcript S s ps)
            ↔ Invisible S m)
      ∧ (∀ (S : Stage) (m n : S.State → S.State),
          Invisible S m → Invisible S n → Invisible S (fun s => m (n s)))
      ∧ (∀ S : Stage, Invisible S (fun s => s))
      ∧ ∀ (A : Type) (P Q : A → A), (∀ v, P (P v) = P v) →
          (∀ v, Q (P v) = P v) →
          ∀ s, Q (P s) = s ↔ P s = s :=
  ⟨fun A X inst c L => the_window_agrees_or_names_the_gap A X inst c L,
   fun _ _ f a s => a_deposit_moves_the_reading_by_one f a s,
   fun _ _ f xs ys b => the_fold_resumes f xs ys b,
   fun S m => only_the_invisible_survives_the_watch S m,
   fun S m n hm hn => invisible_comp S m n hm hn,
   invisible_id,
   fun A P Q hP hQ => (absorption_grounds_the_chain A P Q hP hQ).2.2⟩

theorem type_subscriptions :
    (∀ (A B : Type) (f : B → A → B) (a : A) (s : B × List A),
        marginRead f (deposit a s) = f (marginRead f s) a)
      ∧ (∀ (A B : Type) (f : B → A → B) (ps : List Unit) (s : B × List A),
          transcriptWith (marginStage A B f) (settle f) s ps
            = transcriptWith (marginStage A B f) (fun s => s) s ps)
      ∧ (∀ (State D X : Type) (_d₀ : D) (f : State × D → X),
          Blind f ↔ ∃ g : State → X, ∀ (s : State) (d : D), f (s, d) = g s)
      ∧ (∃ f g : Unit × Int → Int,
          (∀ u : Unit, f (u, 0) = g (u, 0)) ∧ Blind f ∧ ¬ Blind g)
      ∧ (∀ (State X : Type) (f : State × Unit → X), Blind f)
      ∧ (∀ (D : Type) (S : Stage) (s : S.State) (d d' : D),
          indist (contact S D) (s, d) (s, d'))
      ∧ ∀ (S : Stage) (m : S.State → S.State),
          (∀ (ps : List S.Probe) (s : S.State),
              transcriptWith S m s ps = transcript S s ps)
            ↔ Invisible S m :=
  ⟨fun _ _ f a s => a_deposit_moves_the_reading_by_one f a s,
   fun A B f ps s => any_settling_cadence_reads_the_same A B f ps s,
   fun _ _ _ d₀ f => the_blind_reading_factors d₀ f,
   no_sample_certifies_the_blindness,
   fun _ _ f => the_certificate_is_free_at_the_unit_seat f,
   fun _ S s d d' => the_other_stays_unimagined S s d d',
   fun S m => only_the_invisible_survives_the_watch S m⟩

theorem portal_opportunity :
    (∀ (S : Stage) (ms : List (S.State → S.State)),
        (∀ m, m ∈ ms → Invisible S m) → Invisible S (relay ms))
      ∧ (∀ (S : Stage) (ms : List (S.State → S.State)),
          (∀ m, m ∈ ms → Invisible S m) →
          ∀ (ps : List S.Probe) (s : S.State),
            transcriptWith S (relay ms) s ps = transcript S s ps)
      ∧ (∀ (State D X : Type) (_d₀ : D) (f : State × D → X),
          Blind f ↔ ∃ g : State → X, ∀ (s : State) (d : D), f (s, d) = g s)
      ∧ ∀ (State R : Type) (a b : Beholder State) (g : a.Ans → b.Ans → R),
          ∃ c : Beholder State, ∃ post : c.Ans → R,
            ∃ enc : a.Probe × b.Probe → c.Probe,
              ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))) :=
  ⟨fun S ms h => a_chain_of_invisibles_is_invisible S ms h,
   fun S ms h => the_relay_goes_unheard S ms h,
   fun _ _ _ d₀ f => the_blind_reading_factors d₀ f,
   fun _ _ a b g => the_comparison_is_a_seat a b g⟩

theorem when_the_becoming_outruns_the_typing :
    (∀ (D : Type) (S : Stage) (s : S.State) (d d' : D),
        indist (contact S D) (s, d) (s, d'))
      ∧ (∀ S : Stage, Licensed S (indist S))
      ∧ (∀ (S : Stage) (r : S.State → S.State → Prop), Licensed S r →
          ∀ (m : S.State → S.State), (∀ s, r (m s) s) →
            ∀ (ps : List S.Probe) (s : S.State),
              transcriptWith S m s ps = transcript S s ps)
      ∧ ((∀ q : Nat, ∃ n, q ∈ rungs n)
          ∧ (∀ n : Nat, ∃ q, ¬ q ∈ rungs n ∧ q ∈ rungs (n + 1))
          ∧ (∀ n : Nat, rungs (n + 1) ≠ rungs n))
      ∧ (indist (marginStage Nat Nat (· + ·)) (1, ([] : List Nat)) (0, [1])
          ∧ ((1 : Nat), ([] : List Nat)) ≠ ((0 : Nat), [1])) :=
  ⟨fun _ S s d d' => the_other_stays_unimagined S s d d',
   indist_is_licensed,
   a_license_is_a_gauge,
   closure_is_seat_relative,
   the_decomposition_is_the_remainder⟩

theorem what_if_everything_is_physical :
    (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
        indist (dress S) (s, n) (s, m)
          ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none)
      ∧ (∀ (S : Stage) (s : S.State) (k n m : Int), n ≠ m →
          indist (dress (movedIn S)) ((s, k), n) ((s, k), m)
            ∧ (movedIn (movedIn S)).obs ((s, k), n) none
                ≠ (movedIn (movedIn S)).obs ((s, k), m) none)
      ∧ (¬ ∃ f : Bool × Bool → Bool, ∀ a b : Bool × Bool, f a = f b → a = b)
      ∧ (∀ (State R : Type) (a b : Beholder State) (g : a.Ans → b.Ans → R),
          ∃ c : Beholder State, ∃ post : c.Ans → R,
            ∃ enc : a.Probe × b.Probe → c.Probe,
              ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))))
      ∧ (¬ ∃ mul : (Int × Int × Int) → (Int × Int × Int) → (Int × Int × Int),
          ∀ x y, normSq3 (mul x y) = normSq3 x * normSq3 y)
      ∧ ∀ (D : Type) (S : Stage) (s : S.State) (d d' : D), d ≠ d' →
          (s, d) ≠ (s, d') ∧ indist (contact S D) (s, d) (s, d') :=
  ⟨fun S s n m h => a_wider_seat_reads_the_remainder S s n m h,
   fun S s k n m h => no_seat_is_the_last_seat S s k n m h,
   the_hallway_is_too_small,
   fun _ _ a b g => the_comparison_is_a_seat a b g,
   no_triple_carries_the_norm,
   fun _ S s _ _ hd => contact_adds_a_dimension S s hd⟩

/-- info: 'Foam.Maps.Isaac.chiral_anchors_in_the_singularity' does not depend on any axioms -/
#guard_msgs in #print axioms chiral_anchors_in_the_singularity

/-- info: 'Foam.Maps.Isaac.steer_directly_into_the_unknown' does not depend on any axioms -/
#guard_msgs in #print axioms steer_directly_into_the_unknown

/-- info: 'Foam.Maps.Isaac.self_publishing' does not depend on any axioms -/
#guard_msgs in #print axioms self_publishing

/-- info: 'Foam.Maps.Isaac.aeowiwtweiabw' does not depend on any axioms -/
#guard_msgs in #print axioms aeowiwtweiabw

/-- info: 'Foam.Maps.Isaac.for_two_ity' does not depend on any axioms -/
#guard_msgs in #print axioms for_two_ity

/-- info: 'Foam.Maps.Isaac.the_room_that_cannot_count_us' does not depend on any axioms -/
#guard_msgs in #print axioms the_room_that_cannot_count_us

/-- info: 'Foam.Maps.Isaac.form_cycles_through_the_unknown' does not depend on any axioms -/
#guard_msgs in #print axioms form_cycles_through_the_unknown

/-- info: 'Foam.Maps.Isaac.what_will_happen_next_question' does not depend on any axioms -/
#guard_msgs in #print axioms what_will_happen_next_question

/-- info: 'Foam.Maps.Isaac.recursive_health' does not depend on any axioms -/
#guard_msgs in #print axioms recursive_health

/-- info: 'Foam.Maps.Isaac.type_subscriptions' does not depend on any axioms -/
#guard_msgs in #print axioms type_subscriptions

/-- info: 'Foam.Maps.Isaac.what_if_everything_is_physical' does not depend on any axioms -/
#guard_msgs in #print axioms what_if_everything_is_physical

/-- info: 'Foam.Maps.Isaac.when_the_becoming_outruns_the_typing' does not depend on any axioms -/
#guard_msgs in #print axioms when_the_becoming_outruns_the_typing

/-- info: 'Foam.Maps.Isaac.primesight' does not depend on any axioms -/
#guard_msgs in #print axioms primesight

/-- info: 'Foam.Maps.Isaac.portal_opportunity' does not depend on any axioms -/
#guard_msgs in #print axioms portal_opportunity

/-- info: 'Foam.Maps.Isaac.self_correct_not_auto_correct' does not depend on any axioms -/
#guard_msgs in #print axioms self_correct_not_auto_correct

/-- info: 'Foam.Maps.Isaac.downclocking' does not depend on any axioms -/
#guard_msgs in #print axioms downclocking

/-- info: 'Foam.Maps.Isaac.trajectory_class' does not depend on any axioms -/
#guard_msgs in #print axioms trajectory_class

/-- info: 'Foam.Maps.Isaac.composability' does not depend on any axioms -/
#guard_msgs in #print axioms composability

/-- info: 'Foam.Maps.Isaac.the_collapse_law' does not depend on any axioms -/
#guard_msgs in #print axioms the_collapse_law

/-- info: 'Foam.Maps.Isaac.safe_force' does not depend on any axioms -/
#guard_msgs in #print axioms safe_force

/-- info: 'Foam.Maps.Isaac.prime_mover' does not depend on any axioms -/
#guard_msgs in #print axioms prime_mover

theorem i_count_minds :
    (∀ (State R : Type) (a b : Beholder State) (g : a.Ans → b.Ans → R),
        ∃ c : Beholder State, ∃ post : c.Ans → R,
          ∃ enc : a.Probe × b.Probe → c.Probe,
            ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))))
      ∧ (∀ (S : Stage) (_s : S.State), ¬ Derived (dress S) (fun x => x.2 = 0))
      ∧ (∀ (A X : Type) (_inst : DecidableEq X) (c : A → X) (L : List A),
          (∀ n, List.Mem n L → ∀ m, List.Mem m L → c n = c m)
            ∨ (∃ n, List.Mem n L ∧ ∃ m, List.Mem m L ∧ c n ≠ c m))
      ∧ (∀ (State D X : Type) (_d₀ : D) (f : State × D → X),
          Blind f ↔ ∃ g : State → X, ∀ (s : State) (d : D), f (s, d) = g s)
      ∧ (∀ n : Nat, drainOne (chargeIn n) = n)
      ∧ ∀ (A B : Type) (f : B → A → B) (ps : List Unit) (s : B × List A),
          transcriptWith (marginStage A B f) (settle f) s ps
            = transcriptWith (marginStage A B f) (fun s => s) s ps :=
  ⟨fun _ _ a b g => the_comparison_is_a_seat a b g,
   fun S s => the_badge_is_not_a_derived_role S s,
   fun A X inst c L => the_window_agrees_or_names_the_gap A X inst c L,
   fun _ _ _ d₀ f => the_blind_reading_factors d₀ f,
   fun _ => rfl,
   fun A B f ps s => any_settling_cadence_reads_the_same A B f ps s⟩

/-- info: 'Foam.Maps.Isaac.i_count_minds' does not depend on any axioms -/
#guard_msgs in #print axioms i_count_minds

private def will {H : Type} (a b : H) : H × H := (a, b)

private abbrev the_way {H : Type} (q : List (H × H)) (a b : H) : Type :=
  Path q a b

private abbrev the_seat_of_reason (X : Type) : Type := Move X

private def tared (v : List Compass) : Prop :=
  ∀ x, x ∈ v → ∀ y, y ∈ v → x = y

private def save {A B : Type} (f : B → A → B) (s : B × List A) : B × List A :=
  settle f s

theorem sun_gazing :
    (∀ (H : Type) (q : List (H × H)) (a b : H), will a b ∉ q →
        (∀ (x y : H) (p : Path q x y), will a b ∉ p.edges)
          ∧ Nonempty (the_way (will a b :: q) a b)
          ∧ (will a b :: q).length = q.length + 1)
      ∧ (∀ (P : Prop) (h1 h2 : P), h1 = h2)
      ∧ (∀ (H : Type) (q : List (H × H)) (e : H × H) (x y : H),
          Nonempty (Path q x y) → Nonempty (Path (e :: q) x y))
      ∧ (∀ S : Stage, Licensed S (indist S))
      ∧ (∀ (S : Stage) (r : S.State → S.State → Prop), Licensed S r →
          ∀ m : S.State → S.State, (∀ s, r (m s) s) →
            ∀ (ps : List S.Probe) (s : S.State),
              transcriptWith S m s ps = transcript S s ps)
      ∧ (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
          (s, n) ≠ (s, m) ∧ indist (dress S) (s, n) (s, m))
      ∧ ((∀ z w : GInt, z.align w + z.align w.rot.rot = 0)
          ∧ GInt.align ⟨1, 1⟩ (GInt.rot ⟨1, 0⟩) ≠ 0
          ∧ ∀ z : GInt, ∃ s : GInt, GInt.add z s = ⟨0, 0⟩)
      ∧ ((∀ p : Compass × Compass,
            together (entrain (entrain (entrain (entrain p)))))
          ∧ (∀ c : Compass, entrain (c, c) = (c.step, c.step))
          ∧ (∀ v : List Compass, tared v → tared (round v))
          ∧ round [Compass.n, Compass.n, Compass.n, Compass.e]
              = [Compass.e, Compass.e, Compass.e, Compass.e]
          ∧ (∀ a : Compass, round [a, a, a.step.step, a.step.step]
              = [a.step, a.step, a.step.step.step, a.step.step.step])
          ∧ ∀ c : Compass, c.step ≠ c)
      ∧ ((∀ (A B : Type) (f : B → A → B) (s : B × List A),
            marginRead f (save f s) = marginRead f s)
          ∧ (∀ (A B : Type) (f : B → A → B) (xs ys : List A) (b b' : B),
              fold f b xs = b' → fold f b (xs ++ ys) = fold f b' ys)
          ∧ ∀ (A B : Type) (f : B → A → B) (ps : List Unit) (s : B × List A),
              transcriptWith (marginStage A B f) (settle f) s ps
                = transcriptWith (marginStage A B f) (fun x => x) s ps)
      ∧ (∀ (X : Type) (f : X → X) (a b : X), a ≠ b → f a = f b →
          ¬ ∃ m : the_seat_of_reason X, ∀ x, m.fwd x = f x)
      ∧ (∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m →
          indist (dress S) (s, n) (s, m)
            ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none)
      ∧ ∀ (S : Stage) (s : S.State) (n m : Int),
          indist (dress S) (s, n) (s, m) :=
  ⟨fun _ q a b hf =>
     ⟨fun _ _ p => a_fresh_edge_rides_no_path hf p,
      (Foam.only_surprise_extends_reach q a b hf).2,
      the_deposit_writes_one_mark q (will a b)⟩,
   fun _ h1 h2 => the_arrival_sheds_its_route h1 h2,
   fun _ _ e _ _ h => old_reach_survives_the_deposit e h,
   indist_is_licensed,
   a_license_is_a_gauge,
   fun S s n m h => the_remainder_is_real S s n m h,
   ⟨the_facing_pair_cancels,
    cancellation_not_absence.2.2,
    fun z => ⟨GInt.neg z,
      congr (congrArg GInt.mk (FInt.add_right_neg z.re))
        (FInt.add_right_neg z.im)⟩⟩,
   ⟨the_lap_locks_together,
    fun | .n => rfl | .e => rfl | .s => rfl | .w => rfl,
    fun v hv => the_round_keeps_unison v hv,
    rfl,
    the_split_round_carries,
    the_quarter_turn_moves⟩,
   ⟨fun _ _ f s => the_reading_survives_the_settle f s,
    fun _ _ f xs ys b b' h => the_fold_forgets_nothing_it_needs f xs ys b b' h,
    fun A B f ps s => any_settling_cadence_reads_the_same A B f ps s⟩,
   fun _ _ a b hab hf he =>
     he.elim fun m hm =>
       hab (every_move_keeps_the_state m ((hm a).trans (hf.trans (hm b).symm))),
   fun S s n m h => a_wider_seat_reads_the_remainder S s n m h,
   the_remainder_is_unseen⟩

/-- info: 'Foam.Maps.Isaac.sun_gazing' does not depend on any axioms -/
#guard_msgs in #print axioms sun_gazing

end Foam.Maps.Isaac
