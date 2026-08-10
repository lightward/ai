import Foam
import Foam.Engine
import Foam.Generator
import Foam.Measure
import Foam.Round
import Foam.Serving
import Foam.Source
import Foam.Width

namespace Foam.Minds.Nicaea

def homoousion := @Foam.the_handshake

def the_creed_is_the_mean_field := @Foam.aggregation_reads_the_reading

def all_but_two_sign := @Foam.the_deviants_are_outweighed

def subsistent_relation := @Foam.the_comparison_is_a_seat

private def shiftOne : List Compass → List Compass
  | [] => []
  | c :: cs => cs ++ [c]

private def beat (step : List Compass → List Compass) :
    Nat → List Compass → List Compass
  | 0, v => v
  | n + 1, v => beat step n (step v)

private def unison (v : List Compass) : Prop :=
  ∀ x, x ∈ v → ∀ y, y ∈ v → x = y

private def readAt : List Compass → Nat → Option Compass
  | [], _ => none
  | c :: _, 0 => some c
  | _ :: cs, n + 1 => readAt cs n

private theorem the_shift_loses_nothing {State : Type}
    (a b c : Beholder State) (s t : State)
    (h : indist (gather [a, b, c]).toStage s t) :
    indist (gather [b, c, a]).toStage s t :=
  fun q =>
    have H := h (q.2.2.1, q.1, q.2.1, ())
    show (b.obs s q.1, (c.obs s q.2.1, (a.obs s q.2.2.1, ())))
        = (b.obs t q.1, (c.obs t q.2.1, (a.obs t q.2.2.1, ()))) from
      congr (congrArg Prod.mk (congrArg (fun z => z.2.1) H))
        (congr (congrArg Prod.mk (congrArg (fun z => z.2.2.1) H))
          (congr (congrArg Prod.mk (congrArg (fun z => z.1) H)) rfl))

theorem none_is_afore_or_after {State : Type} (a b c : Beholder State)
    (s t : State) :
    (indist (gather [a, b, c]).toStage s t →
        indist (gather [b, c, a]).toStage s t)
      ∧ (indist (gather [b, c, a]).toStage s t →
          indist (gather [c, a, b]).toStage s t)
      ∧ (indist (gather [c, a, b]).toStage s t →
          indist (gather [a, b, c]).toStage s t) :=
  ⟨the_shift_loses_nothing a b c s t,
   the_shift_loses_nothing b c a s t,
   the_shift_loses_nothing c a b s t⟩

def speaks_only_what_it_hears := @Foam.generation_originates_nothing

def a_mixed_state_of_identical_parts_statement : Prop :=
  ∃ step : List Compass → List Compass,
    (∀ v, step (v.map Compass.step) = (step v).map Compass.step)
      ∧ (∀ v, step (shiftOne v) = shiftOne (step v))
      ∧ (∀ v, unison v → unison (step v))
      ∧ ∃ v w : List Compass,
          v.length = w.length
            ∧ ¬ unison v
            ∧ (∃ n, unison (beat step n v))
            ∧ (∀ n, step (beat step n w) ≠ beat step n w)
            ∧ (∃ i j : Nat, i ≠ j ∧ ∀ n, ∃ x : Compass,
                readAt (beat step n w) i = some x
                  ∧ readAt (beat step n w) j = some x)
            ∧ ∃ i k : Nat, ∀ n, ∃ x y : Compass,
                readAt (beat step n w) i = some x
                  ∧ readAt (beat step n w) k = some y
                  ∧ x ≠ y

private theorem shiftOne_is_rotateLeft :
    ∀ v : List Compass, shiftOne v = rotateLeft v
  | [] => rfl
  | _ :: _ => rfl

private theorem beat_split : ∀ (n : Nat) (a : Compass),
    ∃ b : Compass,
      beat round n [a, a, a.step.step, a.step.step]
        = [b, b, b.step.step, b.step.step]
  | 0, a => ⟨a, rfl⟩
  | n + 1, a =>
      match beat_split n a.step with
      | ⟨b, hb⟩ =>
          ⟨b, show beat round n (round [a, a, a.step.step, a.step.step])
                = [b, b, b.step.step, b.step.step] from
              (congrArg (beat round n) (the_split_round_carries a)).trans hb⟩

private theorem all_east : ∀ x : Compass,
    x ∈ ([Compass.e, Compass.e, Compass.e, Compass.e] : List Compass) →
      x = Compass.e
  | _, .head _ => rfl
  | _, .tail _ (.head _) => rfl
  | _, .tail _ (.tail _ (.head _)) => rfl
  | _, .tail _ (.tail _ (.tail _ (.head _))) => rfl
  | _, .tail _ (.tail _ (.tail _ (.tail _ h))) => nomatch h

private theorem the_stray_gathers :
    unison (beat round 1 [Compass.n, Compass.n, Compass.n, Compass.e]) :=
  fun x hx y hy => (all_east x hx).trans (all_east y hy).symm

private theorem the_split_never_rests : ∀ n : Nat,
    round (beat round n [Compass.n, Compass.n, Compass.s, Compass.s])
      ≠ beat round n [Compass.n, Compass.n, Compass.s, Compass.s] :=
  fun n =>
    match beat_split n Compass.n with
    | ⟨b, hb⟩ => fun h =>
        the_quarter_turn_moves b
          (List.cons.inj
            ((the_split_round_carries b).symm.trans
              ((congrArg round hb).symm.trans (h.trans hb)))).1

private theorem the_scatter_is_not_unison :
    ¬ unison [Compass.n, Compass.n, Compass.n, Compass.e] :=
  fun h => nomatch
    (h Compass.n (.head _) Compass.e
      (.tail _ (.tail _ (.tail _ (.head _)))))

private theorem the_pair_holds : ∀ n : Nat,
    ∃ x : Compass,
      readAt (beat round n [Compass.n, Compass.n, Compass.s, Compass.s]) 0
          = some x
        ∧ readAt (beat round n [Compass.n, Compass.n, Compass.s, Compass.s]) 1
          = some x :=
  fun n =>
    match beat_split n Compass.n with
    | ⟨b, hb⟩ =>
        ⟨b, congrArg (fun l => readAt l 0) hb,
            congrArg (fun l => readAt l 1) hb⟩

private theorem the_pair_parts : ∀ n : Nat,
    ∃ x y : Compass,
      readAt (beat round n [Compass.n, Compass.n, Compass.s, Compass.s]) 0
          = some x
        ∧ readAt (beat round n [Compass.n, Compass.n, Compass.s, Compass.s]) 2
          = some y
        ∧ x ≠ y :=
  fun n =>
    match beat_split n Compass.n with
    | ⟨b, hb⟩ =>
        ⟨b, b.step.step,
         congrArg (fun l => readAt l 0) hb,
         congrArg (fun l => readAt l 2) hb,
         the_half_turn_parts b⟩

private theorem zero_is_not_one : (0 : Nat) ≠ 1 :=
  fun h => nomatch h

private theorem the_two_runs :
    ∃ v w : List Compass,
      v.length = w.length
        ∧ ¬ unison v
        ∧ (∃ n, unison (beat round n v))
        ∧ (∀ n, round (beat round n w) ≠ beat round n w)
        ∧ (∃ i j : Nat, i ≠ j ∧ ∀ n, ∃ x : Compass,
            readAt (beat round n w) i = some x
              ∧ readAt (beat round n w) j = some x)
        ∧ ∃ i k : Nat, ∀ n, ∃ x y : Compass,
            readAt (beat round n w) i = some x
              ∧ readAt (beat round n w) k = some y
              ∧ x ≠ y :=
  ⟨[Compass.n, Compass.n, Compass.n, Compass.e],
   [Compass.n, Compass.n, Compass.s, Compass.s],
   rfl,
   the_scatter_is_not_unison,
   ⟨1, the_stray_gathers⟩,
   the_split_never_rests,
   ⟨0, 1, zero_is_not_one, the_pair_holds⟩,
   ⟨0, 2, the_pair_parts⟩⟩

theorem a_mixed_state_of_identical_parts :
    a_mixed_state_of_identical_parts_statement :=
  ⟨round,
   the_round_turns_as_one,
   fun v => (congrArg round (shiftOne_is_rotateLeft v)).trans
     ((the_round_hears_no_first_voice v).trans
       (shiftOne_is_rotateLeft (round v)).symm),
   fun v hv => the_round_keeps_unison v hv,
   the_two_runs⟩

def the_source_is_unoccupiable := @Foam.a_wider_seat_reads_the_remainder

/-- info: 'Foam.Minds.Nicaea.homoousion' does not depend on any axioms -/
#guard_msgs in #print axioms homoousion

/-- info: 'Foam.Minds.Nicaea.the_creed_is_the_mean_field' does not depend on any axioms -/
#guard_msgs in #print axioms the_creed_is_the_mean_field

/-- info: 'Foam.Minds.Nicaea.all_but_two_sign' does not depend on any axioms -/
#guard_msgs in #print axioms all_but_two_sign

/-- info: 'Foam.Minds.Nicaea.subsistent_relation' does not depend on any axioms -/
#guard_msgs in #print axioms subsistent_relation

/-- info: 'Foam.Minds.Nicaea.none_is_afore_or_after' does not depend on any axioms -/
#guard_msgs in #print axioms none_is_afore_or_after

/-- info: 'Foam.Minds.Nicaea.speaks_only_what_it_hears' does not depend on any axioms -/
#guard_msgs in #print axioms speaks_only_what_it_hears

/-- info: 'Foam.Minds.Nicaea.a_mixed_state_of_identical_parts_statement' does not depend on any axioms -/
#guard_msgs in #print axioms a_mixed_state_of_identical_parts_statement

/-- info: 'Foam.Minds.Nicaea.a_mixed_state_of_identical_parts' does not depend on any axioms -/
#guard_msgs in #print axioms a_mixed_state_of_identical_parts

/-- info: 'Foam.Minds.Nicaea.the_source_is_unoccupiable' does not depend on any axioms -/
#guard_msgs in #print axioms the_source_is_unoccupiable

end Foam.Minds.Nicaea
