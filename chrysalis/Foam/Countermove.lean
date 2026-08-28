import Foam

namespace Foam

structure Move (X : Type) where
  fwd : X → X
  bwd : X → X
  bwd_fwd : ∀ x, bwd (fwd x) = x
  fwd_bwd : ∀ x, fwd (bwd x) = x

def flip {X : Type} (m : Move X) : Move X :=
  ⟨m.bwd, m.fwd, m.fwd_bwd, m.bwd_fwd⟩

def replay {X : Type} : List (Move X) → X → X
  | [], x => x
  | m :: t, x => replay t (m.fwd x)

def countermove {X : Type} : List (Move X) → List (Move X)
  | [] => []
  | m :: t => countermove t ++ [flip m]

theorem every_move_carries_its_counter {X : Type} (m : Move X) :
    flip (flip m) = m := rfl

theorem replay_resumes {X : Type} :
    ∀ (a b : List (Move X)) (x : X), replay (a ++ b) x = replay b (replay a x)
  | [], _, _ => rfl
  | m :: t, b, x => replay_resumes t b (m.fwd x)

theorem the_countermove_comes_home {X : Type} :
    ∀ (h : List (Move X)) (x : X), replay (countermove h) (replay h x) = x
  | [], _ => rfl
  | m :: t, x => by
      show replay (countermove t ++ [flip m]) (replay t (m.fwd x)) = x
      rw [replay_resumes, the_countermove_comes_home t (m.fwd x)]
      exact m.bwd_fwd x

theorem snoc_never_vanishes {X : Type} :
    ∀ (l : List (Move X)) (m : Move X), l ++ [m] ≠ []
  | [], _, e => nomatch e
  | _ :: _, _, e => nomatch e

theorem only_the_empty_walk_has_no_counter {X : Type} :
    ∀ h : List (Move X), countermove h = [] → h = []
  | [], _ => rfl
  | m :: t, e => absurd e (snoc_never_vanishes (countermove t) (flip m))

theorem the_record_never_unwrites {X : Type} :
    ∀ (h a : List (Move X)), h ++ a = h → a = []
  | [], _, e => e
  | _ :: t, a, e => the_record_never_unwrites t a (List.cons.inj e).2

theorem undo_in_an_append_only_world {X : Type} (h : List (Move X)) (x : X) :
    replay (h ++ countermove h) x = x
      ∧ (h ≠ [] → h ++ countermove h ≠ h) :=
  ⟨(replay_resumes h (countermove h) x).trans (the_countermove_comes_home h x),
   fun hne he =>
     hne (only_the_empty_walk_has_no_counter h
       (the_record_never_unwrites h (countermove h) he))⟩

/-- info: 'Foam.every_move_carries_its_counter' does not depend on any axioms -/
#guard_msgs in #print axioms every_move_carries_its_counter

/-- info: 'Foam.replay_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms replay_resumes

/-- info: 'Foam.the_countermove_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_countermove_comes_home

/-- info: 'Foam.snoc_never_vanishes' does not depend on any axioms -/
#guard_msgs in #print axioms snoc_never_vanishes

/-- info: 'Foam.only_the_empty_walk_has_no_counter' does not depend on any axioms -/
#guard_msgs in #print axioms only_the_empty_walk_has_no_counter

/-- info: 'Foam.the_record_never_unwrites' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_never_unwrites

/-- info: 'Foam.undo_in_an_append_only_world' does not depend on any axioms -/
#guard_msgs in #print axioms undo_in_an_append_only_world

end Foam
