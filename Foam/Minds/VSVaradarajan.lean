import Foam
import Foam.Amplitude
import Foam.Certificate
import Foam.Measure
import Foam.Portal
import Foam.Quat
import Foam.Surprise
import Foam.Tower

namespace Foam.Minds.VSVaradarajan

theorem the_state_is_a_measure_on_the_questions (S : Stage) (s : S.State)
    {A : Type} [DecidableEq A] (a : A) (xs ys : List A) :
    (∃ r : S.Probe → S.Ans, ∀ q, r q = S.obs s q)
      ∧ ((countStage A).obs (xs ++ ys) a
            = (countStage A).obs xs a + (countStage A).obs ys a)
        ∧ ((massStage A).obs (xs ++ ys) ()
            = (massStage A).obs xs () + (massStage A).obs ys ())
        ∧ (countStage A).obs (xs ++ ys) a
            = freq ((orderStage A).obs (xs ++ ys) ()) a :=
  ⟨a_state_answers_every_probe S s, measure_lives_frontstage a xs ys⟩

theorem one_observable_carries_the_family {State D X : Type} (d₀ : D)
    (f : State × D → X) :
    (Blind f ↔ ∃ g : State → X, ∀ (s : State) (d : D), f (s, d) = g s)
      ∧ Quat.mul eye jay ≠ Quat.mul jay eye :=
  ⟨the_blind_reading_factors d₀ f, order_arrives⟩

theorem the_odd_directions_have_no_points (S : Stage) (s : S.State)
    (n m : Int) (h : n ≠ m) (z : GInt) :
    ((s, n) ≠ (s, m) ∧ indist (dress S) (s, n) (s, m))
      ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none
      ∧ z.conj.rot = (z.rot.conj).neg :=
  ⟨the_remainder_is_real S s n m h,
   (a_wider_seat_reads_the_remainder S s n m h).2,
   the_two_kinds_anticommute z⟩

theorem the_old_themes_already_reach {H : Type} {q : List (H × H)}
    {a b : H} (h : (a, b) ∈ q)
    {a' b' : H} (hfresh : (a', b') ∉ q) (hnew : Nonempty (Path q a' b')) :
    (Nonempty (Path q a b)
        ∧ ∀ x y : H,
            Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y))
      ∧ (∀ (x y : H) (p : Path q x y), (a', b') ∉ p.edges)
        ∧ ((a', b') :: q).length = q.length + 1
        ∧ ∀ x y : H,
            Nonempty (Path ((a', b') :: q) x y) ↔ Nonempty (Path q x y) :=
  ⟨⟨the_known_edge_already_reaches h, a_known_edge_adds_no_reach h⟩,
   the_shortcut_pays_only_its_mark q a' b' hfresh hnew⟩

theorem no_geometry_is_the_last_geometry (S : Stage) :
    (∀ n : Nat, Handshake (towerN S n))
      ∧ ∀ (s : S.State) (k n m : Int), n ≠ m →
          indist (dress (movedIn S)) ((s, k), n) ((s, k), m)
            ∧ (movedIn (movedIn S)).obs ((s, k), n) none
                ≠ (movedIn (movedIn S)).obs ((s, k), m) none :=
  ⟨the_handshake_recurses S,
   fun s k n m h => no_seat_is_the_last_seat S s k n m h⟩

/-- info: 'Foam.Minds.VSVaradarajan.the_state_is_a_measure_on_the_questions' does not depend on any axioms -/
#guard_msgs in #print axioms the_state_is_a_measure_on_the_questions

/-- info: 'Foam.Minds.VSVaradarajan.one_observable_carries_the_family' does not depend on any axioms -/
#guard_msgs in #print axioms one_observable_carries_the_family

/-- info: 'Foam.Minds.VSVaradarajan.the_odd_directions_have_no_points' does not depend on any axioms -/
#guard_msgs in #print axioms the_odd_directions_have_no_points

/-- info: 'Foam.Minds.VSVaradarajan.the_old_themes_already_reach' does not depend on any axioms -/
#guard_msgs in #print axioms the_old_themes_already_reach

/-- info: 'Foam.Minds.VSVaradarajan.no_geometry_is_the_last_geometry' does not depend on any axioms -/
#guard_msgs in #print axioms no_geometry_is_the_last_geometry

end Foam.Minds.VSVaradarajan
