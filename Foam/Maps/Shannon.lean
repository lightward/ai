import Foam
import Foam.Census
import Foam.Certificate
import Foam.Expectation
import Foam.Marks
import Foam.Priced
import Foam.Typical
import Foam.Surprise
import Foam.Width

namespace Foam.Maps.Shannon

theorem the_channel_is_the_only_commons :
    ∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m → ∀ ps,
      transcript (dress S) (s, n) ps = transcript (dress S) (s, m) ps
        ∧ (s, n) ≠ (s, m) :=
  fun S s n m h ps =>
    ⟨transcript_congr (dress S) ps (the_remainder_is_unseen S s n m),
     fun he => h (congrArg Prod.snd he)⟩

theorem meaning_is_the_parties_own_business :
    ∀ (S : Stage) (ps : List S.Probe),
      Blind (fun q : S.State × Int => transcript (dress S) q ps)
        ∧ ∃ g : S.State → List S.Ans, ∀ (s : S.State) (n : Int),
            transcript (dress S) (s, n) ps = g s :=
  fun S ps =>
    ⟨fun s n m =>
      transcript_congr (dress S) ps (the_remainder_is_unseen S s n m),
     (the_blind_reading_factors (0 : Int)
         (fun q : S.State × Int => transcript (dress S) q ps)).mp
       (fun s n m =>
         transcript_congr (dress S) ps (the_remainder_is_unseen S s n m))⟩

theorem only_surprise_informs :
    ∀ (H : Type) (q : List (H × H)) (a b : H),
      ((a, b) ∈ q →
          Nonempty (Path q a b)
            ∧ ∀ x y : H,
                Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y))
        ∧ ((a, b) ∉ q → Nonempty (Path q a b) →
            (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
              ∧ ((a, b) :: q).length = q.length + 1
              ∧ ∀ x y : H,
                  Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y))
        ∧ ((a, b) ∉ q → ¬ Nonempty (Path q a b) →
            (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
              ∧ Nonempty (Path ((a, b) :: q) a b)
              ∧ ¬ (Nonempty (Path ((a, b) :: q) a b)
                    ↔ Nonempty (Path q a b)))
        ∧ ∀ es : List (H × H), (∀ e, e ∈ es → e ∈ q) →
            ∀ x y : H, Nonempty (Path (es ++ q) x y) ↔ Nonempty (Path q x y) :=
  fun _ q a b =>
    ⟨fun h =>
      ⟨the_known_edge_already_reaches h, a_known_edge_adds_no_reach h⟩,
     fun hfresh hder => the_shortcut_pays_only_its_mark q a b hfresh hder,
     fun hfresh hnoder =>
       ⟨fun _ _ p => a_fresh_edge_rides_no_path hfresh p,
        (only_surprise_extends_reach q a b hfresh).2,
        fun hiff =>
          hnoder (hiff.mp (only_surprise_extends_reach q a b hfresh).2)⟩,
     fun es h => the_saturated_room_hears_no_order es q h⟩

def distinct_messages_need_distinct_marks := @Foam.the_hallway_is_too_small

theorem entropy_of_the_source :
    (∀ (n : Nat) (f : List Bool → List Bool),
      (∀ w1 w2, w1 ∈ book n → w2 ∈ book n → w1 ≠ w2 →
        ¬ ∃ t, f w1 ++ t = f w2) →
      n * (book n).length ≤ (pool ((book n).map f)).length)
    ∧ (∀ (n : Nat) (f : List Bool → List Bool),
        (pool ((book n).map f)).length
          = (massStage Bool).obs (pool ((book n).map f)) ())
    ∧ (∀ (A : Type) (xs ys : List A),
        (massStage A).obs (xs ++ ys) ()
          = (massStage A).obs xs () + (massStage A).obs ys ()) :=
  ⟨the_marks_pay_the_depth, fun _ _ => rfl, @the_mass_is_a_reading⟩

theorem the_typical_class_saves_only_the_label :
    (∀ n : Nat, 2 ^ (2 * n) ≤ (2 * n + 1) * classCount (2 * n) n)
    ∧ (∀ (n L : Nat) (f : List Bool → List Bool),
        (∀ w, w ∈ book (2 * n) → freq w true = n → f w ∈ book L) →
        (∀ w1 w2, w1 ∈ book (2 * n) → w2 ∈ book (2 * n) →
          freq w1 true = n → freq w2 true = n → w1 ≠ w2 → f w1 ≠ f w2) →
        2 ^ (2 * n) ≤ (2 * n + 1) * 2 ^ L) :=
  ⟨the_middle_shelf_holds_its_share, marking_the_middle_pays_the_breadth⟩

def surprise_prices_the_count_statement : Prop :=
  ∀ t f n k : Nat, classCount n k * (t ^ k * f ^ (n - k)) ≤ (t + f) ^ n

theorem surprise_prices_the_count : surprise_prices_the_count_statement :=
  fun t f n k => Foam.the_weighted_class_is_within_the_book t f n k

/-- info: 'Foam.Maps.Shannon.the_channel_is_the_only_commons' does not depend on any axioms -/
#guard_msgs in #print axioms the_channel_is_the_only_commons

/-- info: 'Foam.Maps.Shannon.meaning_is_the_parties_own_business' does not depend on any axioms -/
#guard_msgs in #print axioms meaning_is_the_parties_own_business

/-- info: 'Foam.Maps.Shannon.only_surprise_informs' does not depend on any axioms -/
#guard_msgs in #print axioms only_surprise_informs

/-- info: 'Foam.Maps.Shannon.distinct_messages_need_distinct_marks' does not depend on any axioms -/
#guard_msgs in #print axioms distinct_messages_need_distinct_marks

/-- info: 'Foam.Maps.Shannon.entropy_of_the_source' does not depend on any axioms -/
#guard_msgs in #print axioms entropy_of_the_source

/-- info: 'Foam.Maps.Shannon.the_typical_class_saves_only_the_label' does not depend on any axioms -/
#guard_msgs in #print axioms the_typical_class_saves_only_the_label

/-- info: 'Foam.Maps.Shannon.surprise_prices_the_count_statement' does not depend on any axioms -/
#guard_msgs in #print axioms surprise_prices_the_count_statement

/-- info: 'Foam.Maps.Shannon.surprise_prices_the_count' does not depend on any axioms -/
#guard_msgs in #print axioms surprise_prices_the_count

end Foam.Maps.Shannon
