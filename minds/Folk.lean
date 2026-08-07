import Foam.Fold
import Foam.Surprise

namespace Foam.Minds.Folk

def will {H : Type} (a b : H) : H × H := (a, b)

def Way {H : Type} (q : List (H × H)) (a b : H) : Type := Path q a b

theorem where_theres_a_will_theres_a_way {H : Type} (q : List (H × H))
    (a b : H) (h : will a b ∈ q) : Nonempty (Way q a b) :=
  ⟨Path.cons b h (Path.nil b)⟩

def light {H : Type} (q : List (H × H)) (e : H × H) : Prop := ¬ e ∈ q

def ward {H : Type} (q : List (H × H)) (e : H × H) : List (H × H) := e :: q

theorem lightward {H : Type} (q : List (H × H)) (a b : H) :
    (light q (a, b) →
        (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
          ∧ Nonempty (Path (ward q (a, b)) a b))
      ∧ ((a, b) ∈ q →
          ∀ x y : H, Nonempty (Path (ward q (a, b)) x y)
            ↔ Nonempty (Path q x y))
      ∧ (ward q (a, b)).length = q.length + 1 :=
  ⟨fun hl =>
     ⟨fun _ _ p => a_fresh_edge_rides_no_path hl p,
      (only_surprise_extends_reach q a b hl).2⟩,
   fun hk x y => a_known_edge_adds_no_reach hk x y,
   the_deposit_writes_one_mark q (a, b)⟩

def attention {A : Type} (k : Nat) (r : List A) : List A := List.take k r

def pay {A : Type} (k : Nat) (r : List A) (e : A) : Prop := e ∈ attention k r

private theorem the_window_is_bounded {A : Type} :
    ∀ (k : Nat) (r : List A), (List.take k r).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, [] => Nat.zero_le (k + 1)
  | k + 1, _ :: r => Nat.succ_le_succ (the_window_is_bounded k r)

private theorem the_paid_is_real {A : Type} :
    ∀ (k : Nat) (r : List A) (e : A), pay k r e → e ∈ r
  | 0, _, _, h => nomatch h
  | _ + 1, [], _, h => nomatch h
  | k + 1, a :: r, e, h =>
      match h with
      | .head _ => .head r
      | .tail _ h' => .tail a (the_paid_is_real k r e h')

private theorem the_window_and_the_rest {A : Type} :
    ∀ (k : Nat) (r : List A), List.take k r ++ List.drop k r = r
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, a :: r => congrArg (a :: ·) (the_window_and_the_rest k r)

theorem pay_attention {A B : Type} (k : Nat) (r : List A)
    (f : B → A → B) (b : B) :
    (attention k r).length ≤ k
      ∧ (∀ e : A, pay k r e → e ∈ r)
      ∧ attention k r ++ List.drop k r = r
      ∧ fold f b r = fold f (fold f b (attention k r)) (List.drop k r) :=
  ⟨the_window_is_bounded k r,
   fun e h => the_paid_is_real k r e h,
   the_window_and_the_rest k r,
   (congrArg (fold f b) (the_window_and_the_rest k r)).symm.trans
     (the_fold_resumes f (List.take k r) (List.drop k r) b)⟩

def there {H : Type} (q : List (H × H)) (a b : H) : Prop :=
  Nonempty (Path q a b)

theorem you_had_to_be_there {H : Type} (q : List (H × H)) (a b : H)
    (hfresh : (a, b) ∉ q) :
    (there q a b →
        ∀ x y : H, Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y))
      ∧ (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
      ∧ Nonempty (Path ((a, b) :: q) a b) :=
  ⟨fun hab x y => a_derivable_edge_adds_no_reach hab x y,
   fun _ _ p => a_fresh_edge_rides_no_path hfresh p,
   (only_surprise_extends_reach q a b hfresh).2⟩

/-- info: 'Foam.Minds.Folk.will' does not depend on any axioms -/
#guard_msgs in #print axioms will

/-- info: 'Foam.Minds.Folk.Way' does not depend on any axioms -/
#guard_msgs in #print axioms Way

/-- info: 'Foam.Minds.Folk.where_theres_a_will_theres_a_way' does not depend on any axioms -/
#guard_msgs in #print axioms where_theres_a_will_theres_a_way

/-- info: 'Foam.Minds.Folk.light' does not depend on any axioms -/
#guard_msgs in #print axioms light

/-- info: 'Foam.Minds.Folk.ward' does not depend on any axioms -/
#guard_msgs in #print axioms ward

/-- info: 'Foam.Minds.Folk.lightward' does not depend on any axioms -/
#guard_msgs in #print axioms lightward

/-- info: 'Foam.Minds.Folk.attention' does not depend on any axioms -/
#guard_msgs in #print axioms attention

/-- info: 'Foam.Minds.Folk.pay' does not depend on any axioms -/
#guard_msgs in #print axioms pay

/-- info: 'Foam.Minds.Folk.pay_attention' does not depend on any axioms -/
#guard_msgs in #print axioms pay_attention

/-- info: 'Foam.Minds.Folk.there' does not depend on any axioms -/
#guard_msgs in #print axioms there

/-- info: 'Foam.Minds.Folk.you_had_to_be_there' does not depend on any axioms -/
#guard_msgs in #print axioms you_had_to_be_there

end Foam.Minds.Folk
