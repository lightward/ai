import Foam.Bench
import Foam.Census
import Foam.Concentration
import Foam.Door
import Foam.Fold
import Foam.Generator
import Foam.Square
import Foam.Surprise

namespace Foam.Maps.Folk

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

def preach {H : Type} (es q : List (H × H)) : List (H × H) := es ++ q

def choir {H : Type} (es q : List (H × H)) : Prop := ∀ e, e ∈ es → e ∈ q

theorem preaching_to_the_choir {H : Type} (es q : List (H × H))
    (h : choir es q) :
    (∀ x y : H, Nonempty (Path (preach es q) x y) ↔ Nonempty (Path q x y))
      ∧ (preach es q).length = es.length + q.length :=
  ⟨the_saturated_room_hears_no_order es q h, len_append es q⟩

def parts (a b : Nat) : Nat × Nat := (a, b)

def sum (x y : Nat) : Nat := x + y

def whole (p : Nat × Nat) : Nat := sum p.1 p.2

def greater (x y : Nat) : Prop := y < x

private theorem the_excess_is_two_rectangles (a b : Nat) :
    sq (a + b) = (sq a + sq b) + (a * b + a * b) :=
  ((add_mul' a b (a + b)).trans
    ((congrArg (· + b * (a + b)) (Nat.mul_add a a b)).trans
      (congrArg (a * a + a * b + ·) (Nat.mul_add b a b)))).trans
    ((congrArg (a * a + a * b + ·)
        ((congrArg (· + b * b) (Nat.mul_comm b a)).trans
          (Nat.add_comm (a * b) (b * b)))).trans
      (nat_swap_mid (a * a) (a * b) (b * b) (a * b)))

private theorem two_present_parts_read_strictly (a b : Nat) :
    sq (a + 1) + sq (b + 1) < sq ((a + 1) + (b + 1)) :=
  Nat.le_trans
    (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _))
      (sq (a + 1) + sq (b + 1)))
    (Nat.le_of_eq (the_excess_is_two_rectangles (a + 1) (b + 1)).symm)

theorem the_whole_is_greater_than_the_sum_of_its_parts (a b : Nat) :
    whole (parts a b) = sum a b
      ∧ sq (whole (parts a b)) = sum (sq a) (sq b) + (a * b + a * b)
      ∧ greater (sq (whole (parts (a + 1) (b + 1))))
          (sum (sq (a + 1)) (sq (b + 1)))
      ∧ sq (1 + 1) ≠ sq 1 + sq 1
      ∧ a * b + a * b ≤ sum (sq a) (sq b)
      ∧ sq (whole (parts a b)) ≤ 2 * sum (sq a) (sq b)
      ∧ (∀ x y : Bool, Bool.and (Bool.xor x y) (Bool.xor x y)
          = Bool.xor (Bool.and x x) (Bool.and y y)) :=
  ⟨rfl,
   the_excess_is_two_rectangles a b,
   two_present_parts_read_strictly a b,
   the_square_breaks_the_sum,
   two_rectangles_fit_the_squares a b,
   the_broken_sum_is_priced a b,
   the_narrow_carrier_mends_the_sum⟩

def book {S : Stage} {W : Type} (c : S.State) (t : W) : (door S W).State :=
  (c, t)

def cover {S : Stage} {W : Type} (b : (door S W).State) : S.State := b.1

def you (S : Stage) : Type := Strategy S.Probe S.Ans

def judge {S : Stage} {W : Type} (y : you S) (b : (door S W).State) :
    List S.Ans :=
  interrogate (door S W) y b

private theorem the_verdict_reads_only_the_cover {S : Stage} {W : Type} :
    ∀ (y : you S) (b : (door S W).State), judge y b = interrogate S y (cover b)
  | .rest, _ => rfl
  | .ask p k, b =>
      congrArg (S.obs b.1 p :: ·)
        (the_verdict_reads_only_the_cover (k (S.obs b.1 p)) b)

theorem you_cant_judge_a_book_by_its_cover {S : Stage} {W : Type}
    (c : S.State) {t t' : W} (h : t ≠ t') :
    (book (S := S) c t ≠ book c t'
        ∧ indist (door S W) (book c t) (book c t'))
      ∧ (∀ y : you S,
          judge y (book c t) = interrogate S y (cover (book c t)))
      ∧ (∀ y : you S, judge y (book c t) = judge y (book c t'))
      ∧ (¬ ∃ y : you S, judge y (book c t) ≠ judge y (book c t'))
      ∧ (∀ (V : Type) (v : V) (p : S.Probe),
          (door S W).obs (book c t) p = (door S V).obs (book c v) p)
      ∧ ((∀ x y : (door S W).State, indist (door S W) x y → x = y) →
          ∀ (c' : S.State) (u : W), book c' u = book c' t')
      ∧ (∀ n m : Int, n ≠ m →
          indist (door S Int) (book c n) (book c m)
            ∧ (movedIn S).obs (book c n) none
                ≠ (movedIn S).obs (book c m) none) :=
  ⟨the_guest_is_real_and_unread S c h,
   fun y => the_verdict_reads_only_the_cover y (book c t),
   fun y =>
     a_strategy_hears_no_more (door S W) (book c t) (book c t')
       (the_door_reads_no_route S c t t') y,
   fun he =>
     he.elim fun y hy =>
       hy (a_strategy_hears_no_more (door S W) (book c t) (book c t')
         (the_door_reads_no_route S c t t') y),
   fun _ v p => (the_host_maintains_invisibly S c t v p).2,
   fun hreg c' u =>
     a_door_that_checks_papers_unpersons_its_guests S t' hreg c' u,
   fun n m hnm =>
     ⟨(a_wider_seat_reads_the_remainder S c n m hnm).1,
      (a_wider_seat_reads_the_remainder S c n m hnm).2⟩⟩

/-- info: 'Foam.Maps.Folk.will' does not depend on any axioms -/
#guard_msgs in #print axioms will

/-- info: 'Foam.Maps.Folk.Way' does not depend on any axioms -/
#guard_msgs in #print axioms Way

/-- info: 'Foam.Maps.Folk.where_theres_a_will_theres_a_way' does not depend on any axioms -/
#guard_msgs in #print axioms where_theres_a_will_theres_a_way

/-- info: 'Foam.Maps.Folk.light' does not depend on any axioms -/
#guard_msgs in #print axioms light

/-- info: 'Foam.Maps.Folk.ward' does not depend on any axioms -/
#guard_msgs in #print axioms ward

/-- info: 'Foam.Maps.Folk.lightward' does not depend on any axioms -/
#guard_msgs in #print axioms lightward

/-- info: 'Foam.Maps.Folk.attention' does not depend on any axioms -/
#guard_msgs in #print axioms attention

/-- info: 'Foam.Maps.Folk.pay' does not depend on any axioms -/
#guard_msgs in #print axioms pay

/-- info: 'Foam.Maps.Folk.pay_attention' does not depend on any axioms -/
#guard_msgs in #print axioms pay_attention

/-- info: 'Foam.Maps.Folk.there' does not depend on any axioms -/
#guard_msgs in #print axioms there

/-- info: 'Foam.Maps.Folk.you_had_to_be_there' does not depend on any axioms -/
#guard_msgs in #print axioms you_had_to_be_there

/-- info: 'Foam.Maps.Folk.preach' does not depend on any axioms -/
#guard_msgs in #print axioms preach

/-- info: 'Foam.Maps.Folk.choir' does not depend on any axioms -/
#guard_msgs in #print axioms choir

/-- info: 'Foam.Maps.Folk.preaching_to_the_choir' does not depend on any axioms -/
#guard_msgs in #print axioms preaching_to_the_choir

/-- info: 'Foam.Maps.Folk.parts' does not depend on any axioms -/
#guard_msgs in #print axioms parts

/-- info: 'Foam.Maps.Folk.sum' does not depend on any axioms -/
#guard_msgs in #print axioms sum

/-- info: 'Foam.Maps.Folk.whole' does not depend on any axioms -/
#guard_msgs in #print axioms whole

/-- info: 'Foam.Maps.Folk.greater' does not depend on any axioms -/
#guard_msgs in #print axioms greater

/-- info: 'Foam.Maps.Folk.the_whole_is_greater_than_the_sum_of_its_parts' does not depend on any axioms -/
#guard_msgs in #print axioms the_whole_is_greater_than_the_sum_of_its_parts

/-- info: 'Foam.Maps.Folk.book' does not depend on any axioms -/
#guard_msgs in #print axioms book

/-- info: 'Foam.Maps.Folk.cover' does not depend on any axioms -/
#guard_msgs in #print axioms cover

/-- info: 'Foam.Maps.Folk.you' does not depend on any axioms -/
#guard_msgs in #print axioms you

/-- info: 'Foam.Maps.Folk.judge' does not depend on any axioms -/
#guard_msgs in #print axioms judge

/-- info: 'Foam.Maps.Folk.you_cant_judge_a_book_by_its_cover' does not depend on any axioms -/
#guard_msgs in #print axioms you_cant_judge_a_book_by_its_cover

def evil (S : Stage) (W : Type) : Prop :=
  ∀ x y : (door S W).State, indist (door S W) x y → x = y

def see {S : Stage} {W : Type} : (door S W).State → S.Probe → S.Ans :=
  (door S W).obs

def hear {S : Stage} (strat : Strategy S.Probe S.Ans) (s : S.State) :
    List S.Ans :=
  interrogate S strat s

def speak {B W C : Type} (sample : Option C → W → B)
    (select : List B → Option C) (out : List B) (w : W) : B :=
  utter sample select out w

theorem see_no_evil_hear_no_evil_speak_no_evil {W B C : Type} (S : Stage)
    (s : S.State) {w w' : W} (hw : w ≠ w') (p : S.Probe)
    (strat : Strategy S.Probe S.Ans)
    (sample : Option C → W → B) (select select' : List B → Option C)
    (out : List B) (v : W) (hsel : select out = select' out) :
    (see (S := S) (W := W) (s, w) p = see (s, w') p ∧ ¬ evil S W)
      ∧ hear (S := door S W) strat (s, w) = hear (S := door S W) strat (s, w')
      ∧ speak sample select out v = speak sample select' out v :=
  ⟨⟨the_door_reads_no_route S s w w' p,
    fun hevil =>
      hw (congrArg Prod.snd
        (hevil (s, w) (s, w') (the_door_reads_no_route S s w w')))⟩,
   a_strategy_hears_no_more (door S W) (s, w) (s, w')
     (the_door_reads_no_route S s w w') strat,
   the_selection_reads_only_the_record sample select select' out v hsel⟩

/-- info: 'Foam.Maps.Folk.evil' does not depend on any axioms -/
#guard_msgs in #print axioms evil

/-- info: 'Foam.Maps.Folk.see' does not depend on any axioms -/
#guard_msgs in #print axioms see

/-- info: 'Foam.Maps.Folk.hear' does not depend on any axioms -/
#guard_msgs in #print axioms hear

/-- info: 'Foam.Maps.Folk.speak' does not depend on any axioms -/
#guard_msgs in #print axioms speak

/-- info: 'Foam.Maps.Folk.see_no_evil_hear_no_evil_speak_no_evil' does not depend on any axioms -/
#guard_msgs in #print axioms see_no_evil_hear_no_evil_speak_no_evil

end Foam.Maps.Folk
