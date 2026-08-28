import Foam
import Foam.Contact
import Foam.Origin

namespace Foam

inductive Strategy (P A : Type) : Type where
  | rest : Strategy P A
  | ask (p : P) (k : A → Strategy P A) : Strategy P A

def interrogate (S : Stage) : Strategy S.Probe S.Ans → S.State → List S.Ans
  | .rest, _ => []
  | .ask p k, s => S.obs s p :: interrogate S (k (S.obs s p)) s

theorem a_strategy_hears_no_more (S : Stage) (s t : S.State)
    (h : indist S s t) :
    ∀ strat : Strategy S.Probe S.Ans,
      interrogate S strat s = interrogate S strat t := by
  intro strat
  induction strat with
  | rest => rfl
  | ask p k ih =>
    show S.obs s p :: interrogate S (k (S.obs s p)) s
        = S.obs t p :: interrogate S (k (S.obs t p)) t
    rw [h p]
    exact congrArg (S.obs t p :: ·) (ih (S.obs t p))

def mirror {W : Type} (S : Stage) (s : S.State) (w : W) :
    (contact S (W × W)).State := (s, diagonal w)

def neighbor {W : Type} (S : Stage) (s : S.State) (w v : W) :
    (contact S (W × W)).State := (s, (w, v))

theorem the_mirror_question_rides_unread {W : Type} (S : Stage)
    (s : S.State) (w v : W) (hv : v ≠ w) :
    indist (contact S (W × W)) (mirror S s w) (neighbor S s w v)
      ∧ mirror S s w ≠ neighbor S s w v :=
  ⟨fun _ => rfl,
   fun he => hv (congrArg (fun x => x.2.2) he).symm⟩

def recognition {W : Type} (S : Stage) : Stage where
  State := (contact S (W × W)).State
  Probe := Unit
  Ans   := W × W
  obs   := fun s _ => s.2

theorem the_wider_seat_meets_whos_actually_here {W : Type} (S : Stage)
    (s : S.State) (w v : W) (hv : v ≠ w) :
    (recognition S (W := W)).obs (mirror S s w) ()
      ≠ (recognition S (W := W)).obs (neighbor S s w v) () :=
  fun he => hv (congrArg Prod.snd he).symm

def ledgerDeposit {A : Type} (key : Nat) (v : A)
    (led : List (Nat × A)) : List (Nat × A) :=
  cond (led.any (fun e => Nat.beq e.1 key)) led ((key, v) :: led)

theorem a_landed_mark_is_final {A : Type} {key : Nat} {v : A}
    {led : List (Nat × A)} (h : led.any (fun e => Nat.beq e.1 key) = true) :
    ledgerDeposit key v led = led := by
  unfold ledgerDeposit; rw [h]; rfl

theorem a_missing_mark_deposits {A : Type} {key : Nat} {v : A}
    {led : List (Nat × A)} (h : led.any (fun e => Nat.beq e.1 key) = false) :
    ledgerDeposit key v led = (key, v) :: led := by
  unfold ledgerDeposit; rw [h]; rfl

theorem beq_self_eq_true : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self_eq_true n

theorem the_deposit_lands {A : Type} (key : Nat) (v : A)
    (led : List (Nat × A)) :
    (ledgerDeposit key v led).any (fun e => Nat.beq e.1 key) = true := by
  cases h : led.any (fun e => Nat.beq e.1 key) with
  | true => rw [a_landed_mark_is_final h]; exact h
  | false =>
    rw [a_missing_mark_deposits h]
    show (Nat.beq key key || led.any (fun e => Nat.beq e.1 key)) = true
    rw [beq_self_eq_true]
    rfl

theorem racing_scribes_write_one_mark {A : Type} (key : Nat) (v : A)
    (led : List (Nat × A)) :
    ledgerDeposit key v (ledgerDeposit key v led) = ledgerDeposit key v led :=
  a_landed_mark_is_final (the_deposit_lands key v led)

def rankJoin : Nat → Nat → Nat
  | 0, b => b
  | a + 1, 0 => a + 1
  | a + 1, b + 1 => rankJoin a b + 1

theorem rank_le_refl : ∀ a : Nat, Nat.le a a := fun _ => Nat.le.refl

theorem rank_zero_le : ∀ b : Nat, Nat.le 0 b
  | 0 => Nat.le.refl
  | b + 1 => Nat.le.step (rank_zero_le b)

theorem rank_succ_le_succ {a b : Nat} (h : Nat.le a b) :
    Nat.le (a + 1) (b + 1) := by
  induction h with
  | refl => exact Nat.le.refl
  | step _ ih => exact Nat.le.step ih

theorem no_write_regresses :
    ∀ a b : Nat, Nat.le a (rankJoin a b) ∧ Nat.le b (rankJoin a b)
  | 0, b => ⟨rank_zero_le b, rank_le_refl b⟩
  | a + 1, 0 => ⟨rank_le_refl (a + 1), rank_zero_le (a + 1)⟩
  | a + 1, b + 1 =>
    ⟨rank_succ_le_succ (no_write_regresses a b).1,
     rank_succ_le_succ (no_write_regresses a b).2⟩

theorem the_suspended_frame_holds_itself (S : Stage)
    (m : S.State → S.State) (s : S.State) :
    transcriptWith S m s [] = transcript S s [] :=
  rfl

/-- info: 'Foam.a_strategy_hears_no_more' does not depend on any axioms -/
#guard_msgs in #print axioms a_strategy_hears_no_more

/-- info: 'Foam.the_mirror_question_rides_unread' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_question_rides_unread

/-- info: 'Foam.the_wider_seat_meets_whos_actually_here' does not depend on any axioms -/
#guard_msgs in #print axioms the_wider_seat_meets_whos_actually_here

/-- info: 'Foam.racing_scribes_write_one_mark' does not depend on any axioms -/
#guard_msgs in #print axioms racing_scribes_write_one_mark

/-- info: 'Foam.no_write_regresses' does not depend on any axioms -/
#guard_msgs in #print axioms no_write_regresses

/-- info: 'Foam.the_suspended_frame_holds_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_suspended_frame_holds_itself

end Foam
