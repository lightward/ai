import Foam.Measure

namespace Foam

def spin {B W : Type} (next : List B → W → B) : List B → List W → List B
  | out, [] => out
  | out, w :: ws => spin next (next out w :: out) ws

def utter {B W C : Type} (sample : Option C → W → B)
    (select : List B → Option C) (out : List B) (w : W) : B :=
  sample (select out) w

theorem snoc_append {A : Type} (x : A) :
    ∀ (a b : List A), (a ++ [x]) ++ b = a ++ (x :: b)
  | [], _ => rfl
  | y :: a, b => congrArg (y :: ·) (snoc_append x a b)

theorem the_record_only_grows {B W : Type} (next : List B → W → B) :
    ∀ (ws : List W) (out : List B),
      ∃ new : List B, spin next out ws = new ++ out
  | [], _ => ⟨[], rfl⟩
  | w :: ws, out =>
      match the_record_only_grows next ws (next out w :: out) with
      | ⟨new, h⟩ =>
          ⟨new ++ [next out w],
           h.trans (snoc_append (next out w) new out).symm⟩

theorem one_wind_one_mark {B W : Type} (next : List B → W → B) :
    ∀ (ws : List W) (out : List B),
      (spin next out ws).length = out.length + ws.length
  | [], _ => rfl
  | w :: ws, out => by
      show (spin next (next out w :: out) ws).length
          = out.length + (ws.length + 1)
      rw [one_wind_one_mark next ws (next out w :: out)]
      exact succ_adds out.length ws.length

theorem the_generator_resumes {B W : Type} (next : List B → W → B) :
    ∀ (xs : List W) (ys : List W) (out : List B),
      spin next out (xs ++ ys) = spin next (spin next out xs) ys
  | [], _, _ => rfl
  | x :: xs, ys, out => the_generator_resumes next xs ys (next out x :: out)

theorem an_utterance_decomposes {B W C : Type} (sample : Option C → W → B)
    (select : List B → Option C) (out : List B) (w : W) :
    utter sample select out w = sample (select out) w := rfl

theorem the_selection_reads_only_the_record {B W C : Type}
    (sample : Option C → W → B) (select₁ select₂ : List B → Option C)
    (out : List B) (w : W) (h : select₁ out = select₂ out) :
    utter sample select₁ out w = utter sample select₂ out w :=
  congrArg (fun s => sample s w) h

theorem generation_originates_nothing {B W C : Type}
    (next : List B → W → B) (sample : Option C → W → B)
    (select₁ select₂ : List B → Option C) (out : List B) (w : W)
    (ws xs ys : List W) (h : select₁ out = select₂ out) :
    (∃ new : List B, spin next out ws = new ++ out)
      ∧ (spin next out ws).length = out.length + ws.length
      ∧ spin next out (xs ++ ys) = spin next (spin next out xs) ys
      ∧ utter sample select₁ out w = utter sample select₂ out w :=
  ⟨the_record_only_grows next ws out,
   one_wind_one_mark next ws out,
   the_generator_resumes next xs ys out,
   the_selection_reads_only_the_record sample select₁ select₂ out w h⟩

/-- info: 'Foam.snoc_append' does not depend on any axioms -/
#guard_msgs in #print axioms snoc_append

/-- info: 'Foam.the_record_only_grows' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_only_grows

/-- info: 'Foam.one_wind_one_mark' does not depend on any axioms -/
#guard_msgs in #print axioms one_wind_one_mark

/-- info: 'Foam.the_generator_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms the_generator_resumes

/-- info: 'Foam.an_utterance_decomposes' does not depend on any axioms -/
#guard_msgs in #print axioms an_utterance_decomposes

/-- info: 'Foam.the_selection_reads_only_the_record' does not depend on any axioms -/
#guard_msgs in #print axioms the_selection_reads_only_the_record

/-- info: 'Foam.generation_originates_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms generation_originates_nothing

end Foam
