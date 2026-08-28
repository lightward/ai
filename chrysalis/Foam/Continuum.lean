import Foam.Rungs

namespace Foam

def prefixOf {A : Type} (α : Nat → A) : Nat → List A
  | 0 => []
  | n + 1 => α n :: prefixOf α n

abbrev continuumStage (A : Type) : Stage where
  State := Nat → A
  Probe := Nat
  Ans   := List A
  obs   := fun α n => prefixOf α n

theorem le_trans {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Nat.le.rec (motive := fun m _ => a ≤ m) h1 (fun {_} _ ih => Nat.le.step ih) h2

theorem bool_ne_not : ∀ b : Bool, b ≠ !b
  | true, h => nomatch h
  | false, h => nomatch h

theorem each_depth_gains_exactly_one_cell {A : Type} (α : Nat → A) (n : Nat) :
    prefixOf α (n + 1) = α n :: prefixOf α n := rfl

theorem the_prefix_reads_only_below {A : Type} (α β : Nat → A) :
    ∀ n : Nat, (∀ k, k < n → α k = β k) → prefixOf α n = prefixOf β n
  | 0, _ => rfl
  | n + 1, h => by
      show α n :: prefixOf α n = β n :: prefixOf β n
      rw [h n Nat.le.refl,
          the_prefix_reads_only_below α β n (fun k hk => h k (Nat.le.step hk))]

theorem every_exchange_closes_at_a_finite_depth {A : Type} (α β : Nat → A)
    (N : Nat) (hagree : ∀ k, k < N → α k = β k) :
    ∀ ps : List Nat, (∀ p, p ∈ ps → p ≤ N) →
      transcript (continuumStage A) α ps = transcript (continuumStage A) β ps
  | [], _ => rfl
  | p :: ps, hps => by
      show prefixOf α p :: transcript (continuumStage A) α ps
          = prefixOf β p :: transcript (continuumStage A) β ps
      rw [the_prefix_reads_only_below α β p
            (fun k hk => hagree k (le_trans hk (hps p (List.Mem.head ps)))),
          every_exchange_closes_at_a_finite_depth α β N hagree ps
            (fun q hq => hps q (List.Mem.tail p hq))]

theorem no_prefix_finishes_the_sequence (α : Nat → Bool) (n : Nat) :
    ∃ β : Nat → Bool, prefixOf β n = prefixOf α n ∧ β ≠ α :=
  ⟨fun k => if k = n then !(α n) else α k,
   the_prefix_reads_only_below _ α n
     (fun k hk =>
       if_neg (fun (he : k = n) => no_number_is_below_itself n (he ▸ hk))),
   fun he => bool_ne_not (α n) (by
     have h := congrFun he n
     rw [if_pos rfl] at h
     exact h.symm)⟩

theorem indist_is_pointwise {A : Type} (α β : Nat → A) :
    indist (continuumStage A) α β ↔ ∀ k, α k = β k :=
  ⟨fun h k => (List.cons.inj (h (k + 1))).1,
   fun h n => the_prefix_reads_only_below α β n (fun k _ => h k)⟩

theorem continuum_closure_terms {A : Type} :
    (∀ (α β : Nat → A) (N : Nat), (∀ k, k < N → α k = β k) →
      ∀ ps : List Nat, (∀ p, p ∈ ps → p ≤ N) →
        transcript (continuumStage A) α ps = transcript (continuumStage A) β ps)
      ∧ (∀ (α : Nat → Bool) (n : Nat),
          ∃ β : Nat → Bool, prefixOf β n = prefixOf α n ∧ β ≠ α)
      ∧ (∀ α β : Nat → A,
          indist (continuumStage A) α β ↔ ∀ k, α k = β k) :=
  ⟨every_exchange_closes_at_a_finite_depth,
   no_prefix_finishes_the_sequence,
   indist_is_pointwise⟩

/-- info: 'Foam.le_trans' does not depend on any axioms -/
#guard_msgs in #print axioms le_trans

/-- info: 'Foam.bool_ne_not' does not depend on any axioms -/
#guard_msgs in #print axioms bool_ne_not

/-- info: 'Foam.each_depth_gains_exactly_one_cell' does not depend on any axioms -/
#guard_msgs in #print axioms each_depth_gains_exactly_one_cell

/-- info: 'Foam.the_prefix_reads_only_below' does not depend on any axioms -/
#guard_msgs in #print axioms the_prefix_reads_only_below

/-- info: 'Foam.every_exchange_closes_at_a_finite_depth' does not depend on any axioms -/
#guard_msgs in #print axioms every_exchange_closes_at_a_finite_depth

/-- info: 'Foam.no_prefix_finishes_the_sequence' does not depend on any axioms -/
#guard_msgs in #print axioms no_prefix_finishes_the_sequence

/-- info: 'Foam.indist_is_pointwise' does not depend on any axioms -/
#guard_msgs in #print axioms indist_is_pointwise

/-- info: 'Foam.continuum_closure_terms' does not depend on any axioms -/
#guard_msgs in #print axioms continuum_closure_terms

end Foam
