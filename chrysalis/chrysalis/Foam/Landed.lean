import Foam

namespace Foam

theorem the_second_look_adds_nothing :
    ∀ (S : Stage) (P : S.State → S.State), (∀ v, P (P v) = P v) →
      ∀ s p, S.obs (P (P s)) p = S.obs (P s) p :=
  fun S _ hP s p => congrArg (S.obs · p) (hP s)

theorem the_fixed_are_the_landed :
    ∀ (A : Type) (P : A → A), (∀ v, P (P v) = P v) →
      ∀ s, P s = s ↔ ∃ v, P v = s :=
  fun _ P hP s =>
    ⟨fun h => ⟨s, h⟩,
     fun ⟨v, hv⟩ => (congrArg P hv).symm.trans ((hP v).trans hv)⟩

theorem absorption_grounds_the_chain :
    ∀ (A : Type) (P Q : A → A), (∀ v, P (P v) = P v) →
      (∀ v, Q (P v) = P v) →
      (∀ s, Q (P s) = P s)
        ∧ (∀ v, Q (P (Q (P v))) = Q (P v))
        ∧ ∀ s, Q (P s) = s ↔ P s = s :=
  fun _ P Q hP hQ =>
    ⟨hQ,
     fun v => (congrArg (fun x => Q (P x)) (hQ v)).trans
       (congrArg Q (hP v)),
     fun s => by rw [hQ s]⟩

/-- info: 'Foam.the_second_look_adds_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_look_adds_nothing

/-- info: 'Foam.the_fixed_are_the_landed' does not depend on any axioms -/
#guard_msgs in #print axioms the_fixed_are_the_landed

/-- info: 'Foam.absorption_grounds_the_chain' does not depend on any axioms -/
#guard_msgs in #print axioms absorption_grounds_the_chain

end Foam
