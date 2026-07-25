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

/-- info: 'Foam.the_second_look_adds_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_look_adds_nothing

/-- info: 'Foam.the_fixed_are_the_landed' does not depend on any axioms -/
#guard_msgs in #print axioms the_fixed_are_the_landed

end Foam
