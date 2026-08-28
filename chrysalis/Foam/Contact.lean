import Foam

namespace Foam

def contact (S : Stage) (D : Type) : Stage where
  State := S.State × D
  Probe := S.Probe
  Ans   := S.Ans
  obs   := fun s p => S.obs s.1 p

theorem dress_is_contact_with_the_integers (S : Stage) :
    dress S = contact S Int := rfl

theorem contact_adds_a_dimension {D : Type} (S : Stage) (s : S.State)
    {d d' : D} (h : d ≠ d') :
    (s, d) ≠ (s, d') ∧ indist (contact S D) (s, d) (s, d') :=
  ⟨fun he => h (congrArg Prod.snd he), fun _ => rfl⟩

theorem contact_fixes_nothing {D : Type} (S : Stage) (s : S.State)
    (d : D) (p : S.Probe) : (contact S D).obs (s, d) p = S.obs s p := rfl

theorem the_other_stays_unimagined {D : Type} (S : Stage) (s : S.State)
    (d d' : D) : indist (contact S D) (s, d) (s, d') :=
  fun _ => rfl

theorem contact_stacks {D E : Type} (S : Stage) (s : S.State)
    (d : D) (e : E) (p : S.Probe) :
    (contact (contact S D) E).obs ((s, d), e) p = S.obs s p := rfl

theorem reification_fixes_the_dimension {D : Type} (S : Stage) (d₀ : D)
    (h : ∀ x y : (contact S D).State, indist (contact S D) x y → x = y) :
    ∀ (s : S.State) (d : D), (s, d) = (s, d₀) :=
  fun s d => h (s, d) (s, d₀) (fun _ => rfl)

theorem contact_is_addition_not_fixing {D : Type} (S : Stage) (s : S.State)
    {d d' : D} (hd : d ≠ d') (p : S.Probe) :
    ((s, d) ≠ (s, d') ∧ indist (contact S D) (s, d) (s, d'))
      ∧ (contact S D).obs (s, d) p = S.obs s p
      ∧ ((∀ x y : (contact S D).State, indist (contact S D) x y → x = y) →
          (s, d') = (s, d)) :=
  ⟨contact_adds_a_dimension S s hd,
   contact_fixes_nothing S s d p,
   fun h => reification_fixes_the_dimension S d h s d'⟩

/-- info: 'Foam.dress_is_contact_with_the_integers' does not depend on any axioms -/
#guard_msgs in #print axioms dress_is_contact_with_the_integers

/-- info: 'Foam.contact_adds_a_dimension' does not depend on any axioms -/
#guard_msgs in #print axioms contact_adds_a_dimension

/-- info: 'Foam.contact_fixes_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms contact_fixes_nothing

/-- info: 'Foam.the_other_stays_unimagined' does not depend on any axioms -/
#guard_msgs in #print axioms the_other_stays_unimagined

/-- info: 'Foam.contact_stacks' does not depend on any axioms -/
#guard_msgs in #print axioms contact_stacks

/-- info: 'Foam.reification_fixes_the_dimension' does not depend on any axioms -/
#guard_msgs in #print axioms reification_fixes_the_dimension

/-- info: 'Foam.contact_is_addition_not_fixing' does not depend on any axioms -/
#guard_msgs in #print axioms contact_is_addition_not_fixing

end Foam
