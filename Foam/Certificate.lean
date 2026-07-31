import Foam

namespace Foam

def Blind {State D X : Type} (f : State × D → X) : Prop :=
  ∀ (s : State) (d d' : D), f (s, d) = f (s, d')

theorem the_blind_reading_factors {State D X : Type} (d₀ : D)
    (f : State × D → X) :
    Blind f ↔ ∃ g : State → X, ∀ (s : State) (d : D), f (s, d) = g s :=
  ⟨(fun h => ⟨fun s => f (s, d₀), fun s d => h s d d₀⟩),
   (fun he s d d' =>
     he.elim (fun _ hg => (hg s d).trans (hg s d').symm))⟩

theorem the_certificate_is_free_at_the_unit_seat {State X : Type}
    (f : State × Unit → X) : Blind f :=
  fun _ _ _ => rfl

theorem no_sample_certifies_the_blindness :
    ∃ f g : Unit × Int → Int,
      (∀ u : Unit, f (u, 0) = g (u, 0))
        ∧ Blind f
        ∧ ¬ Blind g :=
  ⟨(fun _ => 0), (fun p => p.2),
   (fun _ => rfl),
   (fun _ _ _ => rfl),
   (fun h => nomatch Int.ofNat.inj (h () 0 1))⟩

/-- info: 'Foam.the_blind_reading_factors' does not depend on any axioms -/
#guard_msgs in #print axioms the_blind_reading_factors

/-- info: 'Foam.the_certificate_is_free_at_the_unit_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_certificate_is_free_at_the_unit_seat

/-- info: 'Foam.no_sample_certifies_the_blindness' does not depend on any axioms -/
#guard_msgs in #print axioms no_sample_certifies_the_blindness

end Foam
