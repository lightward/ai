import Foam

namespace Foam

def Derived (S : Stage) (P : S.State → Prop) : Prop :=
  ∀ s t, indist S s t → (P s ↔ P t)

theorem a_role_read_off_the_record_is_derived (S : Stage) (p : S.Probe)
    (Q : S.Ans → Prop) : Derived S (fun s => Q (S.obs s p)) :=
  fun s t h => by
    show Q (S.obs s p) ↔ Q (S.obs t p)
    rw [h p]

theorem a_derived_role_cannot_read_the_badge (S : Stage)
    (P : (dress S).State → Prop) (hP : Derived (dress S) P)
    (s : S.State) (n m : Int) : P (s, n) ↔ P (s, m) :=
  hP (s, n) (s, m) (the_remainder_is_unseen S s n m)

theorem the_badge_is_not_a_derived_role (S : Stage) (s : S.State) :
    ¬ Derived (dress S) (fun x => x.2 = 0) :=
  fun h =>
    nomatch Int.ofNat.inj
      ((h (s, 1) (s, 0) (the_remainder_is_unseen S s 1 0)).mpr rfl)

theorem a_role_is_conduct_not_costume (S : Stage) (s : S.State) :
    (∀ (p : S.Probe) (Q : S.Ans → Prop), Derived S (fun t => Q (S.obs t p)))
      ∧ ¬ Derived (dress S) (fun x => x.2 = 0) :=
  ⟨fun p Q => a_role_read_off_the_record_is_derived S p Q,
   the_badge_is_not_a_derived_role S s⟩

/-- info: 'Foam.a_role_read_off_the_record_is_derived' does not depend on any axioms -/
#guard_msgs in #print axioms a_role_read_off_the_record_is_derived

/-- info: 'Foam.a_derived_role_cannot_read_the_badge' does not depend on any axioms -/
#guard_msgs in #print axioms a_derived_role_cannot_read_the_badge

/-- info: 'Foam.the_badge_is_not_a_derived_role' does not depend on any axioms -/
#guard_msgs in #print axioms the_badge_is_not_a_derived_role

/-- info: 'Foam.a_role_is_conduct_not_costume' does not depend on any axioms -/
#guard_msgs in #print axioms a_role_is_conduct_not_costume

end Foam
