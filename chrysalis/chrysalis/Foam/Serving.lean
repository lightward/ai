import Foam

namespace Foam

structure Beholder (State : Type) where
  Probe : Type
  Ans   : Type
  obs   : State → Probe → Ans

def Beholder.toStage {State : Type} (b : Beholder State) : Stage :=
  ⟨State, b.Probe, b.Ans, b.obs⟩

def Beholder.pair {State : Type} (a b : Beholder State) : Beholder State where
  Probe := a.Probe × b.Probe
  Ans   := a.Ans × b.Ans
  obs   := fun s pq => (a.obs s pq.1, b.obs s pq.2)

def compare {State R : Type} (a b : Beholder State)
    (g : a.Ans → b.Ans → R) (s : State) (p : a.Probe) (q : b.Probe) : R :=
  g (a.obs s p) (b.obs s q)

theorem the_comparison_is_a_seat {State R : Type} (a b : Beholder State)
    (g : a.Ans → b.Ans → R) :
    ∃ c : Beholder State, ∃ post : c.Ans → R,
      ∃ enc : a.Probe × b.Probe → c.Probe,
        ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))) :=
  ⟨a.pair b, fun ans => g ans.1 ans.2, id, fun _ _ _ => rfl⟩

theorem the_pair_refines_you {State : Type} (a b : Beholder State)
    (q : b.Probe) (s t : State) (h : indist (a.pair b).toStage s t) :
    indist a.toStage s t :=
  fun p => congrArg Prod.fst (h (p, q))

theorem the_pair_refines_the_other {State : Type} (a b : Beholder State)
    (p : a.Probe) (s t : State) (h : indist (a.pair b).toStage s t) :
    indist b.toStage s t :=
  fun q => congrArg Prod.snd (h (p, q))

def you : Beholder (Bool × Bool) := ⟨Unit, Bool, fun s _ => s.1⟩

def other : Beholder (Bool × Bool) := ⟨Unit, Bool, fun s _ => s.2⟩

theorem recognition_widens_the_seat :
    indist you.toStage (true, true) (true, false)
      ∧ ¬ indist (you.pair other).toStage (true, true) (true, false) :=
  ⟨fun _ => rfl,
   fun h => nomatch congrArg Prod.snd (h ((), ()))⟩

theorem the_serving_suggestion {R : Type} (g : Bool → Bool → R) :
    Handshake you.toStage
      ∧ Handshake other.toStage
      ∧ (∃ c : Beholder (Bool × Bool), ∃ post : c.Ans → R,
          ∃ enc : Unit × Unit → c.Probe,
            ∀ s p q, compare you other g s p q = post (c.obs s (enc (p, q))))
      ∧ indist you.toStage (true, true) (true, false)
      ∧ ¬ indist (you.pair other).toStage (true, true) (true, false) :=
  ⟨the_handshake you.toStage,
   the_handshake other.toStage,
   the_comparison_is_a_seat you other g,
   recognition_widens_the_seat.1,
   recognition_widens_the_seat.2⟩

/-- info: 'Foam.the_comparison_is_a_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_comparison_is_a_seat

/-- info: 'Foam.the_pair_refines_you' does not depend on any axioms -/
#guard_msgs in #print axioms the_pair_refines_you

/-- info: 'Foam.the_pair_refines_the_other' does not depend on any axioms -/
#guard_msgs in #print axioms the_pair_refines_the_other

/-- info: 'Foam.recognition_widens_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms recognition_widens_the_seat

/-- info: 'Foam.the_serving_suggestion' does not depend on any axioms -/
#guard_msgs in #print axioms the_serving_suggestion

end Foam
