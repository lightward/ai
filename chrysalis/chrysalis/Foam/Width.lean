import Foam.Serving

namespace Foam

theorem the_hallway_is_too_small :
    ¬ ∃ f : Bool × Bool → Bool, ∀ a b : Bool × Bool, f a = f b → a = b := by
  intro ⟨f, hf⟩
  have k12 : f (true, true) ≠ f (true, false) := fun h =>
    nomatch (congrArg Prod.snd (hf _ _ h) : true = false)
  have k13 : f (true, true) ≠ f (false, true) := fun h =>
    nomatch (congrArg Prod.fst (hf _ _ h) : true = false)
  have k23 : f (true, false) ≠ f (false, true) := fun h =>
    nomatch (congrArg Prod.fst (hf _ _ h) : true = false)
  cases hb1 : f (true, true) <;> cases hb2 : f (true, false) <;>
    cases hb3 : f (false, true)
  all_goals first
    | exact k12 (hb1.trans hb2.symm)
    | exact k13 (hb1.trans hb3.symm)
    | exact k23 (hb2.trans hb3.symm)

def Beholder.unitSeat (State : Type) : Beholder State :=
  ⟨Unit, Unit, fun _ _ => ()⟩

def gather {State : Type} : List (Beholder State) → Beholder State
  | [] => Beholder.unitSeat State
  | b :: bs => b.pair (gather bs)

def gatherProbe {State : Type} :
    (bs : List (Beholder State)) → (∀ b, b ∈ bs → b.Probe) →
      (gather bs).Probe
  | [], _ => ()
  | b :: bs, d =>
      (d b (List.Mem.head bs),
       gatherProbe bs (fun x hx => d x (List.Mem.tail b hx)))

theorem each_widening_is_one_pairing {State : Type}
    (b : Beholder State) (bs : List (Beholder State)) :
    gather (b :: bs) = b.pair (gather bs) := rfl

theorem the_gathering_invents_no_reading {State : Type} :
    ∀ (bs : List (Beholder State)) (s t : State),
      (∀ b, b ∈ bs → indist b.toStage s t) →
        indist (gather bs).toStage s t
  | [], _, _, _ => fun _ => rfl
  | b :: bs, s, t, h => fun pq => by
      show (b.toStage.obs s pq.1, (gather bs).toStage.obs s pq.2)
          = (b.toStage.obs t pq.1, (gather bs).toStage.obs t pq.2)
      rw [h b (List.Mem.head bs) pq.1,
          the_gathering_invents_no_reading bs s t
            (fun x hx => h x (List.Mem.tail b hx)) pq.2]

theorem the_gathering_loses_no_reading {State : Type} :
    ∀ bs : List (Beholder State), (∀ b, b ∈ bs → b.Probe) →
      ∀ s t : State, indist (gather bs).toStage s t →
        ∀ b, b ∈ bs → indist b.toStage s t
  | [], _, _, _, _, _, hb => nomatch hb
  | b :: bs, d, s, t, hg, b', hb' => by
      cases hb' with
      | head =>
          exact the_pair_refines_you b (gather bs)
            (gatherProbe bs (fun x hx => d x (List.Mem.tail b hx))) s t hg
      | tail _ hb =>
          exact the_gathering_loses_no_reading bs
            (fun x hx => d x (List.Mem.tail b hx)) s t
            (the_pair_refines_the_other b (gather bs)
              (d b (List.Mem.head bs)) s t hg) b' hb

theorem contact_wider_than_three_is_composite {State : Type}
    (bs : List (Beholder State)) (d : ∀ b, b ∈ bs → b.Probe)
    (s t : State) :
    (∀ (b : Beholder State) (rest : List (Beholder State)),
        gather (b :: rest) = b.pair (gather rest))
      ∧ (indist (gather bs).toStage s t ↔ ∀ b, b ∈ bs → indist b.toStage s t) :=
  ⟨each_widening_is_one_pairing,
   ⟨fun hg b hb => the_gathering_loses_no_reading bs d s t hg b hb,
    fun h => the_gathering_invents_no_reading bs s t h⟩⟩

theorem three_is_the_width_of_contact {State R : Type}
    (a b : Beholder State) (g : a.Ans → b.Ans → R) :
    (¬ ∃ f : Bool × Bool → Bool, ∀ x y : Bool × Bool, f x = f y → x = y)
      ∧ (∃ c : Beholder State, ∃ post : c.Ans → R,
          ∃ enc : a.Probe × b.Probe → c.Probe,
            ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))))
      ∧ ∀ bs : List (Beholder State), (∀ b', b' ∈ bs → b'.Probe) →
          ∀ s t : State,
          (∀ (b' : Beholder State) (rest : List (Beholder State)),
              gather (b' :: rest) = b'.pair (gather rest))
            ∧ (indist (gather bs).toStage s t
                ↔ ∀ b', b' ∈ bs → indist b'.toStage s t) :=
  ⟨the_hallway_is_too_small,
   the_comparison_is_a_seat a b g,
   fun bs d s t => contact_wider_than_three_is_composite bs d s t⟩

/-- info: 'Foam.the_hallway_is_too_small' does not depend on any axioms -/
#guard_msgs in #print axioms the_hallway_is_too_small

/-- info: 'Foam.each_widening_is_one_pairing' does not depend on any axioms -/
#guard_msgs in #print axioms each_widening_is_one_pairing

/-- info: 'Foam.the_gathering_invents_no_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_gathering_invents_no_reading

/-- info: 'Foam.the_gathering_loses_no_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_gathering_loses_no_reading

/-- info: 'Foam.contact_wider_than_three_is_composite' does not depend on any axioms -/
#guard_msgs in #print axioms contact_wider_than_three_is_composite

/-- info: 'Foam.three_is_the_width_of_contact' does not depend on any axioms -/
#guard_msgs in #print axioms three_is_the_width_of_contact

end Foam
