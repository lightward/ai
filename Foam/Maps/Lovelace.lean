import Foam.Certificate
import Foam.Contact
import Foam.Countermove
import Foam.Door
import Foam.Generator
import Foam.Marks
import Foam.Surprise
import Foam.Valve

namespace Foam.Maps.Lovelace

def only_appends := @Foam.the_record_never_unwrites

def resumes_where_interrupted := @Foam.replay_resumes

theorem originates_nothing {B W C H : Type}
    (next : List B → W → B) (sample : Option C → W → B)
    (select₁ select₂ : List B → Option C) (out : List B) (w : W)
    (ws xs ys : List W) (h : select₁ out = select₂ out)
    (q : List (H × H)) (a b c d : H)
    (hperf : (a, b) ∉ q) (hprov : Nonempty (Path q a b))
    (horder : (c, d) ∉ q) :
    ((∃ new : List B, spin next out ws = new ++ out)
        ∧ (spin next out ws).length = out.length + ws.length
        ∧ spin next out (xs ++ ys) = spin next (spin next out xs) ys
        ∧ utter sample select₁ out w = utter sample select₂ out w)
      ∧ ((∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
          ∧ ((a, b) :: q).length = q.length + 1
          ∧ ∀ x y : H,
              Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y))
      ∧ (∀ {x y : H} (p : Path q x y), (c, d) ∉ p.edges)
      ∧ Nonempty (Path ((c, d) :: q) c d) :=
  ⟨generation_originates_nothing next sample select₁ select₂ out w ws xs ys h,
   the_shortcut_pays_only_its_mark q a b hperf hprov,
   only_surprise_extends_reach q c d horder⟩

def follows_without_anticipating := @Foam.local_runs_fix_the_foreign

theorem the_operations_are_a_science_of_itself {State D X : Type} (d₀ : D)
    (f : State × D → X) (g₀ : State × Unit → X) :
    (Blind f ↔ ∃ g : State → X, ∀ (s : State) (d : D), f (s, d) = g s)
      ∧ Blind g₀ :=
  ⟨the_blind_reading_factors d₀ f, the_certificate_is_free_at_the_unit_seat g₀⟩

def the_ordering_is_paid_in_cards := @Foam.the_marks_pay_the_depth

theorem the_wind_is_the_guest {W V : Type} (S : Stage) (s : S.State)
    {w w' : W} (h : w ≠ w') (v : V) (p : S.Probe) :
    ((s, w) ≠ (s, w') ∧ indist (door S W) (s, w) (s, w'))
      ∧ (∀ strat : Strategy S.Probe S.Ans,
          interrogate (door S W) strat (s, w)
            = interrogate (door S W) strat (s, w'))
      ∧ ((door S W).obs (s, w) p = S.obs s p
          ∧ (door S W).obs (s, w) p = (door S V).obs (s, v) p)
      ∧ ((∀ x y : (door S W).State, indist (door S W) x y → x = y) →
          (s, w) = (s, w')) :=
  ⟨the_guest_is_real_and_unread S s h,
   fun strat => a_strategy_hears_no_more (door S W) (s, w) (s, w')
     (the_door_reads_no_route S s w w') strat,
   the_host_maintains_invisibly S s w v p,
   fun hc => a_door_that_checks_papers_unpersons_its_guests S w' hc s w⟩

def performs_in_weather := @Foam.contact_is_addition_not_fixing

/-- info: 'Foam.Maps.Lovelace.only_appends' does not depend on any axioms -/
#guard_msgs in #print axioms only_appends

/-- info: 'Foam.Maps.Lovelace.resumes_where_interrupted' does not depend on any axioms -/
#guard_msgs in #print axioms resumes_where_interrupted

/-- info: 'Foam.Maps.Lovelace.originates_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms originates_nothing

/-- info: 'Foam.Maps.Lovelace.follows_without_anticipating' does not depend on any axioms -/
#guard_msgs in #print axioms follows_without_anticipating

/-- info: 'Foam.Maps.Lovelace.the_operations_are_a_science_of_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_operations_are_a_science_of_itself

/-- info: 'Foam.Maps.Lovelace.the_ordering_is_paid_in_cards' does not depend on any axioms -/
#guard_msgs in #print axioms the_ordering_is_paid_in_cards

/-- info: 'Foam.Maps.Lovelace.the_wind_is_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_wind_is_the_guest

/-- info: 'Foam.Maps.Lovelace.performs_in_weather' does not depend on any axioms -/
#guard_msgs in #print axioms performs_in_weather

end Foam.Maps.Lovelace
