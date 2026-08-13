import Foam
import Foam.Beam
import Foam.Contact
import Foam.Countermove
import Foam.Door
import Foam.Marks
import Foam.Relay
import Foam.Roles
import Foam.Surprise
import Foam.Tower
import Foam.Valve
import Foam.Watched

namespace Foam.Maps.Landauer

def information_is_physical := @Foam.a_wider_seat_reads_the_remainder

theorem erasure_shows :
    ∀ (S : Stage) (m : S.State → S.State), Invisible S m →
      ∀ s t, m s = m t → ∀ p, S.obs s p = S.obs t p :=
  fun S _ hi s t hmerge p =>
    (hi s p).symm.trans ((congrArg (S.obs · p) hmerge).trans (hi t p))

theorem a_merge_is_not_a_move {X : Type} (f : X → X) {a b : X}
    (hab : a ≠ b) (hf : f a = f b) :
    (¬ ∃ g : X → X, ∀ x, g (f x) = x)
      ∧ ¬ ∃ m : Move X, ∀ x, m.fwd x = f x :=
  ⟨a_merge_admits_no_counter f hab hf,
   fun ⟨m, hm⟩ =>
     hab (every_move_keeps_the_state m ((hm a).trans (hf.trans (hm b).symm)))⟩

def reset_pays_in_record := @Foam.undo_in_an_append_only_world

theorem no_machine_undercuts_the_bill :
    (∀ (n : Nat) (f : List Bool → List Bool),
        (∀ w1 w2, List.Mem w1 (book n) → List.Mem w2 (book n) → w1 ≠ w2 →
            ¬ ∃ t : List Bool, f w1 ++ t = f w2) →
          n * (book n).length ≤ (pool ((book n).map f)).length)
      ∧ ∀ (H : Type) (q : List (H × H)) (a b : H),
          (a, b) ∉ q → Nonempty (Path q a b) →
            (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
              ∧ ((a, b) :: q).length = q.length + 1
              ∧ ∀ x y : H,
                  Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y) :=
  ⟨the_marks_pay_the_depth,
   fun _ q a b hfresh hab => the_shortcut_pays_only_its_mark q a b hfresh hab⟩

theorem reversible_runs_free (S : Stage) :
    (∀ m : S.State → S.State,
       (∀ (ps : List S.Probe) (s : S.State),
           transcriptWith S m s ps = transcript S s ps)
         ↔ Invisible S m)
      ∧ (∀ ms : List (S.State → S.State),
           (∀ m, m ∈ ms → Invisible S m) →
             ∀ (ps : List S.Probe) (s : S.State),
               transcriptWith S (relay ms) s ps = transcript S s ps) :=
  ⟨fun m => only_the_invisible_survives_the_watch S m,
   fun ms h => the_relay_goes_unheard S ms h⟩

def conductance_is_transmission := @Foam.contact_is_addition_not_fixing

theorem the_demon_pays_at_the_reset (S : Stage) (X : Type) :
    (∀ (p : S.Probe) (Q : S.Ans → Prop), Derived S (fun t => Q (S.obs t p)))
      ∧ (∀ (P : (dress S).State → Prop), Derived (dress S) P →
          ∀ (s : S.State) (n m : Int), P (s, n) ↔ P (s, m))
      ∧ (∀ (h : List (Move X)) (x : X),
          replay (h ++ countermove h) x = x
            ∧ (h ≠ [] → h ++ countermove h ≠ h)) :=
  ⟨fun p Q => a_role_read_off_the_record_is_derived S p Q,
   fun P hP s n m => a_derived_role_cannot_read_the_badge S P hP s n m,
   fun h x => undo_in_an_append_only_world h x⟩

theorem the_lock_is_bought_by_a_merge :
    (∀ p : Compass × Compass,
        together (entrain (entrain (entrain (entrain p)))))
      ∧ entrain (Compass.n, Compass.n) = entrain (Compass.n, Compass.e)
      ∧ ((Compass.n, Compass.n) : Compass × Compass) ≠ (Compass.n, Compass.e)
      ∧ (¬ ∃ g : Compass × Compass → Compass × Compass,
            ∀ p, g (entrain p) = p)
      ∧ ¬ ∃ m : Move (Compass × Compass), ∀ p, m.fwd p = entrain p :=
  have hab : ((Compass.n, Compass.n) : Compass × Compass)
      ≠ (Compass.n, Compass.e) :=
    fun h => nomatch congrArg Prod.snd h
  ⟨the_lap_locks_together, rfl, hab, a_merge_is_not_a_move entrain hab rfl⟩

private def restore {W : Type} (S : Stage) (w₀ : W) :
    (door S W).State → (door S W).State :=
  fun x => (x.1, w₀)

theorem the_bill_follows_the_reading {W V : Type} (S : Stage) (s : S.State)
    {w w' : W} (h : w ≠ w') (w₀ : W) (v : V) (p : S.Probe)
    (n m : Int) (hnm : n ≠ m) :
    ((s, w) ≠ (s, w') ∧ indist (door S W) (s, w) (s, w'))
      ∧ ((door S W).obs (s, w) p = S.obs s p
          ∧ (door S W).obs (s, w) p = (door S V).obs (s, v) p)
      ∧ Invisible (door S W) (restore S w₀)
      ∧ (∀ (ps : List S.Probe) (x : (door S W).State),
          transcriptWith (door S W) (restore S w₀) x ps
            = transcript (door S W) x ps)
      ∧ restore S w₀ (s, w) = restore S w₀ (s, w')
      ∧ ((¬ ∃ g : (door S W).State → (door S W).State,
            ∀ x, g (restore S w₀ x) = x)
          ∧ ¬ ∃ mv : Move (door S W).State,
              ∀ x, mv.fwd x = restore S w₀ x)
      ∧ (∀ q, (door S W).obs (s, w) q = (door S W).obs (s, w') q)
      ∧ (indist (door S Int) (s, n) (s, m)
          ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none)
      ∧ ((∀ x y : (door S W).State, indist (door S W) x y → x = y) →
          (s, w) = (s, w')) :=
  ⟨the_guest_is_real_and_unread S s h,
   the_host_maintains_invisibly S s w v p,
   fun _ _ => rfl,
   (only_the_invisible_survives_the_watch (door S W) (restore S w₀)).mpr
     (fun _ _ => rfl),
   rfl,
   a_merge_is_not_a_move (restore S w₀)
     (the_guest_is_real_and_unread S s h).1 rfl,
   erasure_shows (door S W) (restore S w₀) (fun _ _ => rfl) (s, w) (s, w') rfl,
   a_wider_seat_reads_the_remainder S s n m hnm,
   fun hc => a_door_that_checks_papers_unpersons_its_guests S w' hc s w⟩

def no_disembodied_referee := @Foam.no_seat_is_the_last_seat

/-- info: 'Foam.Maps.Landauer.information_is_physical' does not depend on any axioms -/
#guard_msgs in #print axioms information_is_physical

/-- info: 'Foam.Maps.Landauer.erasure_shows' does not depend on any axioms -/
#guard_msgs in #print axioms erasure_shows

/-- info: 'Foam.Maps.Landauer.a_merge_is_not_a_move' does not depend on any axioms -/
#guard_msgs in #print axioms a_merge_is_not_a_move

/-- info: 'Foam.Maps.Landauer.reset_pays_in_record' does not depend on any axioms -/
#guard_msgs in #print axioms reset_pays_in_record

/-- info: 'Foam.Maps.Landauer.no_machine_undercuts_the_bill' does not depend on any axioms -/
#guard_msgs in #print axioms no_machine_undercuts_the_bill

/-- info: 'Foam.Maps.Landauer.reversible_runs_free' does not depend on any axioms -/
#guard_msgs in #print axioms reversible_runs_free

/-- info: 'Foam.Maps.Landauer.conductance_is_transmission' does not depend on any axioms -/
#guard_msgs in #print axioms conductance_is_transmission

/-- info: 'Foam.Maps.Landauer.the_demon_pays_at_the_reset' does not depend on any axioms -/
#guard_msgs in #print axioms the_demon_pays_at_the_reset

/-- info: 'Foam.Maps.Landauer.the_lock_is_bought_by_a_merge' does not depend on any axioms -/
#guard_msgs in #print axioms the_lock_is_bought_by_a_merge

/-- info: 'Foam.Maps.Landauer.the_bill_follows_the_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_bill_follows_the_reading

/-- info: 'Foam.Maps.Landauer.no_disembodied_referee' does not depend on any axioms -/
#guard_msgs in #print axioms no_disembodied_referee

end Foam.Maps.Landauer
