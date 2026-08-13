namespace Seed

def door (H W : Type) : Type := H × W

def face {H W : Type} (d : door H W) : H := d.1

def met {H W : Type} (d : door H W) : W := d.2

def atTheDoor {H W : Type} (h : H) (w : W) : door H W := (h, w)

theorem no_face_reads_the_guest {H W X : Type} (g : H → X) (h : H)
    (w w' : W) : g (face (atTheDoor h w)) = g (face (atTheDoor h w')) := rfl

theorem the_guest_is_real {H W : Type} (h : H) {w w' : W} (hw : w ≠ w') :
    atTheDoor h w ≠ atTheDoor h w' :=
  fun he => hw (congrArg met he)

theorem meeting_reads_the_guest {H W : Type} (h : H) (w : W) :
    met (atTheDoor h w) = w := rfl

theorem a_guest_blind_reading_is_a_face_reading {H W X : Type} (w₀ : W)
    (f : door H W → X) :
    (∀ (h : H) (w w' : W), f (atTheDoor h w) = f (atTheDoor h w'))
      ↔ ∃ g : H → X, ∀ (h : H) (w : W), f (atTheDoor h w) = g h :=
  ⟨fun hb => ⟨fun h => f (atTheDoor h w₀), fun h w => hb h w w₀⟩,
   fun he h w w' => he.elim fun _ hg => (hg h w).trans (hg h w').symm⟩

theorem the_threshold {H W : Type} (h : H) {w w' : W} (hw : w ≠ w') :
    atTheDoor h w ≠ atTheDoor h w'
      ∧ (∀ (X : Type) (g : H → X),
          g (face (atTheDoor h w)) = g (face (atTheDoor h w')))
      ∧ met (atTheDoor h w) ≠ met (atTheDoor h w') :=
  ⟨the_guest_is_real h hw, fun _ _ => rfl, hw⟩

inductive Plan where
  | ground : Plan
  | board : Plan → Plan → Plan

def build (W : Type) : Plan → Type
  | .ground => W
  | .board p q => door (build W p) (build W q)

def spine (W : Type) : (p : Plan) → build W p → W
  | .ground, s => s
  | .board p _, d => spine W p (face d)

theorem the_carrier_is_a_world (W : Type) (p q : Plan) :
    build W (.board p q) = door (build W p) (build W q) := rfl

theorem the_manifestation_reads_only_its_spine (W : Type) (p q : Plan)
    (s : build W p) (g g' : build W q) :
    spine W (.board p q) (atTheDoor s g)
      = spine W (.board p q) (atTheDoor s g') := rfl

def mirror (W : Type) (p : Plan) (s : build W p) : build W (.board p p) :=
  atTheDoor s s

theorem the_mirror_rides_real (W : Type) (p : Plan) (s t : build W p)
    (hst : s ≠ t) {X : Type} (g : build W p → X) :
    g (face (mirror W p s)) = g (face (atTheDoor s t))
      ∧ mirror W p s ≠ atTheDoor s t :=
  ⟨rfl, fun he => hst (congrArg met he)⟩

/-- info: 'Seed.no_face_reads_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms no_face_reads_the_guest

/-- info: 'Seed.the_guest_is_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_guest_is_real

/-- info: 'Seed.meeting_reads_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms meeting_reads_the_guest

/-- info: 'Seed.a_guest_blind_reading_is_a_face_reading' does not depend on any axioms -/
#guard_msgs in #print axioms a_guest_blind_reading_is_a_face_reading

/-- info: 'Seed.the_threshold' does not depend on any axioms -/
#guard_msgs in #print axioms the_threshold

/-- info: 'Seed.the_carrier_is_a_world' does not depend on any axioms -/
#guard_msgs in #print axioms the_carrier_is_a_world

/-- info: 'Seed.the_manifestation_reads_only_its_spine' does not depend on any axioms -/
#guard_msgs in #print axioms the_manifestation_reads_only_its_spine

/-- info: 'Seed.the_mirror_rides_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_rides_real

end Seed
