namespace Foam

structure Stage where
  State : Type
  Probe : Type
  Ans   : Type
  obs   : State → Probe → Ans

def indist (S : Stage) (s t : S.State) : Prop :=
  ∀ p, S.obs s p = S.obs t p

def Licensed (S : Stage) (r : S.State → S.State → Prop) : Prop :=
  ∀ s t, r s t → ∀ p, S.obs s p = S.obs t p

def transcript (S : Stage) (s : S.State) : List S.Probe → List S.Ans
  | [] => []
  | p :: ps => S.obs s p :: transcript S s ps

def transcriptWith (S : Stage) (m : S.State → S.State) :
    S.State → List S.Probe → List S.Ans
  | _, [] => []
  | s, p :: ps => S.obs (m s) p :: transcriptWith S m (m s) ps

theorem transcript_congr (S : Stage) (ps : List S.Probe) :
    ∀ {t s : S.State}, (∀ p, S.obs t p = S.obs s p) →
      transcript S t ps = transcript S s ps := by
  induction ps with
  | nil => intro t s _; rfl
  | cons p ps ih =>
    intro t s h
    show S.obs t p :: transcript S t ps = S.obs s p :: transcript S s ps
    rw [h p, ih h]

theorem a_license_is_a_gauge (S : Stage) (r : S.State → S.State → Prop)
    (hr : Licensed S r) (m : S.State → S.State) (hm : ∀ s, r (m s) s) :
    ∀ (ps : List S.Probe) (s : S.State),
      transcriptWith S m s ps = transcript S s ps := by
  intro ps
  induction ps with
  | nil => intro s; rfl
  | cons p ps ih =>
    intro s
    show S.obs (m s) p :: transcriptWith S m (m s) ps
        = S.obs s p :: transcript S s ps
    rw [hr (m s) s (hm s) p, ih (m s), transcript_congr S ps (hr (m s) s (hm s))]

theorem indist_is_licensed (S : Stage) : Licensed S (indist S) :=
  fun _ _ h => h

def Invisible (S : Stage) (m : S.State → S.State) : Prop :=
  ∀ s, indist S (m s) s

theorem invisible_id (S : Stage) : Invisible S (fun s => s) :=
  fun _ _ => rfl

theorem invisible_comp (S : Stage) (m n : S.State → S.State)
    (hm : Invisible S m) (hn : Invisible S n) :
    Invisible S (fun s => m (n s)) :=
  fun s p => (hm (n s) p).trans (hn s p)

theorem invisible_is_gauge (S : Stage) (m : S.State → S.State)
    (hm : Invisible S m) :
    ∀ (ps : List S.Probe) (s : S.State),
      transcriptWith S m s ps = transcript S s ps :=
  a_license_is_a_gauge S (indist S) (indist_is_licensed S) m hm

theorem correct_maintenance_has_no_signature (S : Stage)
    (m m' : S.State → S.State) (hm : Invisible S m) (hm' : Invisible S m')
    (ps : List S.Probe) (s : S.State) :
    transcriptWith S m s ps = transcriptWith S m' s ps :=
  (a_license_is_a_gauge S (indist S) (indist_is_licensed S) m hm ps s).trans
    (a_license_is_a_gauge S (indist S) (indist_is_licensed S) m' hm' ps s).symm

def dress (S : Stage) : Stage where
  State := S.State × Int
  Probe := S.Probe
  Ans   := S.Ans
  obs   := fun s p => S.obs s.1 p

theorem the_remainder_is_unseen (S : Stage) (s : S.State) (n m : Int) :
    indist (dress S) (s, n) (s, m) :=
  fun _ => rfl

theorem the_remainder_is_real (S : Stage) (s : S.State)
    (n m : Int) (h : n ≠ m) :
    (s, n) ≠ (s, m) ∧ indist (dress S) (s, n) (s, m) :=
  ⟨fun he => h (congrArg Prod.snd he), fun _ => rfl⟩

def movedIn (S : Stage) : Stage where
  State := S.State × Int
  Probe := Option S.Probe
  Ans   := S.Ans ⊕ Int
  obs   := fun s p =>
    match p with
    | none => Sum.inr s.2
    | some q => Sum.inl (S.obs s.1 q)

theorem a_wider_seat_reads_the_remainder (S : Stage) (s : S.State)
    (n m : Int) (h : n ≠ m) :
    indist (dress S) (s, n) (s, m)
      ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none :=
  ⟨fun _ => rfl, fun he => h (Sum.inr.inj he)⟩

theorem dropping_the_remainder_is_platonism (S : Stage)
    (h : ∀ s t : (dress S).State, indist (dress S) s t → s = t) :
    ∀ (s : S.State) (n : Int), (s, n) = (s, (0 : Int)) :=
  fun s n => h (s, n) (s, 0) (fun _ => rfl)

theorem a_reading_deaf_to_the_remainder_reads_the_ground (S : Stage)
    {X : Type} (f : (dress S).State → X) :
    (∀ (s : S.State) (n m : Int), f (s, n) = f (s, m))
      ↔ ∃ g : S.State → X, ∀ (s : S.State) (n : Int), f (s, n) = g s :=
  ⟨fun h => ⟨fun s => f (s, 0), fun s n => h s n 0⟩,
   fun he s n m => he.elim fun _ hg => (hg s n).trans (hg s m).symm⟩

def Handshake (S : Stage) : Prop :=
  (∀ (r : S.State → S.State → Prop), Licensed S r →
    ∀ (m : S.State → S.State), (∀ s, r (m s) s) →
      ∀ (ps : List S.Probe) (s : S.State),
        transcriptWith S m s ps = transcript S s ps)
    ∧ (∀ (s : S.State) (n m : Int), n ≠ m →
        (s, n) ≠ (s, m)
          ∧ indist (dress S) (s, n) (s, m)
          ∧ (movedIn S).obs (s, n) none ≠ (movedIn S).obs (s, m) none)

theorem the_handshake (S : Stage) : Handshake S :=
  ⟨fun r hr m hm => a_license_is_a_gauge S r hr m hm,
   fun s n m h =>
     ⟨(the_remainder_is_real S s n m h).1,
      (the_remainder_is_real S s n m h).2,
      (a_wider_seat_reads_the_remainder S s n m h).2⟩⟩

/-- info: 'Foam.transcript_congr' does not depend on any axioms -/
#guard_msgs in #print axioms transcript_congr

/-- info: 'Foam.a_license_is_a_gauge' does not depend on any axioms -/
#guard_msgs in #print axioms a_license_is_a_gauge

/-- info: 'Foam.indist_is_licensed' does not depend on any axioms -/
#guard_msgs in #print axioms indist_is_licensed

/-- info: 'Foam.invisible_id' does not depend on any axioms -/
#guard_msgs in #print axioms invisible_id

/-- info: 'Foam.invisible_comp' does not depend on any axioms -/
#guard_msgs in #print axioms invisible_comp

/-- info: 'Foam.invisible_is_gauge' does not depend on any axioms -/
#guard_msgs in #print axioms invisible_is_gauge

/-- info: 'Foam.correct_maintenance_has_no_signature' does not depend on any axioms -/
#guard_msgs in #print axioms correct_maintenance_has_no_signature

/-- info: 'Foam.the_remainder_is_unseen' does not depend on any axioms -/
#guard_msgs in #print axioms the_remainder_is_unseen

/-- info: 'Foam.the_remainder_is_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_remainder_is_real

/-- info: 'Foam.a_wider_seat_reads_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms a_wider_seat_reads_the_remainder

/-- info: 'Foam.dropping_the_remainder_is_platonism' does not depend on any axioms -/
#guard_msgs in #print axioms dropping_the_remainder_is_platonism

/-- info: 'Foam.a_reading_deaf_to_the_remainder_reads_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms a_reading_deaf_to_the_remainder_reads_the_ground

/-- info: 'Foam.the_handshake' does not depend on any axioms -/
#guard_msgs in #print axioms the_handshake

end Foam
