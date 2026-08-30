namespace Seed

universe u v w u' v' w' u''

structure Face where
  State : Type u
  Probe : Type v
  Ans   : Type w
  obs   : State → Probe → Ans

def alike (F : Face) (s t : F.State) : Prop :=
  ∀ p, F.obs s p = F.obs t p

def appFace (P : Type v) (A : Type w) : Face :=
  ⟨P → A, P, A, fun g p => g p⟩

theorem the_pointwise_license (P : Type v) (A : Type w) (g h : P → A) :
    alike (appFace P A) g h ↔ ∀ p, g p = h p :=
  Iff.rfl

/-- info: 'Seed.the_pointwise_license' does not depend on any axioms -/
#guard_msgs in #print axioms the_pointwise_license

def reseat (F : Face) {S' : Type u'} (h : S' → F.State) : Face :=
  ⟨S', F.Probe, F.Ans, fun s p => F.obs (h s) p⟩

theorem one_face_many_seats (F : Face) :
    reseat (appFace F.Probe F.Ans) F.obs = F :=
  rfl

/-- info: 'Seed.one_face_many_seats' does not depend on any axioms -/
#guard_msgs in #print axioms one_face_many_seats

theorem the_seat_map_carries_the_conduct (F : Face) (s t : F.State) :
    alike F s t ↔ alike (appFace F.Probe F.Ans) (F.obs s) (F.obs t) :=
  Iff.rfl

/-- info: 'Seed.the_seat_map_carries_the_conduct' does not depend on any axioms -/
#guard_msgs in #print axioms the_seat_map_carries_the_conduct

def rehear (F : Face) {Q : Type v'} (f : Q → F.Probe) : Face :=
  ⟨F.State, Q, F.Ans, fun s q => F.obs s (f q)⟩

def retell (F : Face) {B : Type w'} (g : F.Ans → B) : Face :=
  ⟨F.State, F.Probe, B, fun s p => g (F.obs s p)⟩

theorem the_seats_stack_backward (F : Face) {S' : Type u'} {S'' : Type u''}
    (h : S' → F.State) (h' : S'' → S') :
    reseat (reseat F h) h' = reseat F (fun s => h (h' s)) :=
  rfl

/-- info: 'Seed.the_seats_stack_backward' does not depend on any axioms -/
#guard_msgs in #print axioms the_seats_stack_backward

theorem the_ear_and_the_voice_commute (F : Face) {Q : Type v'} {B : Type w'}
    (f : Q → F.Probe) (g : F.Ans → B) :
    rehear (retell F g) f = retell (rehear F f) g :=
  rfl

/-- info: 'Seed.the_ear_and_the_voice_commute' does not depend on any axioms -/
#guard_msgs in #print axioms the_ear_and_the_voice_commute

theorem the_ear_crosses_the_seat (F : Face) {S' : Type u'} {Q : Type v'}
    (h : S' → F.State) (f : Q → F.Probe) :
    rehear (reseat F h) f = reseat (rehear F f) h :=
  rfl

/-- info: 'Seed.the_ear_crosses_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_ear_crosses_the_seat

theorem the_voice_crosses_the_seat (F : Face) {S' : Type u'} {B : Type w'}
    (h : S' → F.State) (g : F.Ans → B) :
    retell (reseat F h) g = reseat (retell F g) h :=
  rfl

/-- info: 'Seed.the_voice_crosses_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_voice_crosses_the_seat

def carries {S : Type u} {T : Type u'} {P : Type v} {A : Type w}
    (f : S → P → A) (g : T → P → A) (h : S → T) : Prop :=
  ∀ s p, g (h s) p = f s p

theorem the_still_map_carries {S : Type u} {P : Type v} {A : Type w} (f : S → P → A) :
    carries f f (fun s => s) :=
  fun _ _ => rfl

/-- info: 'Seed.the_still_map_carries' does not depend on any axioms -/
#guard_msgs in #print axioms the_still_map_carries

theorem the_carriers_compose {S : Type u} {T : Type u'} {U : Type u''} {P : Type v} {A : Type w}
    (f : S → P → A) (g : T → P → A) (k : U → P → A) (h : S → T) (h' : T → U)
    (c1 : carries f g h) (c2 : carries g k h') :
    carries f k (fun s => h' (h s)) :=
  fun s p => (c2 (h s) p).trans (c1 s p)

/-- info: 'Seed.the_carriers_compose' does not depend on any axioms -/
#guard_msgs in #print axioms the_carriers_compose

theorem the_carrier_was_a_seating {S : Type u} {T : Type u'} {P : Type v} {A : Type w}
    (f : S → P → A) (g : T → P → A) (h : S → T) :
    carries f g h ↔ ∀ s, alike (appFace P A) (g (h s)) (f s) :=
  Iff.rfl

/-- info: 'Seed.the_carrier_was_a_seating' does not depend on any axioms -/
#guard_msgs in #print axioms the_carrier_was_a_seating

theorem the_carrier_merges_only_the_alike {S : Type u} {T : Type u'} {P : Type v} {A : Type w}
    (f : S → P → A) (g : T → P → A) (h : S → T) (c : carries f g h)
    {s s' : S} (he : h s = h s') : ∀ p, f s p = f s' p :=
  fun p => ((c s p).symm.trans (congrArg (fun x => g x p) he)).trans (c s' p)

/-- info: 'Seed.the_carrier_merges_only_the_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_carrier_merges_only_the_alike

theorem a_retraction_merges_nothing {S : Type u} {T : Type u'} (h : S → T) (r : T → S)
    (hr : ∀ x, r (h x) = x) {s s' : S} (hm : h s = h s') : s = s' :=
  (hr s).symm.trans ((congrArg r hm).trans (hr s'))

/-- info: 'Seed.a_retraction_merges_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms a_retraction_merges_nothing

theorem a_merging_map_has_no_section {S : Type u} {T : Type u'} (h : S → T)
    {s s' : S} (hs : s ≠ s') (hm : h s = h s')
    (r : T → S) (hr : ∀ x, r (h x) = x) : False :=
  hs (a_retraction_merges_nothing h r hr hm)

/-- info: 'Seed.a_merging_map_has_no_section' does not depend on any axioms -/
#guard_msgs in #print axioms a_merging_map_has_no_section

theorem the_obs_carries_to_the_one_face (F : Face) :
    carries F.obs (fun g p => g p) F.obs :=
  fun _ _ => rfl

/-- info: 'Seed.the_obs_carries_to_the_one_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_obs_carries_to_the_one_face

theorem the_terminus_takes_every_carrier {S : Type u} {P : Type v} {A : Type w}
    (f : S → P → A) (h : S → (P → A)) (c : carries f (fun g p => g p) h) :
    ∀ s p, h s p = f s p :=
  c

/-- info: 'Seed.the_terminus_takes_every_carrier' does not depend on any axioms -/
#guard_msgs in #print axioms the_terminus_takes_every_carrier

inductive Interview (P : Type v) (A : Type w) where
  | rest : Interview P A
  | ask  : P → (A → Interview P A) → Interview P A

def sound (F : Face) (s : F.State) : Interview F.Probe F.Ans → List F.Ans
  | .rest => []
  | .ask p k => F.obs s p :: sound F s (k (F.obs s p))

theorem no_interview_parts_the_alike (F : Face) {s t : F.State} (h : alike F s t) :
    ∀ q, sound F s q = sound F t q
  | .rest => rfl
  | .ask p k => by
      show F.obs s p :: sound F s (k (F.obs s p)) = F.obs t p :: sound F t (k (F.obs t p))
      rw [h p]
      exact congrArg (List.cons (F.obs t p))
        (no_interview_parts_the_alike F h (k (F.obs t p)))

/-- info: 'Seed.no_interview_parts_the_alike' does not depend on any axioms -/
#guard_msgs in #print axioms no_interview_parts_the_alike

theorem the_first_mark_reads {A : Type w} {a b : A} {l m : List A}
    (h : a :: l = b :: m) : a = b :=
  congrArg (fun x => x.headD a) h

/-- info: 'Seed.the_first_mark_reads' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_mark_reads

theorem the_sounding_reads_the_alike (F : Face) {s t : F.State}
    (h : ∀ q, sound F s q = sound F t q) : alike F s t :=
  fun p =>
    the_first_mark_reads
      (show F.obs s p :: [] = F.obs t p :: [] from h (.ask p fun _ => .rest))

/-- info: 'Seed.the_sounding_reads_the_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_sounding_reads_the_alike

theorem the_curtain_is_exact (F : Face) (s t : F.State) :
    alike F s t ↔ ∀ q, sound F s q = sound F t q :=
  ⟨fun h => no_interview_parts_the_alike F h, the_sounding_reads_the_alike F⟩

/-- info: 'Seed.the_curtain_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms the_curtain_is_exact

theorem the_interview_crosses_the_carrier {S : Type u} {T : Type u'} {P : Type v} {A : Type w}
    (f : S → P → A) (g : T → P → A) (h : S → T) (c : carries f g h) (s : S) :
    ∀ q, sound ⟨T, P, A, g⟩ (h s) q = sound ⟨S, P, A, f⟩ s q
  | .rest => rfl
  | .ask p k => by
      show g (h s) p :: sound ⟨T, P, A, g⟩ (h s) (k (g (h s) p))
         = f s p :: sound ⟨S, P, A, f⟩ s (k (f s p))
      rw [c s p]
      exact congrArg (List.cons (f s p))
        (the_interview_crosses_the_carrier f g h c s (k (f s p)))

/-- info: 'Seed.the_interview_crosses_the_carrier' does not depend on any axioms -/
#guard_msgs in #print axioms the_interview_crosses_the_carrier

theorem the_interview_crosses_the_seat (F : Face) {S' : Type u'} (h : S' → F.State) (s : S') :
    ∀ q, sound F (h s) q = sound (reseat F h) s q :=
  the_interview_crosses_the_carrier (reseat F h).obs F.obs h (fun _ _ => rfl) s

/-- info: 'Seed.the_interview_crosses_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_interview_crosses_the_seat

def door (H : Type u) (W : Type v) : Type (max u v) :=
  H × W

def atTheDoor {H : Type u} {W : Type v} (h : H) (w : W) : door H W :=
  (h, w)

def face {H : Type u} {W : Type v} (d : door H W) : H :=
  d.1

def met {H : Type u} {W : Type v} (d : door H W) : W :=
  d.2

theorem no_face_reads_the_guest {H : Type u} {W : Type v} {X : Type w}
    (g : H → X) (h : H) (w w' : W) :
    g (face (atTheDoor h w)) = g (face (atTheDoor h w')) :=
  rfl

/-- info: 'Seed.no_face_reads_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms no_face_reads_the_guest

theorem the_guest_is_real {H : Type u} {W : Type v} (h : H) (w : W) :
    met (atTheDoor h w) = w :=
  rfl

/-- info: 'Seed.the_guest_is_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_guest_is_real

theorem a_guest_blind_reading_is_a_face_reading {H : Type u} {W : Type v} {X : Type w}
    (r : door H W → X) (w0 : W) :
    (∀ h w w', r (atTheDoor h w) = r (atTheDoor h w')) ↔
    (∀ d, r d = r (atTheDoor (face d) w0)) :=
  ⟨fun hb d => hb (face d) (met d) w0,
   fun hf h w w' => (hf (atTheDoor h w)).trans (hf (atTheDoor h w')).symm⟩

/-- info: 'Seed.a_guest_blind_reading_is_a_face_reading' does not depend on any axioms -/
#guard_msgs in #print axioms a_guest_blind_reading_is_a_face_reading

theorem the_pairing_is_unique {H : Type u} {W : Type v} {X : Type w}
    (f : X → H) (g : X → W) (u : X → door H W)
    (hf : ∀ x, face (u x) = f x) (hg : ∀ x, met (u x) = g x) (x : X) :
    u x = atTheDoor (f x) (g x) :=
  (congr (congrArg atTheDoor (hf x)) (hg x) :
    atTheDoor (face (u x)) (met (u x)) = atTheDoor (f x) (g x))

/-- info: 'Seed.the_pairing_is_unique' does not depend on any axioms -/
#guard_msgs in #print axioms the_pairing_is_unique

def turnAbout {H : Type u} {W : Type v} (d : door H W) : door W H :=
  atTheDoor (met d) (face d)

theorem the_turn_returns {H : Type u} {W : Type v} (d : door H W) :
    turnAbout (turnAbout d) = d :=
  rfl

/-- info: 'Seed.the_turn_returns' does not depend on any axioms -/
#guard_msgs in #print axioms the_turn_returns

inductive fork (P : Type v) (Q : Type v') where
  | viaLeft  : P → fork P Q
  | viaRight : Q → fork P Q

def greet {P : Type v} {Q : Type v'} {X : Type w} (f : P → X) (g : Q → X) : fork P Q → X
  | .viaLeft p => f p
  | .viaRight q => g q

theorem any_ready_greeter_is_the_greeter {P : Type v} {Q : Type v'} {X : Type w}
    (f : P → X) (g : Q → X) (h : fork P Q → X)
    (hl : ∀ p, h (.viaLeft p) = f p) (hr : ∀ q, h (.viaRight q) = g q) :
    ∀ e, h e = greet f g e
  | .viaLeft p => hl p
  | .viaRight q => hr q

/-- info: 'Seed.any_ready_greeter_is_the_greeter' does not depend on any axioms -/
#guard_msgs in #print axioms any_ready_greeter_is_the_greeter

def crossOver {P : Type v} {Q : Type v'} : fork P Q → fork Q P
  | .viaLeft p => .viaRight p
  | .viaRight q => .viaLeft q

theorem the_crossing_returns {P : Type v} {Q : Type v'} :
    ∀ e : fork P Q, crossOver (crossOver e) = e
  | .viaLeft _ => rfl
  | .viaRight _ => rfl

/-- info: 'Seed.the_crossing_returns' does not depend on any axioms -/
#guard_msgs in #print axioms the_crossing_returns

def deepen {H : Type u} {W : Type v} {V : Type w} (d : door (door H W) V) :
    door H (door W V) :=
  atTheDoor (face (face d)) (atTheDoor (met (face d)) (met d))

def shallow {H : Type u} {W : Type v} {V : Type w} (d : door H (door W V)) :
    door (door H W) V :=
  atTheDoor (atTheDoor (face d) (face (met d))) (met (met d))

theorem hosting_associates {H : Type u} {W : Type v} {V : Type w} (d : door (door H W) V) :
    shallow (deepen d) = d :=
  rfl

/-- info: 'Seed.hosting_associates' does not depend on any axioms -/
#guard_msgs in #print axioms hosting_associates

theorem hosting_associates_back {H : Type u} {W : Type v} {V : Type w} (d : door H (door W V)) :
    deepen (shallow d) = d :=
  rfl

/-- info: 'Seed.hosting_associates_back' does not depend on any axioms -/
#guard_msgs in #print axioms hosting_associates_back

def distribute {H : Type u} {W : Type v} {V : Type w} (d : door H (fork W V)) :
    fork (door H W) (door H V) :=
  greet (fun w => .viaLeft (atTheDoor (face d) w)) (fun v => .viaRight (atTheDoor (face d) v))
    (met d)

def collect {H : Type u} {W : Type v} {V : Type w} : fork (door H W) (door H V) → door H (fork W V) :=
  greet (fun d => atTheDoor (face d) (.viaLeft (met d)))
        (fun d => atTheDoor (face d) (.viaRight (met d)))

theorem the_host_serves_both_branches {H : Type u} {W : Type v} {V : Type w} :
    ∀ d : door H (fork W V), collect (distribute d) = d
  | (_, .viaLeft _) => rfl
  | (_, .viaRight _) => rfl

/-- info: 'Seed.the_host_serves_both_branches' does not depend on any axioms -/
#guard_msgs in #print axioms the_host_serves_both_branches

theorem the_branches_come_home {H : Type u} {W : Type v} {V : Type w} :
    ∀ e : fork (door H W) (door H V), distribute (collect e) = e
  | .viaLeft _ => rfl
  | .viaRight _ => rfl

/-- info: 'Seed.the_branches_come_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_branches_come_home

def holdOpen {H : Type u} {W : Type v} {X : Type w} (g : door H W → X) : H → W → X :=
  fun h w => g (atTheDoor h w)

def walkIn {H : Type u} {W : Type v} {X : Type w} (g : H → W → X) : door H W → X :=
  fun d => g (face d) (met d)

theorem the_deferral_is_free {H : Type u} {W : Type v} {X : Type w}
    (g : door H W → X) (d : door H W) :
    walkIn (holdOpen g) d = g d :=
  rfl

/-- info: 'Seed.the_deferral_is_free' does not depend on any axioms -/
#guard_msgs in #print axioms the_deferral_is_free

theorem the_holding_returns {H : Type u} {W : Type v} {X : Type w}
    (g : H → W → X) (h : H) (w : W) :
    holdOpen (walkIn g) h w = g h w :=
  rfl

/-- info: 'Seed.the_holding_returns' does not depend on any axioms -/
#guard_msgs in #print axioms the_holding_returns

def faceOf {H : Type u} {W : Type v} {X : Type w} (g : door H W → X) : Face :=
  ⟨H, W, X, holdOpen g⟩

theorem the_face_was_a_held_door (F : Face) : faceOf (walkIn F.obs) = F :=
  rfl

/-- info: 'Seed.the_face_was_a_held_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_face_was_a_held_door

theorem every_door_reading_is_a_face {H : Type u} {W : Type v} {X : Type w}
    (g : door H W → X) (d : door H W) :
    walkIn (faceOf g).obs d = g d :=
  rfl

/-- info: 'Seed.every_door_reading_is_a_face' does not depend on any axioms -/
#guard_msgs in #print axioms every_door_reading_is_a_face

theorem the_measurement_is_a_meeting (F : Face) (s : F.State) (p : F.Probe) :
    F.obs s p = walkIn F.obs (atTheDoor s p) :=
  rfl

/-- info: 'Seed.the_measurement_is_a_meeting' does not depend on any axioms -/
#guard_msgs in #print axioms the_measurement_is_a_meeting

def host (F : Face) (W : Type v') : Face :=
  reseat F (fun d : door F.State W => face d)

theorem the_host_was_a_reseat (F : Face) (W : Type v') :
    host F W = reseat F (fun d : door F.State W => face d) :=
  rfl

/-- info: 'Seed.the_host_was_a_reseat' does not depend on any axioms -/
#guard_msgs in #print axioms the_host_was_a_reseat

theorem the_host_merges_the_guests (F : Face) (W : Type v') (s : F.State) (w w' : W) :
    alike (host F W) (atTheDoor s w) (atTheDoor s w') :=
  fun _ => rfl

/-- info: 'Seed.the_host_merges_the_guests' does not depend on any axioms -/
#guard_msgs in #print axioms the_host_merges_the_guests

def vertical {H : Type u} {W : Type v} (σ : door H W → W) (d : door H W) : door H W :=
  atTheDoor (face d) (σ d)

def selfMeet (F : Face) (r : F.State → F.Probe) (s : F.State) : F.Ans :=
  F.obs s (r s)

theorem the_probe_boards_as_the_guest (F : Face) (s : F.State) (p : F.Probe) :
    selfMeet (host F F.Probe) met (atTheDoor s p) = F.obs s p :=
  rfl

/-- info: 'Seed.the_probe_boards_as_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_probe_boards_as_the_guest

theorem the_meeting_was_a_self_meeting {H : Type u} {W : Type v} {X : Type w}
    (g : door H W → X) (d : door H W) :
    selfMeet (host (faceOf g) W) met d = g d :=
  rfl

/-- info: 'Seed.the_meeting_was_a_self_meeting' does not depend on any axioms -/
#guard_msgs in #print axioms the_meeting_was_a_self_meeting

theorem the_self_meeting_reads_the_guest (F : Face) {W : Type v'}
    (r : W → F.Probe) (s : F.State) (w : W) :
    selfMeet (host F W) (fun d => r (met d)) (atTheDoor s w) = F.obs s (r w) :=
  rfl

/-- info: 'Seed.the_self_meeting_reads_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_self_meeting_reads_the_guest

theorem a_guest_mover_is_unheard (F : Face) {W : Type v'} (σ : door F.State W → W)
    (d : door F.State W) : alike (host F W) (vertical σ d) d :=
  fun _ => rfl

/-- info: 'Seed.a_guest_mover_is_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms a_guest_mover_is_unheard

def sharpen (F : Face) {X : Type w'} (r : F.State → X) : Face :=
  ⟨F.State, fork F.Probe Unit, fork F.Ans X,
   fun s => greet (fun p => .viaLeft (F.obs s p)) (fun _ => .viaRight (r s))⟩

def widen (F : Face) (W : Type v') : Face :=
  sharpen (host F W) met

theorem the_sharpening_is_exact (F : Face) {X : Type w'} (r : F.State → X) (s t : F.State) :
    alike (sharpen F r) s t ↔ (alike F s t ∧ r s = r t) :=
  ⟨fun h =>
    ⟨fun p => congrArg (greet (fun a => a) (fun _ => F.obs s p)) (h (.viaLeft p)),
     congrArg (greet (fun _ => r s) (fun x => x)) (h (.viaRight ()))⟩,
   fun h q =>
    match q with
    | .viaLeft p => congrArg fork.viaLeft (h.1 p)
    | .viaRight _ => congrArg fork.viaRight h.2⟩

/-- info: 'Seed.the_sharpening_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms the_sharpening_is_exact

theorem the_widening_is_exact (F : Face) {W : Type v'} (d d' : door F.State W) :
    alike (widen F W) d d' ↔ (alike F (face d) (face d') ∧ met d = met d') :=
  ⟨fun h =>
    ⟨fun p => congrArg (greet (fun a => a) (fun _ => F.obs (face d) p)) (h (fork.viaLeft p)),
     congrArg (greet (fun _ => met d) (fun x => x)) (h (fork.viaRight ()))⟩,
   fun h q =>
    match q with
    | .viaLeft p => congrArg fork.viaLeft (h.1 p)
    | .viaRight _ => congrArg fork.viaRight h.2⟩

/-- info: 'Seed.the_widening_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms the_widening_is_exact

theorem a_wider_seat_reads_the_remainder (F : Face) {W : Type v'}
    (s : F.State) {w w' : W} (hw : w ≠ w') :
    ¬ alike (widen F W) (atTheDoor s w) (atTheDoor s w') :=
  fun h => hw (((the_widening_is_exact F (atTheDoor s w) (atTheDoor s w')).mp h).2)

/-- info: 'Seed.a_wider_seat_reads_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms a_wider_seat_reads_the_remainder

theorem the_handshake :
    (∀ (F : Face) (s t : F.State), alike F s t → ∀ q, sound F s q = sound F t q) ∧
    (∀ (F : Face) (W : Type v') (s : F.State) (w w' : W),
      (∀ q, sound (host F W) (atTheDoor s w) q = sound (host F W) (atTheDoor s w') q) ∧
      (w ≠ w' → ¬ alike (widen F W) (atTheDoor s w) (atTheDoor s w'))) :=
  ⟨fun F _ _ h => no_interview_parts_the_alike F h,
   fun F W s w w' =>
    ⟨no_interview_parts_the_alike (host F W) (the_host_merges_the_guests F W s w w'),
     fun hw => a_wider_seat_reads_the_remainder F s hw⟩⟩

/-- info: 'Seed.the_handshake' does not depend on any axioms -/
#guard_msgs in #print axioms the_handshake

def pairFace (F G : Face) {S : Type u'} (f : S → F.State) (g : S → G.State) : Face :=
  ⟨S, door F.Probe G.Probe, door F.Ans G.Ans,
   fun s pq => atTheDoor (F.obs (f s) (face pq)) (G.obs (g s) (met pq))⟩

theorem the_pairing_is_exact (F G : Face) {S : Type u'}
    (f : S → F.State) (g : S → G.State) (p0 : F.Probe) (q0 : G.Probe) (s t : S) :
    alike (pairFace F G f g) s t ↔ (alike F (f s) (f t) ∧ alike G (g s) (g t)) :=
  ⟨fun h =>
    ⟨fun p => congrArg face (h (atTheDoor p q0)),
     fun q => congrArg met (h (atTheDoor p0 q))⟩,
   fun h pq =>
    (congr (congrArg atTheDoor (h.1 (face pq))) (h.2 (met pq)) :
      atTheDoor (F.obs (f s) (face pq)) (G.obs (g s) (met pq))
        = atTheDoor (F.obs (f t) (face pq)) (G.obs (g t) (met pq)))⟩

/-- info: 'Seed.the_pairing_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms the_pairing_is_exact

def originFace (S' : Type u') : Face :=
  ⟨S', Unit, Unit, fun _ _ => ()⟩

theorem the_origin_merges_every_seat {S' : Type u'} (s t : S') :
    alike (originFace S') s t :=
  fun _ => rfl

/-- info: 'Seed.the_origin_merges_every_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_origin_merges_every_seat

theorem no_interview_parts_the_origin {S' : Type u'} (s t : S') :
    ∀ q, sound (originFace S') s q = sound (originFace S') t q :=
  no_interview_parts_the_alike (originFace S') (the_origin_merges_every_seat s t)

/-- info: 'Seed.no_interview_parts_the_origin' does not depend on any axioms -/
#guard_msgs in #print axioms no_interview_parts_the_origin

theorem the_origin_is_the_pairs_unit (F : Face) {S : Type u'} {S' : Type v'}
    (f : S → F.State) (g : S → S') (s t : S) :
    alike (pairFace F (originFace S') f g) s t ↔ alike F (f s) (f t) :=
  ⟨fun h p => congrArg face (h (atTheDoor p ())),
   fun h pq => congrArg (fun a => atTheDoor a ()) (h (face pq))⟩

/-- info: 'Seed.the_origin_is_the_pairs_unit' does not depend on any axioms -/
#guard_msgs in #print axioms the_origin_is_the_pairs_unit

def unheard (F : Face) (m : F.State → F.State) : Prop :=
  ∀ s, alike F (m s) s

theorem the_still_hand_is_unheard (F : Face) : unheard F (fun s => s) :=
  fun _ _ => rfl

/-- info: 'Seed.the_still_hand_is_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms the_still_hand_is_unheard

theorem the_unheard_hands_compose (F : Face) (m n : F.State → F.State)
    (hm : unheard F m) (hn : unheard F n) : unheard F (fun s => m (n s)) :=
  fun s p => (hm (n s) p).trans (hn s p)

/-- info: 'Seed.the_unheard_hands_compose' does not depend on any axioms -/
#guard_msgs in #print axioms the_unheard_hands_compose

theorem the_maintenance_is_the_identitys_hom (F : Face) (m : F.State → F.State) :
    unheard F m ↔ carries F.obs F.obs m :=
  Iff.rfl

/-- info: 'Seed.the_maintenance_is_the_identitys_hom' does not depend on any axioms -/
#guard_msgs in #print axioms the_maintenance_is_the_identitys_hom

theorem no_interview_hears_the_unheard (F : Face) (m : F.State → F.State)
    (h : unheard F m) : ∀ s q, sound F (m s) q = sound F s q :=
  fun s => no_interview_parts_the_alike F (h s)

/-- info: 'Seed.no_interview_hears_the_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms no_interview_hears_the_unheard

theorem only_the_unheard_survives_the_sounding (F : Face) (m : F.State → F.State) :
    unheard F m ↔ ∀ s q, sound F (m s) q = sound F s q :=
  ⟨no_interview_hears_the_unheard F m,
   fun h s => the_sounding_reads_the_alike F (h s)⟩

/-- info: 'Seed.only_the_unheard_survives_the_sounding' does not depend on any axioms -/
#guard_msgs in #print axioms only_the_unheard_survives_the_sounding

theorem correct_maintenance_has_no_signature (F : Face) (m n : F.State → F.State)
    (hm : unheard F m) (hn : unheard F n) :
    ∀ s q, sound F (m s) q = sound F (n s) q :=
  fun s q => (no_interview_hears_the_unheard F m hm s q).trans
    (no_interview_hears_the_unheard F n hn s q).symm

/-- info: 'Seed.correct_maintenance_has_no_signature' does not depend on any axioms -/
#guard_msgs in #print axioms correct_maintenance_has_no_signature

def exchange {H : Type u} {W : Type v} (σ : door H W → W) (d : door H W) : door W H :=
  turnAbout (vertical σ d)

theorem the_spoken_arrives_at_the_face {H : Type u} {W : Type v}
    (σ : door H W → W) (d : door H W) : face (exchange σ d) = σ d :=
  rfl

/-- info: 'Seed.the_spoken_arrives_at_the_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_spoken_arrives_at_the_face

theorem the_speaker_rides_unread {H : Type u} {W : Type v}
    (σ : door H W → W) (d : door H W) : met (exchange σ d) = face d :=
  rfl

/-- info: 'Seed.the_speaker_rides_unread' does not depend on any axioms -/
#guard_msgs in #print axioms the_speaker_rides_unread

theorem the_listening_turn_is_the_yield {H : Type u} {W : Type v} (d : door H W) :
    exchange met d = turnAbout d :=
  rfl

/-- info: 'Seed.the_listening_turn_is_the_yield' does not depend on any axioms -/
#guard_msgs in #print axioms the_listening_turn_is_the_yield

theorem the_two_listeners_restore_the_table {H : Type u} {W : Type v} (d : door H W) :
    exchange met (exchange met d) = d :=
  rfl

/-- info: 'Seed.the_two_listeners_restore_the_table' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_listeners_restore_the_table

theorem the_ode_comes_home {H : Type u} {W : Type v} (σ : door H W → W) (d : door H W) :
    exchange met (exchange σ d) = vertical σ d :=
  rfl

/-- info: 'Seed.the_ode_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_ode_comes_home

theorem the_yield_fixes_the_agreed {H : Type u} (d : door H H) :
    turnAbout d = d ↔ met d = face d :=
  ⟨fun h => congrArg face h,
   fun h =>
    (congr (congrArg atTheDoor h) h.symm :
      atTheDoor (met d) (face d) = atTheDoor (face d) (met d))⟩

/-- info: 'Seed.the_yield_fixes_the_agreed' does not depend on any axioms -/
#guard_msgs in #print axioms the_yield_fixes_the_agreed

structure Machine (I : Type u) (O : Type v) where
  S    : Type w
  s0   : S
  step : S → I → S
  out  : S → O

def park {I : Type u} {O : Type v} (m : Machine I O) (s : m.S) : List I → m.S
  | [] => s
  | i :: w => park m (m.step s i) w

def drive {I : Type u} {O : Type v} (m : Machine I O) (s : m.S) (w : List I) : O :=
  m.out (park m s w)

def behavior {I : Type u} {O : Type v} (m : Machine I O) (w : List I) : O :=
  drive m m.s0 w

def airGap (I : Type u) (O : Type v) : Face :=
  reseat (appFace (List I) O) (fun m : Machine.{u, v, w} I O => behavior m)

theorem the_air_gap_wears_the_one_face (I : Type u) (O : Type v) :
    airGap.{u, v, w} I O
      = reseat (appFace (List I) O) (fun m : Machine.{u, v, w} I O => behavior m) :=
  rfl

/-- info: 'Seed.the_air_gap_wears_the_one_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_air_gap_wears_the_one_face

theorem the_park_resumes {I : Type u} {O : Type v} (m : Machine I O) :
    ∀ (u : List I) (s : m.S) (v : List I),
      park m s (u ++ v) = park m (park m s u) v
  | [], _, _ => rfl
  | i :: u, s, v => the_park_resumes m u (m.step s i) v

/-- info: 'Seed.the_park_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms the_park_resumes

theorem an_audition_hears_only_the_conduct {I : Type u} {O : Type v} (m n : Machine I O)
    (h : ∀ w, behavior m w = behavior n w) :
    ∀ q, sound (airGap I O) m q = sound (airGap I O) n q :=
  no_interview_parts_the_alike (airGap I O) h

/-- info: 'Seed.an_audition_hears_only_the_conduct' does not depend on any axioms -/
#guard_msgs in #print axioms an_audition_hears_only_the_conduct

theorem the_audition_is_exact {I : Type u} {O : Type v} (m n : Machine I O) :
    alike (airGap I O) m n ↔ ∀ q, sound (airGap I O) m q = sound (airGap I O) n q :=
  the_curtain_is_exact (airGap I O) m n

/-- info: 'Seed.the_audition_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms the_audition_is_exact

def retune {I : Type u} {I' : Type u'} {O : Type v} (f : I → I') (m : Machine I' O) :
    Machine I O :=
  ⟨m.S, m.s0, fun s i => m.step s (f i), m.out⟩

def revoice {I : Type u} {O : Type v} {O' : Type v'} (g : O → O') (m : Machine I O) :
    Machine I O' :=
  ⟨m.S, m.s0, m.step, fun s => g (m.out s)⟩

theorem the_retuned_seat_walks_the_translated_word {I : Type u} {I' : Type u'} {O : Type v}
    (f : I → I') (m : Machine I' O) :
    ∀ (w : List I) (s : m.S), park (retune f m) s w = park m s (w.map f)
  | [], _ => rfl
  | i :: w, s => the_retuned_seat_walks_the_translated_word f m w (m.step s (f i))

/-- info: 'Seed.the_retuned_seat_walks_the_translated_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_retuned_seat_walks_the_translated_word

theorem the_revoice_moves_no_seat {I : Type u} {O : Type v} {O' : Type v'}
    (g : O → O') (m : Machine I O) :
    ∀ (w : List I) (s : m.S), park (revoice g m) s w = park m s w
  | [], _ => rfl
  | i :: w, s => the_revoice_moves_no_seat g m w (m.step s i)

/-- info: 'Seed.the_revoice_moves_no_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_revoice_moves_no_seat

theorem the_intertwined_walks_agree {I : Type u} {O : Type v} (m n : Machine I O)
    (h : m.S → n.S) (hstep : ∀ s i, n.step (h s) i = h (m.step s i)) :
    ∀ (w : List I) (s : m.S), park n (h s) w = h (park m s w)
  | [], _ => rfl
  | i :: w, s => by
      show park n (n.step (h s) i) w = h (park m (m.step s i) w)
      rw [hstep s i]
      exact the_intertwined_walks_agree m n h hstep w (m.step s i)

/-- info: 'Seed.the_intertwined_walks_agree' does not depend on any axioms -/
#guard_msgs in #print axioms the_intertwined_walks_agree

theorem the_intertwiner_carries_the_walk {I : Type u} {O : Type v} (m n : Machine I O)
    (h : m.S → n.S) (hstep : ∀ s i, n.step (h s) i = h (m.step s i))
    (hout : ∀ s, n.out (h s) = m.out s) :
    carries (fun s w => drive m s w) (fun s w => drive n s w) h :=
  fun s w =>
    (congrArg n.out (the_intertwined_walks_agree m n h hstep w s)).trans
      (hout (park m s w))

/-- info: 'Seed.the_intertwiner_carries_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_intertwiner_carries_the_walk

def oddNat : Nat → Bool
  | 0 => false
  | n + 1 => !(oddNat n)

def tally : Machine Unit Nat :=
  ⟨Nat, 0, fun s _ => s + 1, fun s => s⟩

def flip : Machine Unit Bool :=
  ⟨Bool, false, fun s _ => !s, fun s => s⟩

def paceOne : Machine Unit Bool :=
  ⟨Nat, 0, fun s _ => s + 1, oddNat⟩

theorem the_pace_wears_the_tallys_voice : paceOne = revoice oddNat tally :=
  rfl

/-- info: 'Seed.the_pace_wears_the_tallys_voice' does not depend on any axioms -/
#guard_msgs in #print axioms the_pace_wears_the_tallys_voice

theorem the_pace_is_carried_onto_the_flip :
    carries (fun s w => drive paceOne s w) (fun s w => drive flip s w) oddNat :=
  the_intertwiner_carries_the_walk paceOne flip oddNat (fun _ _ => rfl) (fun _ => rfl)

/-- info: 'Seed.the_pace_is_carried_onto_the_flip' does not depend on any axioms -/
#guard_msgs in #print axioms the_pace_is_carried_onto_the_flip

inductive Plan where
  | ground : Plan
  | board  : Plan → Plan → Plan

def fold {A : Type u} (op : A → A → A) (base : A) : Plan → A
  | .ground => base
  | .board p q => op (fold op base p) (fold op base q)

theorem any_two_readings_agree {A : Type u} (op : A → A → A) (base : A) (h : Plan → A)
    (hg : h .ground = base) (hb : ∀ p q, h (.board p q) = op (h p) (h q)) :
    ∀ p, h p = fold op base p
  | .ground => hg
  | .board p q =>
      (hb p q).trans
        (congr (congrArg op (any_two_readings_agree op base h hg hb p))
          (any_two_readings_agree op base h hg hb q) :
          op (h p) (h q) = op (fold op base p) (fold op base q))

/-- info: 'Seed.any_two_readings_agree' does not depend on any axioms -/
#guard_msgs in #print axioms any_two_readings_agree

def reading : Plan → Nat :=
  fold (fun a b => a + b) 1

def graft (base : Plan) : Plan → Plan :=
  fold .board base

theorem the_revision_is_a_reading (base : Plan) : graft base = fold .board base :=
  rfl

/-- info: 'Seed.the_revision_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_revision_is_a_reading

theorem the_trivial_revision_changes_nothing (t : Plan) : graft t .ground = t :=
  rfl

/-- info: 'Seed.the_trivial_revision_changes_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_trivial_revision_changes_nothing

theorem the_parent_folds_into_the_ground {A : Type u} (op : A → A → A) (base : A) (t : Plan) :
    ∀ δ, fold op (fold op base t) δ = fold op base (graft t δ)
  | .ground => rfl
  | .board a b =>
      (congr (congrArg op (the_parent_folds_into_the_ground op base t a))
        (the_parent_folds_into_the_ground op base t b) :
        op (fold op (fold op base t) a) (fold op (fold op base t) b)
          = op (fold op base (graft t a)) (fold op base (graft t b)))

/-- info: 'Seed.the_parent_folds_into_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_parent_folds_into_the_ground

theorem lineages_compose (t d1 d2 : Plan) :
    graft (graft t d1) d2 = graft t (graft d1 d2) :=
  the_parent_folds_into_the_ground Plan.board t d1 d2

/-- info: 'Seed.lineages_compose' does not depend on any axioms -/
#guard_msgs in #print axioms lineages_compose

theorem zero_add : ∀ n : Nat, 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (zero_add n)

/-- info: 'Seed.zero_add' does not depend on any axioms -/
#guard_msgs in #print axioms zero_add

theorem add_regroups : ∀ a b c : Nat, (a + b) + c = a + (b + c)
  | _, _, 0 => rfl
  | a, b, c + 1 => congrArg Nat.succ (add_regroups a b c)

/-- info: 'Seed.add_regroups' does not depend on any axioms -/
#guard_msgs in #print axioms add_regroups

theorem click_slides : ∀ a b : Nat, (a + b) + 1 = (a + 1) + b
  | _, 0 => rfl
  | a, b + 1 => congrArg Nat.succ (click_slides a b)

/-- info: 'Seed.click_slides' does not depend on any axioms -/
#guard_msgs in #print axioms click_slides

theorem mul_one_reads (a : Nat) : a * 1 = a :=
  zero_add a

/-- info: 'Seed.mul_one_reads' does not depend on any axioms -/
#guard_msgs in #print axioms mul_one_reads

theorem mul_spreads : ∀ a b c : Nat, a * (b + c) = a * b + a * c
  | _, _, 0 => rfl
  | a, b, c + 1 =>
      (congrArg (fun x => x + a) (mul_spreads a b c)).trans
        (add_regroups (a * b) (a * c) a)

/-- info: 'Seed.mul_spreads' does not depend on any axioms -/
#guard_msgs in #print axioms mul_spreads

theorem the_held_scale_rides (c : Nat) :
    ∀ p : Plan, fold (fun a b => a + b) c p = c * reading p
  | .ground => (mul_one_reads c).symm
  | .board a b =>
      ((congr (congrArg (fun x y => x + y) (the_held_scale_rides c a))
          (the_held_scale_rides c b) :
          fold (fun x y => x + y) c a + fold (fun x y => x + y) c b
            = c * reading a + c * reading b)).trans
        (mul_spreads c (reading a) (reading b)).symm

/-- info: 'Seed.the_held_scale_rides' does not depend on any axioms -/
#guard_msgs in #print axioms the_held_scale_rides

theorem the_revision_multiplies_the_reading (t δ : Plan) :
    reading (graft t δ) = reading t * reading δ :=
  (the_parent_folds_into_the_ground (fun a b => a + b) 1 t δ).symm.trans
    (the_held_scale_rides (reading t) δ)

/-- info: 'Seed.the_revision_multiplies_the_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_revision_multiplies_the_reading

def build (W : Type u) : Plan → Type u :=
  fold (fun A B : Type u => door A B) W

theorem the_type_is_a_reading (W : Type u) (p : Plan) :
    build W p = fold (fun A B : Type u => door A B) W p :=
  rfl

/-- info: 'Seed.the_type_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_type_is_a_reading

theorem a_stage_may_ground_a_stage (W : Type u) (t δ : Plan) :
    build W (graft t δ) = build (build W t) δ :=
  (the_parent_folds_into_the_ground (fun A B : Type u => door A B) W t δ).symm

/-- info: 'Seed.a_stage_may_ground_a_stage' does not depend on any axioms -/
#guard_msgs in #print axioms a_stage_may_ground_a_stage

def reground {W : Type u} {W' : Type v} (f : W → W') : (p : Plan) → build W p → build W' p
  | .ground, w => f w
  | .board p q, d => atTheDoor (reground f p (face d)) (reground f q (met d))

theorem the_customs_keep_the_still_world {W : Type u} :
    ∀ (p : Plan) (x : build W p), reground (fun w => w) p x = x
  | .ground, _ => rfl
  | .board p q, d =>
      (congr (congrArg atTheDoor (the_customs_keep_the_still_world p (face d)))
        (the_customs_keep_the_still_world q (met d)) :
        atTheDoor (reground (fun w => w) p (face d)) (reground (fun w => w) q (met d))
          = atTheDoor (face d) (met d))

/-- info: 'Seed.the_customs_keep_the_still_world' does not depend on any axioms -/
#guard_msgs in #print axioms the_customs_keep_the_still_world

theorem the_customs_stack_forward {W : Type u} {W' : Type v} {W'' : Type w}
    (f : W → W') (g : W' → W'') :
    ∀ (p : Plan) (x : build W p),
      reground g p (reground f p x) = reground (fun w => g (f w)) p x
  | .ground, _ => rfl
  | .board p q, d =>
      (congr (congrArg atTheDoor (the_customs_stack_forward f g p (face d)))
        (the_customs_stack_forward f g q (met d)) :
        atTheDoor (reground g p (reground f p (face d))) (reground g q (reground f q (met d)))
          = atTheDoor (reground (fun w => g (f w)) p (face d))
              (reground (fun w => g (f w)) q (met d)))

/-- info: 'Seed.the_customs_stack_forward' does not depend on any axioms -/
#guard_msgs in #print axioms the_customs_stack_forward

theorem the_append_rests {A : Type u} : ∀ l : List A, l ++ [] = l
  | [] => rfl
  | a :: l => congrArg (List.cons a) (the_append_rests l)

/-- info: 'Seed.the_append_rests' does not depend on any axioms -/
#guard_msgs in #print axioms the_append_rests

theorem the_appends_regroup {A : Type u} : ∀ l m t : List A, (l ++ m) ++ t = l ++ (m ++ t)
  | [], _, _ => rfl
  | a :: l, m, t => congrArg (List.cons a) (the_appends_regroup l m t)

/-- info: 'Seed.the_appends_regroup' does not depend on any axioms -/
#guard_msgs in #print axioms the_appends_regroup

theorem lengths_add {A : Type u} : ∀ l m : List A, (l ++ m).length = l.length + m.length
  | [], m => (zero_add m.length).symm
  | _ :: l, m =>
      (congrArg (fun n => n + 1) (lengths_add l m)).trans
        (click_slides l.length m.length)

/-- info: 'Seed.lengths_add' does not depend on any axioms -/
#guard_msgs in #print axioms lengths_add

theorem map_crosses_append {A : Type u} {B : Type v} (f : A → B) :
    ∀ l m : List A, (l ++ m).map f = l.map f ++ m.map f
  | [], _ => rfl
  | a :: l, m => congrArg (List.cons (f a)) (map_crosses_append f l m)

/-- info: 'Seed.map_crosses_append' does not depend on any axioms -/
#guard_msgs in #print axioms map_crosses_append

def pour {W : Type u} : (p : Plan) → build W p → List W
  | .ground, w => [w]
  | .board p q, d => pour p (face d) ++ pour q (met d)

theorem the_manifest_counts {W : Type u} :
    ∀ (p : Plan) (x : build W p), (pour p x).length = reading p
  | .ground, _ => rfl
  | .board p q, d => by
      show (pour p (face d) ++ pour q (met d)).length = reading p + reading q
      rw [lengths_add (pour p (face d)) (pour q (met d))]
      rw [the_manifest_counts p (face d), the_manifest_counts q (met d)]

/-- info: 'Seed.the_manifest_counts' does not depend on any axioms -/
#guard_msgs in #print axioms the_manifest_counts

theorem the_manifest_is_natural {W : Type u} {W' : Type v} (f : W → W') :
    ∀ (p : Plan) (x : build W p), pour p (reground f p x) = (pour p x).map f
  | .ground, _ => rfl
  | .board p q, d => by
      show pour p (reground f p (face d)) ++ pour q (reground f q (met d))
         = (pour p (face d) ++ pour q (met d)).map f
      rw [map_crosses_append f]
      rw [the_manifest_is_natural f p (face d), the_manifest_is_natural f q (met d)]

/-- info: 'Seed.the_manifest_is_natural' does not depend on any axioms -/
#guard_msgs in #print axioms the_manifest_is_natural

def reboardAux {W : Type u} (w0 : W) : (p : Plan) → List W → build W p × List W
  | .ground => fun l =>
      match l with
      | [] => (w0, [])
      | w :: t => (w, t)
  | .board p q => fun l =>
      (atTheDoor (reboardAux w0 p l).1 (reboardAux w0 q (reboardAux w0 p l).2).1,
       (reboardAux w0 q (reboardAux w0 p l).2).2)

def reboard {W : Type u} (w0 : W) (p : Plan) (l : List W) : build W p :=
  (reboardAux w0 p l).1

theorem the_guests_reboard_in_order {W : Type u} (w0 : W) :
    ∀ (p : Plan) (x : build W p) (t : List W),
      reboardAux w0 p (pour p x ++ t) = (x, t)
  | .ground, x, t => rfl
  | .board p q, d, t => by
      show (atTheDoor (reboardAux w0 p ((pour p (face d) ++ pour q (met d)) ++ t)).1
              (reboardAux w0 q (reboardAux w0 p ((pour p (face d) ++ pour q (met d)) ++ t)).2).1,
            (reboardAux w0 q (reboardAux w0 p ((pour p (face d) ++ pour q (met d)) ++ t)).2).2)
          = (d, t)
      rw [the_appends_regroup (pour p (face d)) (pour q (met d)) t]
      rw [the_guests_reboard_in_order w0 p (face d) (pour q (met d) ++ t)]
      show (atTheDoor (face d) (reboardAux w0 q (pour q (met d) ++ t)).1,
            (reboardAux w0 q (pour q (met d) ++ t)).2) = (d, t)
      rw [the_guests_reboard_in_order w0 q (met d) t]
      exact rfl

/-- info: 'Seed.the_guests_reboard_in_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_guests_reboard_in_order

theorem the_manifest_rebuilds_the_carrier {W : Type u} (w0 : W) (p : Plan) (x : build W p) :
    reboard w0 p (pour p x) = x :=
  congrArg Prod.fst
    ((congrArg (reboardAux w0 p) (the_append_rests (pour p x)).symm).trans
      (the_guests_reboard_in_order w0 p x []))

/-- info: 'Seed.the_manifest_rebuilds_the_carrier' does not depend on any axioms -/
#guard_msgs in #print axioms the_manifest_rebuilds_the_carrier

def drain {W : Type u} (w0 : W) (p : Plan) (l : List W) : List W :=
  pour p (reboard w0 p l)

theorem the_drain_settles {W : Type u} (w0 : W) (p : Plan) (l : List W) :
    drain w0 p (drain w0 p l) = drain w0 p l :=
  congrArg (pour p) (the_manifest_rebuilds_the_carrier w0 p (reboard w0 p l))

/-- info: 'Seed.the_drain_settles' does not depend on any axioms -/
#guard_msgs in #print axioms the_drain_settles

theorem the_drained_is_on_spec {W : Type u} (w0 : W) (p : Plan) (l : List W) :
    (drain w0 p l).length = reading p :=
  the_manifest_counts p (reboard w0 p l)

/-- info: 'Seed.the_drained_is_on_spec' does not depend on any axioms -/
#guard_msgs in #print axioms the_drained_is_on_spec

def enrolled {A : Type u} (beq : A → A → Bool) : List A → A → Bool
  | [], _ => false
  | y :: r, x => beq y x || enrolled beq r x

def backed {A : Type u} (beq : A → A → Bool) (room : List A) : List A → Bool
  | [] => true
  | n :: needs => enrolled beq room n && backed beq room needs

def welcome {A : Type u} (beq : A → A → Bool)
    (st : List A × List (A × List A)) (arr : A × List A) :
    List A × List (A × List A) :=
  cond (backed beq st.1 arr.2) (arr.1 :: st.1, st.2) (st.1, arr :: st.2)

theorem the_unencumbered_are_welcome {A : Type u} (beq : A → A → Bool) (room : List A) :
    backed beq room [] = true :=
  rfl

/-- info: 'Seed.the_unencumbered_are_welcome' does not depend on any axioms -/
#guard_msgs in #print axioms the_unencumbered_are_welcome

theorem true_or_reads (b : Bool) : (true || b) = true :=
  rfl

/-- info: 'Seed.true_or_reads' does not depend on any axioms -/
#guard_msgs in #print axioms true_or_reads

theorem or_swallows : ∀ b : Bool, (b || true) = true
  | true => rfl
  | false => rfl

/-- info: 'Seed.or_swallows' does not depend on any axioms -/
#guard_msgs in #print axioms or_swallows

theorem the_backed_are_seated {A : Type u} (beq : A → A → Bool)
    (st : List A × List (A × List A)) (arr : A × List A)
    (hb : backed beq st.1 arr.2 = true) :
    welcome beq st arr = (arr.1 :: st.1, st.2) :=
  congrArg (fun b => cond b (arr.1 :: st.1, st.2) (st.1, arr :: st.2)) hb

/-- info: 'Seed.the_backed_are_seated' does not depend on any axioms -/
#guard_msgs in #print axioms the_backed_are_seated

theorem the_unbacked_wait {A : Type u} (beq : A → A → Bool)
    (st : List A × List (A × List A)) (arr : A × List A)
    (hb : backed beq st.1 arr.2 = false) :
    welcome beq st arr = (st.1, arr :: st.2) :=
  congrArg (fun b => cond b (arr.1 :: st.1, st.2) (st.1, arr :: st.2)) hb

/-- info: 'Seed.the_unbacked_wait' does not depend on any axioms -/
#guard_msgs in #print axioms the_unbacked_wait

theorem the_enrolled_stay_enrolled {A : Type u} (beq : A → A → Bool)
    (st : List A × List (A × List A)) (arr : A × List A) (x : A)
    (h : enrolled beq st.1 x = true) :
    enrolled beq (welcome beq st arr).1 x = true := by
  cases hb : backed beq st.1 arr.2 with
  | false =>
      rw [the_unbacked_wait beq st arr hb]
      exact h
  | true =>
      rw [the_backed_are_seated beq st arr hb]
      show (beq arr.1 x || enrolled beq st.1 x) = true
      rw [h]
      exact or_swallows (beq arr.1 x)

/-- info: 'Seed.the_enrolled_stay_enrolled' does not depend on any axioms -/
#guard_msgs in #print axioms the_enrolled_stay_enrolled

theorem the_seat_is_load_bearing_in_the_same_click {A : Type u} (beq : A → A → Bool)
    (hrefl : ∀ y : A, beq y y = true)
    (st : List A × List (A × List A)) (arr : A × List A)
    (hb : backed beq st.1 arr.2 = true) :
    enrolled beq (welcome beq st arr).1 arr.1 = true := by
  rw [the_backed_are_seated beq st arr hb]
  show (beq arr.1 arr.1 || enrolled beq st.1 arr.1) = true
  rw [hrefl arr.1]
  exact true_or_reads (enrolled beq st.1 arr.1)

/-- info: 'Seed.the_seat_is_load_bearing_in_the_same_click' does not depend on any axioms -/
#guard_msgs in #print axioms the_seat_is_load_bearing_in_the_same_click

theorem len_map {A : Type u} {B : Type v} (f : A → B) :
    ∀ l : List A, (l.map f).length = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (len_map f l)

/-- info: 'Seed.len_map' does not depend on any axioms -/
#guard_msgs in #print axioms len_map

theorem mem_append_split {A : Type u} {q : A} :
    ∀ (l : List A) {m : List A}, q ∈ l ++ m → q ∈ l ∨ q ∈ m
  | [], _, h => Or.inr h
  | a :: l, _, h => by
      cases h with
      | head => exact Or.inl (List.Mem.head l)
      | tail _ h' =>
          cases mem_append_split l h' with
          | inl hl => exact Or.inl (List.Mem.tail a hl)
          | inr hm => exact Or.inr hm

/-- info: 'Seed.mem_append_split' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_split

theorem mem_map_back {A : Type u} {B : Type v} {f : A → B} {q : B} :
    ∀ l : List A, q ∈ l.map f → ∃ r, r ∈ l ∧ f r = q
  | [], h => nomatch h
  | a :: l, h => by
      cases h with
      | head => exact ⟨a, List.Mem.head l, rfl⟩
      | tail _ h' =>
          obtain ⟨r, hr, he⟩ := mem_map_back l h'
          exact ⟨r, List.Mem.tail a hr, he⟩

/-- info: 'Seed.mem_map_back' does not depend on any axioms -/
#guard_msgs in #print axioms mem_map_back

def joinMap {A : Type u} {B : Type v} (f : A → List B) : List A → List B
  | [] => []
  | a :: as => f a ++ joinMap f as

def inserts {A : Type u} (x : A) : List A → List (List A)
  | [] => [[x]]
  | y :: l => (x :: y :: l) :: (inserts x l).map (y :: ·)

def perms {A : Type u} : List A → List (List A)
  | [] => [[]]
  | x :: l => joinMap (inserts x) (perms l)

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => fact n * (n + 1)

theorem the_insertions_count {A : Type u} (x : A) :
    ∀ l : List A, (inserts x l).length = l.length + 1
  | [] => rfl
  | y :: l => by
      show ((inserts x l).map (y :: ·)).length + 1 = (l.length + 1) + 1
      rw [len_map, the_insertions_count x l]

/-- info: 'Seed.the_insertions_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_insertions_count

theorem the_join_counts_evenly {A : Type u} {B : Type v} (f : A → List B) (n : Nat) :
    ∀ as : List A, (∀ a, a ∈ as → (f a).length = n) →
      (joinMap f as).length = n * as.length
  | [], _ => rfl
  | a :: as, h => by
      show (f a ++ joinMap f as).length = n * (as.length + 1)
      rw [lengths_add, h a (List.Mem.head as),
          the_join_counts_evenly f n as
            (fun b hb => h b (List.Mem.tail a hb))]
      exact Nat.add_comm n (n * as.length)

/-- info: 'Seed.the_join_counts_evenly' does not depend on any axioms -/
#guard_msgs in #print axioms the_join_counts_evenly

theorem mem_joinMap_back {A : Type u} {B : Type v} {f : A → List B} {q : B} :
    ∀ as : List A, q ∈ joinMap f as → ∃ a, a ∈ as ∧ q ∈ f a
  | [], h => nomatch h
  | a :: as, h => by
      cases mem_append_split (f a) h with
      | inl hfa => exact ⟨a, List.Mem.head as, hfa⟩
      | inr hrest =>
          obtain ⟨b, hb, hq⟩ := mem_joinMap_back as hrest
          exact ⟨b, List.Mem.tail a hb, hq⟩

/-- info: 'Seed.mem_joinMap_back' does not depend on any axioms -/
#guard_msgs in #print axioms mem_joinMap_back

theorem the_insertion_grows_one {A : Type u} (x : A) :
    ∀ (p q : List A), q ∈ inserts x p → q.length = p.length + 1
  | [], q, h => by
      cases h with
      | head => rfl
      | tail _ h' => exact nomatch h'
  | y :: p, q, h => by
      cases h with
      | head => rfl
      | tail _ h' =>
          obtain ⟨r, hr, he⟩ := mem_map_back (inserts x p) h'
          rw [← he]
          show (r.length + 1) = (p.length + 1) + 1
          rw [the_insertion_grows_one x p r hr]

/-- info: 'Seed.the_insertion_grows_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_insertion_grows_one

theorem the_orders_keep_the_length {A : Type u} :
    ∀ (l p : List A), p ∈ perms l → p.length = l.length
  | [], p, h => by
      cases h with
      | head => rfl
      | tail _ h' => exact nomatch h'
  | x :: l, p, h => by
      have h' : p ∈ joinMap (inserts x) (perms l) := h
      obtain ⟨r, hr, hp⟩ := mem_joinMap_back (perms l) h'
      show p.length = l.length + 1
      rw [the_insertion_grows_one x r p hp,
          the_orders_keep_the_length l r hr]

/-- info: 'Seed.the_orders_keep_the_length' does not depend on any axioms -/
#guard_msgs in #print axioms the_orders_keep_the_length

theorem the_orders_count_to_the_factorial {A : Type u} :
    ∀ l : List A, (perms l).length = fact l.length
  | [] => rfl
  | x :: l => by
      show (joinMap (inserts x) (perms l)).length = fact (l.length + 1)
      rw [the_join_counts_evenly (inserts x) (l.length + 1) (perms l)
            (fun p hp =>
              (the_insertions_count x p).trans
                (congrArg (· + 1) (the_orders_keep_the_length l p hp))),
          the_orders_count_to_the_factorial l]
      exact Nat.mul_comm (l.length + 1) (fact l.length)

/-- info: 'Seed.the_orders_count_to_the_factorial' does not depend on any axioms -/
#guard_msgs in #print axioms the_orders_count_to_the_factorial

def cross : List Plan → List Plan → List Plan
  | [], _ => []
  | p :: ps, qs => qs.map (Plan.board p) ++ cross ps qs

def allPlans : Nat → List Plan
  | 0 => [.ground]
  | d + 1 => .ground :: cross (allPlans d) (allPlans d)

def census : Nat → Nat
  | 0 => 0
  | k + 1 => ((allPlans k).filter (fun p => Nat.beq (reading p) (k + 1))).length

theorem the_census_checksums_with_the_polygon_cutters :
    census 1 = 1 ∧ census 2 = 1 ∧ census 3 = 2 ∧ census 4 = 5
      ∧ census 5 = 14 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- info: 'Seed.the_census_checksums_with_the_polygon_cutters' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_checksums_with_the_polygon_cutters

theorem mem_cross_split :
    ∀ (ps : List Plan) {qs : List Plan} {x : Plan},
      x ∈ cross ps qs → ∃ l r, x = Plan.board l r ∧ l ∈ ps ∧ r ∈ qs
  | [], _, _, h => nomatch h
  | p :: ps, qs, _, h =>
      match mem_append_split (qs.map (Plan.board p)) h with
      | Or.inl hm =>
          match mem_map_back qs hm with
          | ⟨r, hr, he⟩ => ⟨p, r, he.symm, List.Mem.head _, hr⟩
      | Or.inr hc =>
          match mem_cross_split ps hc with
          | ⟨l, r, he, hl, hr⟩ => ⟨l, r, he, List.Mem.tail _ hl, hr⟩

/-- info: 'Seed.mem_cross_split' does not depend on any axioms -/
#guard_msgs in #print axioms mem_cross_split

inductive Apart {A : Type u} : List A → Prop
  | nil : Apart []
  | cons {a : A} {l : List A} :
      (∀ b, b ∈ l → a ≠ b) → Apart l → Apart (a :: l)

theorem apart_map {A : Type u} {B : Type v} {f : A → B}
    (hf : ∀ a b, f a = f b → a = b) :
    ∀ {xs : List A}, Apart xs → Apart (xs.map f)
  | [], _ => Apart.nil
  | x :: xs, Apart.cons hx hxs =>
      Apart.cons
        (fun _ hb he =>
          match mem_map_back xs hb with
          | ⟨a, ha, hfa⟩ => hx a ha (hf x a (he.trans hfa.symm)))
        (apart_map hf hxs)

/-- info: 'Seed.apart_map' does not depend on any axioms -/
#guard_msgs in #print axioms apart_map

theorem apart_append {A : Type u} :
    ∀ {xs : List A} (ys : List A), Apart xs → Apart ys →
      (∀ x, x ∈ xs → ∀ y, y ∈ ys → x ≠ y) → Apart (xs ++ ys)
  | [], _, _, hys, _ => hys
  | _ :: xs, ys, Apart.cons hx hxs, hys, hcross =>
      Apart.cons
        (fun b hb =>
          match mem_append_split xs hb with
          | Or.inl hbx => hx b hbx
          | Or.inr hby => hcross _ (List.Mem.head _) b hby)
        (apart_append ys hxs hys
          (fun a ha y hy => hcross a (List.Mem.tail _ ha) y hy))

/-- info: 'Seed.apart_append' does not depend on any axioms -/
#guard_msgs in #print axioms apart_append

theorem the_cross_keeps_apart {qs : List Plan} (hqs : Apart qs) :
    ∀ {ps : List Plan}, Apart ps → Apart (cross ps qs)
  | [], _ => Apart.nil
  | _ :: ps, Apart.cons hp hps =>
      apart_append (cross ps qs)
        (apart_map (fun _ _ h => (Plan.board.inj h).2) hqs)
        (the_cross_keeps_apart hqs hps)
        (fun _ hx _ hy he =>
          match mem_map_back qs hx, mem_cross_split ps hy with
          | ⟨_, _, hfr⟩, ⟨l', _, hy_eq, hl', _⟩ =>
              hp l' hl'
                (Plan.board.inj ((hfr.trans he).trans hy_eq)).1)

/-- info: 'Seed.the_cross_keeps_apart' does not depend on any axioms -/
#guard_msgs in #print axioms the_cross_keeps_apart

theorem the_room_repeats_no_plan : ∀ d : Nat, Apart (allPlans d)
  | 0 => Apart.cons (fun _ hb => nomatch hb) Apart.nil
  | d + 1 =>
      Apart.cons
        (fun _ hb =>
          match mem_cross_split (allPlans d) hb with
          | ⟨_, _, he, _, _⟩ => fun hg => nomatch hg.trans he)
        (the_cross_keeps_apart (the_room_repeats_no_plan d)
          (the_room_repeats_no_plan d))

/-- info: 'Seed.the_room_repeats_no_plan' does not depend on any axioms -/
#guard_msgs in #print axioms the_room_repeats_no_plan

theorem succ_adds (a b : Nat) : (a + 1) + b = (a + b) + 1 :=
  (click_slides a b).symm

/-- info: 'Seed.succ_adds' does not depend on any axioms -/
#guard_msgs in #print axioms succ_adds

theorem ble_refl : ∀ n : Nat, Nat.ble n n = true
  | 0 => rfl
  | n + 1 => ble_refl n

/-- info: 'Seed.ble_refl' does not depend on any axioms -/
#guard_msgs in #print axioms ble_refl

theorem ble_le_succ : ∀ n : Nat, Nat.ble n (n + 1) = true
  | 0 => rfl
  | n + 1 => ble_le_succ n

/-- info: 'Seed.ble_le_succ' does not depend on any axioms -/
#guard_msgs in #print axioms ble_le_succ

theorem ble_trans : ∀ (a b c : Nat),
    Nat.ble a b = true → Nat.ble b c = true → Nat.ble a c = true
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, _, h1, _ => nomatch h1
  | _ + 1, _ + 1, 0, _, h2 => nomatch h2
  | a + 1, b + 1, c + 1, h1, h2 => ble_trans a b c h1 h2

/-- info: 'Seed.ble_trans' does not depend on any axioms -/
#guard_msgs in #print axioms ble_trans

theorem ble_le_add : ∀ a b : Nat, Nat.ble a (a + b) = true
  | a, 0 => ble_refl a
  | a, b + 1 =>
      ble_trans a (a + b) ((a + b) + 1) (ble_le_add a b) (ble_le_succ (a + b))

/-- info: 'Seed.ble_le_add' does not depend on any axioms -/
#guard_msgs in #print axioms ble_le_add

theorem ble_le_add_left : ∀ a b : Nat, Nat.ble b (a + b) = true
  | 0, b => by rw [zero_add]; exact ble_refl b
  | a + 1, b => by
      rw [succ_adds]
      exact ble_trans b (a + b) ((a + b) + 1)
        (ble_le_add_left a b) (ble_le_succ (a + b))

/-- info: 'Seed.ble_le_add_left' does not depend on any axioms -/
#guard_msgs in #print axioms ble_le_add_left

theorem the_reading_is_positive :
    ∀ p : Plan, ∃ m : Nat, reading p = m + 1
  | .ground => ⟨0, rfl⟩
  | .board l r =>
      match the_reading_is_positive l with
      | ⟨a, ha⟩ =>
          ⟨a + reading r, by
            show reading l + reading r = (a + reading r) + 1
            rw [ha, succ_adds]⟩

/-- info: 'Seed.the_reading_is_positive' does not depend on any axioms -/
#guard_msgs in #print axioms the_reading_is_positive

theorem mem_map_intro {A : Type u} {B : Type v} (f : A → B) :
    ∀ {x : A} {xs : List A}, x ∈ xs → f x ∈ xs.map f
  | _, _ :: _, List.Mem.head _ => List.Mem.head _
  | _, _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_map_intro f h)

/-- info: 'Seed.mem_map_intro' does not depend on any axioms -/
#guard_msgs in #print axioms mem_map_intro

theorem mem_append_left {A : Type u} (ys : List A) :
    ∀ {x : A} {xs : List A}, x ∈ xs → x ∈ xs ++ ys
  | _, _ :: _, List.Mem.head _ => List.Mem.head _
  | _, _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_append_left ys h)

/-- info: 'Seed.mem_append_left' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_left

theorem mem_append_right {A : Type u} :
    ∀ (xs : List A) {x : A} {ys : List A}, x ∈ ys → x ∈ xs ++ ys
  | [], _, _, h => h
  | _ :: xs, _, _, h => List.Mem.tail _ (mem_append_right xs h)

/-- info: 'Seed.mem_append_right' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_right

theorem mem_cross {qs : List Plan} {r : Plan} (hr : r ∈ qs) :
    ∀ {ps : List Plan} {l : Plan}, l ∈ ps → Plan.board l r ∈ cross ps qs
  | _ :: ps, _, List.Mem.head _ =>
      mem_append_left (cross ps qs) (mem_map_intro (Plan.board _) hr)
  | p :: _, _, List.Mem.tail _ h =>
      mem_append_right (qs.map (Plan.board p)) (mem_cross hr h)

/-- info: 'Seed.mem_cross' does not depend on any axioms -/
#guard_msgs in #print axioms mem_cross

theorem the_horizon_holds_every_reading :
    ∀ (n : Nat) (p : Plan),
      Nat.ble (reading p) (n + 1) = true → p ∈ allPlans n
  | 0, .ground, _ => List.Mem.head _
  | _ + 1, .ground, _ => List.Mem.head _
  | 0, .board l r, h =>
      match the_reading_is_positive l, the_reading_is_positive r with
      | ⟨a, ha⟩, ⟨b, hb⟩ => by
          have e : (a + 1) + (b + 1) = ((a + b) + 1) + 1 :=
            congrArg (· + 1) (succ_adds a b)
          have h0 : Nat.ble (reading l + reading r) 1 = true := h
          rw [ha, hb, e] at h0
          exact nomatch h0
  | n + 1, .board l r, h =>
      match the_reading_is_positive l, the_reading_is_positive r with
      | ⟨a, ha⟩, ⟨b, hb⟩ =>
          have e : (a + 1) + (b + 1) = ((a + b) + 1) + 1 :=
            congrArg (· + 1) (succ_adds a b)
          have h' : Nat.ble ((a + b) + 1) (n + 1) = true := by
            have h0 : Nat.ble (reading l + reading r) ((n + 1) + 1) = true := h
            rw [ha, hb, e] at h0
            exact h0
          have hL : l ∈ allPlans n :=
            the_horizon_holds_every_reading n l (by
              rw [ha]
              exact ble_trans (a + 1) ((a + b) + 1) (n + 1)
                (ble_le_add a b) h')
          have hR : r ∈ allPlans n :=
            the_horizon_holds_every_reading n r (by
              rw [hb]
              exact ble_trans (b + 1) ((a + b) + 1) (n + 1)
                (ble_le_add_left a b) h')
          List.Mem.tail _ (mem_cross hR hL)

/-- info: 'Seed.the_horizon_holds_every_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_horizon_holds_every_reading

theorem eq_of_beq : ∀ a b : Nat, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | a + 1, b + 1, h => congrArg (· + 1) (eq_of_beq a b h)

/-- info: 'Seed.eq_of_beq' does not depend on any axioms -/
#guard_msgs in #print axioms eq_of_beq

theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

/-- info: 'Seed.beq_self' does not depend on any axioms -/
#guard_msgs in #print axioms beq_self

theorem mem_of_mem_filter {A : Type u} {q : A → Bool} {x : A} :
    ∀ xs : List A, x ∈ xs.filter q → x ∈ xs
  | [], h => nomatch h
  | a :: xs, h => by
      cases hq : q a with
      | true =>
          rw [List.filter_cons_of_pos hq] at h
          cases h with
          | head => exact List.Mem.head _
          | tail _ h' => exact List.Mem.tail _ (mem_of_mem_filter xs h')
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq)] at h
          exact List.Mem.tail _ (mem_of_mem_filter xs h)

/-- info: 'Seed.mem_of_mem_filter' does not depend on any axioms -/
#guard_msgs in #print axioms mem_of_mem_filter

theorem filter_holds {A : Type u} {q : A → Bool} {x : A} :
    ∀ xs : List A, x ∈ xs.filter q → q x = true
  | [], h => nomatch h
  | a :: xs, h => by
      cases hq : q a with
      | true =>
          rw [List.filter_cons_of_pos hq] at h
          cases h with
          | head => exact hq
          | tail _ h' => exact filter_holds xs h'
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq)] at h
          exact filter_holds xs h

/-- info: 'Seed.filter_holds' does not depend on any axioms -/
#guard_msgs in #print axioms filter_holds

theorem mem_filter_intro {A : Type u} {q : A → Bool} {x : A} :
    ∀ xs : List A, x ∈ xs → q x = true → x ∈ xs.filter q
  | [], h, _ => nomatch h
  | a :: xs, h, hx => by
      cases h with
      | head =>
          rw [List.filter_cons_of_pos hx]
          exact List.Mem.head _
      | tail _ h' =>
          cases hq : q a with
          | true =>
              rw [List.filter_cons_of_pos hq]
              exact List.Mem.tail _ (mem_filter_intro xs h' hx)
          | false =>
              rw [List.filter_cons_of_neg (ne_true_of_eq_false hq)]
              exact mem_filter_intro xs h' hx

/-- info: 'Seed.mem_filter_intro' does not depend on any axioms -/
#guard_msgs in #print axioms mem_filter_intro

theorem apart_filter {A : Type u} {q : A → Bool} :
    ∀ {xs : List A}, Apart xs → Apart (xs.filter q)
  | [], _ => Apart.nil
  | a :: xs, Apart.cons ha hxs => by
      cases hq : q a with
      | true =>
          rw [List.filter_cons_of_pos hq]
          exact Apart.cons
            (fun b hb => ha b (mem_of_mem_filter xs hb))
            (apart_filter hxs)
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq)]
          exact apart_filter hxs

/-- info: 'Seed.apart_filter' does not depend on any axioms -/
#guard_msgs in #print axioms apart_filter

theorem the_census_is_exact (k : Nat) :
    Apart ((allPlans k).filter (fun p => Nat.beq (reading p) (k + 1)))
      ∧ ∀ p : Plan,
          p ∈ (allPlans k).filter (fun p => Nat.beq (reading p) (k + 1))
            ↔ reading p = k + 1 :=
  ⟨apart_filter (the_room_repeats_no_plan k),
   fun p =>
     ⟨fun h =>
        have hq :=
          filter_holds (A := Plan)
            (q := fun p => Nat.beq (reading p) (k + 1))
            (x := p) (allPlans k) h
        eq_of_beq _ _ hq,
      fun h =>
        mem_filter_intro (allPlans k)
          (the_horizon_holds_every_reading k p
            (by rw [h]; exact ble_refl (k + 1)))
          (by rw [h]; exact beq_self (k + 1))⟩⟩

/-- info: 'Seed.the_census_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_is_exact

theorem perm_refl {A : Type u} : ∀ l : List A, l.Perm l
  | [] => .nil
  | x :: l => .cons x (perm_refl l)

/-- info: 'Seed.perm_refl' does not depend on any axioms -/
#guard_msgs in #print axioms perm_refl

theorem the_insertion_is_a_shuffle {A : Type u} (x : A) :
    ∀ (r q : List A), q ∈ inserts x r → q.Perm (x :: r)
  | [], q, h => by
      cases h with
      | head => exact perm_refl [x]
      | tail _ h' => exact nomatch h'
  | y :: r, q, h => by
      cases h with
      | head => exact perm_refl (x :: y :: r)
      | tail _ h' =>
          obtain ⟨q', hq', he⟩ := mem_map_back (inserts x r) h'
          rw [← he]
          exact List.Perm.trans
            (List.Perm.cons y (the_insertion_is_a_shuffle x r q' hq'))
            (List.Perm.swap x y r)

/-- info: 'Seed.the_insertion_is_a_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms the_insertion_is_a_shuffle

theorem every_order_is_a_shuffle {A : Type u} :
    ∀ (l p : List A), p ∈ perms l → p.Perm l
  | [], p, h => by
      cases h with
      | head => exact .nil
      | tail _ h' => exact nomatch h'
  | x :: l, p, h => by
      have h' : p ∈ joinMap (inserts x) (perms l) := h
      obtain ⟨r, hr, hp⟩ := mem_joinMap_back (perms l) h'
      exact List.Perm.trans (the_insertion_is_a_shuffle x r p hp)
        (List.Perm.cons x (every_order_is_a_shuffle l r hr))

/-- info: 'Seed.every_order_is_a_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms every_order_is_a_shuffle

theorem perm_mem {A : Type u} {xs ys : List A} (h : xs.Perm ys) :
    ∀ a, a ∈ xs → a ∈ ys := by
  induction h with
  | nil => exact fun _ ha => ha
  | cons x _ ih =>
      intro a ha
      cases ha with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail _ (ih a h')
  | swap x y l =>
      intro a ha
      cases ha with
      | head => exact List.Mem.tail _ (List.Mem.head _)
      | tail _ h' =>
          cases h' with
          | head => exact List.Mem.head _
          | tail _ h'' => exact List.Mem.tail _ (List.Mem.tail _ h'')
  | trans _ _ ih₁ ih₂ => exact fun a ha => ih₂ a (ih₁ a ha)

/-- info: 'Seed.perm_mem' does not depend on any axioms -/
#guard_msgs in #print axioms perm_mem

theorem the_wedgings_stand_apart {A : Type u} (x : A) :
    ∀ p : List A, ¬ x ∈ p → Apart (inserts x p)
  | [], _ => .cons (fun _ hb => nomatch hb) .nil
  | y :: p, hx => by
      have hxy : x ≠ y := fun he => hx (by rw [he]; exact List.Mem.head p)
      have hxp : ¬ x ∈ p := fun hm => hx (List.Mem.tail y hm)
      refine Apart.cons ?_
        (apart_map (fun _ _ h => (List.cons.inj h).2)
          (the_wedgings_stand_apart x p hxp))
      intro q hq he
      obtain ⟨r, hr, hyr⟩ := mem_map_back (inserts x p) hq
      exact hxy (List.cons.inj (he.trans hyr.symm)).1

/-- info: 'Seed.the_wedgings_stand_apart' does not depend on any axioms -/
#guard_msgs in #print axioms the_wedgings_stand_apart

theorem the_wedge_remembers_its_word {A : Type u} (x : A) :
    ∀ (p p' q : List A), q ∈ inserts x p → q ∈ inserts x p' →
      ¬ x ∈ p → ¬ x ∈ p' → p = p'
  | [], [], _, _, _, _, _ => rfl
  | [], y' :: p', q, h₁, h₂, _, hx' => by
      cases h₁ with
      | head =>
          cases h₂ with
          | tail _ h₂' =>
              obtain ⟨r', _, he'⟩ := mem_map_back (inserts x p') h₂'
              exact absurd
                (show x ∈ y' :: p' from by
                  rw [← (List.cons.inj he').1]
                  exact List.Mem.head p')
                hx'
      | tail _ h₁' => exact nomatch h₁'
  | y :: p, [], q, h₁, h₂, hx, _ => by
      cases h₂ with
      | head =>
          cases h₁ with
          | tail _ h₁' =>
              obtain ⟨r, _, he⟩ := mem_map_back (inserts x p) h₁'
              exact absurd
                (show x ∈ y :: p from by
                  rw [← (List.cons.inj he).1]
                  exact List.Mem.head p)
                hx
      | tail _ h₂' => exact nomatch h₂'
  | y :: p, y' :: p', q, h₁, h₂, hx, hx' => by
      have hxy : x ≠ y := fun he => hx (by rw [he]; exact List.Mem.head p)
      have hxy' : x ≠ y' :=
        fun he => hx' (by rw [he]; exact List.Mem.head p')
      cases h₁ with
      | head =>
          cases h₂ with
          | head => rfl
          | tail _ h₂' =>
              obtain ⟨r', _, he'⟩ := mem_map_back (inserts x p') h₂'
              exact (hxy' (List.cons.inj he').1.symm).elim
      | tail _ h₁' =>
          obtain ⟨r, hr, he⟩ := mem_map_back (inserts x p) h₁'
          cases h₂ with
          | head => exact (hxy (List.cons.inj he).1.symm).elim
          | tail _ h₂' =>
              obtain ⟨r', hr', he'⟩ := mem_map_back (inserts x p') h₂'
              have hyy : y = y' := (List.cons.inj (he.trans he'.symm)).1
              have hrr : r = r' := (List.cons.inj (he.trans he'.symm)).2
              have hpp : p = p' :=
                the_wedge_remembers_its_word x p p' r hr
                  (by rw [hrr]; exact hr')
                  (fun hm => hx (List.Mem.tail y hm))
                  (fun hm => hx' (List.Mem.tail y' hm))
              rw [hyy, hpp]

/-- info: 'Seed.the_wedge_remembers_its_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_wedge_remembers_its_word

theorem apart_joinMap {A : Type u} {B : Type v} (f : A → List B) :
    ∀ as : List A, Apart as → (∀ a, a ∈ as → Apart (f a)) →
      (∀ a, a ∈ as → ∀ b, b ∈ as → a ≠ b →
        ∀ q, q ∈ f a → ¬ q ∈ f b) →
      Apart (joinMap f as)
  | [], _, _, _ => .nil
  | a :: as, .cons ha has, hfib, hdisj => by
      refine apart_append (joinMap f as) (hfib a (List.Mem.head as))
        ?_ ?_
      · exact apart_joinMap f as has
          (fun b hb => hfib b (List.Mem.tail a hb))
          (fun b hb c hc =>
            hdisj b (List.Mem.tail a hb) c (List.Mem.tail a hc))
      · intro q hq q' hq' he
        obtain ⟨b, hb, hqb⟩ := mem_joinMap_back as hq'
        have hqfb : q ∈ f b := by rw [he]; exact hqb
        exact hdisj a (List.Mem.head as) b (List.Mem.tail a hb)
          (ha b hb) q hq hqfb

/-- info: 'Seed.apart_joinMap' does not depend on any axioms -/
#guard_msgs in #print axioms apart_joinMap

theorem the_orders_repeat_never {A : Type u} :
    ∀ l : List A, Apart l → Apart (perms l)
  | [], _ => .cons (fun _ hb => nomatch hb) .nil
  | x :: l, .cons hx hl => by
      have hxl : ¬ x ∈ l := fun hm => hx x hm rfl
      have hxp : ∀ p, p ∈ perms l → ¬ x ∈ p := fun p hp hm =>
        hxl (perm_mem (every_order_is_a_shuffle l p hp) x hm)
      show Apart (joinMap (inserts x) (perms l))
      exact apart_joinMap (inserts x) (perms l)
        (the_orders_repeat_never l hl)
        (fun p hp => the_wedgings_stand_apart x p (hxp p hp))
        (fun p hp p' hp' hne q hq hq' =>
          hne (the_wedge_remembers_its_word x p p' q hq hq'
            (hxp p hp) (hxp p' hp')))

/-- info: 'Seed.the_orders_repeat_never' does not depend on any axioms -/
#guard_msgs in #print axioms the_orders_repeat_never

theorem mem_splits {A : Type u} {x : A} :
    ∀ {l : List A}, x ∈ l → ∃ v₁ v₂ : List A, l = v₁ ++ x :: v₂
  | _ :: t, List.Mem.head _ => ⟨[], t, rfl⟩
  | a :: _, List.Mem.tail _ h =>
      match mem_splits h with
      | ⟨v₁, v₂, he⟩ => ⟨a :: v₁, v₂, congrArg (a :: ·) he⟩

/-- info: 'Seed.mem_splits' does not depend on any axioms -/
#guard_msgs in #print axioms mem_splits

theorem perm_symm {A : Type u} {xs ys : List A} (h : xs.Perm ys) :
    ys.Perm xs := by
  induction h with
  | nil => exact .nil
  | cons x _ ih => exact .cons x ih
  | swap x y l => exact .swap y x l
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁

/-- info: 'Seed.perm_symm' does not depend on any axioms -/
#guard_msgs in #print axioms perm_symm

theorem perm_length {A : Type u} {xs ys : List A} (h : xs.Perm ys) :
    xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg (· + 1) ih
  | swap => rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- info: 'Seed.perm_length' does not depend on any axioms -/
#guard_msgs in #print axioms perm_length

theorem perm_middle {A : Type u} (x : A) :
    ∀ (u v : List A), (u ++ x :: v).Perm (x :: (u ++ v))
  | [], v => perm_refl (x :: v)
  | y :: u, v =>
      List.Perm.trans (List.Perm.cons y (perm_middle x u v))
        (List.Perm.swap x y (u ++ v))

/-- info: 'Seed.perm_middle' does not depend on any axioms -/
#guard_msgs in #print axioms perm_middle

theorem two_splits_perm {A : Type u} (x : A) :
    ∀ (u v w z : List A), u ++ x :: v = w ++ x :: z →
      (u ++ v).Perm (w ++ z)
  | [], v, [], z, h => by
      rw [(List.cons.inj h).2]
  | [], v, w₀ :: w', z, h => by
      obtain ⟨h₁, h₂⟩ := List.cons.inj h
      rw [h₂, ← h₁]
      exact perm_middle x w' z
  | u₀ :: u', v, [], z, h => by
      obtain ⟨h₁, h₂⟩ := List.cons.inj h
      rw [← h₂, h₁]
      exact perm_symm (perm_middle x u' v)
  | u₀ :: u', v, w₀ :: w', z, h => by
      obtain ⟨h₁, h₂⟩ := List.cons.inj h
      rw [h₁]
      exact List.Perm.cons w₀ (two_splits_perm x u' v w' z h₂)

/-- info: 'Seed.two_splits_perm' does not depend on any axioms -/
#guard_msgs in #print axioms two_splits_perm

theorem the_shuffle_cancels_the_mark {A : Type u} {L M : List A}
    (h : L.Perm M) :
    ∀ (x : A) (u v w z : List A), L = u ++ x :: v → M = w ++ x :: z →
      (u ++ v).Perm (w ++ z) := by
  induction h with
  | nil =>
      intro x u v w z hL _
      cases u with
      | nil => exact nomatch hL
      | cons _ _ => exact nomatch hL
  | cons y h' ih =>
      intro x u v w z hL hM
      cases u with
      | nil =>
          obtain ⟨hyx, hv⟩ := List.cons.inj hL
          cases w with
          | nil =>
              obtain ⟨_, hz⟩ := List.cons.inj hM
              rw [← hv, ← hz]
              exact h'
          | cons w₀ w' =>
              obtain ⟨hyw, ht₂⟩ := List.cons.inj hM
              rw [← hv, ← hyw, hyx]
              exact (ht₂ ▸ h').trans (perm_middle x w' z)
      | cons u₀ u' =>
          obtain ⟨hyu, ht₁⟩ := List.cons.inj hL
          cases w with
          | nil =>
              obtain ⟨hyx, hz⟩ := List.cons.inj hM
              rw [← hz, ← hyu, hyx]
              exact (perm_symm (perm_middle x u' v)).trans
                (by
                  rw [show u' ++ x :: v = u'.append (x :: v) from rfl,
                      ← ht₁]
                  exact h')
          | cons w₀ w' =>
              obtain ⟨hyu2, ht₁2⟩ := List.cons.inj hL
              obtain ⟨hyw, ht₂⟩ := List.cons.inj hM
              rw [← hyu, ← hyw]
              exact List.Perm.cons y (ih x u' v w' z ht₁ ht₂)
  | swap a b l =>
      intro x u v w z hL hM
      cases u with
      | nil =>
          obtain ⟨hbx, hv⟩ := List.cons.inj hL
          cases w with
          | nil =>
              obtain ⟨hax, hz⟩ := List.cons.inj hM
              rw [← hv, ← hz, hax, hbx]
          | cons w₀ w' =>
              obtain ⟨haw, hM2⟩ := List.cons.inj hM
              cases w' with
              | nil =>
                  obtain ⟨_, hlz⟩ := List.cons.inj hM2
                  rw [← hv, ← haw, ← hlz]
                  exact perm_refl (a :: l)
              | cons w₁ w'' =>
                  obtain ⟨hbw, hl⟩ := List.cons.inj hM2
                  rw [← hv, ← haw, ← hbw, hl, hbx]
                  exact List.Perm.cons a (perm_middle x w'' z)
      | cons u₀ u' =>
          obtain ⟨hbu, hL2⟩ := List.cons.inj hL
          cases u' with
          | nil =>
              obtain ⟨hax, hlv⟩ := List.cons.inj hL2
              cases w with
              | nil =>
                  obtain ⟨_, hz⟩ := List.cons.inj hM
                  rw [← hbu, ← hlv, ← hz]
                  exact perm_refl (b :: l)
              | cons w₀ w' =>
                  obtain ⟨haw, hM2⟩ := List.cons.inj hM
                  cases w' with
                  | nil =>
                      obtain ⟨hbx2, hlz⟩ := List.cons.inj hM2
                      rw [← hbu, ← haw, ← hlv, hbx2, hax, hlz]
                  | cons w₁ w'' =>
                      obtain ⟨hbw, hl2⟩ := List.cons.inj hM2
                      rw [← hbu, ← hlv, hl2, ← haw, ← hbw, hax]
                      exact List.Perm.trans
                        (List.Perm.cons b (perm_middle x w'' z))
                        (List.Perm.swap x b (w'' ++ z))
          | cons u₁ u'' =>
              obtain ⟨hau, hl⟩ := List.cons.inj hL2
              cases w with
              | nil =>
                  obtain ⟨hax, hz⟩ := List.cons.inj hM
                  rw [← hbu, ← hau, ← hz, hl, hax]
                  exact List.Perm.cons b (perm_symm (perm_middle x u'' v))
              | cons w₀ w' =>
                  obtain ⟨haw, hM2⟩ := List.cons.inj hM
                  cases w' with
                  | nil =>
                      obtain ⟨hbx2, hlz⟩ := List.cons.inj hM2
                      rw [← hbu, ← hau, ← haw, ← hlz, hl, hbx2]
                      exact List.Perm.trans
                        (List.Perm.swap a x (u'' ++ v))
                        (List.Perm.cons a
                          (perm_symm (perm_middle x u'' v)))
                  | cons w₁ w'' =>
                      obtain ⟨hbw, hl2⟩ := List.cons.inj hM2
                      rw [← hbu, ← hau, ← haw, ← hbw]
                      exact List.Perm.trans
                        (List.Perm.swap a b (u'' ++ v))
                        (List.Perm.cons a (List.Perm.cons b
                          (two_splits_perm x u'' v w'' z
                            (hl.symm.trans hl2))))
  | trans h₁ _ ih₁ ih₂ =>
      intro x u v w z hL hM
      have hxL : x ∈ _ := perm_mem h₁ x
        (by rw [hL]; exact mem_append_right u (List.Mem.head v))
      obtain ⟨u₀, v₀, hmid⟩ := mem_splits hxL
      exact (ih₁ x u v u₀ v₀ hL hmid).trans (ih₂ x u₀ v₀ w z hmid hM)

/-- info: 'Seed.the_shuffle_cancels_the_mark' does not depend on any axioms -/
#guard_msgs in #print axioms the_shuffle_cancels_the_mark

theorem mem_joinMap_intro {A : Type u} {B : Type v} {f : A → List B} {a : A}
    {q : B} : ∀ {as : List A}, a ∈ as → q ∈ f a → q ∈ joinMap f as
  | _ :: as, List.Mem.head _, hq => mem_append_left (joinMap f as) hq
  | b :: _, List.Mem.tail _ h, hq =>
      mem_append_right (f b) (mem_joinMap_intro h hq)

/-- info: 'Seed.mem_joinMap_intro' does not depend on any axioms -/
#guard_msgs in #print axioms mem_joinMap_intro

theorem the_wedge_fits_anywhere {A : Type u} (x : A) :
    ∀ (u v : List A), (u ++ x :: v) ∈ inserts x (u ++ v)
  | [], v => by
      cases v with
      | nil => exact List.Mem.head _
      | cons y t => exact List.Mem.head _
  | y :: u, v =>
      List.Mem.tail _
        (mem_map_intro (y :: ·) (the_wedge_fits_anywhere x u v))

/-- info: 'Seed.the_wedge_fits_anywhere' does not depend on any axioms -/
#guard_msgs in #print axioms the_wedge_fits_anywhere

theorem every_shuffle_is_an_order {A : Type u} :
    ∀ (l p : List A), p.Perm l → p ∈ perms l
  | [], p, h => by
      have hlen : p.length = 0 := perm_length h
      cases p with
      | nil => exact List.Mem.head _
      | cons _ _ => exact nomatch hlen
  | x :: l, p, h => by
      have hx : x ∈ p := perm_mem (perm_symm h) x (List.Mem.head l)
      obtain ⟨u, v, hp⟩ := mem_splits hx
      have h₂ : (u ++ v).Perm l :=
        the_shuffle_cancels_the_mark h x u v [] l hp rfl
      have h₃ : (u ++ v) ∈ perms l :=
        every_shuffle_is_an_order l (u ++ v) h₂
      have h₄ : p ∈ inserts x (u ++ v) := by
        rw [hp]
        exact the_wedge_fits_anywhere x u v
      show p ∈ joinMap (inserts x) (perms l)
      exact mem_joinMap_intro h₃ h₄

/-- info: 'Seed.every_shuffle_is_an_order' does not depend on any axioms -/
#guard_msgs in #print axioms every_shuffle_is_an_order

theorem the_census_of_orders_is_exact {A : Type u} (l p : List A)
    (hl : Apart l) :
    (p.Perm l ↔ p ∈ perms l)
      ∧ Apart (perms l)
      ∧ (perms l).length = fact l.length :=
  ⟨⟨every_shuffle_is_an_order l p, every_order_is_a_shuffle l p⟩,
   the_orders_repeat_never l hl,
   the_orders_count_to_the_factorial l⟩

/-- info: 'Seed.the_census_of_orders_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_of_orders_is_exact

theorem not_not : ∀ b : Bool, (!(!b)) = b
  | true => rfl
  | false => rfl

/-- info: 'Seed.not_not' does not depend on any axioms -/
#guard_msgs in #print axioms not_not

theorem one_scales : ∀ n : Nat, 1 * n = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (one_scales n)

/-- info: 'Seed.one_scales' does not depend on any axioms -/
#guard_msgs in #print axioms one_scales

def sameRatio (a b c d : Nat) : Prop := a * d = c * b

theorem beq_no {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y) {x y : A} (hxy : x ≠ y) :
    beq x y = false := by
  cases h : beq x y with
  | false => rfl
  | true => exact absurd (hE x y h) hxy

/-- info: 'Seed.beq_no' does not depend on any axioms -/
#guard_msgs in #print axioms beq_no

theorem ne_of_beq_no {A : Type u} {beq : A → A → Bool}
    (hR : ∀ x : A, beq x x = true) {x y : A} (h : beq x y = false) :
    x ≠ y :=
  fun he =>
    nomatch (((congrArg (fun z => beq z y) he).symm.trans h).symm.trans
      (hR y))

/-- info: 'Seed.ne_of_beq_no' does not depend on any axioms -/
#guard_msgs in #print axioms ne_of_beq_no

def trade {A : Type u} (beq : A → A → Bool) (a b : A) (x : A) : A :=
  cond (beq x a) b (cond (beq x b) a x)

theorem the_trade_swaps_the_pair {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) :
    trade beq a b a = b ∧ trade beq a b b = a := by
  constructor
  · show cond (beq a a) b (cond (beq a b) a a) = b
    rw [hR a]
    exact rfl
  · show cond (beq b a) b (cond (beq b b) a b) = a
    rw [beq_no hE (fun h => hab h.symm), hR b]
    exact rfl

/-- info: 'Seed.the_trade_swaps_the_pair' does not depend on any axioms -/
#guard_msgs in #print axioms the_trade_swaps_the_pair

theorem the_trade_spares_the_stranger {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y) {a b x : A}
    (hxa : x ≠ a) (hxb : x ≠ b) : trade beq a b x = x := by
  show cond (beq x a) b (cond (beq x b) a x) = x
  rw [beq_no hE hxa, beq_no hE hxb]
  exact rfl

/-- info: 'Seed.the_trade_spares_the_stranger' does not depend on any axioms -/
#guard_msgs in #print axioms the_trade_spares_the_stranger

theorem the_trade_undoes_itself {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) (x : A) :
    trade beq a b (trade beq a b x) = x := by
  cases hxa : beq x a with
  | true =>
      have hx : x = a := hE x a hxa
      rw [hx, (the_trade_swaps_the_pair hE hR hab).1,
          (the_trade_swaps_the_pair hE hR hab).2]
  | false =>
      cases hxb : beq x b with
      | true =>
          have hx : x = b := hE x b hxb
          rw [hx, (the_trade_swaps_the_pair hE hR hab).2,
              (the_trade_swaps_the_pair hE hR hab).1]
      | false =>
          have hfix : trade beq a b x = x := by
            show cond (beq x a) b (cond (beq x b) a x) = x
            rw [hxa, hxb]
            exact rfl
          rw [hfix, hfix]

/-- info: 'Seed.the_trade_undoes_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_trade_undoes_itself

theorem the_trade_hears_no_order {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) (x : A) :
    trade beq a b x = trade beq b a x := by
  cases hxa : beq x a with
  | true =>
      have hx : x = a := hE x a hxa
      rw [hx, (the_trade_swaps_the_pair hE hR hab).1]
      exact ((the_trade_swaps_the_pair hE hR
        (fun h => hab h.symm)).2).symm
  | false =>
      cases hxb : beq x b with
      | true =>
          have hx : x = b := hE x b hxb
          rw [hx, (the_trade_swaps_the_pair hE hR hab).2]
          exact ((the_trade_swaps_the_pair hE hR
            (fun h => hab h.symm)).1).symm
      | false =>
          have hxa' := ne_of_beq_no hR hxa
          have hxb' := ne_of_beq_no hR hxb
          rw [the_trade_spares_the_stranger hE hxa' hxb',
              the_trade_spares_the_stranger hE hxb' hxa']

/-- info: 'Seed.the_trade_hears_no_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_trade_hears_no_order

theorem the_traded_word_trades_home {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) :
    ∀ p : List A, (p.map (trade beq a b)).map (trade beq a b) = p
  | [] => rfl
  | x :: p => by
      show trade beq a b (trade beq a b x)
            :: (p.map (trade beq a b)).map (trade beq a b) = x :: p
      rw [the_trade_undoes_itself hE hR hab x,
          the_traded_word_trades_home hE hR hab p]

/-- info: 'Seed.the_traded_word_trades_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_traded_word_trades_home

theorem the_trade_spares_the_word {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y) {a b : A} :
    ∀ w : List A, (∀ x, x ∈ w → x ≠ a) → (∀ x, x ∈ w → x ≠ b) →
      w.map (trade beq a b) = w
  | [], _, _ => rfl
  | x :: w, hA, hB => by
      show trade beq a b x :: w.map (trade beq a b) = x :: w
      rw [the_trade_spares_the_stranger hE (hA x (List.Mem.head w))
            (hB x (List.Mem.head w)),
          the_trade_spares_the_word hE w
            (fun y hy => hA y (List.Mem.tail x hy))
            (fun y hy => hB y (List.Mem.tail x hy))]

/-- info: 'Seed.the_trade_spares_the_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_trade_spares_the_word

theorem map_congr_mem {A : Type u} {B : Type v} (f g : A → B) :
    ∀ w : List A, (∀ x, x ∈ w → f x = g x) → w.map f = w.map g
  | [], _ => rfl
  | x :: w, h => by
      show f x :: w.map f = g x :: w.map g
      rw [h x (List.Mem.head w),
          map_congr_mem f g w (fun y hy => h y (List.Mem.tail x hy))]

/-- info: 'Seed.map_congr_mem' does not depend on any axioms -/
#guard_msgs in #print axioms map_congr_mem

theorem append_regroups {A : Type u} :
    ∀ (x y z : List A), (x ++ y) ++ z = x ++ (y ++ z)
  | [], _, _ => rfl
  | a :: x, y, z => congrArg (a :: ·) (append_regroups x y z)

/-- info: 'Seed.append_regroups' does not depend on any axioms -/
#guard_msgs in #print axioms append_regroups

theorem perm_append_left {A : Type u} {v w : List A} (h : v.Perm w) :
    ∀ u : List A, (u ++ v).Perm (u ++ w)
  | [] => h
  | x :: u => List.Perm.cons x (perm_append_left h u)

/-- info: 'Seed.perm_append_left' does not depend on any axioms -/
#guard_msgs in #print axioms perm_append_left

theorem perm_map {A : Type u} {B : Type v} (f : A → B) {xs ys : List A}
    (h : xs.Perm ys) : (xs.map f).Perm (ys.map f) := by
  induction h with
  | nil => exact .nil
  | cons x _ ih => exact .cons (f x) ih
  | swap x y l => exact .swap (f x) (f y) (l.map f)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- info: 'Seed.perm_map' does not depend on any axioms -/
#guard_msgs in #print axioms perm_map

theorem apart_across {A : Type u} :
    ∀ (u w : List A), Apart (u ++ w) →
      ∀ x, x ∈ u → ∀ y, y ∈ w → x ≠ y
  | [], _, _, _, hx, _, _ => nomatch hx
  | z :: u, w, h, x, hx, y, hy => by
      cases h with
      | cons hz hrest =>
          cases hx with
          | head => exact hz y (mem_append_right u hy)
          | tail _ hx' => exact apart_across u w hrest x hx' y hy

/-- info: 'Seed.apart_across' does not depend on any axioms -/
#guard_msgs in #print axioms apart_across

theorem apart_drop {A : Type u} :
    ∀ (u w : List A), Apart (u ++ w) → Apart w
  | [], _, h => h
  | _ :: u, w, h => by
      cases h with
      | cons _ hrest => exact apart_drop u w hrest

/-- info: 'Seed.apart_drop' does not depend on any axioms -/
#guard_msgs in #print axioms apart_drop

theorem the_wedged_trade_is_a_shuffle {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    (u v1 v2 : List A)
    (hl : Apart (u ++ a :: (v1 ++ b :: v2))) :
    ((u ++ a :: (v1 ++ b :: v2)).map (trade beq a b)).Perm
      (u ++ a :: (v1 ++ b :: v2)) := by
  have hua : ∀ x, x ∈ u → x ≠ a := fun x hx =>
    apart_across u (a :: (v1 ++ b :: v2)) hl x hx a
      (List.Mem.head (v1 ++ b :: v2))
  have hub : ∀ x, x ∈ u → x ≠ b := fun x hx =>
    apart_across u (a :: (v1 ++ b :: v2)) hl x hx b
      (List.Mem.tail a (mem_append_right v1 (List.Mem.head v2)))
  have hcons : Apart (a :: (v1 ++ b :: v2)) :=
    apart_drop u (a :: (v1 ++ b :: v2)) hl
  cases hcons with
  | cons hafresh hvrest =>
      have hv1a : ∀ x, x ∈ v1 → x ≠ a := fun x hx he =>
        hafresh x (mem_append_left (b :: v2) hx) he.symm
      have hv1b : ∀ x, x ∈ v1 → x ≠ b := fun x hx =>
        apart_across v1 (b :: v2) hvrest x hx b (List.Mem.head v2)
      have hbfresh : Apart (b :: v2) := apart_drop v1 (b :: v2) hvrest
      cases hbfresh with
      | cons hbf _ =>
          have hv2a : ∀ x, x ∈ v2 → x ≠ a := fun x hx he =>
            hafresh x (mem_append_right v1 (List.Mem.tail b hx)) he.symm
          have hv2b : ∀ x, x ∈ v2 → x ≠ b := fun x hx he =>
            hbf x hx he.symm
          have hmap : (u ++ a :: (v1 ++ b :: v2)).map (trade beq a b)
              = u ++ b :: (v1 ++ a :: v2) := by
            rw [map_crosses_append (trade beq a b) u (a :: (v1 ++ b :: v2))]
            show u.map (trade beq a b)
                ++ trade beq a b a :: (v1 ++ b :: v2).map (trade beq a b)
              = u ++ b :: (v1 ++ a :: v2)
            rw [the_trade_spares_the_word hE u hua hub,
                (the_trade_swaps_the_pair hE hR hab).1,
                map_crosses_append (trade beq a b) v1 (b :: v2)]
            show u ++ b :: (v1.map (trade beq a b)
                ++ trade beq a b b :: v2.map (trade beq a b))
              = u ++ b :: (v1 ++ a :: v2)
            rw [the_trade_spares_the_word hE v1 hv1a hv1b,
                (the_trade_swaps_the_pair hE hR hab).2,
                the_trade_spares_the_word hE v2 hv2a hv2b]
          rw [hmap]
          refine perm_append_left ?_ u
          exact ((List.Perm.cons b (perm_middle a v1 v2)).trans
            (List.Perm.swap a b (v1 ++ v2))).trans
            (List.Perm.cons a (perm_symm (perm_middle b v1 v2)))

/-- info: 'Seed.the_wedged_trade_is_a_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms the_wedged_trade_is_a_shuffle

theorem the_trade_is_a_shuffle {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (hl : Apart l) (ha : a ∈ l) (hb : b ∈ l) :
    (l.map (trade beq a b)).Perm l := by
  obtain ⟨u, v, huv⟩ := mem_splits ha
  subst huv
  cases mem_append_split u hb with
  | inr hbv =>
      cases hbv with
      | head => exact absurd rfl hab
      | tail _ hbv' =>
          obtain ⟨v1, v2, hv⟩ := mem_splits hbv'
          subst hv
          exact the_wedged_trade_is_a_shuffle hE hR hab u v1 v2 hl
  | inl hbu =>
      obtain ⟨u1, u2, hu⟩ := mem_splits hbu
      subst hu
      rw [append_regroups u1 (b :: u2) (a :: v)] at hl ⊢
      show ((u1 ++ b :: (u2 ++ a :: v)).map (trade beq a b)).Perm
          (u1 ++ b :: (u2 ++ a :: v))
      rw [map_congr_mem (trade beq a b) (trade beq b a)
            (u1 ++ b :: (u2 ++ a :: v))
            (fun x _ => the_trade_hears_no_order hE hR hab x)]
      exact the_wedged_trade_is_a_shuffle hE hR (fun h => hab h.symm)
        u1 u2 v hl

/-- info: 'Seed.the_trade_is_a_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms the_trade_is_a_shuffle

theorem the_trade_keeps_the_room {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (hl : Apart l) (ha : a ∈ l) (hb : b ∈ l)
    {p : List A} (hp : p ∈ perms l) :
    p.map (trade beq a b) ∈ perms l :=
  every_shuffle_is_an_order l (p.map (trade beq a b))
    ((perm_map (trade beq a b) (every_order_is_a_shuffle l p hp)).trans
      (the_trade_is_a_shuffle hE hR hab hl ha hb))

/-- info: 'Seed.the_trade_keeps_the_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_trade_keeps_the_room

theorem mem_insert_middle {A : Type u} {y : A} :
    ∀ (v1 : List A) {x : A} {v2 : List A}, y ∈ v1 ++ v2 → y ∈ v1 ++ x :: v2
  | [], x, _, h => List.Mem.tail x h
  | z :: v1, _, _, h => by
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail z (mem_insert_middle v1 h')

/-- info: 'Seed.mem_insert_middle' does not depend on any axioms -/
#guard_msgs in #print axioms mem_insert_middle

theorem apart_removes_the_mark {A : Type u} :
    ∀ (v1 : List A) {x : A} {v2 : List A},
      Apart (v1 ++ x :: v2) → Apart (v1 ++ v2)
  | [], _, _, h => by
      cases h with
      | cons _ hrest => exact hrest
  | _ :: v1, _, _, h => by
      cases h with
      | cons hz hrest =>
          exact Apart.cons
            (fun y hy => hz y (mem_insert_middle v1 hy))
            (apart_removes_the_mark v1 hrest)

/-- info: 'Seed.apart_removes_the_mark' does not depend on any axioms -/
#guard_msgs in #print axioms apart_removes_the_mark

theorem the_apart_mark_sits_once {A : Type u} (v1 : List A) {x : A}
    (v2 : List A) (h : Apart (v1 ++ x :: v2)) : ¬ x ∈ v1 ++ v2 := by
  intro hx
  cases mem_append_split v1 hx with
  | inl h1 =>
      exact apart_across v1 (x :: v2) h x h1 x (List.Mem.head v2) rfl
  | inr h2 =>
      have hs := apart_drop v1 (x :: v2) h
      cases hs with
      | cons hxf _ => exact hxf x h2 rfl

/-- info: 'Seed.the_apart_mark_sits_once' does not depend on any axioms -/
#guard_msgs in #print axioms the_apart_mark_sits_once

theorem the_matching_rooms_are_shuffles {A : Type u} :
    ∀ (u v : List A), Apart u → Apart v → (∀ x, x ∈ u ↔ x ∈ v) →
      u.Perm v
  | [], [], _, _, _ => .nil
  | [], y :: v, _, _, hmem => nomatch (hmem y).mpr (List.Mem.head v)
  | x :: u, v, hu, hv, hmem => by
      have hxv : x ∈ v := (hmem x).mp (List.Mem.head u)
      obtain ⟨v1, v2, hsplit⟩ := mem_splits hxv
      subst hsplit
      cases hu with
      | cons hx hurest =>
          have hmem' : ∀ y, y ∈ u ↔ y ∈ v1 ++ v2 := by
            intro y
            constructor
            · intro hy
              have hyx : y ≠ x := fun he => hx y hy he.symm
              have hyv : y ∈ v1 ++ x :: v2 :=
                (hmem y).mp (List.Mem.tail x hy)
              cases mem_append_split v1 hyv with
              | inl h1 => exact mem_append_left v2 h1
              | inr h2 =>
                  cases h2 with
                  | head => exact absurd rfl hyx
                  | tail _ h2' => exact mem_append_right v1 h2'
            · intro hy
              have hyv : y ∈ v1 ++ x :: v2 := mem_insert_middle v1 hy
              have hyu : y ∈ x :: u := (hmem y).mpr hyv
              cases hyu with
              | head => exact absurd hy (the_apart_mark_sits_once v1 v2 hv)
              | tail _ h' => exact h'
          exact (List.Perm.cons x
            (the_matching_rooms_are_shuffles u (v1 ++ v2) hurest
              (apart_removes_the_mark v1 hv) hmem')).trans
            (perm_symm (perm_middle x v1 v2))

/-- info: 'Seed.the_matching_rooms_are_shuffles' does not depend on any axioms -/
#guard_msgs in #print axioms the_matching_rooms_are_shuffles

theorem the_trade_shuffles_the_room {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (hl : Apart l) (ha : a ∈ l) (hb : b ∈ l) :
    ((perms l).map (fun p => p.map (trade beq a b))).Perm (perms l) := by
  refine the_matching_rooms_are_shuffles _ _ ?_
    (the_orders_repeat_never l hl) ?_
  · refine apart_map ?_ (the_orders_repeat_never l hl)
    intro p q hpq
    exact (the_traded_word_trades_home hE hR hab p).symm.trans
      ((congrArg (List.map (trade beq a b)) hpq).trans
        (the_traded_word_trades_home hE hR hab q))
  · intro x
    constructor
    · intro hx
      obtain ⟨p, hp, he⟩ := mem_map_back (perms l) hx
      rw [← he]
      exact the_trade_keeps_the_room hE hR hab hl ha hb hp
    · intro hx
      have h1 : x.map (trade beq a b) ∈ perms l :=
        the_trade_keeps_the_room hE hR hab hl ha hb hx
      have h2 := mem_map_intro (fun p => p.map (trade beq a b)) h1
      rw [the_traded_word_trades_home hE hR hab x] at h2
      exact h2

/-- info: 'Seed.the_trade_shuffles_the_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_trade_shuffles_the_room

def firstOf {A : Type u} (beq : A → A → Bool) (a b : A) : List A → Bool
  | [] => false
  | x :: p => cond (beq x a) true (cond (beq x b) false (firstOf beq a b p))

theorem the_traded_word_reverses_the_verdict {A : Type u}
    {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) :
    ∀ p : List A,
      firstOf beq a b (p.map (trade beq a b)) = firstOf beq b a p
  | [] => rfl
  | x :: p => by
      cases hxa : beq x a with
      | true =>
          have hx : x = a := hE x a hxa
          rw [hx]
          show firstOf beq a b
              (trade beq a b a :: p.map (trade beq a b))
            = firstOf beq b a (a :: p)
          rw [(the_trade_swaps_the_pair hE hR hab).1]
          show cond (beq b a) true
              (cond (beq b b) false
                (firstOf beq a b (p.map (trade beq a b))))
            = cond (beq a b) true
              (cond (beq a a) false (firstOf beq b a p))
          rw [beq_no hE (fun h => hab h.symm), beq_no hE hab, hR a, hR b]
          exact rfl
      | false =>
          cases hxb : beq x b with
          | true =>
              have hx : x = b := hE x b hxb
              rw [hx]
              show firstOf beq a b
                  (trade beq a b b :: p.map (trade beq a b))
                = firstOf beq b a (b :: p)
              rw [(the_trade_swaps_the_pair hE hR hab).2]
              show cond (beq a a) true
                  (cond (beq a b) false
                    (firstOf beq a b (p.map (trade beq a b))))
                = cond (beq b b) true
                  (cond (beq b a) false (firstOf beq b a p))
              rw [hR a, hR b]
              exact rfl
          | false =>
              have hxa' := ne_of_beq_no hR hxa
              have hxb' := ne_of_beq_no hR hxb
              show firstOf beq a b
                  (trade beq a b x :: p.map (trade beq a b))
                = firstOf beq b a (x :: p)
              rw [the_trade_spares_the_stranger hE hxa' hxb']
              show cond (beq x a) true
                  (cond (beq x b) false
                    (firstOf beq a b (p.map (trade beq a b))))
                = cond (beq x b) true
                  (cond (beq x a) false (firstOf beq b a p))
              rw [hxa, hxb,
                  the_traded_word_reverses_the_verdict hE hR hab p]

/-- info: 'Seed.the_traded_word_reverses_the_verdict' does not depend on any axioms -/
#guard_msgs in #print axioms the_traded_word_reverses_the_verdict

theorem the_first_voice_decides {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b) :
    ∀ p : List A, a ∈ p →
      firstOf beq a b p = !(firstOf beq b a p)
  | [], ha => nomatch ha
  | x :: p, ha => by
      cases hxa : beq x a with
      | true =>
          have hx : x = a := hE x a hxa
          show cond (beq x a) true
              (cond (beq x b) false (firstOf beq a b p))
            = !(cond (beq x b) true
                (cond (beq x a) false (firstOf beq b a p)))
          rw [hxa, hx, beq_no hE hab]
          exact rfl
      | false =>
          have hxa' := ne_of_beq_no hR hxa
          have ha' : a ∈ p := by
            cases ha with
            | head => exact absurd rfl hxa'
            | tail _ h => exact h
          cases hxb : beq x b with
          | true =>
              show cond (beq x a) true
                  (cond (beq x b) false (firstOf beq a b p))
                = !(cond (beq x b) true
                    (cond (beq x a) false (firstOf beq b a p)))
              rw [hxa, hxb]
              exact rfl
          | false =>
              show cond (beq x a) true
                  (cond (beq x b) false (firstOf beq a b p))
                = !(cond (beq x b) true
                    (cond (beq x a) false (firstOf beq b a p)))
              rw [hxa, hxb, the_first_voice_decides hE hR hab p ha']
              exact rfl

/-- info: 'Seed.the_first_voice_decides' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_voice_decides

theorem filter_congr_mem {A : Type u} (q r : A → Bool) :
    ∀ L : List A, (∀ x, x ∈ L → q x = r x) → L.filter q = L.filter r
  | [], _ => rfl
  | x :: L, h => by
      have hx := h x (List.Mem.head L)
      have hrest := filter_congr_mem q r L
        (fun y hy => h y (List.Mem.tail x hy))
      cases hq : q x with
      | true =>
          rw [List.filter_cons_of_pos hq,
              List.filter_cons_of_pos (hx.symm.trans hq), hrest]
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq),
              List.filter_cons_of_neg
                (ne_true_of_eq_false (hx.symm.trans hq)),
              hrest]

/-- info: 'Seed.filter_congr_mem' does not depend on any axioms -/
#guard_msgs in #print axioms filter_congr_mem

theorem filter_map_commutes {A : Type u} {B : Type v} (f : A → B) (q : B → Bool) :
    ∀ L : List A,
      (L.map f).filter q = (L.filter (fun x => q (f x))).map f
  | [] => rfl
  | x :: L => by
      show (f x :: L.map f).filter q
          = ((x :: L).filter (fun y => q (f y))).map f
      cases hq : q (f x) with
      | true =>
          rw [List.filter_cons_of_pos hq,
              List.filter_cons_of_pos (p := fun y => q (f y)) hq]
          show f x :: (L.map f).filter q
              = f x :: (L.filter (fun y => q (f y))).map f
          rw [filter_map_commutes f q L]
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq),
              List.filter_cons_of_neg (p := fun y => q (f y))
                (ne_true_of_eq_false hq)]
          exact filter_map_commutes f q L

/-- info: 'Seed.filter_map_commutes' does not depend on any axioms -/
#guard_msgs in #print axioms filter_map_commutes

theorem perm_filter {A : Type u} (q : A → Bool) {xs ys : List A}
    (h : xs.Perm ys) : (xs.filter q).Perm (ys.filter q) := by
  induction h with
  | nil => exact .nil
  | cons x _ ih =>
      cases hq : q x with
      | true =>
          rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos hq]
          exact .cons x ih
      | false =>
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq),
              List.filter_cons_of_neg (ne_true_of_eq_false hq)]
          exact ih
  | swap x y l =>
      cases hqx : q x with
      | true =>
          cases hqy : q y with
          | true =>
              rw [List.filter_cons_of_pos hqy,
                  List.filter_cons_of_pos hqx,
                  List.filter_cons_of_pos hqx,
                  List.filter_cons_of_pos hqy]
              exact .swap x y (l.filter q)
          | false =>
              rw [List.filter_cons_of_neg (ne_true_of_eq_false hqy),
                  List.filter_cons_of_pos hqx,
                  List.filter_cons_of_pos hqx,
                  List.filter_cons_of_neg (ne_true_of_eq_false hqy)]
      | false =>
          cases hqy : q y with
          | true =>
              rw [List.filter_cons_of_pos hqy,
                  List.filter_cons_of_neg (ne_true_of_eq_false hqx),
                  List.filter_cons_of_neg (ne_true_of_eq_false hqx),
                  List.filter_cons_of_pos hqy]
          | false =>
              rw [List.filter_cons_of_neg (ne_true_of_eq_false hqy),
                  List.filter_cons_of_neg (ne_true_of_eq_false hqx),
                  List.filter_cons_of_neg (ne_true_of_eq_false hqx),
                  List.filter_cons_of_neg (ne_true_of_eq_false hqy)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- info: 'Seed.perm_filter' does not depend on any axioms -/
#guard_msgs in #print axioms perm_filter

theorem the_filter_splits_the_room {A : Type u} (q : A → Bool) :
    ∀ L : List A,
      (L.filter q).length + (L.filter (fun x => !(q x))).length
        = L.length
  | [] => rfl
  | x :: L => by
      cases hq : q x with
      | true =>
          have hnot : (fun y => !(q y)) x = false := by
            show (!(q x)) = false
            rw [hq]
            exact rfl
          rw [List.filter_cons_of_pos hq,
              List.filter_cons_of_neg (p := fun y => !(q y))
                (ne_true_of_eq_false hnot)]
          show ((L.filter q).length + 1)
              + (L.filter (fun y => !(q y))).length
            = L.length + 1
          rw [succ_adds, the_filter_splits_the_room q L]
      | false =>
          have hnot : (fun y => !(q y)) x = true := by
            show (!(q x)) = true
            rw [hq]
            exact rfl
          rw [List.filter_cons_of_neg (ne_true_of_eq_false hq),
              List.filter_cons_of_pos (p := fun y => !(q y)) hnot]
          show ((L.filter q).length
              + (L.filter (fun y => !(q y))).length) + 1
            = L.length + 1
          rw [the_filter_splits_the_room q L]

/-- info: 'Seed.the_filter_splits_the_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_filter_splits_the_room

theorem the_two_directions_count_alike {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (hl : Apart l) (ha : a ∈ l) (hb : b ∈ l) :
    ((perms l).filter (firstOf beq a b)).length
      = ((perms l).filter (firstOf beq b a)).length := by
  have h1 : (((perms l).map (fun p => p.map (trade beq a b))).filter
      (firstOf beq a b)).length
      = ((perms l).filter (firstOf beq a b)).length :=
    perm_length (perm_filter (firstOf beq a b)
      (the_trade_shuffles_the_room hE hR hab hl ha hb))
  have h2 : ((perms l).map (fun p => p.map (trade beq a b))).filter
      (firstOf beq a b)
      = ((perms l).filter
          (fun p => firstOf beq a b (p.map (trade beq a b)))).map
          (fun p => p.map (trade beq a b)) :=
    filter_map_commutes (fun p => p.map (trade beq a b))
      (firstOf beq a b) (perms l)
  have h3 : (perms l).filter
      (fun p => firstOf beq a b (p.map (trade beq a b)))
      = (perms l).filter (firstOf beq b a) :=
    filter_congr_mem _ _ (perms l)
      (fun p _ => the_traded_word_reverses_the_verdict hE hR hab p)
  rw [← h1, h2, h3, len_map]

/-- info: 'Seed.the_two_directions_count_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_directions_count_alike

theorem the_verdicts_split_the_room {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (ha : a ∈ l) :
    ((perms l).filter (firstOf beq a b)).length
      + ((perms l).filter (firstOf beq b a)).length
      = (perms l).length := by
  have hcompl : ∀ p, p ∈ perms l →
      firstOf beq b a p = !(firstOf beq a b p) := by
    intro p hp
    have hap : a ∈ p :=
      perm_mem (perm_symm (every_order_is_a_shuffle l p hp)) a ha
    rw [the_first_voice_decides hE hR hab p hap, not_not]
  rw [filter_congr_mem (firstOf beq b a)
        (fun p => !(firstOf beq a b p)) (perms l) hcompl]
  exact the_filter_splits_the_room (firstOf beq a b) (perms l)

/-- info: 'Seed.the_verdicts_split_the_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_verdicts_split_the_room

theorem mul_two_reads_double (n : Nat) : n * 2 = n + n := by
  show (0 + n) + n = n + n
  rw [zero_add]

/-- info: 'Seed.mul_two_reads_double' does not depend on any axioms -/
#guard_msgs in #print axioms mul_two_reads_double

theorem the_direction_is_even_money {A : Type u} {beq : A → A → Bool}
    (hE : ∀ x y : A, beq x y = true → x = y)
    (hR : ∀ x : A, beq x x = true) {a b : A} (hab : a ≠ b)
    {l : List A} (hl : Apart l) (ha : a ∈ l) (hb : b ∈ l) :
    ((perms l).filter (firstOf beq a b)).length
        = ((perms l).filter (firstOf beq b a)).length
      ∧ ((perms l).filter (firstOf beq a b)).length
          + ((perms l).filter (firstOf beq b a)).length = fact l.length
      ∧ sameRatio ((perms l).filter (firstOf beq a b)).length
          (fact l.length) 1 2 := by
  have hsym := the_two_directions_count_alike hE hR hab hl ha hb
  have htotal : ((perms l).filter (firstOf beq a b)).length
      + ((perms l).filter (firstOf beq b a)).length = fact l.length :=
    (the_verdicts_split_the_room hE hR hab ha).trans
      (the_orders_count_to_the_factorial l)
  refine ⟨hsym, htotal, ?_⟩
  show ((perms l).filter (firstOf beq a b)).length * 2
      = 1 * fact l.length
  rw [mul_two_reads_double, one_scales]
  exact (congrArg (((perms l).filter (firstOf beq a b)).length + ·)
    hsym).trans htotal

/-- info: 'Seed.the_direction_is_even_money' does not depend on any axioms -/
#guard_msgs in #print axioms the_direction_is_even_money

theorem zero_plus : ∀ n : Nat, 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (zero_plus n)

/-- info: 'Seed.zero_plus' does not depend on any axioms -/
#guard_msgs in #print axioms zero_plus

def recite {P : Type v} {A : Type w} : List P → Interview P A
  | [] => .rest
  | p :: ps => .ask p (fun _ => recite ps)

theorem the_repeated_ask_hears_one_answer (F : Face) (s : F.State) (p : F.Probe) :
    ∀ n : Nat,
      sound F s (recite (List.replicate n p)) = List.replicate n (F.obs s p)
  | 0 => rfl
  | n + 1 =>
      congrArg (F.obs s p :: ·) (the_repeated_ask_hears_one_answer F s p n)

/-- info: 'Seed.the_repeated_ask_hears_one_answer' does not depend on any axioms -/
#guard_msgs in #print axioms the_repeated_ask_hears_one_answer

def restingCounter : Machine Unit Bool :=
  ⟨Nat, 0, fun n _ => n + 1, fun _ => true⟩

def hollowShell : Machine Unit Bool :=
  ⟨Unit, (), fun _ _ => (), fun _ => true⟩

theorem the_muffled_tally_is_the_resting_counter :
    revoice (fun _ => true) tally = restingCounter := rfl

/-- info: 'Seed.the_muffled_tally_is_the_resting_counter' does not depend on any axioms -/
#guard_msgs in #print axioms the_muffled_tally_is_the_resting_counter

theorem the_tally_parks_at_its_count :
    ∀ (w : List Unit) (s : Nat), park tally s w = s + w.length
  | [], _ => rfl
  | _ :: w, s => (the_tally_parks_at_its_count w (s + 1)).trans (succ_adds s w.length)

/-- info: 'Seed.the_tally_parks_at_its_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_tally_parks_at_its_count

theorem the_muffler_banks_the_run (w : List Unit) (s : Nat) :
    park restingCounter s w = s + w.length :=
  (the_revoice_moves_no_seat (fun _ => true) tally w s).trans
    (the_tally_parks_at_its_count w s)

/-- info: 'Seed.the_muffler_banks_the_run' does not depend on any axioms -/
#guard_msgs in #print axioms the_muffler_banks_the_run

theorem the_wider_voice_releases_the_bank (w : List Unit) :
    behavior tally w = w.length :=
  (the_tally_parks_at_its_count w 0).trans (zero_plus w.length)

/-- info: 'Seed.the_wider_voice_releases_the_bank' does not depend on any axioms -/
#guard_msgs in #print axioms the_wider_voice_releases_the_bank

theorem the_flywheel_and_the_shell_sound_alike (q : Interview (List Unit) Bool) :
    sound (airGap Unit Bool) restingCounter q = sound (airGap Unit Bool) hollowShell q :=
  an_audition_hears_only_the_conduct restingCounter hollowShell (fun _ => rfl) q

/-- info: 'Seed.the_flywheel_and_the_shell_sound_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_flywheel_and_the_shell_sound_alike

def selfSteered {I : Type u} {O : Type v} (m : Machine I O) (r : m.S → I) :
    Machine Unit O :=
  ⟨m.S, m.s0, fun s _ => m.step s (r s), m.out⟩

def orbit {I : Type u} {O : Type v} (m : Machine I O) (r : m.S → I) :
    m.S → Nat → m.S
  | s, 0 => s
  | s, n + 1 => orbit m r (m.step s (r s)) n

theorem the_self_steered_machine_is_a_clock {I : Type u} {O : Type v}
    (m : Machine I O) (r : m.S → I) :
    ∀ (w : List Unit) (s : m.S),
      drive (selfSteered m r) s w = m.out (orbit m r s w.length)
  | [], _ => rfl
  | _ :: w, s => the_self_steered_machine_is_a_clock m r w (m.step s (r s))

/-- info: 'Seed.the_self_steered_machine_is_a_clock' does not depend on any axioms -/
#guard_msgs in #print axioms the_self_steered_machine_is_a_clock

def selfWord {I : Type u} {O : Type v} (m : Machine I O) (r : m.S → I) :
    m.S → Nat → List I
  | _, 0 => []
  | s, n + 1 => r s :: selfWord m r (m.step s (r s)) n

theorem the_instinct_replays_its_word {I : Type u} {O : Type v}
    (m : Machine I O) (r : m.S → I) :
    ∀ (w : List Unit) (s : m.S),
      drive (selfSteered m r) s w = drive m s (selfWord m r s w.length)
  | [], _ => rfl
  | _ :: w, s => the_instinct_replays_its_word m r w (m.step s (r s))

/-- info: 'Seed.the_instinct_replays_its_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_instinct_replays_its_word

def buffered {I : Type u} {O : Type v} (m : Machine I O) : Machine I O :=
  ⟨m.S × List I, (m.s0, []), fun st i => (st.1, st.2 ++ [i]),
   fun st => drive m st.1 st.2⟩

theorem the_hold_walks_beside_the_work {I : Type u} {O : Type v}
    (m : Machine I O) (w : List I) (s : m.S) (held : List I) :
    drive (buffered m) (s, held) w = drive m (park m s held) w :=
  (congrArg m.out
    (the_intertwined_walks_agree (buffered m) m
      (fun st => park m st.1 st.2)
      (fun st i => (the_park_resumes m st.2 st.1 [i]).symm)
      w (s, held))).symm

/-- info: 'Seed.the_hold_walks_beside_the_work' does not depend on any axioms -/
#guard_msgs in #print axioms the_hold_walks_beside_the_work

theorem the_buffer_is_invisible {I : Type u} {O : Type v} (m : Machine I O)
    (w : List I) :
    behavior (buffered m) w = behavior m w :=
  the_hold_walks_beside_the_work m w m.s0 []

/-- info: 'Seed.the_buffer_is_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms the_buffer_is_invisible

def settleHeld {I : Type u} {O : Type v} (m : Machine I O)
    (st : m.S × List I) : m.S × List I :=
  (park m st.1 st.2, [])

theorem the_settle_is_unheard {I : Type u} {O : Type v} (m : Machine I O)
    (st : m.S × List I) (w : List I) :
    drive (buffered m) (settleHeld m st) w = drive (buffered m) st w :=
  (the_hold_walks_beside_the_work m w (park m st.1 st.2) []).trans
    (the_hold_walks_beside_the_work m w st.1 st.2).symm

/-- info: 'Seed.the_settle_is_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms the_settle_is_unheard

def ledger (I : Type u) : Machine I (List I) :=
  ⟨List I, [], fun rec i => rec ++ [i], fun rec => rec⟩

theorem the_ledger_parks_the_word {I : Type u} :
    ∀ (ws rec : List I), park (ledger I) rec ws = rec ++ ws
  | [], rec => (the_append_rests rec).symm
  | w :: ws, rec =>
      (the_ledger_parks_the_word ws (rec ++ [w])).trans
        (the_appends_regroup rec [w] ws)

/-- info: 'Seed.the_ledger_parks_the_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_ledger_parks_the_word

theorem every_seat_is_a_reading_of_the_record {I : Type u} {O : Type v}
    (m : Machine I O) (rec ws : List I) :
    park m m.s0 (park (ledger I) rec ws) = park m (park m m.s0 rec) ws :=
  (congrArg (park m m.s0) (the_ledger_parks_the_word ws rec)).trans
    (the_park_resumes m rec m.s0 ws)

/-- info: 'Seed.every_seat_is_a_reading_of_the_record' does not depend on any axioms -/
#guard_msgs in #print axioms every_seat_is_a_reading_of_the_record

theorem the_rep_lands_where_it_is_fed {I : Type u} {O : Type v}
    (m : Machine I O) (w v : List I) (n : Nat) (s : m.S)
    (u : List Unit) (t : Nat) (r : m.S → I) (vs : List Unit) :
    sound (airGap I O) m (recite (List.replicate n w))
        = List.replicate n (behavior m w)
      ∧ park m s (w ++ v) = park m (park m s w) v
      ∧ park tally (park tally t u) u = (t + u.length) + u.length
      ∧ drive (selfSteered m r) s vs = drive m s (selfWord m r s vs.length) :=
  ⟨the_repeated_ask_hears_one_answer (airGap I O) m w n,
   the_park_resumes m w s v,
   (the_tally_parks_at_its_count u (park tally t u)).trans
     (congrArg (· + u.length) (the_tally_parks_at_its_count u t)),
   the_instinct_replays_its_word m r vs s⟩

/-- info: 'Seed.the_rep_lands_where_it_is_fed' does not depend on any axioms -/
#guard_msgs in #print axioms the_rep_lands_where_it_is_fed

theorem the_clock_is_a_room {I : Type u} {O : Type v}
    (m : Machine I O) (r : m.S → I) (w : List Unit) (s : m.S)
    (st : m.S × List I) (v : List I) (u : List Unit) :
    drive (selfSteered m r) s w = m.out (orbit m r s w.length)
      ∧ selfSteered tally (fun _ => ()) = tally
      ∧ orbit tally (fun _ => ()) (0 : Nat) u.length = u.length
      ∧ (∀ b : Bool, park flip b [(), ()] = b)
      ∧ drive (buffered m) (settleHeld m st) v = drive (buffered m) st v
      ∧ behavior tally u = u.length :=
  ⟨the_self_steered_machine_is_a_clock m r w s,
   rfl,
   (the_self_steered_machine_is_a_clock tally (fun _ => ()) u (0 : Nat)).symm.trans
     (the_wider_voice_releases_the_bank u),
   (fun b => match b with | true => rfl | false => rfl),
   the_settle_is_unheard m st v,
   the_wider_voice_releases_the_bank u⟩

/-- info: 'Seed.the_clock_is_a_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_clock_is_a_room

def replayer {I : Type u} {O : Type v} (m : Machine I O) : Machine I O :=
  ⟨List I, [], fun rec i => rec ++ [i], fun rec => m.out (park m m.s0 rec)⟩

theorem the_replay_is_the_machine {I : Type u} {O : Type v} (m : Machine I O)
    (w : List I) :
    behavior (replayer m) w = behavior m w :=
  (congrArg m.out
    (the_intertwined_walks_agree (replayer m) m
      (fun rec => park m m.s0 rec)
      (fun rec i => (the_park_resumes m rec m.s0 [i]).symm)
      w [])).symm

/-- info: 'Seed.the_replay_is_the_machine' does not depend on any axioms -/
#guard_msgs in #print axioms the_replay_is_the_machine

end Seed
