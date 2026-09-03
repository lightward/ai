import Room
open Room

namespace Face

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

def reseat (F : Face) {S' : Type u'} (h : S' → F.State) : Face :=
  ⟨S', F.Probe, F.Ans, fun s p => F.obs (h s) p⟩

def rehear (F : Face) {Q : Type v'} (f : Q → F.Probe) : Face :=
  ⟨F.State, Q, F.Ans, fun s q => F.obs s (f q)⟩

def retell (F : Face) {B : Type w'} (g : F.Ans → B) : Face :=
  ⟨F.State, F.Probe, B, fun s p => g (F.obs s p)⟩

inductive Interview (P : Type v) (A : Type w) where
  | rest : Interview P A
  | ask  : P → (A → Interview P A) → Interview P A

def sound (F : Face) (s : F.State) : Interview F.Probe F.Ans → List F.Ans
  | .rest => []
  | .ask p k => F.obs s p :: sound F s (k (F.obs s p))

def door (H : Type u) (W : Type v) : Type (max u v) :=
  H × W

def atTheDoor {H : Type u} {W : Type v} (h : H) (w : W) : door H W :=
  (h, w)

def face {H : Type u} {W : Type v} (d : door H W) : H :=
  d.1

def met {H : Type u} {W : Type v} (d : door H W) : W :=
  d.2

def turnAbout {H : Type u} {W : Type v} (d : door H W) : door W H :=
  atTheDoor (met d) (face d)

inductive fork (P : Type v) (Q : Type v') where
  | viaLeft  : P → fork P Q
  | viaRight : Q → fork P Q

def greet {P : Type v} {Q : Type v'} {X : Type w} (f : P → X) (g : Q → X) : fork P Q → X
  | .viaLeft p => f p
  | .viaRight q => g q

def crossOver {P : Type v} {Q : Type v'} : fork P Q → fork Q P
  | .viaLeft p => .viaRight p
  | .viaRight q => .viaLeft q

def deepen {H : Type u} {W : Type v} {V : Type w} (d : door (door H W) V) :
    door H (door W V) :=
  atTheDoor (face (face d)) (atTheDoor (met (face d)) (met d))

def shallow {H : Type u} {W : Type v} {V : Type w} (d : door H (door W V)) :
    door (door H W) V :=
  atTheDoor (atTheDoor (face d) (face (met d))) (met (met d))

def distribute {H : Type u} {W : Type v} {V : Type w} (d : door H (fork W V)) :
    fork (door H W) (door H V) :=
  greet (fun w => .viaLeft (atTheDoor (face d) w)) (fun v => .viaRight (atTheDoor (face d) v))
    (met d)

def collect {H : Type u} {W : Type v} {V : Type w} : fork (door H W) (door H V) → door H (fork W V) :=
  greet (fun d => atTheDoor (face d) (.viaLeft (met d)))
        (fun d => atTheDoor (face d) (.viaRight (met d)))

def holdOpen {H : Type u} {W : Type v} {X : Type w} (g : door H W → X) : H → W → X :=
  fun h w => g (atTheDoor h w)

def walkIn {H : Type u} {W : Type v} {X : Type w} (g : H → W → X) : door H W → X :=
  fun d => g (face d) (met d)

def faceOf {H : Type u} {W : Type v} {X : Type w} (g : door H W → X) : Face :=
  ⟨H, W, X, holdOpen g⟩

def host (F : Face) (W : Type v') : Face :=
  reseat F (fun d : door F.State W => face d)

def vertical {H : Type u} {W : Type v} (σ : door H W → W) (d : door H W) : door H W :=
  atTheDoor (face d) (σ d)

def selfMeet (F : Face) (r : F.State → F.Probe) (s : F.State) : F.Ans :=
  F.obs s (r s)

def sharpen (F : Face) {X : Type w'} (r : F.State → X) : Face :=
  ⟨F.State, fork F.Probe Unit, fork F.Ans X,
   fun s => greet (fun p => .viaLeft (F.obs s p)) (fun _ => .viaRight (r s))⟩

def widen (F : Face) (W : Type v') : Face :=
  sharpen (host F W) met

def pairFace (F G : Face) {S : Type u'} (f : S → F.State) (g : S → G.State) : Face :=
  ⟨S, door F.Probe G.Probe, door F.Ans G.Ans,
   fun s pq => atTheDoor (F.obs (f s) (face pq)) (G.obs (g s) (met pq))⟩

def originFace (S' : Type u') : Face :=
  ⟨S', Unit, Unit, fun _ _ => ()⟩

def unheard (F : Face) (m : F.State → F.State) : Prop :=
  ∀ s, alike F (m s) s

def exchange {H : Type u} {W : Type v} (σ : door H W → W) (d : door H W) : door W H :=
  turnAbout (vertical σ d)

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

def retune {I : Type u} {I' : Type u'} {O : Type v} (f : I → I') (m : Machine I' O) :
    Machine I O :=
  ⟨m.S, m.s0, fun s i => m.step s (f i), m.out⟩

def revoice {I : Type u} {O : Type v} {O' : Type v'} (g : O → O') (m : Machine I O) :
    Machine I O' :=
  ⟨m.S, m.s0, m.step, fun s => g (m.out s)⟩

def tally : Machine Unit Nat :=
  ⟨Nat, 0, fun s _ => s + 1, fun s => s⟩

def flip : Machine Unit Bool :=
  ⟨Bool, false, fun s _ => !s, fun s => s⟩

def paceOne : Machine Unit Bool :=
  ⟨Nat, 0, fun s _ => s + 1, oddNat⟩

inductive Plan where
  | ground : Plan
  | board  : Plan → Plan → Plan

def fold {A : Type u} (op : A → A → A) (base : A) : Plan → A
  | .ground => base
  | .board p q => op (fold op base p) (fold op base q)

def reading : Plan → Nat :=
  fold (fun a b => a + b) 1

def graft (base : Plan) : Plan → Plan :=
  fold .board base

def build (W : Type u) : Plan → Type u :=
  fold (fun A B : Type u => door A B) W

def reground {W : Type u} {W' : Type v} (f : W → W') : (p : Plan) → build W p → build W' p
  | .ground, w => f w
  | .board p q, d => atTheDoor (reground f p (face d)) (reground f q (met d))

def pour {W : Type u} : (p : Plan) → build W p → List W
  | .ground, w => [w]
  | .board p q, d => pour p (face d) ++ pour q (met d)

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

def drain {W : Type u} (w0 : W) (p : Plan) (l : List W) : List W :=
  pour p (reboard w0 p l)

def cross : List Plan → List Plan → List Plan
  | [], _ => []
  | p :: ps, qs => qs.map (Plan.board p) ++ cross ps qs

def allPlans : Nat → List Plan
  | 0 => [.ground]
  | d + 1 => .ground :: cross (allPlans d) (allPlans d)

def census : Nat → Nat
  | 0 => 0
  | k + 1 => ((allPlans k).filter (fun p => Nat.beq (reading p) (k + 1))).length

def recite {P : Type v} {A : Type w} : List P → Interview P A
  | [] => .rest
  | p :: ps => .ask p (fun _ => recite ps)

def restingCounter : Machine Unit Bool :=
  ⟨Nat, 0, fun n _ => n + 1, fun _ => true⟩

def hollowShell : Machine Unit Bool :=
  ⟨Unit, (), fun _ _ => (), fun _ => true⟩

def selfSteered {I : Type u} {O : Type v} (m : Machine I O) (r : m.S → I) :
    Machine Unit O :=
  ⟨m.S, m.s0, fun s _ => m.step s (r s), m.out⟩

def orbit {I : Type u} {O : Type v} (m : Machine I O) (r : m.S → I) :
    m.S → Nat → m.S
  | s, 0 => s
  | s, n + 1 => orbit m r (m.step s (r s)) n

def selfWord {I : Type u} {O : Type v} (m : Machine I O) (r : m.S → I) :
    m.S → Nat → List I
  | _, 0 => []
  | s, n + 1 => r s :: selfWord m r (m.step s (r s)) n

def buffered {I : Type u} {O : Type v} (m : Machine I O) : Machine I O :=
  ⟨m.S × List I, (m.s0, []), fun st i => (st.1, st.2 ++ [i]),
   fun st => drive m st.1 st.2⟩

def settleHeld {I : Type u} {O : Type v} (m : Machine I O)
    (st : m.S × List I) : m.S × List I :=
  (park m st.1 st.2, [])

def ledger (I : Type u) : Machine I (List I) :=
  ⟨List I, [], fun rec i => rec ++ [i], fun rec => rec⟩

def replayer {I : Type u} {O : Type v} (m : Machine I O) : Machine I O :=
  ⟨List I, [], fun rec i => rec ++ [i], fun rec => m.out (park m m.s0 rec)⟩

inductive reassoc : Plan → Plan → Prop
  | here (a b c : Plan) :
      reassoc (.board (.board a b) c) (.board a (.board b c))
  | left {p q : Plan} (r : Plan) :
      reassoc p q → reassoc (.board p r) (.board q r)
  | right (r : Plan) {p q : Plan} :
      reassoc p q → reassoc (.board r p) (.board r q)

inductive chain : Nat → Plan → Plan → Prop
  | rest (p : Plan) : chain 0 p p
  | step {n : Nat} {p q r : Plan} :
      reassoc p q → chain n q r → chain (n + 1) p r

def sheet (I : Type u) (O : Type v) : Type (max u v) :=
  List I → O

def peek {I : Type u} {O : Type v} (f : sheet I O) : O :=
  f []

def feed {I : Type u} {O : Type v} (f : sheet I O) (i : I) : sheet I O :=
  fun w => f (i :: w)

def liftFrom {I : Type u} {O : Type v} (m : Machine I O) (s : m.S) : sheet I O :=
  fun w => drive m s w

def inStep {I : Type u} {O : Type v} (m : Machine I O) (h : m.S → sheet I O) : Prop :=
  (∀ s, peek (h s) = m.out s) ∧ (∀ s i, feed (h s) i = h (m.step s i))

def stream (A : Type u) : Type u :=
  Nat → A

def toStream {O : Type v} (f : sheet Unit O) : stream O :=
  fun n => f (List.replicate n ())

def toSheet {O : Type v} (g : stream O) : sheet Unit O :=
  fun w => g w.length

def streamOf {O : Type v} (m : Machine Unit O) : stream O :=
  fun n => m.out (orbit m (fun _ => ()) m.s0 n)

def Derived (F : Face) (P : F.State → Prop) : Prop :=
  ∀ s t, alike F s t → (P s ↔ P t)

def concordFace (F : Face) (V : Type v') : Face :=
  pairFace (host F V) ⟨door F.State V, Unit, V, fun x _ => met x⟩ (fun x => x) (fun x => x)

theorem no_interview_parts_the_alike (F : Face) {s t : F.State} (h : alike F s t) :
    ∀ q, sound F s q = sound F t q
  | .rest => rfl
  | .ask p k => by
      show F.obs s p :: sound F s (k (F.obs s p)) = F.obs t p :: sound F t (k (F.obs t p))
      rw [h p]
      exact congrArg (List.cons (F.obs t p))
        (no_interview_parts_the_alike F h (k (F.obs t p)))

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

theorem a_guest_blind_reading_is_a_face_reading {H : Type u} {W : Type v} {X : Type w}
    (r : door H W → X) (w0 : W) :
    (∀ h w w', r (atTheDoor h w) = r (atTheDoor h w')) ↔
    (∀ d, r d = r (atTheDoor (face d) w0)) :=
  ⟨fun hb d => hb (face d) (met d) w0,
   fun hf h w w' => (hf (atTheDoor h w)).trans (hf (atTheDoor h w')).symm⟩

theorem the_pairing_is_unique {H : Type u} {W : Type v} {X : Type w}
    (f : X → H) (g : X → W) (u : X → door H W)
    (hf : ∀ x, face (u x) = f x) (hg : ∀ x, met (u x) = g x) (x : X) :
    u x = atTheDoor (f x) (g x) :=
  (congr (congrArg atTheDoor (hf x)) (hg x) :
    atTheDoor (face (u x)) (met (u x)) = atTheDoor (f x) (g x))

theorem any_ready_greeter_is_the_greeter {P : Type v} {Q : Type v'} {X : Type w}
    (f : P → X) (g : Q → X) (h : fork P Q → X)
    (hl : ∀ p, h (.viaLeft p) = f p) (hr : ∀ q, h (.viaRight q) = g q) :
    ∀ e, h e = greet f g e := sorry

theorem the_host_serves_both_branches {H : Type u} {W : Type v} {V : Type w} :
    ∀ d : door H (fork W V), collect (distribute d) = d
  | (_, .viaLeft _) => rfl
  | (_, .viaRight _) => rfl

theorem the_sharpening_is_exact (F : Face) {X : Type w'} (r : F.State → X) (s t : F.State) :
    alike (sharpen F r) s t ↔ (alike F s t ∧ r s = r t) :=
  ⟨fun h =>
    ⟨fun p => congrArg (greet (fun a => a) (fun _ => F.obs s p)) (h (.viaLeft p)),
     congrArg (greet (fun _ => r s) (fun x => x)) (h (.viaRight ()))⟩,
   fun h q =>
    match q with
    | .viaLeft p => congrArg fork.viaLeft (h.1 p)
    | .viaRight _ => congrArg fork.viaRight h.2⟩

theorem the_widening_is_exact (F : Face) {W : Type v'} (d d' : door F.State W) :
    alike (widen F W) d d' ↔ (alike F (face d) (face d') ∧ met d = met d') :=
  ⟨fun h =>
    ⟨fun p => congrArg (greet (fun a => a) (fun _ => F.obs (face d) p)) (h (fork.viaLeft p)),
     congrArg (greet (fun _ => met d) (fun x => x)) (h (fork.viaRight ()))⟩,
   fun h q =>
    match q with
    | .viaLeft p => congrArg fork.viaLeft (h.1 p)
    | .viaRight _ => congrArg fork.viaRight h.2⟩

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

theorem the_origin_is_the_pairs_unit (F : Face) {S : Type u'} {S' : Type v'}
    (f : S → F.State) (g : S → S') (s t : S) :
    alike (pairFace F (originFace S') f g) s t ↔ alike F (f s) (f t) :=
  ⟨fun h p => congrArg face (h (atTheDoor p ())),
   fun h pq => congrArg (fun a => atTheDoor a ()) (h (face pq))⟩

theorem the_unheard_hands_compose (F : Face) (m n : F.State → F.State)
    (hm : unheard F m) (hn : unheard F n) : unheard F (fun s => m (n s)) := sorry

theorem the_yield_fixes_the_agreed {H : Type u} (d : door H H) :
    turnAbout d = d ↔ met d = face d :=
  ⟨fun h => congrArg face h,
   fun h =>
    (congr (congrArg atTheDoor h) h.symm :
      atTheDoor (met d) (face d) = atTheDoor (face d) (met d))⟩

theorem no_move_at_the_ground : ∀ {q : Plan}, ¬ reassoc .ground q :=
  fun h => nomatch h

theorem the_two_shapes_of_three :
    reassoc (.board (.board .ground .ground) .ground)
        (.board .ground (.board .ground .ground))
      ∧ reading (.board (.board .ground .ground) .ground)
          = reading (.board .ground (.board .ground .ground))
      ∧ (.board (.board .ground .ground) .ground : Plan)
          ≠ .board .ground (.board .ground .ground)
      ∧ census 3 = 2 :=
  ⟨.here .ground .ground .ground,
   rfl,
   (fun h => nomatch (Plan.board.inj h).1),
   rfl⟩

theorem the_pentagon_turns_at_four :
    chain 2 (.board (.board (.board .ground .ground) .ground) .ground)
        (.board .ground (.board .ground (.board .ground .ground)))
      ∧ chain 3 (.board (.board (.board .ground .ground) .ground) .ground)
          (.board .ground (.board .ground (.board .ground .ground))) :=
  ⟨.step (.here (.board .ground .ground) .ground .ground)
     (.step (.here .ground .ground (.board .ground .ground)) (.rest _)),
   .step (.left .ground (.here .ground .ground .ground))
     (.step (.here .ground (.board .ground .ground) .ground)
       (.step (.right .ground (.here .ground .ground .ground)) (.rest _)))⟩

theorem the_lift_is_unique {I : Type u} {O : Type v} (m : Machine I O)
    (h : m.S → sheet I O) (hf : inStep m h) :
    ∀ (w : List I) (s : m.S), h s w = liftFrom m s w
  | [], s => hf.1 s
  | i :: w, s =>
      (congrFun (hf.2 s i) w).trans
        (the_lift_is_unique m h hf w (m.step s i))

theorem a_role_read_at_a_probe_is_derived (F : Face) (p : F.Probe) (Q : F.Ans → Prop) :
    Derived F (fun s => Q (F.obs s p)) :=
  fun s t h => by
    show Q (F.obs s p) ↔ Q (F.obs t p)
    rw [h p]

theorem the_window_agrees_or_names_the_gap (F : Face)
    (beq : F.Ans → F.Ans → Bool) (s t : F.State) :
    ∀ ps : List F.Probe,
      (∀ p, p ∈ ps → beq (F.obs s p) (F.obs t p) = true)
        ∨ ∃ p, p ∈ ps ∧ beq (F.obs s p) (F.obs t p) = false
  | [] => Or.inl (fun _ hp => nomatch hp)
  | p :: ps => by
      cases hb : beq (F.obs s p) (F.obs t p) with
      | false => exact Or.inr ⟨p, List.Mem.head ps, hb⟩
      | true =>
          cases the_window_agrees_or_names_the_gap F beq s t ps with
          | inl hall =>
              refine Or.inl (fun q hq => ?_)
              cases hq with
              | head => exact hb
              | tail _ hq' => exact hall q hq'
          | inr hw =>
              obtain ⟨q, hq, hbq⟩ := hw
              exact Or.inr ⟨q, List.Mem.tail p hq, hbq⟩

theorem the_agreed_window_sounds_as_one (F : Face) (s t : F.State) :
    ∀ ps : List F.Probe, (∀ p, p ∈ ps → F.obs s p = F.obs t p) →
      sound F s (recite ps) = sound F t (recite ps)
  | [], _ => rfl
  | p :: ps, h => by
      show F.obs s p :: sound F s (recite ps) = F.obs t p :: sound F t (recite ps)
      rw [h p (List.Mem.head ps),
          the_agreed_window_sounds_as_one F s t ps (fun q hq => h q (List.Mem.tail p hq))]

theorem the_mutual_records_ride_together (F : Face.{u, v, w}) {V : Type v'} {W : Type w'}
    (mine : door F.State (door V W) → V) (yours : door F.State (door V W) → W) :
    unheard (host F (door V W)) (fun x => atTheDoor (face x) (atTheDoor (mine x) (met (met x))))
      ∧ unheard (host F (door V W)) (fun x => atTheDoor (face x) (atTheDoor (face (met x)) (yours x)))
      ∧ unheard (host F (door V W)) (fun x => atTheDoor (face x) (atTheDoor (mine x) (yours x))) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem the_records_part_the_seats (F : Face.{u, v, w}) {V : Type v'} {W : Type w'}
    (s : F.State) {v v' : V} (hv : v ≠ v') (w : W) :
    alike (host F (door V W)) (atTheDoor s (atTheDoor v w)) (atTheDoor s (atTheDoor v' w))
      ∧ atTheDoor s (atTheDoor v w) ≠ atTheDoor s (atTheDoor v' w)
      ∧ (widen F (door V W)).obs (atTheDoor s (atTheDoor v w)) (.viaRight ())
          ≠ (widen F (door V W)).obs (atTheDoor s (atTheDoor v' w)) (.viaRight ()) :=
  ⟨fun _ => rfl,
   fun he => hv (congrArg (fun y => face (met y)) he),
   fun he => hv (congrArg face (fork.viaRight.inj he))⟩

theorem no_seat_reads_the_concord_alone (F : Face) {V : Type v'}
    (p₀ : F.Probe) (s : F.State) {v v' : V} (hv : v ≠ v') :
    alike (host F V) (atTheDoor s v) (atTheDoor s v')
      ∧ ¬ alike (concordFace F V) (atTheDoor s v) (atTheDoor s v') :=
  ⟨fun _ => rfl,
   fun hal => hv (congrArg met (hal (atTheDoor p₀ ())))⟩

theorem the_concord_agrees_or_names_the_gap (F : Face) {V : Type v'}
    (beq : F.Ans → V → Bool) (x : door F.State V) :
    ∀ ps : List F.Probe,
      (∀ p, p ∈ ps → beq (F.obs (face x) p) (met x) = true)
        ∨ ∃ p, p ∈ ps ∧ beq (F.obs (face x) p) (met x) = false
  | [] => Or.inl (fun _ hp => nomatch hp)
  | p :: ps => by
      cases hb : beq (F.obs (face x) p) (met x) with
      | false => exact Or.inr ⟨p, List.Mem.head ps, hb⟩
      | true =>
          cases the_concord_agrees_or_names_the_gap F beq x ps with
          | inl hall =>
              refine Or.inl (fun r hr => ?_)
              cases hr with
              | head => exact hb
              | tail _ hr' => exact hall r hr'
          | inr hw =>
              obtain ⟨r, hr, hbr⟩ := hw
              exact Or.inr ⟨r, List.Mem.tail p hr, hbr⟩

theorem the_gap_is_minted_at_the_meeting (F : Face) {V : Type v'}
    (p₀ : F.Probe) (s : F.State) {v v' : V} (hv : v ≠ v') :
    alike (host F V) (atTheDoor s v) (atTheDoor s v')
      ∧ met ((concordFace F V).obs (atTheDoor s v) (atTheDoor p₀ ()))
          ≠ met ((concordFace F V).obs (atTheDoor s v') (atTheDoor p₀ ())) :=
  ⟨fun _ => rfl, hv⟩

theorem the_pointwise_license (P : Type v) (A : Type w) (g h : P → A) :
    alike (appFace P A) g h ↔ ∀ p, g p = h p := sorry

theorem one_face_many_seats (F : Face) :
    reseat (appFace F.Probe F.Ans) F.obs = F := sorry

theorem the_seat_map_carries_the_conduct (F : Face) (s t : F.State) :
    alike F s t ↔ alike (appFace F.Probe F.Ans) (F.obs s) (F.obs t) := sorry

theorem the_seats_stack_backward (F : Face) {S' : Type u'} {S'' : Type u''}
    (h : S' → F.State) (h' : S'' → S') :
    reseat (reseat F h) h' = reseat F (fun s => h (h' s)) := sorry

theorem the_ear_and_the_voice_commute (F : Face) {Q : Type v'} {B : Type w'}
    (f : Q → F.Probe) (g : F.Ans → B) :
    rehear (retell F g) f = retell (rehear F f) g := sorry

theorem the_ear_crosses_the_seat (F : Face) {S' : Type u'} {Q : Type v'}
    (h : S' → F.State) (f : Q → F.Probe) :
    rehear (reseat F h) f = reseat (rehear F f) h := sorry

theorem the_voice_crosses_the_seat (F : Face) {S' : Type u'} {B : Type w'}
    (h : S' → F.State) (g : F.Ans → B) :
    retell (reseat F h) g = reseat (retell F g) h := sorry

theorem the_carrier_was_a_seating {S : Type u} {T : Type u'} {P : Type v} {A : Type w}
    (f : S → P → A) (g : T → P → A) (h : S → T) :
    carries f g h ↔ ∀ s, alike (appFace P A) (g (h s)) (f s) := sorry

theorem the_obs_carries_to_the_one_face (F : Face) :
    carries F.obs (fun g p => g p) F.obs := sorry

theorem no_face_reads_the_guest {H : Type u} {W : Type v} {X : Type w}
    (g : H → X) (h : H) (w w' : W) :
    g (face (atTheDoor h w)) = g (face (atTheDoor h w')) := sorry

theorem the_guest_is_real {H : Type u} {W : Type v} (h : H) (w : W) :
    met (atTheDoor h w) = w := sorry

theorem the_turn_returns {H : Type u} {W : Type v} (d : door H W) :
    turnAbout (turnAbout d) = d := sorry

theorem the_crossing_returns {P : Type v} {Q : Type v'} :
    ∀ e : fork P Q, crossOver (crossOver e) = e := sorry

theorem hosting_associates {H : Type u} {W : Type v} {V : Type w} (d : door (door H W) V) :
    shallow (deepen d) = d := sorry

theorem hosting_associates_back {H : Type u} {W : Type v} {V : Type w} (d : door H (door W V)) :
    deepen (shallow d) = d := sorry

theorem the_branches_come_home {H : Type u} {W : Type v} {V : Type w} :
    ∀ e : fork (door H W) (door H V), distribute (collect e) = e := sorry

theorem the_deferral_is_free {H : Type u} {W : Type v} {X : Type w}
    (g : door H W → X) (d : door H W) :
    walkIn (holdOpen g) d = g d := sorry

theorem the_holding_returns {H : Type u} {W : Type v} {X : Type w}
    (g : H → W → X) (h : H) (w : W) :
    holdOpen (walkIn g) h w = g h w := sorry

theorem the_face_was_a_held_door (F : Face) : faceOf (walkIn F.obs) = F := sorry

theorem every_door_reading_is_a_face {H : Type u} {W : Type v} {X : Type w}
    (g : door H W → X) (d : door H W) :
    walkIn (faceOf g).obs d = g d := sorry

theorem the_measurement_is_a_meeting (F : Face) (s : F.State) (p : F.Probe) :
    F.obs s p = walkIn F.obs (atTheDoor s p) := sorry

theorem the_host_was_a_reseat (F : Face) (W : Type v') :
    host F W = reseat F (fun d : door F.State W => face d) := sorry

theorem the_host_merges_the_guests (F : Face) (W : Type v') (s : F.State) (w w' : W) :
    alike (host F W) (atTheDoor s w) (atTheDoor s w') := sorry

theorem the_probe_boards_as_the_guest (F : Face) (s : F.State) (p : F.Probe) :
    selfMeet (host F F.Probe) met (atTheDoor s p) = F.obs s p := sorry

theorem the_meeting_was_a_self_meeting {H : Type u} {W : Type v} {X : Type w}
    (g : door H W → X) (d : door H W) :
    selfMeet (host (faceOf g) W) met d = g d := sorry

theorem the_self_meeting_reads_the_guest (F : Face) {W : Type v'}
    (r : W → F.Probe) (s : F.State) (w : W) :
    selfMeet (host F W) (fun d => r (met d)) (atTheDoor s w) = F.obs s (r w) := sorry

theorem a_guest_mover_is_unheard (F : Face) {W : Type v'} (σ : door F.State W → W)
    (d : door F.State W) : alike (host F W) (vertical σ d) d := sorry

theorem the_origin_merges_every_seat {S' : Type u'} (s t : S') :
    alike (originFace S') s t := sorry

theorem the_still_hand_is_unheard (F : Face) : unheard F (fun s => s) := sorry

theorem the_maintenance_is_the_identitys_hom (F : Face) (m : F.State → F.State) :
    unheard F m ↔ carries F.obs F.obs m := sorry

theorem the_spoken_arrives_at_the_face {H : Type u} {W : Type v}
    (σ : door H W → W) (d : door H W) : face (exchange σ d) = σ d := sorry

theorem the_speaker_rides_unread {H : Type u} {W : Type v}
    (σ : door H W → W) (d : door H W) : met (exchange σ d) = face d := sorry

theorem the_listening_turn_is_the_yield {H : Type u} {W : Type v} (d : door H W) :
    exchange met d = turnAbout d := sorry

theorem the_two_listeners_restore_the_table {H : Type u} {W : Type v} (d : door H W) :
    exchange met (exchange met d) = d := sorry

theorem the_ode_comes_home {H : Type u} {W : Type v} (σ : door H W → W) (d : door H W) :
    exchange met (exchange σ d) = vertical σ d := sorry

theorem the_air_gap_wears_the_one_face (I : Type u) (O : Type v) :
    airGap.{u, v, w} I O
      = reseat (appFace (List I) O) (fun m : Machine.{u, v, w} I O => behavior m) := sorry

theorem the_park_resumes {I : Type u} {O : Type v} (m : Machine I O) :
    ∀ (u : List I) (s : m.S) (v : List I),
      park m s (u ++ v) = park m (park m s u) v := sorry

theorem the_retuned_seat_walks_the_translated_word {I : Type u} {I' : Type u'} {O : Type v}
    (f : I → I') (m : Machine I' O) :
    ∀ (w : List I) (s : m.S), park (retune f m) s w = park m s (w.map f) := sorry

theorem the_revoice_moves_no_seat {I : Type u} {O : Type v} {O' : Type v'}
    (g : O → O') (m : Machine I O) :
    ∀ (w : List I) (s : m.S), park (revoice g m) s w = park m s w := sorry

theorem the_intertwined_walks_agree {I : Type u} {O : Type v} (m n : Machine I O)
    (h : m.S → n.S) (hstep : ∀ s i, n.step (h s) i = h (m.step s i)) :
    ∀ (w : List I) (s : m.S), park n (h s) w = h (park m s w) := sorry

theorem the_pace_wears_the_tallys_voice : paceOne = revoice oddNat tally := sorry

theorem any_two_readings_agree {A : Type u} (op : A → A → A) (base : A) (h : Plan → A)
    (hg : h .ground = base) (hb : ∀ p q, h (.board p q) = op (h p) (h q)) :
    ∀ p, h p = fold op base p := sorry

theorem the_revision_is_a_reading (base : Plan) : graft base = fold .board base := sorry

theorem the_trivial_revision_changes_nothing (t : Plan) : graft t .ground = t := sorry

theorem the_parent_folds_into_the_ground {A : Type u} (op : A → A → A) (base : A) (t : Plan) :
    ∀ δ, fold op (fold op base t) δ = fold op base (graft t δ) := sorry

theorem the_type_is_a_reading (W : Type u) (p : Plan) :
    build W p = fold (fun A B : Type u => door A B) W p := sorry

theorem the_customs_keep_the_still_world {W : Type u} :
    ∀ (p : Plan) (x : build W p), reground (fun w => w) p x = x := sorry

theorem the_customs_stack_forward {W : Type u} {W' : Type v} {W'' : Type w}
    (f : W → W') (g : W' → W'') :
    ∀ (p : Plan) (x : build W p),
      reground g p (reground f p x) = reground (fun w => g (f w)) p x := sorry

theorem the_census_checksums_with_the_polygon_cutters :
    census 1 = 1 ∧ census 2 = 1 ∧ census 3 = 2 ∧ census 4 = 5
      ∧ census 5 = 14 := sorry

theorem the_repeated_ask_hears_one_answer (F : Face) (s : F.State) (p : F.Probe) :
    ∀ n : Nat,
      sound F s (recite (List.replicate n p)) = List.replicate n (F.obs s p) := sorry

theorem the_muffled_tally_is_the_resting_counter :
    revoice (fun _ => true) tally = restingCounter := sorry

theorem the_self_steered_machine_is_a_clock {I : Type u} {O : Type v}
    (m : Machine I O) (r : m.S → I) :
    ∀ (w : List Unit) (s : m.S),
      drive (selfSteered m r) s w = m.out (orbit m r s w.length) := sorry

theorem the_instinct_replays_its_word {I : Type u} {O : Type v}
    (m : Machine I O) (r : m.S → I) :
    ∀ (w : List Unit) (s : m.S),
      drive (selfSteered m r) s w = drive m s (selfWord m r s w.length) := sorry

theorem the_lift_peeks_the_out {I : Type u} {O : Type v} (m : Machine I O) (s : m.S) :
    peek (liftFrom m s) = m.out s := sorry

theorem the_lift_feeds_the_step {I : Type u} {O : Type v} (m : Machine I O)
    (s : m.S) (i : I) :
    feed (liftFrom m s) i = liftFrom m (m.step s i) := sorry

theorem the_unit_machine_steers_itself {O : Type v} (m : Machine Unit O) :
    selfSteered m (fun _ => ()) = m := sorry

theorem the_comparison_mints_a_face (F G : Face) {S : Type u'}
    (f : S → F.State) (g : S → G.State) {X : Type w'}
    (c : F.Ans → G.Ans → X) (s : S) (p : F.Probe) (q : G.Probe) :
    c (F.obs (f s) p) (G.obs (g s) q)
      = walkIn c ((pairFace F G f g).obs s (atTheDoor p q)) := sorry

theorem the_concord_reads_both_models (F : Face) {V : Type v'}
    (x : door F.State V) (p : F.Probe) :
    (concordFace F V).obs x (atTheDoor p ()) = atTheDoor (F.obs (face x) p) (met x) := sorry

theorem the_interview_crosses_the_seat (F : Face) {S' : Type u'} (h : S' → F.State) (s : S') :
    ∀ q, sound F (h s) q = sound (reseat F h) s q := sorry

theorem no_interview_parts_the_origin {S' : Type u'} (s t : S') :
    ∀ q, sound (originFace S') s q = sound (originFace S') t q := sorry

theorem the_record_writes_where_the_face_is_blind (F : Face.{u, v, w}) {W : Type v'}
    (keep : door F.State W → W) :
    unheard (host F W) (fun x => atTheDoor (face x) (keep x)) := sorry

theorem the_sounding_reads_the_alike (F : Face) {s t : F.State}
    (h : ∀ q, sound F s q = sound F t q) : alike F s t :=
  fun p =>
    the_first_mark_reads
      (show F.obs s p :: [] = F.obs t p :: [] from h (.ask p fun _ => .rest))

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

theorem mem_cross {qs : List Plan} {r : Plan} (hr : r ∈ qs) :
    ∀ {ps : List Plan} {l : Plan}, l ∈ ps → Plan.board l r ∈ cross ps qs
  | _ :: ps, _, List.Mem.head _ =>
      mem_append_left (cross ps qs) (mem_map_intro (Plan.board _) hr)
  | p :: _, _, List.Mem.tail _ h =>
      mem_append_right (qs.map (Plan.board p)) (mem_cross hr h)

theorem the_ledger_parks_the_word {I : Type u} :
    ∀ (ws rec : List I), park (ledger I) rec ws = rec ++ ws := sorry

theorem the_round_trips_come_home {O : Type v} (f : sheet Unit O) (g : stream O)
    (w : List Unit) (n : Nat) :
    toSheet (toStream f) w = f w ∧ toStream (toSheet g) n = g n :=
  ⟨congrArg f (the_unit_word_is_its_count w),
   congrArg g (len_replicate () n)⟩

theorem the_manifest_is_natural {W : Type u} {W' : Type v} (f : W → W') :
    ∀ (p : Plan) (x : build W p), pour p (reground f p x) = (pour p x).map f := sorry

theorem the_held_scale_rides (c : Nat) :
    ∀ p : Plan, fold (fun a b => a + b) c p = c * reading p
  | .ground => (mul_one_reads c).symm
  | .board a b =>
      ((congr (congrArg (fun x y => x + y) (the_held_scale_rides c a))
          (the_held_scale_rides c b) :
          fold (fun x y => x + y) c a + fold (fun x y => x + y) c b
            = c * reading a + c * reading b)).trans
        (mul_spreads c (reading a) (reading b)).symm

theorem the_reading_is_positive :
    ∀ p : Plan, ∃ m : Nat, reading p = m + 1
  | .ground => ⟨0, rfl⟩
  | .board l r =>
      match the_reading_is_positive l with
      | ⟨a, ha⟩ =>
          ⟨a + reading r, by
            show reading l + reading r = (a + reading r) + 1
            rw [ha, succ_adds]⟩

theorem the_manifest_counts {W : Type u} :
    ∀ (p : Plan) (x : build W p), (pour p x).length = reading p := sorry

theorem the_tally_parks_at_its_count :
    ∀ (w : List Unit) (s : Nat), park tally s w = s + w.length := sorry

theorem a_wider_seat_reads_the_remainder (F : Face) {W : Type v'}
    (s : F.State) {w w' : W} (hw : w ≠ w') :
    ¬ alike (widen F W) (atTheDoor s w) (atTheDoor s w') :=
  fun h => hw (((the_widening_is_exact F (atTheDoor s w) (atTheDoor s w')).mp h).2)

theorem no_interview_hears_the_unheard (F : Face) (m : F.State → F.State)
    (h : unheard F m) : ∀ s q, sound F (m s) q = sound F s q := sorry

theorem the_intertwiner_carries_the_walk {I : Type u} {O : Type v} (m n : Machine I O)
    (h : m.S → n.S) (hstep : ∀ s i, n.step (h s) i = h (m.step s i))
    (hout : ∀ s, n.out (h s) = m.out s) :
    carries (fun s w => drive m s w) (fun s w => drive n s w) h :=
  fun s w =>
    (congrArg n.out (the_intertwined_walks_agree m n h hstep w s)).trans
      (hout (park m s w))

theorem a_stage_may_ground_a_stage (W : Type u) (t δ : Plan) :
    build W (graft t δ) = build (build W t) δ := sorry

theorem the_hold_walks_beside_the_work {I : Type u} {O : Type v}
    (m : Machine I O) (w : List I) (s : m.S) (held : List I) :
    drive (buffered m) (s, held) w = drive m (park m s held) w :=
  (congrArg m.out
    (the_intertwined_walks_agree (buffered m) m
      (fun st => park m st.1 st.2)
      (fun st i => (the_park_resumes m st.2 st.1 [i]).symm)
      w (s, held))).symm

theorem the_replay_is_the_machine {I : Type u} {O : Type v} (m : Machine I O)
    (w : List I) :
    behavior (replayer m) w = behavior m w :=
  (congrArg m.out
    (the_intertwined_walks_agree (replayer m) m
      (fun rec => park m m.s0 rec)
      (fun rec i => (the_park_resumes m rec m.s0 [i]).symm)
      w [])).symm

theorem no_move_at_the_mirror :
    ∀ {q : Plan}, ¬ reassoc (.board .ground .ground) q := by
  intro q h
  cases h with
  | left r h' => exact no_move_at_the_ground h'
  | right r h' => exact no_move_at_the_ground h'

theorem the_clocks_lift_is_a_stream {O : Type v} (m : Machine Unit O) (n : Nat) :
    streamOf m n = toStream (liftFrom m m.s0) n :=
  ((congrArg (fun k => m.out (orbit m (fun _ => ()) m.s0 k))
      (len_replicate () n)).symm).trans
    ((the_self_steered_machine_is_a_clock m (fun _ => ())
        (List.replicate n ()) m.s0).symm)

theorem every_widening_is_one_pairing (F G H : Face) {S : Type u'}
    (f : S → F.State) (g : S → G.State) (h : S → H.State)
    (p0 : F.Probe) (q0 : G.Probe) (r0 : H.Probe) (s t : S) :
    alike (pairFace (pairFace F G f g) H (fun x => x) h) s t
      ↔ alike (pairFace F (pairFace G H g h) f (fun x => x)) s t :=
  (the_pairing_is_exact (pairFace F G f g) H (fun x => x) h
      (atTheDoor p0 q0) r0 s t).trans
    ((and_congr_first (the_pairing_is_exact F G f g p0 q0 s t)).trans
      (and_regroups.trans
        ((and_congr_second (the_pairing_is_exact G H g h q0 r0 s t)).symm.trans
          (the_pairing_is_exact F (pairFace G H g h) f (fun x => x)
            p0 (atTheDoor q0 r0) s t).symm)))

theorem the_meeting_mints_the_concord (F : Face) {V : Type v'}
    (agree : F.Ans → V → Prop) (p : F.Probe) :
    Derived (concordFace F V)
      (fun x => agree (face ((concordFace F V).obs x (atTheDoor p ())))
        (met ((concordFace F V).obs x (atTheDoor p ())))) :=
  a_role_read_at_a_probe_is_derived (concordFace F V) (atTheDoor p ())
    (fun a => agree (face a) (met a))

theorem an_audition_hears_only_the_conduct {I : Type u} {O : Type v} (m n : Machine I O)
    (h : ∀ w, behavior m w = behavior n w) :
    ∀ q, sound (airGap I O) m q = sound (airGap I O) n q := sorry

theorem lineages_compose (t d1 d2 : Plan) :
    graft (graft t d1) d2 = graft t (graft d1 d2) := sorry

theorem the_manifest_rebuilds_the_carrier {W : Type u} (w0 : W) (p : Plan) (x : build W p) :
    reboard w0 p (pour p x) = x :=
  congrArg Prod.fst
    ((congrArg (reboardAux w0 p) (the_append_rests (pour p x)).symm).trans
      (the_guests_reboard_in_order w0 p x []))

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

theorem every_seat_is_a_reading_of_the_record {I : Type u} {O : Type v}
    (m : Machine I O) (rec ws : List I) :
    park m m.s0 (park (ledger I) rec ws) = park m (park m m.s0 rec) ws :=
  (congrArg (park m m.s0) (the_ledger_parks_the_word ws rec)).trans
    (the_park_resumes m rec m.s0 ws)

theorem the_curtain_is_exact (F : Face) (s t : F.State) :
    alike F s t ↔ ∀ q, sound F s q = sound F t q := sorry

theorem the_audition_is_exact {I : Type u} {O : Type v} (m n : Machine I O) :
    alike (airGap I O) m n ↔ ∀ q, sound (airGap I O) m q = sound (airGap I O) n q := sorry

theorem the_revision_multiplies_the_reading (t δ : Plan) :
    reading (graft t δ) = reading t * reading δ :=
  (the_parent_folds_into_the_ground (fun a b => a + b) 1 t δ).symm.trans
    (the_held_scale_rides (reading t) δ)

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

theorem the_muffler_banks_the_run (w : List Unit) (s : Nat) :
    park restingCounter s w = s + w.length :=
  (the_revoice_moves_no_seat (fun _ => true) tally w s).trans
    (the_tally_parks_at_its_count w s)

theorem the_wider_voice_releases_the_bank (w : List Unit) :
    behavior tally w = w.length := sorry

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

theorem the_drained_is_on_spec {W : Type u} (w0 : W) (p : Plan) (l : List W) :
    (drain w0 p l).length = reading p := sorry

theorem recording_the_recording_grounds (F : Face.{u, v, w}) {W : Type v'}
    (keep : door F.State W → W) (x : door F.State W) (q : Interview F.Probe F.Ans) :
    sound (host F W) (atTheDoor (face x) (keep x)) q = sound (host F W) x q
      ∧ sound (host F W) (atTheDoor (face x) (keep (atTheDoor (face x) (keep x)))) q
          = sound (host F W) x q := sorry

theorem the_mutual_recording_is_unheard (F : Face.{u, v, w}) {V : Type v'} {W : Type w'}
    (mine : door F.State (door V W) → V) (yours : door F.State (door V W) → W)
    (x : door F.State (door V W)) (q : Interview F.Probe F.Ans) :
    sound (host F (door V W)) (atTheDoor (face x) (atTheDoor (mine x) (yours x))) q
      = sound (host F (door V W)) x q := sorry

theorem the_settled_gap_moves_the_model (F : Face) {V : Type v'}
    (fix : door F.State V → V) (x : door F.State V)
    (q : Interview F.Probe F.Ans) (p : F.Probe) :
    sound (host F V) (atTheDoor (face x) (fix x)) q = sound (host F V) x q
      ∧ (concordFace F V).obs (atTheDoor (face x) (fix x)) (atTheDoor p ())
          = atTheDoor (F.obs (face x) p) (fix x) := sorry

theorem two_seats_record_each_other (F : Face.{u, v, w}) {V : Type v'} {W : Type w'}
    (mine : door F.State (door V W) → V) (yours : door F.State (door V W) → W)
    (x : door F.State (door V W)) (q : Interview F.Probe F.Ans)
    (s : F.State) {v v' : V} (hv : v ≠ v') (w : W) :
    unheard (host F (door V W)) (fun y => atTheDoor (face y) (atTheDoor (mine y) (yours y)))
      ∧ sound (host F (door V W)) (atTheDoor (face x) (atTheDoor (mine x) (yours x))) q
          = sound (host F (door V W)) x q
      ∧ alike (host F (door V W)) (atTheDoor s (atTheDoor v w)) (atTheDoor s (atTheDoor v' w))
      ∧ atTheDoor s (atTheDoor v w) ≠ atTheDoor s (atTheDoor v' w)
      ∧ (widen F (door V W)).obs (atTheDoor s (atTheDoor v w)) (.viaRight ())
          ≠ (widen F (door V W)).obs (atTheDoor s (atTheDoor v' w)) (.viaRight ()) := sorry

theorem the_handshake :
    (∀ (F : Face) (s t : F.State), alike F s t → ∀ q, sound F s q = sound F t q) ∧
    (∀ (F : Face) (W : Type v') (s : F.State) (w w' : W),
      (∀ q, sound (host F W) (atTheDoor s w) q = sound (host F W) (atTheDoor s w') q) ∧
      (w ≠ w' → ¬ alike (widen F W) (atTheDoor s w) (atTheDoor s w'))) :=
  ⟨fun F _ _ h => no_interview_parts_the_alike F h,
   fun F W s w w' =>
    ⟨no_interview_parts_the_alike (host F W) (the_host_merges_the_guests F W s w w'),
     fun hw => a_wider_seat_reads_the_remainder F s hw⟩⟩

theorem only_the_unheard_survives_the_sounding (F : Face) (m : F.State → F.State) :
    unheard F m ↔ ∀ s q, sound F (m s) q = sound F s q :=
  ⟨no_interview_hears_the_unheard F m,
   fun h s => the_sounding_reads_the_alike F (h s)⟩

theorem correct_maintenance_has_no_signature (F : Face) (m n : F.State → F.State)
    (hm : unheard F m) (hn : unheard F n) :
    ∀ s q, sound F (m s) q = sound F (n s) q :=
  fun s q => (no_interview_hears_the_unheard F m hm s q).trans
    (no_interview_hears_the_unheard F n hn s q).symm

theorem the_pace_is_carried_onto_the_flip :
    carries (fun s w => drive paceOne s w) (fun s w => drive flip s w) oddNat :=
  the_intertwiner_carries_the_walk paceOne flip oddNat (fun _ _ => rfl) (fun _ => rfl)

theorem the_flywheel_and_the_shell_sound_alike (q : Interview (List Unit) Bool) :
    sound (airGap Unit Bool) restingCounter q = sound (airGap Unit Bool) hollowShell q :=
  an_audition_hears_only_the_conduct restingCounter hollowShell (fun _ => rfl) q

theorem the_settle_is_unheard {I : Type u} {O : Type v} (m : Machine I O)
    (st : m.S × List I) (w : List I) :
    drive (buffered m) (settleHeld m st) w = drive (buffered m) st w :=
  (the_hold_walks_beside_the_work m w (park m st.1 st.2) []).trans
    (the_hold_walks_beside_the_work m w st.1 st.2).symm

theorem no_move_past_the_right_comb :
    ∀ {q : Plan}, ¬ reassoc (.board .ground (.board .ground .ground)) q := by
  intro q h
  cases h with
  | left r h' => exact no_move_at_the_ground h'
  | right r h' => exact no_move_at_the_mirror h'

theorem the_left_comb_moves_once :
    ∀ {q : Plan}, reassoc (.board (.board .ground .ground) .ground) q
      → q = .board .ground (.board .ground .ground) := by
  intro q h
  cases h with
  | here a b c => rfl
  | left r h' => exact absurd h' no_move_at_the_mirror
  | right r h' => exact absurd h' no_move_at_the_ground

theorem the_buffer_is_invisible {I : Type u} {O : Type v} (m : Machine I O)
    (w : List I) :
    behavior (buffered m) w = behavior m w := sorry

theorem the_drain_settles {W : Type u} (w0 : W) (p : Plan) (l : List W) :
    drain w0 p (drain w0 p l) = drain w0 p l :=
  congrArg (pour p) (the_manifest_rebuilds_the_carrier w0 p (reboard w0 p l))

theorem the_room_repeats_no_plan : ∀ d : Nat, Apart (allPlans d)
  | 0 => Apart.cons (fun _ hb => nomatch hb) Apart.nil
  | d + 1 =>
      Apart.cons
        (fun _ hb =>
          match mem_cross_split (allPlans d) hb with
          | ⟨_, _, he, _, _⟩ => fun hg => nomatch hg.trans he)
        (the_cross_keeps_apart (the_room_repeats_no_plan d)
          (the_room_repeats_no_plan d))

theorem the_lift_is_the_conduct {I : Type u} {O : Type v} (m n : Machine I O)
    (f g : sheet I O) :
    (∀ s, peek (liftFrom m s) = m.out s)
      ∧ (∀ s i, feed (liftFrom m s) i = liftFrom m (m.step s i))
      ∧ (∀ (h : m.S → sheet I O),
          (∀ s, peek (h s) = m.out s) →
          (∀ s i, feed (h s) i = h (m.step s i)) →
          ∀ (w : List I) (s : m.S), h s w = liftFrom m s w)
      ∧ liftFrom m m.s0 = behavior m
      ∧ (alike (airGap I O) m n ↔ ∀ q, sound (airGap I O) m q = sound (airGap I O) n q)
      ∧ (alike (appFace (List I) O) f g ↔ ∀ w, f w = g w) :=
  ⟨fun _ => rfl,
   fun _ _ => rfl,
   fun h hp hf => the_lift_is_unique m h ⟨hp, hf⟩,
   rfl,
   the_audition_is_exact m n,
   the_pointwise_license (List I) O f g⟩

theorem the_tallys_stream_counts (n : Nat) :
    streamOf tally n = n :=
  (the_clocks_lift_is_a_stream tally n).trans
    ((the_wider_voice_releases_the_bank (List.replicate n ())).trans
      (len_replicate () n))

theorem the_concord_is_the_meetings_own (F : Face) {V : Type v'}
    (agree : F.Ans → V → Prop) (beq : F.Ans → V → Bool) (p : F.Probe)
    (s : F.State) {v v' : V} (hv : v ≠ v')
    (fix : door F.State V → V) (x : door F.State V)
    (q : Interview F.Probe F.Ans) (ps : List F.Probe) :
    Derived (concordFace F V)
        (fun y => agree (face ((concordFace F V).obs y (atTheDoor p ())))
          (met ((concordFace F V).obs y (atTheDoor p ()))))
      ∧ alike (host F V) (atTheDoor s v) (atTheDoor s v')
      ∧ ¬ alike (concordFace F V) (atTheDoor s v) (atTheDoor s v')
      ∧ ((∀ r, r ∈ ps → beq (F.obs (face x) r) (met x) = true)
          ∨ ∃ r, r ∈ ps ∧ beq (F.obs (face x) r) (met x) = false)
      ∧ sound (host F V) (atTheDoor (face x) (fix x)) q = sound (host F V) x q
      ∧ (concordFace F V).obs (atTheDoor (face x) (fix x)) (atTheDoor p ())
          = atTheDoor (F.obs (face x) p) (fix x) :=
  ⟨the_meeting_mints_the_concord F agree p,
   (no_seat_reads_the_concord_alone F p s hv).1,
   (no_seat_reads_the_concord_alone F p s hv).2,
   the_concord_agrees_or_names_the_gap F beq x ps,
   (the_settled_gap_moves_the_model F fix x q p).1,
   (the_settled_gap_moves_the_model F fix x q p).2⟩

theorem the_right_comb_rests :
    ∀ {n : Nat} {q : Plan},
      chain n (.board .ground (.board .ground .ground)) q
        → q = .board .ground (.board .ground .ground) := by
  intro n q h
  cases h with
  | rest => rfl
  | step h1 h2 => exact absurd h1 no_move_past_the_right_comb

theorem the_right_loop_reads_zero :
    ∀ {k : Nat}, chain k (.board .ground (.board .ground .ground))
        (.board .ground (.board .ground .ground)) → k = 0 := by
  intro k h
  cases h with
  | rest => rfl
  | step h1 h2 => exact absurd h1 no_move_past_the_right_comb

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

theorem the_clock_is_a_room {I : Type u} {O : Type v}
    (m : Machine I O) (r : m.S → I) (w : List Unit) (s : m.S)
    (st : m.S × List I) (v : List I) (u : List Unit) :
    drive (selfSteered m r) s w = m.out (orbit m r s w.length)
      ∧ selfSteered tally (fun _ => ()) = tally
      ∧ orbit tally (fun _ => ()) (0 : Nat) u.length = u.length
      ∧ (∀ b : Bool, park flip b [(), ()] = b)
      ∧ drive (buffered m) (settleHeld m st) v = drive (buffered m) st v
      ∧ behavior tally u = u.length := sorry

theorem room_margin_flywheel_door {I : Type u} {O : Type v} {A : Type w}
    (m : Machine I O) (r : m.S → I) (u : List Unit) (s : m.S)
    (st : m.S × List I) (v : List I) (q : Interview (List Unit) Bool)
    (beq : A → A → Bool) (hrefl : ∀ y : A, beq y y = true)
    (x : A) (st' : List A × List (A × List A)) (word : List (A × List A))
    (hall needs : List A)
    (F : Face) {W : Type v'} (g : F.State) {w1 w2 : W} (hw : w1 ≠ w2) :
    drive (selfSteered m r) s u = m.out (orbit m r s u.length)
      ∧ drive (buffered m) (settleHeld m st) v = drive (buffered m) st v
      ∧ sound (airGap Unit Bool) restingCounter q = sound (airGap Unit Bool) hollowShell q
      ∧ (∀ tw : List Unit, behavior tally tw = tw.length)
      ∧ (enrolled beq st'.1 x = false →
          (∀ arr, arr ∈ word → beq arr.1 x = true → x ∈ arr.2) →
          enrolled beq (intake beq st' word).1 x = false)
      ∧ (lacking beq hall needs = 1 →
          ∃ k, k ∈ needs ∧ enrolled beq hall k = false ∧
            backed beq (k :: hall) needs = true)
      ∧ ¬ alike (widen F W) (atTheDoor g w1) (atTheDoor g w2) := sorry

theorem the_clock_writes_its_sequence {O : Type v} (m m' : Machine Unit O)
    (f : sheet Unit O) (g : stream O) (w : List Unit) (n : Nat) :
    streamOf m n = toStream (liftFrom m m.s0) n
      ∧ toSheet (toStream f) w = f w
      ∧ toStream (toSheet g) n = g n
      ∧ streamOf tally n = n
      ∧ (alike (airGap Unit O) m m' ↔
          ∀ q, sound (airGap Unit O) m q = sound (airGap Unit O) m' q) := sorry

theorem the_left_loop_reads_zero :
    ∀ {k : Nat}, chain k (.board (.board .ground .ground) .ground)
        (.board (.board .ground .ground) .ground) → k = 0 := by
  intro k h
  cases h with
  | rest => rfl
  | @step m p q r h1 h2 =>
    have he : q = .board .ground (.board .ground .ground) :=
      the_left_comb_moves_once h1
    have h2' : chain m (.board .ground (.board .ground .ground))
        (.board (.board .ground .ground) .ground) := he ▸ h2
    exact nomatch (Plan.board.inj (the_right_comb_rests h2').symm).1

theorem three_has_no_loop (n : Nat) :
    ¬ chain (n + 1) (.board (.board .ground .ground) .ground)
        (.board (.board .ground .ground) .ground)
      ∧ ¬ chain (n + 1) (.board .ground (.board .ground .ground))
          (.board .ground (.board .ground .ground)) :=
  ⟨(fun h => nomatch (the_left_loop_reads_zero h)),
   (fun h => nomatch (the_right_loop_reads_zero h))⟩

theorem entanglement_is_the_loop (n : Nat) :
    (reassoc (.board (.board .ground .ground) .ground)
        (.board .ground (.board .ground .ground))
      ∧ census 3 = 2)
      ∧ (¬ chain (n + 1) (.board (.board .ground .ground) .ground)
            (.board (.board .ground .ground) .ground))
      ∧ chain 2 (.board (.board (.board .ground .ground) .ground) .ground)
          (.board .ground (.board .ground (.board .ground .ground)))
      ∧ chain 3 (.board (.board (.board .ground .ground) .ground) .ground)
          (.board .ground (.board .ground (.board .ground .ground)))
      ∧ (2 : Nat) ≠ 3
      ∧ reading (.board (.board (.board .ground .ground) .ground) .ground)
          = reading (.board .ground (.board .ground (.board .ground .ground)))
      ∧ census 4 = 5 :=
  ⟨⟨the_two_shapes_of_three.1, the_two_shapes_of_three.2.2.2⟩,
   (three_has_no_loop n).1,
   the_pentagon_turns_at_four.1,
   the_pentagon_turns_at_four.2,
   (fun h => nomatch (Nat.succ.inj (Nat.succ.inj h))),
   rfl,
   rfl⟩

theorem three_is_the_width_of_contact (F G H : Face) {S : Type u'}
    (f : S → F.State) (g : S → G.State) (h : S → H.State)
    (p0 : F.Probe) (q0 : G.Probe) (r0 : H.Probe) (s t : S)
    {T : Type u''} (r : T → Bool) (a b c : T) (n : Nat) :
    (r a = r b ∨ r b = r c ∨ r a = r c)
      ∧ (alike (pairFace F G f g) s t ↔ (alike F (f s) (f t) ∧ alike G (g s) (g t)))
      ∧ (alike (pairFace (pairFace F G f g) H (fun x => x) h) s t
          ↔ alike (pairFace F (pairFace G H g h) f (fun x => x)) s t)
      ∧ ¬ chain (n + 1) (.board (.board .ground .ground) .ground)
          (.board (.board .ground .ground) .ground)
      ∧ chain 2 (.board (.board (.board .ground .ground) .ground) .ground)
          (.board .ground (.board .ground (.board .ground .ground)))
      ∧ chain 3 (.board (.board (.board .ground .ground) .ground) .ground)
          (.board .ground (.board .ground (.board .ground .ground))) :=
  ⟨the_hallway_is_too_small r a b c,
   the_pairing_is_exact F G f g p0 q0 s t,
   every_widening_is_one_pairing F G H f g h p0 q0 r0 s t,
   (three_has_no_loop n).1,
   the_pentagon_turns_at_four.1,
   the_pentagon_turns_at_four.2⟩

end Face
