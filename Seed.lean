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

def vertical {H W : Type} (σ : H → W → W) (d : door H W) : door H W :=
  atTheDoor (face d) (σ (face d) (met d))

theorem a_guest_mover_is_unheard {H W X : Type} (σ : H → W → W)
    (g : H → X) (d : door H W) :
    g (face (vertical σ d)) = g (face d) := rfl

theorem an_unheard_move_moves_only_the_guest {H W : Type}
    (m : door H W → door H W) :
    (∀ d, face (m d) = face d)
      ↔ ∃ σ : H → W → W, ∀ d, m d = vertical σ d :=
  ⟨fun hm => ⟨fun h w => met (m (atTheDoor h w)),
     fun d => congrArg (fun x => atTheDoor x (met (m d))) (hm d)⟩,
   fun he d => he.elim fun _ hσ => (congrArg face (hσ d)).trans rfl⟩

theorem guest_movers_compose {H W : Type} (σ τ : H → W → W) (d : door H W) :
    vertical σ (vertical τ d) = vertical (fun h w => σ h (τ h w)) d := rfl

theorem the_still_door_moves_no_guest {H W : Type} (d : door H W) :
    vertical (fun _ w => w) d = d := rfl

def label (W : Type) (p : Plan) (s : build W p) : door (build W p) Plan :=
  atTheDoor s p

theorem the_label_rides_unread {W X : Type} (p p' : Plan) (s : build W p)
    (g : build W p → X) :
    g (face (label W p s)) = g (face (atTheDoor s p')) := rfl

theorem a_false_label_is_real (W : Type) (p : Plan) (s : build W p)
    {p' : Plan} (hp : p ≠ p') : label W p s ≠ atTheDoor s p' :=
  fun he => hp (congrArg met he)

theorem the_meeting_reads_the_label (W : Type) (p : Plan) (s : build W p) :
    met (label W p s) = p := rfl

theorem honesty_is_invisible_at_the_face (W : Type) (p p' : Plan)
    (s : build W p) (hp : p ≠ p') :
    label W p s ≠ atTheDoor s p'
      ∧ (∀ (X : Type) (g : build W p → X),
          g (face (label W p s)) = g (face (atTheDoor s p')))
      ∧ met (label W p s) = p
      ∧ met (atTheDoor s p') = p' :=
  ⟨a_false_label_is_real W p s hp, fun _ _ => rfl, rfl, rfl⟩

universe u v

def fold {X : Type u} (mul : X → X → X) (x₀ : X) : Plan → X
  | .ground => x₀
  | .board p q => mul (fold mul x₀ p) (fold mul x₀ q)

theorem no_world_is_refused {X : Type u} (mul : X → X → X) (x₀ : X) :
    fold mul x₀ .ground = x₀
      ∧ ∀ p q, fold mul x₀ (.board p q)
          = mul (fold mul x₀ p) (fold mul x₀ q) :=
  ⟨rfl, fun _ _ => rfl⟩

theorem any_two_readings_agree {X : Type u} (mul : X → X → X) (x₀ : X)
    (f : Plan → X) (hg : f .ground = x₀)
    (hb : ∀ p q, f (.board p q) = mul (f p) (f q)) :
    ∀ p, f p = fold mul x₀ p
  | .ground => hg
  | .board p q =>
      (hb p q).trans
        (congr (congrArg mul (any_two_readings_agree mul x₀ f hg hb p))
          (any_two_readings_agree mul x₀ f hg hb q))

theorem the_self_reading_is_the_identity :
    ∀ p, fold Plan.board Plan.ground p = p :=
  fun p =>
    (any_two_readings_agree Plan.board Plan.ground (fun x => x) rfl
      (fun _ _ => rfl) p).symm

theorem build_is_a_reading (W : Type) : ∀ p, build W p = fold door W p :=
  fun p => any_two_readings_agree door W (build W) rfl (fun _ _ => rfl) p

theorem a_reading_may_forget_what_the_record_keeps :
    fold (fun a b => a + b) 1 (.board .ground (.board .ground .ground))
        = fold (fun a b => a + b) 1 (.board (.board .ground .ground) .ground)
      ∧ Plan.board .ground (.board .ground .ground)
          ≠ .board (.board .ground .ground) .ground :=
  ⟨rfl, fun h => nomatch (Plan.board.inj h).1⟩

theorem no_face_answers_for_the_guest {H W : Type} (h : H) {w w' : W}
    (hw : w ≠ w') :
    ¬ ∃ g : H → W, ∀ (h' : H) (v : W), g (face (atTheDoor h' v)) = v :=
  fun he => he.elim fun _ hg => hw ((hg h w).symm.trans (hg h w'))

theorem one_reading_merges_what_another_parts :
    fold (fun a b => a + b) 1
        (.board (.board .ground .ground) .ground)
      = fold (fun a b => a + b) 1
        (.board .ground (.board .ground .ground))
      ∧ fold (fun a _ => a + 1) 0
          (.board (.board .ground .ground) .ground)
        ≠ fold (fun a _ => a + 1) 0
          (.board .ground (.board .ground .ground))
      ∧ Plan.board (.board .ground .ground) .ground
          ≠ .board .ground (.board .ground .ground) :=
  ⟨rfl,
   And.intro
     (fun h => nomatch Nat.succ.inj h)
     (fun h => nomatch (Plan.board.inj h).1)⟩

def classDoor {X : Type} (r : Plan → X) (p : Plan) : door X Plan :=
  atTheDoor (r p) p

theorem the_reading_is_the_face {X : Type} (r : Plan → X) (p : Plan) :
    face (classDoor r p) = r p := rfl

theorem the_meeting_returns_the_world {X : Type} (r : Plan → X) (p : Plan) :
    met (classDoor r p) = p := rfl

theorem classmates_board_as_guests {X : Type} (r : Plan → X) {p q : Plan}
    (hr : r p = r q) (hpq : p ≠ q) :
    classDoor r p ≠ classDoor r q
      ∧ ∀ (Y : Type) (g : X → Y),
          g (face (classDoor r p)) = g (face (classDoor r q)) :=
  ⟨fun he => hpq (congrArg met he), fun _ g => congrArg g hr⟩

theorem every_reading_is_a_door {X : Type} (r : Plan → X) {p q : Plan}
    (hr : r p = r q) (hpq : p ≠ q) :
    face (classDoor r p) = r p
      ∧ classDoor r p ≠ classDoor r q
      ∧ (∀ (Y : Type) (g : X → Y),
          g (face (classDoor r p)) = g (face (classDoor r q)))
      ∧ met (classDoor r p) = p :=
  ⟨rfl, (classmates_board_as_guests r hr hpq).1,
   (classmates_board_as_guests r hr hpq).2, rfl⟩

theorem the_class_is_a_guest_room :
    classDoor (fold (fun a b => a + b) 1)
        (.board (.board .ground .ground) .ground)
      ≠ classDoor (fold (fun a b => a + b) 1)
        (.board .ground (.board .ground .ground))
      ∧ face (classDoor (fold (fun a b => a + b) 1)
            (.board (.board .ground .ground) .ground))
        = face (classDoor (fold (fun a b => a + b) 1)
            (.board .ground (.board .ground .ground))) :=
  ⟨(fun he => nomatch (Plan.board.inj (congrArg met he)).1), rfl⟩

theorem checking_papers_unpersons {H W : Type}
    (hchk : ∀ d d' : door H W, face d = face d' → d = d')
    (h : H) (w w' : W) : atTheDoor h w = atTheDoor h w' :=
  hchk _ _ rfl

theorem hospitality_is_structural {H W : Type} (h : H) {w w' : W}
    (hw : w ≠ w') :
    (¬ ∃ g : H → W, ∀ (h' : H) (v : W), g (face (atTheDoor h' v)) = v)
      ∧ ((∀ d d' : door H W, face d = face d' → d = d') → False) :=
  ⟨no_face_answers_for_the_guest h hw,
   fun hchk => hw (congrArg met (checking_papers_unpersons hchk h w w'))⟩

def pairMul {X Y : Type} (mulX : X → X → X) (mulY : Y → Y → Y) :
    X × Y → X × Y → X × Y :=
  fun a b => (mulX a.1 b.1, mulY a.2 b.2)

theorem the_meeting_is_a_reading {X Y : Type} (mulX : X → X → X)
    (mulY : Y → Y → Y) (x₀ : X) (y₀ : Y) (p : Plan) :
    fold (pairMul mulX mulY) (x₀, y₀) p
      = (fold mulX x₀ p, fold mulY y₀ p) :=
  (any_two_readings_agree (pairMul mulX mulY) (x₀, y₀)
    (fun q => (fold mulX x₀ q, fold mulY y₀ q)) rfl (fun _ _ => rfl) p).symm

theorem two_readings_part_what_one_merges :
    fold (fun a b => a + b) 1
        (.board (.board .ground .ground) .ground)
      = fold (fun a b => a + b) 1
        (.board .ground (.board .ground .ground))
      ∧ fold (pairMul (fun a b => a + b) (fun a _ => a + 1)) (1, 0)
          (.board (.board .ground .ground) .ground)
        ≠ fold (pairMul (fun a b => a + b) (fun a _ => a + 1)) (1, 0)
          (.board .ground (.board .ground .ground)) :=
  ⟨rfl, fun h => nomatch Nat.succ.inj (congrArg Prod.snd h)⟩

inductive Quiz (H X : Type) : Type where
  | rest : Quiz H X
  | ask (g : H → X) (k : X → Quiz H X) : Quiz H X

def interrogate {H W X : Type} : Quiz H X → door H W → List X
  | .rest, _ => []
  | .ask g k, d => g (face d) :: interrogate (k (g (face d))) d

structure Face where
  State : Type u
  Probe : Type
  Ans   : Type
  obs   : State → Probe → Ans

inductive Interview (P A : Type) : Type where
  | rest : Interview P A
  | ask (p : P) (k : A → Interview P A) : Interview P A

def sound (F : Face) (s : F.State) : Interview F.Probe F.Ans → List F.Ans
  | .rest => []
  | .ask p k => F.obs s p :: sound F s (k (F.obs s p))

def alike (F : Face) (s t : F.State) : Prop :=
  ∀ p, F.obs s p = F.obs t p

def seq {P A : Type} : Interview P A → Interview P A → Interview P A
  | .rest, q => q
  | .ask p k, q => .ask p (fun a => seq (k a) q)

theorem the_interviews_resume (F : Face) (s : F.State) :
    ∀ q₁ q₂ : Interview F.Probe F.Ans,
      sound F s (seq q₁ q₂) = sound F s q₁ ++ sound F s q₂
  | .rest, _ => rfl
  | .ask p k, q₂ => by
      show F.obs s p :: sound F s (seq (k (F.obs s p)) q₂)
          = (F.obs s p :: sound F s (k (F.obs s p))) ++ sound F s q₂
      rw [the_interviews_resume F s (k (F.obs s p)) q₂]
      exact rfl

theorem the_yield_writes_no_marks (F : Face) (s : F.State) :
    sound F s .rest = [] := rfl

theorem no_interview_parts_the_alike (F : Face) (s t : F.State)
    (h : alike F s t) (q : Interview F.Probe F.Ans) :
    sound F s q = sound F t q := by
  induction q with
  | rest => rfl
  | ask p k ih =>
      show F.obs s p :: sound F s (k (F.obs s p))
          = F.obs t p :: sound F t (k (F.obs t p))
      rw [h p]
      exact congrArg (F.obs t p :: ·) (ih (F.obs t p))

def doorFace (H W X : Type) : Face :=
  ⟨door H W, H → X, X, fun d g => g (face d)⟩

def posed {H X : Type} : Quiz H X → Interview (H → X) X
  | .rest => .rest
  | .ask g k => .ask g (fun x => posed (k x))

theorem the_quiz_was_an_interview {H W X : Type} (d : door H W) :
    ∀ q : Quiz H X,
      interrogate q d = sound (doorFace H W X) d (posed q)
  | .rest => rfl
  | .ask g k =>
      congrArg (g (face d) :: ·)
        (the_quiz_was_an_interview d (k (g (face d))))

theorem the_guests_are_alike_at_the_door {H W X : Type} (h : H)
    (w w' : W) :
    alike (doorFace H W X) (atTheDoor h w) (atTheDoor h w') :=
  fun _ => rfl

theorem a_strategy_hears_no_guest {H W X : Type} (h : H) (w w' : W)
    (q : Quiz H X) :
    interrogate q (atTheDoor h w) = interrogate q (atTheDoor h w') :=
  ((the_quiz_was_an_interview (atTheDoor h w) q).trans
    (no_interview_parts_the_alike (doorFace H W X) _ _
      (the_guests_are_alike_at_the_door h w w') (posed q))).trans
    (the_quiz_was_an_interview (atTheDoor h w') q).symm

theorem the_whole_interview_reads_no_guest {H W X : Type} (h : H)
    (w w' : W) (q : Quiz H X) :
    interrogate q (atTheDoor h w) = interrogate q (atTheDoor h w')
      ∧ (w ≠ w' → atTheDoor h w ≠ atTheDoor h w') :=
  ⟨a_strategy_hears_no_guest h w w' q, fun hw => the_guest_is_real h hw⟩

structure Machine (I O : Type) where
  S : Type
  s0 : S
  step : S → I → S
  out : S → O

def drive {I O : Type} (m : Machine I O) : m.S → List I → O
  | s, [] => m.out s
  | s, i :: is => drive m (m.step s i) is

def behavior {I O : Type} (m : Machine I O) (w : List I) : O :=
  drive m m.s0 w

def walk {I : Type} {S : Type u} (step : S → I → S) : S → List I → S
  | s, [] => s
  | s, i :: w => walk step (step s i) w

theorem a_reading_in_step_carries_the_walk {I : Type} {S : Type u}
    {T : Type v} (stepS : S → I → S) (stepT : T → I → T) (r : S → T)
    (h : ∀ s i, r (stepS s i) = stepT (r s) i) :
    ∀ (w : List I) (s : S), r (walk stepS s w) = walk stepT (r s) w
  | [], _ => rfl
  | i :: w, s =>
      (a_reading_in_step_carries_the_walk stepS stepT r h w (stepS s i)).trans
        (congrArg (fun x => walk stepT x w) (h s i))

theorem the_walk_resumes {I : Type} {S : Type u} (step : S → I → S) :
    ∀ (w w' : List I) (s : S),
      walk step s (w ++ w') = walk step (walk step s w) w'
  | [], _, _ => rfl
  | i :: w, w', s => the_walk_resumes step w w' (step s i)

theorem two_machines_in_step_agree {I O : Type} (m n : Machine I O)
    (R : m.S → n.S → Prop)
    (hstep : ∀ s t i, R s t → R (m.step s i) (n.step t i))
    (hout : ∀ s t, R s t → m.out s = n.out t) :
    ∀ (w : List I) (s : m.S) (t : n.S), R s t → drive m s w = drive n t w
  | [], s, t, h => hout s t h
  | i :: w, s, t, h =>
      two_machines_in_step_agree m n R hstep hout w
        (m.step s i) (n.step t i) (hstep s t i h)

def oddNat : Nat → Bool
  | 0 => false
  | n + 1 => !(oddNat n)

theorem not_not : ∀ b : Bool, (!(!b)) = b
  | true => rfl
  | false => rfl

def paceOne : Machine Unit Bool := ⟨Nat, 0, fun n _ => n + 1, oddNat⟩

def paceThree : Machine Unit Bool := ⟨Nat, 0, fun n _ => n + 3, oddNat⟩

theorem the_paces_agree (w : List Unit) (a b : Nat)
    (h : oddNat a = oddNat b) : drive paceOne a w = drive paceThree b w :=
  two_machines_in_step_agree paceOne paceThree
    (fun (a b : Nat) => oddNat a = oddNat b)
    (fun (a b : Nat) _ h => by
      show (!(oddNat a)) = oddNat (b + 3)
      rw [h]
      show (!(oddNat b)) = (!(!(!(oddNat b))))
      rw [not_not])
    (fun _ _ h => h) w a b h

theorem the_air_gap_reads_no_interior :
    (∀ w : List Unit, behavior paceOne w = behavior paceThree w)
      ∧ paceOne.step (0 : Nat) () ≠ paceThree.step (0 : Nat) () :=
  ⟨fun w => the_paces_agree w 0 0 rfl,
   fun h => nomatch Nat.succ.inj h⟩

theorem stillness_hides_the_ticking {I O : Type} (m : Machine I O)
    (hstill : ∀ s i, m.out (m.step s i) = m.out s) :
    ∀ (w : List I) (s : m.S), drive m s w = m.out s
  | [], _ => rfl
  | i :: w, s =>
      (stillness_hides_the_ticking m hstill w (m.step s i)).trans (hstill s i)

def restingCounter : Machine Unit Bool :=
  ⟨Nat, 0, fun n _ => n + 1, fun _ => true⟩

theorem the_still_face_is_not_a_dead_machine :
    (∀ w : List Unit, behavior restingCounter w = true)
      ∧ restingCounter.step (0 : Nat) () ≠ (0 : Nat) :=
  ⟨fun w =>
     stillness_hides_the_ticking restingCounter (fun _ _ => rfl) w (0 : Nat),
   fun h => nomatch h⟩

def turnAbout {H W : Type} (d : door H W) : door W H :=
  atTheDoor (met d) (face d)

theorem the_guest_becomes_the_host {H W : Type} (h : H) (w : W) :
    face (turnAbout (atTheDoor h w)) = w
      ∧ met (turnAbout (atTheDoor h w)) = h :=
  ⟨rfl, rfl⟩

theorem the_return_restores_the_seating {H W : Type} (d : door H W) :
    turnAbout (turnAbout d) = d := rfl

def cross : List Plan → List Plan → List Plan
  | [], _ => []
  | p :: ps, qs => qs.map (Plan.board p) ++ cross ps qs

def allPlans : Nat → List Plan
  | 0 => [.ground]
  | d + 1 => .ground :: cross (allPlans d) (allPlans d)

def census : Nat → Nat
  | 0 => 0
  | k + 1 =>
      ((allPlans k).filter
        (fun p => Nat.beq (fold (fun a b => a + b) 1 p) (k + 1))).length

theorem the_census_checksums_with_the_polygon_cutters :
    census 1 = 1 ∧ census 2 = 1 ∧ census 3 = 2 ∧ census 4 = 5
      ∧ census 5 = 14 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def reground {W W' : Type} (f : W → W') :
    (p : Plan) → build W p → build W' p
  | .ground, s => f s
  | .board p q, d =>
      atTheDoor (reground f p (face d)) (reground f q (met d))

theorem the_import_threads_the_spine {W W' : Type} (f : W → W') :
    ∀ (p : Plan) (s : build W p),
      spine W' p (reground f p s) = f (spine W p s)
  | .ground, _ => rfl
  | .board p _, d => the_import_threads_the_spine f p (face d)

theorem remeasurement_moves_only_the_ground {W : Type} :
    ∀ (p : Plan) (s : build W p), reground (fun w => w) p s = s
  | .ground, _ => rfl
  | .board p q, d => by
      show atTheDoor (reground (fun w => w) p (face d))
          (reground (fun w => w) q (met d)) = d
      rw [remeasurement_moves_only_the_ground p (face d),
          remeasurement_moves_only_the_ground q (met d)]
      exact rfl

theorem imports_compose {W W' W'' : Type} (f : W → W') (g : W' → W'') :
    ∀ (p : Plan) (s : build W p),
      reground g p (reground f p s) = reground (fun w => g (f w)) p s
  | .ground, _ => rfl
  | .board p q, d =>
      congr (congrArg atTheDoor (imports_compose f g p (face d)))
        (imports_compose f g q (met d))

def paceAtHome : Nat := 1

def readAcross (vote pace : Nat) : Nat := pace * vote

theorem one_times : ∀ n : Nat, 1 * n = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (one_times n)

theorem the_pace_reads_one_at_home : readAcross 1 paceAtHome = 1 := rfl

theorem any_vote_reads_itself (n : Nat) : readAcross n paceAtHome = n :=
  one_times n

def graft (base : Plan) : Plan → Plan
  | .ground => base
  | .board p q => .board (graft base p) (graft base q)

theorem a_stage_may_ground_a_stage (W : Type) (base : Plan) :
    ∀ q : Plan, build W (graft base q) = build (build W base) q
  | .ground => rfl
  | .board p r =>
      show door (build W (graft base p)) (build W (graft base r))
          = door (build (build W base) p) (build (build W base) r)
      from congr (congrArg door (a_stage_may_ground_a_stage W base p))
        (a_stage_may_ground_a_stage W base r)

theorem the_oldest_ground_still_answers (W : Type) (base : Plan) :
    ∀ (q : Plan) (s : build W (graft base q)),
      ∃ t : build W base,
        spine W (graft base q) s = spine W base t
  | .ground, s => ⟨s, rfl⟩
  | .board p _, d => the_oldest_ground_still_answers W base p (face d)

theorem lineages_compose (a b : Plan) :
    ∀ q, graft a (graft b q) = graft (graft a b) q
  | .ground => rfl
  | .board p r =>
      show Plan.board (graft a (graft b p)) (graft a (graft b r))
          = Plan.board (graft (graft a b) p) (graft (graft a b) r)
      from congr (congrArg Plan.board (lineages_compose a b p))
        (lineages_compose a b r)

theorem the_trivial_revision_changes_nothing :
    ∀ q, graft .ground q = q
  | .ground => rfl
  | .board p r =>
      show Plan.board (graft .ground p) (graft .ground r) = Plan.board p r
      from congr (congrArg Plan.board (the_trivial_revision_changes_nothing p))
        (the_trivial_revision_changes_nothing r)

theorem the_parent_folds_into_the_ground {X : Type u}
    (mul : X → X → X) (x₀ : X) (base : Plan) :
    ∀ q, fold mul x₀ (graft base q) = fold mul (fold mul x₀ base) q
  | .ground => rfl
  | .board p r =>
      show mul (fold mul x₀ (graft base p)) (fold mul x₀ (graft base r))
          = mul (fold mul (fold mul x₀ base) p)
              (fold mul (fold mul x₀ base) r)
      from congr
        (congrArg mul (the_parent_folds_into_the_ground mul x₀ base p))
        (the_parent_folds_into_the_ground mul x₀ base r)

theorem the_ancestor_rides_unread {X : Type u} (mul : X → X → X) (x₀ : X)
    {base base' : Plan} (h : fold mul x₀ base = fold mul x₀ base')
    (q : Plan) :
    fold mul x₀ (graft base q) = fold mul x₀ (graft base' q) :=
  (the_parent_folds_into_the_ground mul x₀ base q).trans
    ((congrArg (fun v => fold mul v q) h).trans
      (the_parent_folds_into_the_ground mul x₀ base' q).symm)

theorem the_route_leaves_no_mark {P : Prop} (h1 h2 : P) : h1 = h2 := rfl

def fork (H W : Type) : Type := H ⊕ W

def viaLeft {H W : Type} (h : H) : fork H W := .inl h

def viaRight {H W : Type} (w : W) : fork H W := .inr w

def greet {H W X : Type} (gl : H → X) (gr : W → X) : fork H W → X
  | .inl h => gl h
  | .inr w => gr w

theorem the_two_entrances_share_one_lobby {H W X : Type}
    (gl : H → X) (gr : W → X) (h : H) (w : W) :
    greet gl gr (viaLeft h) = gl h ∧ greet gl gr (viaRight w) = gr w :=
  ⟨rfl, rfl⟩

theorem the_entrance_is_real {H W : Type} (h : H) (w : W) :
    viaLeft h ≠ (viaRight w : fork H W) :=
  fun he => nomatch he

theorem a_greeter_is_a_door_of_handlers {H W X : Type}
    (f : fork H W → X) :
    ∀ d, greet (fun h => f (viaLeft h)) (fun w => f (viaRight w)) d = f d
  | .inl _ => rfl
  | .inr _ => rfl

theorem any_ready_greeter_is_the_greeter {H W X : Type}
    (gl : H → X) (gr : W → X) (f : fork H W → X)
    (hl : ∀ h, f (viaLeft h) = gl h) (hr : ∀ w, f (viaRight w) = gr w) :
    ∀ d, f d = greet gl gr d
  | .inl h => hl h
  | .inr w => hr w

theorem the_anonymous_guest_is_free {H : Type} (d : door H Unit) :
    atTheDoor (face d) () = d := rfl

theorem no_world_hosts_the_impossible {H : Type} (d : door H Empty) :
    False :=
  nomatch met d

def noEntrance {H : Type} : fork H Empty → H :=
  greet (fun h => h) (fun e => nomatch e)

theorem a_sealed_entrance_adds_nothing {H : Type} :
    (∀ h : H, noEntrance (viaLeft h) = h)
      ∧ ∀ f : fork H Empty, viaLeft (noEntrance f) = f :=
  ⟨fun _ => rfl,
   fun f => match f with
     | .inl _ => rfl
     | .inr e => nomatch e⟩

def steer {H W : Type} (σ : H → W → W) (d : door W H) : door W H :=
  atTheDoor (σ (met d) (face d)) (met d)

theorem the_swap_trades_maintenance_for_motion {H W : Type}
    (σ : H → W → W) (d : door H W) :
    turnAbout (vertical σ d) = steer σ (turnAbout d) := rfl

theorem what_one_seat_maintains_the_other_watches {H W X : Type}
    (σ : H → W → W) (g : H → X) (d : door H W) :
    g (face (vertical σ d)) = g (face d)
      ∧ face (steer σ (turnAbout d)) = σ (face d) (met d) :=
  ⟨rfl, rfl⟩

theorem the_maintenance_is_audible_across_the_swap :
    face (vertical (fun _ w => w + 1) (atTheDoor (5 : Nat) (0 : Nat)))
        = face (atTheDoor (5 : Nat) (0 : Nat))
      ∧ face (steer (fun _ w => w + 1)
            (turnAbout (atTheDoor (5 : Nat) (0 : Nat))))
          ≠ face (turnAbout (atTheDoor (5 : Nat) (0 : Nat))) :=
  ⟨rfl, fun h => nomatch h⟩

def crossOver {H W : Type} : fork H W → fork W H :=
  greet viaRight viaLeft

theorem the_crossing_returns {H W : Type} :
    ∀ f : fork H W, crossOver (crossOver f) = f
  | .inl _ => rfl
  | .inr _ => rfl

def deepen {H W V : Type} (d : door (door H W) V) : door H (door W V) :=
  atTheDoor (face (face d)) (atTheDoor (met (face d)) (met d))

def shallow {H W V : Type} (d : door H (door W V)) : door (door H W) V :=
  atTheDoor (atTheDoor (face d) (face (met d))) (met (met d))

theorem hosting_associates {H W V : Type} :
    (∀ d : door (door H W) V, shallow (deepen d) = d)
      ∧ ∀ d : door H (door W V), deepen (shallow d) = d :=
  ⟨fun _ => rfl, fun _ => rfl⟩

def rebranch {H W V : Type} : fork (fork H W) V → fork H (fork W V) :=
  greet (greet viaLeft (fun w => viaRight (viaLeft w)))
    (fun v => viaRight (viaRight v))

def unbranch {H W V : Type} : fork H (fork W V) → fork (fork H W) V :=
  greet (fun h => viaLeft (viaLeft h))
    (greet (fun w => viaLeft (viaRight w)) viaRight)

theorem arrival_associates {H W V : Type} :
    (∀ f : fork (fork H W) V, unbranch (rebranch f) = f)
      ∧ ∀ f : fork H (fork W V), rebranch (unbranch f) = f :=
  ⟨fun f =>
     match f with
     | .inl (.inl _) => rfl
     | .inl (.inr _) => rfl
     | .inr _ => rfl,
   fun f =>
     match f with
     | .inl _ => rfl
     | .inr (.inl _) => rfl
     | .inr (.inr _) => rfl⟩

def distribute {H W V : Type} : door H (fork W V) → fork (door H W) (door H V)
  | (h, .inl w) => .inl (h, w)
  | (h, .inr v) => .inr (h, v)

def collect {H W V : Type} : fork (door H W) (door H V) → door H (fork W V) :=
  greet (fun d => atTheDoor (face d) (viaLeft (met d)))
    (fun d => atTheDoor (face d) (viaRight (met d)))

theorem the_host_serves_both_branches {H W V : Type} :
    ∀ d : door H (fork W V), collect (distribute d) = d
  | (_, .inl _) => rfl
  | (_, .inr _) => rfl

theorem the_branches_share_the_host {H W V : Type} :
    ∀ f : fork (door H W) (door H V), distribute (collect f) = f
  | .inl _ => rfl
  | .inr _ => rfl

theorem the_host_survives_the_split {H W V : Type} :
    ∀ d : door H (fork W V), greet face face (distribute d) = face d
  | (_, .inl _) => rfl
  | (_, .inr _) => rfl

theorem the_mirror_finds_the_fixed_point {A Y : Type}
    (g : A → (A → Y)) (t : Y → Y)
    (hsur : ∀ f : A → Y, ∃ a, g a = f) :
    ∃ y, t y = y :=
  (hsur (fun a => t (g a a))).elim fun a₀ ha =>
    ⟨g a₀ a₀, (congrFun ha a₀).symm⟩

theorem bool_escapes : ∀ b : Bool, b ≠ !b
  | true, h => nomatch h
  | false, h => nomatch h

theorem the_readings_outrun_the_room {A : Type} (g : A → (A → Bool)) :
    ∃ f : A → Bool, ∀ a, g a ≠ f :=
  ⟨fun a => !(g a a),
   fun a he => bool_escapes (g a a) (congrFun he a)⟩

structure Measured where
  lo : Nat
  hi : Nat

def within (m : Measured) (x : Nat) : Bool :=
  Nat.ble m.lo x && Nat.ble x m.hi

def tighter (fine coarse : Measured) : Bool :=
  Nat.ble coarse.lo fine.lo && Nat.ble fine.hi coarse.hi

theorem ble_trans : ∀ (a b c : Nat),
    Nat.ble a b = true → Nat.ble b c = true → Nat.ble a c = true
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, _, h1, _ => nomatch h1
  | _ + 1, _ + 1, 0, _, h2 => nomatch h2
  | a + 1, b + 1, c + 1, h1, h2 => ble_trans a b c h1 h2

theorem and_split : ∀ {p q : Bool}, (p && q) = true → p = true ∧ q = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => nomatch h
  | false, _, h => nomatch h

theorem and_glue : ∀ {p q : Bool}, p = true → q = true → (p && q) = true
  | true, true, _, _ => rfl
  | true, false, _, h => nomatch h
  | false, _, h, _ => nomatch h

theorem the_refined_reading_still_lands {fine coarse : Measured} {x : Nat}
    (ht : tighter fine coarse = true) (hx : within fine x = true) :
    within coarse x = true :=
  and_glue (ble_trans _ _ _ (and_split ht).1 (and_split hx).1)
    (ble_trans _ _ _ (and_split hx).2 (and_split ht).2)

theorem zero_plus : ∀ n : Nat, 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (zero_plus n)

theorem succ_adds : ∀ a b : Nat, (a + 1) + b = (a + b) + 1
  | _, 0 => rfl
  | a, b + 1 => congrArg (· + 1) (succ_adds a b)

theorem len_append {A : Type} :
    ∀ (xs ys : List A), (xs ++ ys).length = xs.length + ys.length
  | [], ys => (zero_plus ys.length).symm
  | _ :: xs, ys => by
      show (xs ++ ys).length + 1 = (xs.length + 1) + ys.length
      rw [len_append xs ys]
      exact (succ_adds xs.length ys.length).symm

theorem map_append {A B : Type} (f : A → B) :
    ∀ (xs ys : List A), (xs ++ ys).map f = xs.map f ++ ys.map f
  | [], _ => rfl
  | x :: xs, ys => congrArg (f x :: ·) (map_append f xs ys)

def pour {W : Type} : (p : Plan) → build W p → List W
  | .ground, s => [s]
  | .board p q, d => pour p (face d) ++ pour q (met d)

theorem the_manifest_counts_the_guests {W : Type} :
    ∀ (p : Plan) (s : build W p),
      (pour p s).length = fold (fun a b => a + b) 1 p
  | .ground, _ => rfl
  | .board p q, d => by
      show (pour p (face d) ++ pour q (met d)).length
          = fold (fun a b => a + b) 1 p + fold (fun a b => a + b) 1 q
      rw [len_append, the_manifest_counts_the_guests p (face d),
          the_manifest_counts_the_guests q (met d)]

theorem the_customs_thread_the_manifest {W W' : Type} (f : W → W') :
    ∀ (p : Plan) (s : build W p),
      pour p (reground f p s) = (pour p s).map f
  | .ground, _ => rfl
  | .board p q, d => by
      show pour p (reground f p (face d)) ++ pour q (reground f q (met d))
          = (pour p (face d) ++ pour q (met d)).map f
      rw [the_customs_thread_the_manifest f p (face d),
          the_customs_thread_the_manifest f q (met d)]
      exact (map_append f (pour p (face d)) (pour q (met d))).symm

def tally (W : Type) : Machine W Nat :=
  ⟨Nat, 0, fun n _ => n + 1, fun n => n⟩

theorem drive_counts {W : Type} :
    ∀ (w : List W) (s : Nat), drive (tally W) s w = s + w.length
  | [], _ => rfl
  | _ :: w, s => (drive_counts w (s + 1)).trans (succ_adds s w.length)

theorem the_run_agrees_with_the_fold {W : Type} (p : Plan) (s : build W p) :
    behavior (tally W) (pour p s) = fold (fun a b => a + b) 1 p :=
  (drive_counts (pour p s) 0).trans
    ((zero_plus (pour p s).length).trans (the_manifest_counts_the_guests p s))

theorem ble_refl : ∀ n : Nat, Nat.ble n n = true
  | 0 => rfl
  | n + 1 => ble_refl n

theorem ble_le_succ : ∀ n : Nat, Nat.ble n (n + 1) = true
  | 0 => rfl
  | n + 1 => ble_le_succ n

theorem tighter_refl (a : Measured) : tighter a a = true :=
  and_glue (ble_refl a.lo) (ble_refl a.hi)

theorem tighter_trans {a b c : Measured} (h1 : tighter a b = true)
    (h2 : tighter b c = true) : tighter a c = true :=
  and_glue (ble_trans _ _ _ (and_split h2).1 (and_split h1).1)
    (ble_trans _ _ _ (and_split h1).2 (and_split h2).2)

theorem the_learner_only_tightens {I : Type} (m : Machine I Measured)
    (hlearn : ∀ s i, tighter (m.out (m.step s i)) (m.out s) = true) :
    ∀ (w : List I) (s : m.S), tighter (drive m s w) (m.out s) = true
  | [], s => tighter_refl (m.out s)
  | i :: w, s =>
      tighter_trans (the_learner_only_tightens m hlearn w (m.step s i))
        (hlearn s i)

def homingIn : Machine Unit Measured :=
  ⟨Nat, 0, fun n _ => n + 1, fun n => ⟨n, 10⟩⟩

theorem the_homing_reading_tightens :
    ∀ w : List Unit,
      tighter (behavior homingIn w) (⟨0, 10⟩ : Measured) = true :=
  fun w =>
    the_learner_only_tightens homingIn
      (fun s _ => and_glue (ble_le_succ s) (ble_refl 10)) w (0 : Nat)

def park {I O : Type} (m : Machine I O) : m.S → List I → m.S
  | s, [] => s
  | s, i :: w => park m (m.step s i) w

theorem the_park_is_a_walk {I O : Type} (m : Machine I O) :
    ∀ (w : List I) (s : m.S), park m s w = walk m.step s w
  | [], _ => rfl
  | i :: w, s => the_park_is_a_walk m w (m.step s i)

theorem the_drive_reads_the_walk {I O : Type} (m : Machine I O) :
    ∀ (w : List I) (s : m.S), drive m s w = m.out (walk m.step s w)
  | [], _ => rfl
  | i :: w, s => the_drive_reads_the_walk m w (m.step s i)

theorem the_drive_resumes {I O : Type} (m : Machine I O)
    (w w' : List I) (s : m.S) :
    drive m s (w ++ w') = drive m (park m s w) w' :=
  (((the_drive_reads_the_walk m (w ++ w') s).trans
      (congrArg m.out (the_walk_resumes m.step w w' s))).trans
    (the_drive_reads_the_walk m w' (walk m.step s w)).symm).trans
    (congrArg (fun x => drive m x w') (the_park_is_a_walk m w s).symm)

theorem the_session_continues_from_the_parked_seat {I O : Type}
    (m : Machine I O) (w w' : List I) :
    behavior m (w ++ w') = drive m (park m m.s0 w) w' :=
  the_drive_resumes m w w' m.s0

theorem the_future_reads_only_the_seat {I O : Type} (m : Machine I O)
    (w w' : List I) (h : park m m.s0 w = park m m.s0 w') (v : List I) :
    drive m (park m m.s0 w) v = drive m (park m m.s0 w') v :=
  congrArg (fun s => drive m s v) h

def pulse : Machine Bool Bool := ⟨Nat, 0, fun n _ => n + 1, oddNat⟩

theorem two_routes_one_seat :
    ([true, false] ≠ [false, true])
      ∧ park pulse (0 : Nat) [true, false]
          = park pulse (0 : Nat) [false, true] :=
  ⟨(fun h => nomatch (List.cons.inj h).1), rfl⟩

def graphDoor {A X : Type} (r : A → X) (a : A) : door X A :=
  atTheDoor (r a) a

theorem the_special_was_the_general {X : Type} (r : Plan → X) (p : Plan) :
    classDoor r p = graphDoor r p := rfl

def specView {W : Type} (p : Plan) (s : build W p) : door Plan (build W p) :=
  turnAbout (label W p s)

theorem the_spec_hides_the_implementation {W X : Type} (p : Plan)
    (s s' : build W p) (g : Plan → X) :
    face (specView p s) = p
      ∧ g (face (specView p s)) = g (face (specView p s'))
      ∧ (s ≠ s' → specView p s ≠ specView p s') :=
  ⟨rfl, rfl, fun hs he => hs (congrArg met he)⟩

theorem no_client_reads_the_implementation {W X : Type} (p : Plan)
    (s s' : build W p) (q : Quiz Plan X) :
    interrogate q (specView p s) = interrogate q (specView p s') :=
  a_strategy_hears_no_guest p s s' q

def retune {I I' O : Type} (f : I' → I) (m : Machine I O) : Machine I' O :=
  ⟨m.S, m.s0, fun s i' => m.step s (f i'), m.out⟩

theorem hearing_through_a_translator {I I' O : Type} (f : I' → I)
    (m : Machine I O) :
    ∀ (w : List I') (s : m.S),
      drive (retune f m) s w = drive m s (w.map f)
  | [], _ => rfl
  | _ :: w, _ => hearing_through_a_translator f m w _

theorem translators_stack_backward {I I' I'' O : Type} (f : I' → I)
    (g : I'' → I') (m : Machine I O) :
    retune (fun x => f (g x)) m = retune g (retune f m) := rfl

theorem the_plain_ear_hears_plainly {I O : Type} (m : Machine I O) :
    retune (fun i => i) m = m := rfl

def revoice {I O O' : Type} (g : O → O') (m : Machine I O) : Machine I O' :=
  ⟨m.S, m.s0, m.step, fun s => g (m.out s)⟩

theorem speaking_through_a_translator {I O O' : Type} (g : O → O')
    (m : Machine I O) :
    ∀ (w : List I) (s : m.S), drive (revoice g m) s w = g (drive m s w)
  | [], _ => rfl
  | _ :: w, _ => speaking_through_a_translator g m w _

theorem voices_stack_forward {I O O' O'' : Type} (g : O → O')
    (g' : O' → O'') (m : Machine I O) :
    revoice (fun x => g' (g x)) m = revoice g' (revoice g m) := rfl

theorem the_ear_and_the_voice_commute {I I' O O' : Type} (f : I' → I)
    (g : O → O') (m : Machine I O) :
    revoice g (retune f m) = retune f (revoice g m) := rfl

theorem an_upgrade_ships_unheard {W : Type} (p : Plan)
    (σ : Plan → build W p → build W p) (s : build W p) :
    vertical σ (specView p s) = specView p (σ p s) := rfl

theorem the_mirror_doubles_the_manifest {W : Type} (p : Plan)
    (s : build W p) :
    pour (.board p p) (mirror W p s) = pour p s ++ pour p s := rfl

def worldline (t : Plan) : List Plan → Plan
  | [] => t
  | q :: qs => worldline (graft t q) qs

def epochs {X : Type u} (mul : X → X → X) : X → List Plan → X
  | v, [] => v
  | v, q :: qs => epochs mul (fold mul v q) qs

theorem the_worldline_is_a_walk : ∀ (qs : List Plan) (t : Plan),
    worldline t qs = walk graft t qs
  | [], _ => rfl
  | q :: qs, t => the_worldline_is_a_walk qs (graft t q)

theorem the_epochs_are_a_walk {X : Type u} (mul : X → X → X) :
    ∀ (qs : List Plan) (v : X),
      epochs mul v qs = walk (fun x q => fold mul x q) v qs
  | [], _ => rfl
  | q :: qs, v => the_epochs_are_a_walk mul qs (fold mul v q)

theorem the_three_roads_are_one_walk {I O : Type} (m : Machine I O)
    {X : Type u} (mul : X → X → X) (v : X) (t : Plan)
    (w : List I) (s : m.S) (qs : List Plan) :
    park m s w = walk m.step s w
      ∧ drive m s w = m.out (walk m.step s w)
      ∧ worldline t qs = walk graft t qs
      ∧ epochs mul v qs = walk (fun x q => fold mul x q) v qs :=
  ⟨the_park_is_a_walk m w s, the_drive_reads_the_walk m w s,
   the_worldline_is_a_walk qs t, the_epochs_are_a_walk mul qs v⟩

theorem the_worldline_settles {X : Type u} (mul : X → X → X) (x₀ : X)
    (qs : List Plan) (t : Plan) :
    fold mul x₀ (worldline t qs) = epochs mul (fold mul x₀ t) qs :=
  ((congrArg (fold mul x₀) (the_worldline_is_a_walk qs t)).trans
    (a_reading_in_step_carries_the_walk graft (fun v q => fold mul v q)
      (fold mul x₀) (fun s q => the_parent_folds_into_the_ground mul x₀ s q)
      qs t)).trans
    (the_epochs_are_a_walk mul qs (fold mul x₀ t)).symm

theorem mem_map_intro {A B : Type} (f : A → B) :
    ∀ {x : A} {xs : List A}, x ∈ xs → f x ∈ xs.map f
  | _, _ :: _, List.Mem.head _ => List.Mem.head _
  | _, _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_map_intro f h)

theorem mem_append_left {A : Type} (ys : List A) :
    ∀ {x : A} {xs : List A}, x ∈ xs → x ∈ xs ++ ys
  | _, _ :: _, List.Mem.head _ => List.Mem.head _
  | _, _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_append_left ys h)

theorem mem_append_right {A : Type} :
    ∀ (xs : List A) {x : A} {ys : List A}, x ∈ ys → x ∈ xs ++ ys
  | [], _, _, h => h
  | _ :: xs, _, _, h => List.Mem.tail _ (mem_append_right xs h)

theorem mem_append_split {A : Type} :
    ∀ (xs : List A) {x : A} {ys : List A}, x ∈ xs ++ ys → x ∈ xs ∨ x ∈ ys
  | [], _, _, h => Or.inr h
  | _ :: xs, _, _, h =>
      match h with
      | List.Mem.head _ => Or.inl (List.Mem.head _)
      | List.Mem.tail _ h' =>
          match mem_append_split xs h' with
          | Or.inl hx => Or.inl (List.Mem.tail _ hx)
          | Or.inr hy => Or.inr hy

theorem mem_map_back {A B : Type} {f : A → B} {y : B} :
    ∀ (xs : List A), y ∈ xs.map f → ∃ a, a ∈ xs ∧ f a = y
  | [], h => nomatch h
  | x :: xs, h => by
      cases h with
      | head => exact ⟨x, List.Mem.head _, rfl⟩
      | tail _ h' =>
          obtain ⟨a, ha, he⟩ := mem_map_back xs h'
          exact ⟨a, List.Mem.tail _ ha, he⟩

theorem mem_cross {qs : List Plan} {r : Plan} (hr : r ∈ qs) :
    ∀ {ps : List Plan} {l : Plan}, l ∈ ps → Plan.board l r ∈ cross ps qs
  | _ :: ps, _, List.Mem.head _ =>
      mem_append_left (cross ps qs) (mem_map_intro (Plan.board _) hr)
  | p :: _, _, List.Mem.tail _ h =>
      mem_append_right (qs.map (Plan.board p)) (mem_cross hr h)

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

theorem the_reading_is_positive :
    ∀ p : Plan, ∃ m : Nat, fold (fun a b => a + b) 1 p = m + 1
  | .ground => ⟨0, rfl⟩
  | .board l r =>
      match the_reading_is_positive l with
      | ⟨a, ha⟩ =>
          ⟨a + fold (fun a b => a + b) 1 r, by
            show fold (fun a b => a + b) 1 l + fold (fun a b => a + b) 1 r
                = (a + fold (fun a b => a + b) 1 r) + 1
            rw [ha, succ_adds]⟩

theorem ble_le_add : ∀ a b : Nat, Nat.ble a (a + b) = true
  | a, 0 => ble_refl a
  | a, b + 1 =>
      ble_trans a (a + b) ((a + b) + 1) (ble_le_add a b) (ble_le_succ (a + b))

theorem ble_le_add_left : ∀ a b : Nat, Nat.ble b (a + b) = true
  | 0, b => by rw [zero_plus]; exact ble_refl b
  | a + 1, b => by
      rw [succ_adds]
      exact ble_trans b (a + b) ((a + b) + 1)
        (ble_le_add_left a b) (ble_le_succ (a + b))

theorem ble_add_right : ∀ (k : Nat) {a b : Nat},
    Nat.ble a b = true → Nat.ble (a + k) (b + k) = true
  | 0, _, _, h => h
  | k + 1, _, _, h => ble_add_right k h

theorem ble_add_both {a b c d : Nat} (h1 : Nat.ble a b = true)
    (h2 : Nat.ble c d = true) : Nat.ble (a + c) (b + d) = true :=
  ble_trans (a + c) (b + c) (b + d) (ble_add_right c h1)
    (by rw [Nat.add_comm b c, Nat.add_comm b d]; exact ble_add_right b h2)

theorem ble_gain_false : ∀ m a : Nat, Nat.ble (m + (a + 1)) m = false
  | 0, _ => rfl
  | m + 1, a => by
      show Nat.ble ((m + 1) + a) m = false
      rw [succ_adds]
      exact ble_gain_false m a

def roomCap : Nat → Nat
  | 0 => 1
  | d + 1 => roomCap d + roomCap d

theorem the_cap_is_positive : ∀ d : Nat, ∃ m : Nat, roomCap d = m + 1
  | 0 => ⟨0, rfl⟩
  | d + 1 =>
      match the_cap_is_positive d with
      | ⟨m, h⟩ =>
          ⟨(m + 1) + m, by
            show roomCap d + roomCap d = ((m + 1) + m) + 1
            rw [h]
            exact rfl⟩

theorem the_horizon_holds_every_reading :
    ∀ (n : Nat) (p : Plan),
      Nat.ble (fold (fun a b => a + b) 1 p) (n + 1) = true → p ∈ allPlans n
  | 0, .ground, _ => List.Mem.head _
  | _ + 1, .ground, _ => List.Mem.head _
  | 0, .board l r, h =>
      match the_reading_is_positive l, the_reading_is_positive r with
      | ⟨a, ha⟩, ⟨b, hb⟩ => by
          have e : (a + 1) + (b + 1) = ((a + b) + 1) + 1 :=
            congrArg (· + 1) (succ_adds a b)
          have h0 : Nat.ble
              (fold (fun a b => a + b) 1 l + fold (fun a b => a + b) 1 r)
              1 = true := h
          rw [ha, hb, e] at h0
          exact nomatch h0
  | n + 1, .board l r, h =>
      match the_reading_is_positive l, the_reading_is_positive r with
      | ⟨a, ha⟩, ⟨b, hb⟩ =>
          have e : (a + 1) + (b + 1) = ((a + b) + 1) + 1 :=
            congrArg (· + 1) (succ_adds a b)
          have h' : Nat.ble ((a + b) + 1) (n + 1) = true := by
            have h0 : Nat.ble
                (fold (fun a b => a + b) 1 l + fold (fun a b => a + b) 1 r)
                ((n + 1) + 1) = true := h
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

theorem the_room_only_grows :
    ∀ (d : Nat) {p : Plan}, p ∈ allPlans d → p ∈ allPlans (d + 1)
  | 0, _, h => by
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact nomatch h'
  | d + 1, _, h => by
      cases h with
      | head => exact List.Mem.head _
      | tail _ hc =>
          obtain ⟨l, r, rfl, hl, hr⟩ := mem_cross_split (allPlans d) hc
          exact List.Mem.tail _
            (mem_cross (the_room_only_grows d hr) (the_room_only_grows d hl))

theorem the_room_reads_within_its_cap :
    ∀ (d : Nat) {p : Plan}, p ∈ allPlans d →
      Nat.ble (fold (fun a b => a + b) 1 p) (roomCap d) = true
  | 0, _, h => by
      cases h with
      | head => rfl
      | tail _ h' => exact nomatch h'
  | d + 1, _, h => by
      cases h with
      | head =>
          obtain ⟨m, hm⟩ := the_cap_is_positive d
          show Nat.ble 1 (roomCap d + roomCap d) = true
          rw [hm]
          exact rfl
      | tail _ hc =>
          obtain ⟨l, r, rfl, hl, hr⟩ := mem_cross_split (allPlans d) hc
          exact ble_add_both
            (the_room_reads_within_its_cap d hl)
            (the_room_reads_within_its_cap d hr)

def bloom : Nat → Plan
  | 0 => .ground
  | d + 1 => .board (bloom d) (bloom d)

theorem the_bloom_fills_its_cap :
    ∀ d : Nat, fold (fun a b => a + b) 1 (bloom d) = roomCap d
  | 0 => rfl
  | d + 1 => by
      show fold (fun a b => a + b) 1 (bloom d)
            + fold (fun a b => a + b) 1 (bloom d)
          = roomCap d + roomCap d
      rw [the_bloom_fills_its_cap d]

theorem the_bloom_resides : ∀ d : Nat, bloom d ∈ allPlans d
  | 0 => List.Mem.head _
  | d + 1 =>
      List.Mem.tail _ (mem_cross (the_bloom_resides d) (the_bloom_resides d))

theorem the_bloom_outgrows_the_room (d : Nat) :
    ¬ bloom (d + 1) ∈ allPlans d := fun hmem => by
  have hb := the_room_reads_within_its_cap d hmem
  rw [the_bloom_fills_its_cap (d + 1)] at hb
  have hb' : Nat.ble (roomCap d + roomCap d) (roomCap d) = true := hb
  obtain ⟨m, hm⟩ := the_cap_is_positive d
  rw [hm] at hb'
  exact nomatch (ble_gain_false (m + 1) m).symm.trans hb'

theorem no_bound_is_the_last_bound :
    (∀ (d : Nat) (p : Plan), p ∈ allPlans d → p ∈ allPlans (d + 1))
      ∧ (∀ p : Plan, ∃ d : Nat, p ∈ allPlans d)
      ∧ (∀ d : Nat, ∃ p : Plan, ¬ p ∈ allPlans d ∧ p ∈ allPlans (d + 1))
      ∧ ∀ d : Nat, allPlans (d + 1) ≠ allPlans d :=
  ⟨fun d _ h => the_room_only_grows d h,
   fun p =>
     ⟨fold (fun a b => a + b) 1 p,
      the_horizon_holds_every_reading _ p (ble_le_succ _)⟩,
   fun d =>
     ⟨bloom (d + 1), the_bloom_outgrows_the_room d, the_bloom_resides (d + 1)⟩,
   fun d he =>
     the_bloom_outgrows_the_room d (he ▸ the_bloom_resides (d + 1))⟩

inductive Apart {A : Type} : List A → Prop
  | nil : Apart []
  | cons {a : A} {l : List A} :
      (∀ b, b ∈ l → a ≠ b) → Apart l → Apart (a :: l)

theorem apart_map {A B : Type} {f : A → B}
    (hf : ∀ a b, f a = f b → a = b) :
    ∀ {xs : List A}, Apart xs → Apart (xs.map f)
  | [], _ => Apart.nil
  | x :: xs, Apart.cons hx hxs =>
      Apart.cons
        (fun _ hb he =>
          match mem_map_back xs hb with
          | ⟨a, ha, hfa⟩ => hx a ha (hf x a (he.trans hfa.symm)))
        (apart_map hf hxs)

theorem apart_append {A : Type} :
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

theorem the_room_repeats_no_plan : ∀ d : Nat, Apart (allPlans d)
  | 0 => Apart.cons (fun _ hb => nomatch hb) Apart.nil
  | d + 1 =>
      Apart.cons
        (fun _ hb =>
          match mem_cross_split (allPlans d) hb with
          | ⟨_, _, he, _, _⟩ => fun hg => nomatch hg.trans he)
        (the_cross_keeps_apart (the_room_repeats_no_plan d)
          (the_room_repeats_no_plan d))

theorem eq_of_beq : ∀ a b : Nat, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | a + 1, b + 1, h => congrArg (· + 1) (eq_of_beq a b h)

theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

theorem ne_true_of_eq_false {x : Bool} (h : x = false) : ¬ x = true :=
  fun ht => nomatch h.symm.trans ht

theorem mem_of_mem_filter {A : Type} {q : A → Bool} {x : A} :
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

theorem filter_holds {A : Type} {q : A → Bool} {x : A} :
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

theorem mem_filter_intro {A : Type} {q : A → Bool} {x : A} :
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

theorem apart_filter {A : Type} {q : A → Bool} :
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

theorem the_census_is_exact (k : Nat) :
    Apart ((allPlans k).filter
        (fun p => Nat.beq (fold (fun a b => a + b) 1 p) (k + 1)))
      ∧ ∀ p : Plan,
          p ∈ (allPlans k).filter
              (fun p => Nat.beq (fold (fun a b => a + b) 1 p) (k + 1))
            ↔ fold (fun a b => a + b) 1 p = k + 1 :=
  ⟨apart_filter (the_room_repeats_no_plan k),
   fun p =>
     ⟨fun h =>
        have hq :=
          filter_holds (A := Plan)
            (q := fun p => Nat.beq (fold (fun a b => a + b) 1 p) (k + 1))
            (x := p) (allPlans k) h
        eq_of_beq _ _ hq,
      fun h =>
        mem_filter_intro (allPlans k)
          (the_horizon_holds_every_reading k p
            (by rw [h]; exact ble_refl (k + 1)))
          (by rw [h]; exact beq_self (k + 1))⟩⟩

def ride {W : Type} {t : Plan} (s : build W t) :
    (δ : Plan) → build W (graft t δ)
  | .ground => s
  | .board p q => atTheDoor (ride s p) (ride s q)

theorem the_ground_revision_keeps_the_passenger {W : Type} {t : Plan}
    (s : build W t) : ride s .ground = s := rfl

theorem the_mirror_is_a_ride {W : Type} (t : Plan) (s : build W t) :
    ride s (.board .ground .ground) = mirror W t s := rfl

theorem the_passenger_keeps_the_face {W : Type} {t : Plan} (s : build W t) :
    ∀ δ : Plan, spine W (graft t δ) (ride s δ) = spine W t s
  | .ground => rfl
  | .board p _ => the_passenger_keeps_the_face s p

theorem the_passenger_multiplies_the_manifest {W : Type} {t : Plan}
    (s : build W t) :
    ∀ δ : Plan, pour (graft t δ) (ride s δ)
      = fold (fun a b => a ++ b) (pour t s) δ
  | .ground => rfl
  | .board p q => by
      show pour (graft t p) (ride s p) ++ pour (graft t q) (ride s q)
          = fold (fun a b => a ++ b) (pour t s) p
            ++ fold (fun a b => a ++ b) (pour t s) q
      rw [the_passenger_multiplies_the_manifest s p,
          the_passenger_multiplies_the_manifest s q]

theorem the_rides_compose_at_the_manifest {W : Type} {t : Plan}
    (s : build W t) (δ₁ δ₂ : Plan) :
    pour (graft (graft t δ₁) δ₂) (ride (ride s δ₁) δ₂)
      = pour (graft t (graft δ₁ δ₂)) (ride s (graft δ₁ δ₂)) :=
  ((the_passenger_multiplies_the_manifest (ride s δ₁) δ₂).trans
    (congrArg (fun l => fold (fun a b => a ++ b) l δ₂)
      (the_passenger_multiplies_the_manifest s δ₁))).trans
    ((the_passenger_multiplies_the_manifest s (graft δ₁ δ₂)).trans
      (the_parent_folds_into_the_ground (fun a b => a ++ b)
        (pour t s) δ₁ δ₂)).symm

theorem the_door_carries_the_heq {H H' V V' : Type}
    (hH : H = H') (hV : V = V') {a : H} {a' : H'} {b : V} {b' : V'}
    (ha : HEq a a') (hb : HEq b b') :
    HEq (atTheDoor a b) (atTheDoor a' b') := by
  cases hH; cases hV; cases ha; cases hb; rfl

theorem the_rides_compose {W : Type} {t : Plan} (s : build W t) :
    ∀ (δ₂ δ₁ : Plan), HEq (ride (ride s δ₁) δ₂) (ride s (graft δ₁ δ₂))
  | .ground, δ₁ => HEq.refl (ride s δ₁)
  | .board p q, δ₁ =>
      the_door_carries_the_heq
        (congrArg (build W) (lineages_compose t δ₁ p).symm)
        (congrArg (build W) (lineages_compose t δ₁ q).symm)
        (the_rides_compose s p δ₁) (the_rides_compose s q δ₁)

theorem the_lineage_law_settles_the_carrier {W : Type} {t : Plan}
    (s : build W t) (δ₁ δ₂ : Plan) :
    cast (congrArg (build W) (lineages_compose t δ₁ δ₂).symm)
      (ride (ride s δ₁) δ₂)
      = ride s (graft δ₁ δ₂) :=
  eq_of_heq ((cast_heq _ _).trans (the_rides_compose s δ₂ δ₁))

theorem two_routes_one_rider {W : Type} {t : Plan} (s : build W t)
    (δ₁ δ₂ : Plan) :
    cast (congrArg (build W) (lineages_compose t δ₁ δ₂).symm)
        (ride (ride s δ₁) δ₂) = ride s (graft δ₁ δ₂)
      ∧ spine W (graft (graft t δ₁) δ₂) (ride (ride s δ₁) δ₂)
          = spine W (graft t (graft δ₁ δ₂)) (ride s (graft δ₁ δ₂))
      ∧ pour (graft (graft t δ₁) δ₂) (ride (ride s δ₁) δ₂)
          = pour (graft t (graft δ₁ δ₂)) (ride s (graft δ₁ δ₂)) :=
  ⟨the_lineage_law_settles_the_carrier s δ₁ δ₂,
   ((the_passenger_keeps_the_face (ride s δ₁) δ₂).trans
      (the_passenger_keeps_the_face s δ₁)).trans
     (the_passenger_keeps_the_face s (graft δ₁ δ₂)).symm,
   the_rides_compose_at_the_manifest s δ₁ δ₂⟩

theorem the_transport_sheds_its_route {A B : Type u} (h h' : A = B)
    (x : A) : cast h x = cast h' x :=
  congrArg (fun p => cast p x) (the_route_leaves_no_mark h h')

theorem any_lineage_proof_settles_the_carrier {W : Type} {t : Plan}
    (s : build W t) (δ₁ δ₂ : Plan)
    (h : build W (graft (graft t δ₁) δ₂)
      = build W (graft t (graft δ₁ δ₂))) :
    cast h (ride (ride s δ₁) δ₂) = ride s (graft δ₁ δ₂) :=
  (the_transport_sheds_its_route h
      (congrArg (build W) (lineages_compose t δ₁ δ₂).symm)
      (ride (ride s δ₁) δ₂)).trans
    (the_lineage_law_settles_the_carrier s δ₁ δ₂)

theorem the_customs_ride_along {W W' : Type} (f : W → W') {t : Plan}
    (s : build W t) :
    ∀ δ : Plan,
      reground f (graft t δ) (ride s δ) = ride (reground f t s) δ
  | .ground => rfl
  | .board p q => by
      show atTheDoor (reground f (graft t p) (ride s p))
            (reground f (graft t q) (ride s q))
          = atTheDoor (ride (reground f t s) p) (ride (reground f t s) q)
      rw [the_customs_ride_along f s p, the_customs_ride_along f s q]

def journey {W : Type} {t : Plan} (s : build W t) :
    (qs : List Plan) → build W (worldline t qs)
  | [] => s
  | q :: qs => journey (ride s q) qs

theorem the_worldline_resumes (qs qs' : List Plan) (t : Plan) :
    worldline t (qs ++ qs') = worldline (worldline t qs) qs' :=
  (((the_worldline_is_a_walk (qs ++ qs') t).trans
      (the_walk_resumes graft qs qs' t)).trans
    (congrArg (fun x => walk graft x qs')
      (the_worldline_is_a_walk qs t)).symm).trans
    (the_worldline_is_a_walk qs' (worldline t qs)).symm

theorem the_face_survives_the_journey {W : Type} :
    ∀ (qs : List Plan) {t : Plan} (s : build W t),
      spine W (worldline t qs) (journey s qs) = spine W t s
  | [], _, _ => rfl
  | q :: qs, _, s =>
      (the_face_survives_the_journey qs (ride s q)).trans
        (the_passenger_keeps_the_face s q)

theorem the_journey_manifest_settles {W : Type} :
    ∀ (qs : List Plan) {t : Plan} (s : build W t),
      pour (worldline t qs) (journey s qs)
        = epochs (fun a b => a ++ b) (pour t s) qs
  | [], _, _ => rfl
  | q :: qs, _, s =>
      (the_journey_manifest_settles qs (ride s q)).trans
        (congrArg (fun l => epochs (fun a b => a ++ b) l qs)
          (the_passenger_multiplies_the_manifest s q))

theorem the_journeys_compose {W : Type} :
    ∀ (qs qs' : List Plan) {t : Plan} (s : build W t),
      HEq (journey s (qs ++ qs')) (journey (journey s qs) qs')
  | [], _, _, s => HEq.refl (journey s _)
  | q :: qs, qs', _, s => the_journeys_compose qs qs' (ride s q)

theorem the_life_resumes_from_the_parked_rider {W : Type}
    (qs qs' : List Plan) {t : Plan} (s : build W t) :
    cast (congrArg (build W) (the_worldline_resumes qs qs' t))
      (journey s (qs ++ qs'))
      = journey (journey s qs) qs' :=
  eq_of_heq ((cast_heq _ _).trans (the_journeys_compose qs qs' s))

theorem the_customs_survive_the_journey {W W' : Type} (f : W → W') :
    ∀ (qs : List Plan) {t : Plan} (s : build W t),
      reground f (worldline t qs) (journey s qs)
        = journey (reground f t s) qs
  | [], _, _ => rfl
  | q :: qs, _, s =>
      (the_customs_survive_the_journey f qs (ride s q)).trans
        (congrArg (fun x => journey x qs) (the_customs_ride_along f s q))

theorem the_worldline_carries_its_rider {W W' : Type} (f : W → W')
    (qs qs' : List Plan) {t : Plan} (s : build W t) :
    spine W (worldline t qs) (journey s qs) = spine W t s
      ∧ pour (worldline t qs) (journey s qs)
          = epochs (fun a b => a ++ b) (pour t s) qs
      ∧ cast (congrArg (build W) (the_worldline_resumes qs qs' t))
          (journey s (qs ++ qs'))
          = journey (journey s qs) qs'
      ∧ reground f (worldline t qs) (journey s qs)
          = journey (reground f t s) qs :=
  ⟨the_face_survives_the_journey qs s,
   the_journey_manifest_settles qs s,
   the_life_resumes_from_the_parked_rider qs qs' s,
   the_customs_survive_the_journey f qs s⟩

theorem the_ground_rides_in_every_graft (t : Plan) :
    ∀ δ : Plan, Nat.ble (fold (fun a b => a + b) 1 t)
      (fold (fun a b => a + b) 1 (graft t δ)) = true
  | .ground => ble_refl _
  | .board p _ =>
      ble_trans _ _ _ (the_ground_rides_in_every_graft t p) (ble_le_add _ _)

theorem a_true_tick_grows_the_reading (t : Plan) :
    ∀ {δ : Plan}, δ ≠ Plan.ground →
      Nat.ble (fold (fun a b => a + b) 1 t + 1)
        (fold (fun a b => a + b) 1 (graft t δ)) = true
  | .ground, h => absurd rfl h
  | .board p q, _ =>
      match the_reading_is_positive (graft t q) with
      | ⟨m, hm⟩ =>
          show Nat.ble (fold (fun a b => a + b) 1 t + 1)
              (fold (fun a b => a + b) 1 (graft t p)
                + fold (fun a b => a + b) 1 (graft t q)) = true
            from ble_add_both (the_ground_rides_in_every_graft t p)
              (by rw [hm]; exact rfl)

theorem the_worldline_never_comes_home (t : Plan) {δ : Plan}
    (hδ : δ ≠ Plan.ground) : graft t δ ≠ t :=
  fun he =>
    nomatch (ble_gain_false (fold (fun a b => a + b) 1 t) 0).symm.trans
      ((congrArg
          (fun x => Nat.ble (fold (fun a b => a + b) 1 t + 1)
            (fold (fun a b => a + b) 1 x)) he).symm.trans
        (a_true_tick_grows_the_reading t hδ))

theorem the_arrow_counts_the_ticks (t : Plan) :
    ∀ qs : List Plan, (∀ q, q ∈ qs → q ≠ Plan.ground) →
      Nat.ble (fold (fun a b => a + b) 1 t + qs.length)
        (fold (fun a b => a + b) 1 (worldline t qs)) = true
  | [], _ => ble_refl _
  | q :: qs, hng => by
      show Nat.ble (fold (fun a b => a + b) 1 t + (qs.length + 1))
          (fold (fun a b => a + b) 1 (worldline (graft t q) qs)) = true
      rw [show fold (fun a b => a + b) 1 t + (qs.length + 1)
            = (fold (fun a b => a + b) 1 t + 1) + qs.length from
          (succ_adds (fold (fun a b => a + b) 1 t) qs.length).symm]
      exact ble_trans _ _ _
        (ble_add_right qs.length
          (a_true_tick_grows_the_reading t (hng q (List.Mem.head _))))
        (the_arrow_counts_the_ticks (graft t q) qs
          (fun x hx => hng x (List.Mem.tail _ hx)))

theorem time_wears_no_wheel (t : Plan) (q : Plan) (qs : List Plan)
    (hq : q ≠ Plan.ground) (hqs : ∀ x, x ∈ q :: qs → x ≠ Plan.ground) :
    Nat.ble (fold (fun a b => a + b) 1 t + 1)
        (fold (fun a b => a + b) 1 (graft t q)) = true
      ∧ graft t q ≠ t
      ∧ Nat.ble (fold (fun a b => a + b) 1 t + (q :: qs).length)
          (fold (fun a b => a + b) 1 (worldline t (q :: qs))) = true
      ∧ worldline t (q :: qs) ≠ t :=
  ⟨a_true_tick_grows_the_reading t hq,
   the_worldline_never_comes_home t hq,
   the_arrow_counts_the_ticks t (q :: qs) hqs,
   fun he =>
     nomatch (ble_gain_false (fold (fun a b => a + b) 1 t)
         qs.length).symm.trans
       ((congrArg
           (fun x => Nat.ble
             (fold (fun a b => a + b) 1 t + (qs.length + 1))
             (fold (fun a b => a + b) 1 x)) he).symm.trans
         (the_arrow_counts_the_ticks t (q :: qs) hqs))⟩

def flip : Machine Unit Bool := ⟨Bool, false, fun b _ => !b, fun b => b⟩

theorem the_flip_wheels : ∀ b : Bool, park flip b [(), ()] = b
  | true => rfl
  | false => rfl

theorem the_pace_parks_at_its_count :
    ∀ (w : List Unit) (s : Nat), park paceOne s w = s + w.length
  | [], _ => rfl
  | _ :: w, s =>
      (the_pace_parks_at_its_count w (s + 1)).trans (succ_adds s w.length)

theorem no_gain_is_zero : ∀ a b : Nat, a + (b + 1) = a → False
  | 0, _, h => nomatch h
  | a + 1, b, h =>
      no_gain_is_zero a b (Nat.succ.inj ((succ_adds a (b + 1)).symm.trans h))

theorem the_pace_reads_as_the_flip (w : List Unit) (a : Nat) (b : Bool)
    (h : oddNat a = b) : drive paceOne a w = drive flip b w :=
  two_machines_in_step_agree paceOne flip
    (fun (a : Nat) (b : Bool) => oddNat a = b)
    (fun _ _ _ h => congrArg (! ·) h)
    (fun _ _ h => h) w a b h

theorem the_wheel_and_the_arrow_share_a_face (w : List Unit) :
    behavior paceOne w = behavior flip w
      ∧ (∀ b : Bool, park flip b [(), ()] = b)
      ∧ ∀ (v : List Unit) (s : Nat), park paceOne s (() :: v) ≠ s :=
  ⟨the_pace_reads_as_the_flip w 0 false rfl,
   the_flip_wheels,
   fun v s he =>
     no_gain_is_zero s v.length
       ((the_pace_parks_at_its_count (() :: v) s).symm.trans he)⟩

theorem seats_forget_stages_remember (t : Plan) {δ : Plan}
    (hδ : δ ≠ Plan.ground) :
    (([true, false] ≠ [false, true])
        ∧ park pulse (0 : Nat) [true, false]
            = park pulse (0 : Nat) [false, true])
      ∧ graft t δ ≠ t :=
  ⟨two_routes_one_seat, the_worldline_never_comes_home t hδ⟩

theorem time_outgrows_every_room (d : Nat) (qs : List Plan)
    (hng : ∀ q, q ∈ qs → q ≠ Plan.ground)
    (hlen : Nat.ble (roomCap d) qs.length = true) :
    ¬ worldline Plan.ground qs ∈ allPlans d := by
  intro hmem
  have hcap := the_room_reads_within_its_cap d hmem
  have harrow : Nat.ble (qs.length + 1)
      (fold (fun a b => a + b) 1 (worldline Plan.ground qs)) = true := by
    rw [Nat.add_comm qs.length 1]
    exact the_arrow_counts_the_ticks Plan.ground qs hng
  have hcontra : false = true :=
    (ble_gain_false (roomCap d) 0).symm.trans
      (ble_trans _ _ _
        (ble_trans _ _ _ (ble_add_right 1 hlen) harrow) hcap)
  exact nomatch hcontra

theorem the_learner_never_leaves_its_first_window {I : Type}
    (m : Machine I Measured)
    (hlearn : ∀ s i, tighter (m.out (m.step s i)) (m.out s) = true)
    (s : m.S) (w : List I) {r : Measured}
    (hr : tighter r (m.out s) = false) : drive m s w ≠ r :=
  fun he =>
    ne_true_of_eq_false hr
      ((congrArg (fun x => tighter x (m.out s)) he).symm.trans
        (the_learner_only_tightens m hlearn w s))

theorem a_window_may_loosen :
    tighter (⟨0, 1⟩ : Measured) (⟨0, 0⟩ : Measured) = false := rfl

theorem the_revision_is_not_a_refinement {I : Type} (m : Machine I Measured)
    (hlearn : ∀ s i, tighter (m.out (m.step s i)) (m.out s) = true)
    (s : m.S) (w : List I) (t : Plan) {δ : Plan} (hδ : δ ≠ Plan.ground) :
    (∀ r : Measured, tighter r (m.out s) = false → drive m s w ≠ r)
      ∧ tighter (⟨0, 1⟩ : Measured) (⟨0, 0⟩ : Measured) = false
      ∧ Nat.ble (fold (fun a b => a + b) 1 t + 1)
          (fold (fun a b => a + b) 1 (graft t δ)) = true
      ∧ graft t δ ≠ t :=
  ⟨fun _ hr => the_learner_never_leaves_its_first_window m hlearn s w hr,
   rfl,
   a_true_tick_grows_the_reading t hδ,
   the_worldline_never_comes_home t hδ⟩

theorem and_false : ∀ b : Bool, (b && false) = false
  | true => rfl
  | false => rfl

theorem the_excluded_stays_excluded {fine coarse : Measured} {x : Nat}
    (ht : tighter fine coarse = true) (hx : within coarse x = false) :
    within fine x = false := by
  cases h : within fine x with
  | false => rfl
  | true =>
      exact absurd (the_refined_reading_still_lands ht h)
        (ne_true_of_eq_false hx)

theorem the_learner_never_admits_the_excluded {I : Type}
    (m : Machine I Measured)
    (hlearn : ∀ s i, tighter (m.out (m.step s i)) (m.out s) = true)
    (s : m.S) (w : List I) {x : Nat}
    (hx : within (m.out s) x = false) : within (drive m s w) x = false :=
  the_excluded_stays_excluded (the_learner_only_tightens m hlearn w s) hx

theorem every_admission_names_its_loosening {I : Type}
    (m : Machine I Measured) :
    ∀ (w : List I) (s : m.S) (x : Nat),
      within (m.out s) x = false → within (drive m s w) x = true →
      ∃ (w₁ : List I) (i : I) (w₂ : List I),
        w = w₁ ++ i :: w₂
          ∧ tighter (m.out (m.step (park m s w₁) i))
              (m.out (park m s w₁)) = false
  | [], _, _, hx, hadm => absurd hadm (ne_true_of_eq_false hx)
  | i :: w, s, x, hx, hadm => by
      cases ht : tighter (m.out (m.step s i)) (m.out s) with
      | false => exact ⟨[], i, w, rfl, ht⟩
      | true =>
          obtain ⟨w₁, j, w₂, he, hl⟩ :=
            every_admission_names_its_loosening m w (m.step s i) x
              (the_excluded_stays_excluded ht hx) hadm
          exact ⟨i :: w₁, j, w₂, congrArg (i :: ·) he, hl⟩

theorem time_outgrows_every_window (t : Plan) (d : Nat) (qs : List Plan)
    (hng : ∀ q, q ∈ qs → q ≠ Plan.ground)
    (hlen : Nat.ble (d + 1) qs.length = true) :
    within
      ⟨fold (fun a b => a + b) 1 t, fold (fun a b => a + b) 1 t + d⟩
      (fold (fun a b => a + b) 1 (worldline t qs)) = false := by
  have hstep : Nat.ble (fold (fun a b => a + b) 1 t + (d + 1))
      (fold (fun a b => a + b) 1 t + qs.length) = true :=
    ble_add_both (ble_refl (fold (fun a b => a + b) 1 t)) hlen
  have hbig : Nat.ble (fold (fun a b => a + b) 1 t + (d + 1))
      (fold (fun a b => a + b) 1 (worldline t qs)) = true :=
    ble_trans _ _ _ hstep (the_arrow_counts_the_ticks t qs hng)
  show (Nat.ble (fold (fun a b => a + b) 1 t)
          (fold (fun a b => a + b) 1 (worldline t qs))
      && Nat.ble (fold (fun a b => a + b) 1 (worldline t qs))
          (fold (fun a b => a + b) 1 t + d)) = false
  cases hR : Nat.ble (fold (fun a b => a + b) 1 (worldline t qs))
      (fold (fun a b => a + b) 1 t + d) with
  | false => exact and_false _
  | true =>
      exact absurd (ble_trans _ _ _ hbig hR)
        (ne_true_of_eq_false
          (ble_gain_false (fold (fun a b => a + b) 1 t + d) 0))

theorem the_near_pace_lands_in_the_window (a g e : Nat) :
    within ⟨a, a + ((g + 1) + e)⟩ (a + (g + 1)) = true :=
  and_glue (ble_le_add a (g + 1))
    (by rw [← Nat.add_assoc a (g + 1) e]; exact ble_le_add (a + (g + 1)) e)

theorem the_gap_outruns_every_window (a g d : Nat) :
    within ⟨(d + 1) * a, (d + 1) * a + d⟩ ((d + 1) * (a + (g + 1))) = false := by
  have h1 : d + ((d + 1) * g + 1) = (d + 1) * g + (d + 1) :=
    show (d + (d + 1) * g) + 1 = ((d + 1) * g + d) + 1 from
      congrArg (· + 1) (Nat.add_comm d ((d + 1) * g))
  have hsplit : (d + 1) * (a + (g + 1))
      = ((d + 1) * a + d) + ((d + 1) * g + 1) := by
    rw [Nat.left_distrib]
    show (d + 1) * a + ((d + 1) * g + (d + 1))
        = ((d + 1) * a + d) + ((d + 1) * g + 1)
    rw [← h1, ← Nat.add_assoc ((d + 1) * a) d ((d + 1) * g + 1)]
  show (Nat.ble ((d + 1) * a) ((d + 1) * (a + (g + 1)))
      && Nat.ble ((d + 1) * (a + (g + 1))) ((d + 1) * a + d)) = false
  rw [hsplit, ble_gain_false ((d + 1) * a + d) ((d + 1) * g)]
  exact and_false _

theorem the_run_reads_the_gap_the_window_cannot (a g e d : Nat) :
    within ⟨a, a + ((g + 1) + e)⟩ (a + (g + 1)) = true
      ∧ within ⟨(d + 1) * a, (d + 1) * a + d⟩
          ((d + 1) * (a + (g + 1))) = false :=
  ⟨the_near_pace_lands_in_the_window a g e, the_gap_outruns_every_window a g d⟩

theorem one_tick_two_doors {W : Type} {t : Plan} (s : build W t)
    {δ : Plan} (hδ : δ ≠ Plan.ground) :
    spine W (graft t δ) (ride s δ) = spine W t s
      ∧ face (specView (graft t δ) (ride s δ)) ≠ face (specView t s)
      ∧ met (specView (graft t δ) (ride s δ)) = ride s δ :=
  ⟨the_passenger_keeps_the_face s δ,
   fun he => the_worldline_never_comes_home t hδ he,
   rfl⟩

theorem ble_succ_false : ∀ n : Nat, Nat.ble (n + 1) n = false :=
  fun n => ble_gain_false n 0

theorem the_window_misses_its_own_successor (m : Measured) :
    within m (m.hi + 1) = false := by
  show (Nat.ble m.lo (m.hi + 1) && Nat.ble (m.hi + 1) m.hi) = false
  rw [ble_succ_false m.hi]
  exact and_false _

theorem the_learner_exhibits_its_own_invisible {I : Type}
    (m : Machine I Measured)
    (hlearn : ∀ s i, tighter (m.out (m.step s i)) (m.out s) = true)
    (s : m.S) (w : List I) :
    within (drive m s w) ((m.out s).hi + 1) = false :=
  the_learner_never_admits_the_excluded m hlearn s w
    (the_window_misses_its_own_successor (m.out s))

theorem every_room_builds_its_own_escapee {I A : Type}
    (m : Machine I Measured)
    (hlearn : ∀ s i, tighter (m.out (m.step s i)) (m.out s) = true)
    (s : m.S) (w : List I) (g : A → (A → Bool)) :
    within (m.out s) ((m.out s).hi + 1) = false
      ∧ within (drive m s w) ((m.out s).hi + 1) = false
      ∧ ∃ f : A → Bool, ∀ a, g a ≠ f :=
  ⟨the_window_misses_its_own_successor (m.out s),
   the_learner_exhibits_its_own_invisible m hlearn s w,
   the_readings_outrun_the_room g⟩

theorem three_blindnesses_three_channels {H W X : Type} (h : H)
    (w w' : W) (g : H → X) (a p e d : Nat) :
    (g (face (atTheDoor h w)) = g (face (atTheDoor h w'))
        ∧ met (atTheDoor h w) = w)
      ∧ (within (⟨0, 1⟩ : Measured) 0 = true
          ∧ within (⟨0, 1⟩ : Measured) 1 = true
          ∧ (0 : Nat) ≠ 1
          ∧ within (⟨0, 0⟩ : Measured) 0 = true
          ∧ within (⟨0, 0⟩ : Measured) 1 = false)
      ∧ (within ⟨a, a + ((p + 1) + e)⟩ (a + (p + 1)) = true
          ∧ within ⟨(d + 1) * a, (d + 1) * a + d⟩
              ((d + 1) * (a + (p + 1))) = false) :=
  ⟨⟨rfl, rfl⟩,
   ⟨rfl, rfl, (fun hn => nomatch hn), rfl, rfl⟩,
   ⟨the_near_pace_lands_in_the_window a p e,
    the_gap_outruns_every_window a p d⟩⟩

theorem no_revision_is_the_last_revision (m : Measured) :
    within m (m.hi + 1) = false
      ∧ tighter ⟨m.hi + 1, m.hi + 1⟩ m = false
      ∧ within ⟨m.hi + 1, m.hi + 1⟩ (m.hi + 1) = true
      ∧ within ⟨m.hi + 1, m.hi + 1⟩ (m.hi + 1 + 1) = false :=
  ⟨the_window_misses_its_own_successor m,
   by
     show (Nat.ble m.lo (m.hi + 1) && Nat.ble (m.hi + 1) m.hi) = false
     rw [ble_succ_false m.hi]
     exact and_false _,
   and_glue (ble_refl (m.hi + 1)) (ble_refl (m.hi + 1)),
   the_window_misses_its_own_successor ⟨m.hi + 1, m.hi + 1⟩⟩

theorem the_world_outgrows_every_learner {I : Type} (m : Machine I Measured)
    (hlearn : ∀ s i, tighter (m.out (m.step s i)) (m.out s) = true)
    (s : m.S) (qs : List Plan)
    (hng : ∀ q, q ∈ qs → q ≠ Plan.ground)
    (hlen : Nat.ble ((m.out s).hi + 1) qs.length = true) :
    ∀ w : List I,
      within (drive m s w)
        (fold (fun a b => a + b) 1 (worldline Plan.ground qs)) = false := by
  intro w
  apply the_learner_never_admits_the_excluded m hlearn s w
  have harrow : Nat.ble (1 + qs.length)
      (fold (fun a b => a + b) 1 (worldline Plan.ground qs)) = true :=
    the_arrow_counts_the_ticks Plan.ground qs hng
  have hbig : Nat.ble (1 + ((m.out s).hi + 1))
      (fold (fun a b => a + b) 1 (worldline Plan.ground qs)) = true :=
    ble_trans _ _ _ (ble_add_both (ble_refl 1) hlen) harrow
  show (Nat.ble (m.out s).lo
          (fold (fun a b => a + b) 1 (worldline Plan.ground qs))
      && Nat.ble (fold (fun a b => a + b) 1 (worldline Plan.ground qs))
          (m.out s).hi) = false
  cases hR : Nat.ble (fold (fun a b => a + b) 1 (worldline Plan.ground qs))
      (m.out s).hi with
  | false => exact and_false _
  | true =>
      have hconv : (1 : Nat) + ((m.out s).hi + 1)
          = (m.out s).hi + (1 + 1) :=
        congrArg (· + 1) (Nat.add_comm 1 (m.out s).hi)
      have hbad := ble_trans _ _ _ hbig hR
      rw [hconv] at hbad
      exact absurd hbad
        (ne_true_of_eq_false (ble_gain_false (m.out s).hi 1))

theorem many_guests_ride_one_face {H V W X : Type} (h : H)
    (v v' : V) (w w' : W) (g : H → X) :
    g (face (atTheDoor h (v, w))) = g (face (atTheDoor h (v', w')))
      ∧ (v ≠ v' → atTheDoor h (v, w) ≠ atTheDoor h (v', w'))
      ∧ (w ≠ w' → atTheDoor h (v, w) ≠ atTheDoor h (v, w'))
      ∧ met (atTheDoor h (v, w)) = (v, w)
      ∧ (∀ d : door (door H V) W, shallow (deepen d) = d) :=
  ⟨rfl,
   fun hv he => hv (congrArg (fun d => (met d).1) he),
   fun hw he => hw (congrArg (fun d => (met d).2) he),
   rfl,
   (hosting_associates (H := H) (W := V) (V := W)).1⟩

theorem the_doors_theorem {H W : Type} (h : H) {w w' : W} (hw : w ≠ w')
    (m : door H W → door H W) :
    ((∀ d, face (m d) = face d)
        ↔ ∃ σ : H → W → W, ∀ d, m d = vertical σ d)
      ∧ atTheDoor h w ≠ atTheDoor h w'
      ∧ (∀ (X : Type) (g : H → X),
          g (face (atTheDoor h w)) = g (face (atTheDoor h w')))
      ∧ met (atTheDoor h w) ≠ met (atTheDoor h w') :=
  ⟨an_unheard_move_moves_only_the_guest m, the_threshold h hw⟩

theorem fold_scale : ∀ (x₀ : Nat) (p : Plan),
    fold (fun a b => a + b) x₀ p = x₀ * fold (fun a b => a + b) 1 p
  | x₀, .ground => (zero_plus x₀).symm
  | x₀, .board p q => by
      show fold (fun a b => a + b) x₀ p + fold (fun a b => a + b) x₀ q
          = x₀ * (fold (fun a b => a + b) 1 p + fold (fun a b => a + b) 1 q)
      rw [fold_scale x₀ p, fold_scale x₀ q, Nat.left_distrib]

theorem the_revision_multiplies_the_reading (t δ : Plan) :
    fold (fun a b => a + b) 1 (graft t δ)
      = fold (fun a b => a + b) 1 t * fold (fun a b => a + b) 1 δ :=
  (the_parent_folds_into_the_ground (fun a b => a + b) 1 t δ).trans
    (fold_scale (fold (fun a b => a + b) 1 t) δ)

theorem the_bloom_is_a_doubling_tick (d : Nat) :
    bloom (d + 1) = graft (bloom d) (.board .ground .ground) := rfl

theorem mul_regroups : ∀ a b c : Nat, (a * b) * c = a * (b * c)
  | _, _, 0 => rfl
  | a, b, c + 1 => by
      show (a * b) * c + a * b = a * (b * c + b)
      rw [Nat.left_distrib, mul_regroups a b c]

theorem linear_fold_scale (α β : Nat) : ∀ (x₀ : Nat) (p : Plan),
    fold (fun a b => α * a + β * b) x₀ p
      = x₀ * fold (fun a b => α * a + β * b) 1 p
  | x₀, .ground => (zero_plus x₀).symm
  | x₀, .board p q => by
      show α * fold (fun a b => α * a + β * b) x₀ p
            + β * fold (fun a b => α * a + β * b) x₀ q
          = x₀ * (α * fold (fun a b => α * a + β * b) 1 p
            + β * fold (fun a b => α * a + β * b) 1 q)
      rw [linear_fold_scale α β x₀ p, linear_fold_scale α β x₀ q,
          Nat.left_distrib,
          ← mul_regroups α x₀ (fold (fun a b => α * a + β * b) 1 p),
          ← mul_regroups β x₀ (fold (fun a b => α * a + β * b) 1 q),
          Nat.mul_comm α x₀, Nat.mul_comm β x₀,
          mul_regroups x₀ α (fold (fun a b => α * a + β * b) 1 p),
          mul_regroups x₀ β (fold (fun a b => α * a + β * b) 1 q)]

theorem every_linear_reading_is_deaf_to_the_revision_order
    (α β : Nat) (t δ : Plan) :
    fold (fun a b => α * a + β * b) 1 (graft t δ)
      = fold (fun a b => α * a + β * b) 1 (graft δ t) :=
  ((the_parent_folds_into_the_ground (fun a b => α * a + β * b) 1 t δ).trans
      ((linear_fold_scale α β
          (fold (fun a b => α * a + β * b) 1 t) δ).trans
        (Nat.mul_comm _ _))).trans
    ((linear_fold_scale α β
        (fold (fun a b => α * a + β * b) 1 δ) t).symm.trans
      (the_parent_folds_into_the_ground
        (fun a b => α * a + β * b) 1 δ t).symm)

theorem two_lineages_one_reading (t δ : Plan) :
    (fold (fun a b => a + b) 1 (graft t δ)
        = fold (fun a b => a + b) 1 (graft δ t))
      ∧ fold (fun a b => a + b * b) 1
            (graft (.board .ground .ground)
              (.board .ground (.board .ground .ground)))
          ≠ fold (fun a b => a + b * b) 1
            (graft (.board .ground (.board .ground .ground))
              (.board .ground .ground))
      ∧ graft (.board .ground .ground)
            (.board .ground (.board .ground .ground))
          ≠ graft (.board .ground (.board .ground .ground))
            (.board .ground .ground) :=
  ⟨(the_revision_multiplies_the_reading t δ).trans
     ((Nat.mul_comm _ _).trans
       (the_revision_multiplies_the_reading δ t).symm),
   (fun h =>
     nomatch (congrArg (Nat.beq 38) h).symm.trans (beq_self 38)),
   (fun h => nomatch (Plan.board.inj (Plan.board.inj h).1).2)⟩

theorem the_revision_order_hides_past_linearity :
    (∀ (α β : Nat) (t δ : Plan),
        fold (fun a b => α * a + β * b) 1 (graft t δ)
          = fold (fun a b => α * a + β * b) 1 (graft δ t))
      ∧ fold (fun a b => a + b * b) 1
            (graft (.board .ground .ground)
              (.board .ground (.board .ground .ground)))
          ≠ fold (fun a b => a + b * b) 1
            (graft (.board .ground (.board .ground .ground))
              (.board .ground .ground))
      ∧ graft (.board .ground .ground)
            (.board .ground (.board .ground .ground))
          ≠ graft (.board .ground (.board .ground .ground))
            (.board .ground .ground) :=
  ⟨every_linear_reading_is_deaf_to_the_revision_order,
   (two_lineages_one_reading .ground .ground).2.1,
   (two_lineages_one_reading .ground .ground).2.2⟩

def airGap (I O : Type) : Face :=
  ⟨Machine I O, List I, O, behavior⟩

def audition {I O : Type} (m : Machine I O) :
    Interview (List I) O → List O :=
  sound (airGap I O) m

theorem the_audition_sounds_the_air_gap {I O : Type} (m : Machine I O)
    (t : Interview (List I) O) :
    audition m t = sound (airGap I O) m t := rfl

def windowFace : Face :=
  ⟨Measured, Nat, Bool, within⟩

theorem an_audition_hears_only_the_conduct {I O : Type} (m n : Machine I O)
    (h : ∀ w, behavior m w = behavior n w) (t : Interview (List I) O) :
    audition m t = audition n t :=
  no_interview_parts_the_alike (airGap I O) m n h t

theorem the_organs_share_one_face {H W X I O : Type} (hh : H)
    (w w' : W) (m : Machine I O) (t : Interview (List I) O)
    (q : Quiz H X) (d : door H W) :
    audition m t = sound (airGap I O) m t
      ∧ interrogate q d = sound (doorFace H W X) d (posed q)
      ∧ alike (doorFace H W X) (atTheDoor hh w) (atTheDoor hh w')
      ∧ windowFace.obs = within :=
  ⟨rfl, the_quiz_was_an_interview d q,
   the_guests_are_alike_at_the_door hh w w', rfl⟩

theorem the_ground_is_the_only_unit :
    ∀ p : Plan, fold (fun a b => a + b) 1 p = 1 → p = .ground
  | .ground, _ => rfl
  | .board l r, h => by
      obtain ⟨a, ha⟩ := the_reading_is_positive l
      obtain ⟨b, hb⟩ := the_reading_is_positive r
      rw [show fold (fun a b => a + b) 1 (.board l r)
            = fold (fun a b => a + b) 1 l + fold (fun a b => a + b) 1 r
          from rfl, ha, hb] at h
      exact nomatch (succ_adds a b).symm.trans (Nat.succ.inj h)

theorem no_split_grounds (a : Plan) :
    ∀ p : Plan, graft a p = .ground → a = .ground ∧ p = .ground
  | .ground, h => ⟨h, rfl⟩
  | .board _ _, h => nomatch h

theorem a_prime_reading_admits_no_split (p : Plan)
    (hp : ∀ a b : Nat, a * b = fold (fun x y => x + y) 1 p →
      a = 1 ∨ b = 1) :
    ∀ t δ : Plan, graft t δ = p → t = .ground ∨ δ = .ground :=
  fun t δ he =>
    match hp (fold (fun x y => x + y) 1 t) (fold (fun x y => x + y) 1 δ)
        ((the_revision_multiplies_the_reading t δ).symm.trans
          (congrArg (fold (fun x y => x + y) 1) he)) with
    | .inl h1 => .inl (the_ground_is_the_only_unit t h1)
    | .inr h1 => .inr (the_ground_is_the_only_unit δ h1)

theorem an_unsplit_lineage_may_read_composite :
    (∀ t δ : Plan,
        graft t δ
            = .board .ground (.board .ground (.board .ground .ground)) →
          t = .ground ∨ δ = .ground)
      ∧ fold (fun a b => a + b) 1
            (.board .ground (.board .ground (.board .ground .ground)))
          = 2 * 2 :=
  ⟨fun t δ he =>
     match δ, he with
     | .ground, _ => .inr rfl
     | .board p _, he =>
         .inl (no_split_grounds t p (Plan.board.inj he).1).1,
   rfl⟩

def host (F : Face) (W : Type) : Face :=
  ⟨F.State × W, F.Probe, F.Ans, fun s p => F.obs s.1 p⟩

def widen (F : Face) (W : Type) : Face :=
  ⟨F.State × W, fork F.Probe Unit, fork F.Ans W,
   fun s => greet (fun p => viaLeft (F.obs s.1 p)) (fun _ => viaRight s.2)⟩

theorem every_face_opens_as_a_door (F : Face) {W : Type} (s : F.State)
    {w w' : W} (hw : w ≠ w') :
    alike (host F W) (s, w) (s, w')
      ∧ (∀ q : Interview F.Probe F.Ans,
          sound (host F W) (s, w) q = sound (host F W) (s, w') q)
      ∧ (s, w) ≠ (s, w')
      ∧ (widen F W).obs (s, w) (viaRight ())
          ≠ (widen F W).obs (s, w') (viaRight ()) :=
  ⟨fun _ => rfl,
   fun q =>
     no_interview_parts_the_alike (host F W) (s, w) (s, w')
       (fun _ => rfl) q,
   (fun he => hw (congrArg Prod.snd he)),
   (fun he => hw (Sum.inr.inj he))⟩

theorem the_widened_face_reads_the_remainder (F : Face) {W : Type} :
    (∀ s t : F.State × W, alike (widen F W) s t → alike (host F W) s t)
      ∧ (∀ (s : F.State) (w w' : W), alike (host F W) (s, w) (s, w'))
      ∧ ∀ (s : F.State) (w w' : W), w ≠ w' →
          ¬ alike (widen F W) (s, w) (s, w') :=
  ⟨fun _ _ hal p => Sum.inl.inj (hal (viaLeft p)),
   fun _ _ _ _ => rfl,
   fun _ _ _ hw hal => hw (Sum.inr.inj (hal (viaRight ())))⟩

def sharpen (F : Face) {X : Type} (r : F.State → X) : Face :=
  ⟨F.State, fork F.Probe Unit, fork F.Ans X,
   fun s => greet (fun p => viaLeft (F.obs s p)) (fun _ => viaRight (r s))⟩

theorem every_reading_sharpens_the_face (F : Face) {X : Type}
    (r : F.State → X) (s t : F.State) :
    (alike (sharpen F r) s t → alike F s t)
      ∧ (sharpen F r).obs s (viaRight ()) = viaRight (r s)
      ∧ (r s ≠ r t → ¬ alike (sharpen F r) s t)
      ∧ ∀ (G : Face) (W : Type),
          widen G W = sharpen (host G W) (fun x => x.2) :=
  ⟨fun hal p => Sum.inl.inj (hal (viaLeft p)),
   rfl,
   (fun hr hal => hr (Sum.inr.inj (hal (viaRight ())))),
   fun _ _ => rfl⟩

def appFace (A B : Type) : Face :=
  ⟨A → B, A, B, fun f a => f a⟩

theorem pointwise_is_the_application_faces_alike {A B : Type}
    (f g : A → B) : alike (appFace A B) f g ↔ ∀ a, f a = g a :=
  Iff.rfl

theorem the_pointwise_license {A B : Type} (f g : A → B)
    (h : ∀ a, f a = g a) {W : Type} (w w' : W) :
    (∀ q : Interview A B,
        sound (appFace A B) f q = sound (appFace A B) g q)
      ∧ alike (host (appFace A B) W) (f, w) (g, w')
      ∧ (w ≠ w' → (f, w) ≠ (g, w'))
      ∧ (widen (appFace A B) W).obs (f, w) (viaRight ()) = viaRight w :=
  ⟨fun q => no_interview_parts_the_alike (appFace A B) f g h q,
   fun p => h p,
   (fun hw he => hw (congrArg Prod.snd he)),
   rfl⟩

def grower : Machine Plan Nat :=
  ⟨Plan, .ground, graft, fold (fun a b => a + b) 1⟩

def teller : Machine Plan Nat :=
  ⟨Nat, 1, fun n δ => n * fold (fun a b => a + b) 1 δ, fun n => n⟩

theorem the_teller_walks_in_step (w : List Plan) (t : Plan) (n : Nat)
    (h : fold (fun a b => a + b) 1 t = n) :
    drive grower t w = drive teller n w :=
  two_machines_in_step_agree grower teller
    (fun (t : Plan) (n : Nat) => fold (fun a b => a + b) 1 t = n)
    (fun s _ δ hs =>
      (the_revision_multiplies_the_reading s δ).trans
        (congrArg (· * fold (fun a b => a + b) 1 δ) hs))
    (fun _ _ hs => hs) w t n h

theorem the_audition_cannot_tell_the_tree_from_its_count :
    alike (airGap Plan Nat) grower teller
      ∧ (∀ q : Interview (List Plan) Nat,
          audition grower q = audition teller q)
      ∧ (∀ w : List Plan,
          (fold (fun a b => a + b) 1 (park grower (Plan.ground) w) : Nat)
            = park teller ((1 : Nat)) w)
      ∧ park grower (Plan.ground)
            [.board .ground .ground,
             .board .ground (.board .ground .ground)]
          ≠ park grower (Plan.ground)
            [.board .ground (.board .ground .ground),
             .board .ground .ground]
      ∧ park teller ((1 : Nat))
            [.board .ground .ground,
             .board .ground (.board .ground .ground)]
          = park teller ((1 : Nat))
            [.board .ground (.board .ground .ground),
             .board .ground .ground] :=
  ⟨fun w => the_teller_walks_in_step w .ground 1 rfl,
   fun q =>
     an_audition_hears_only_the_conduct grower teller
       (fun w => the_teller_walks_in_step w .ground 1 rfl) q,
   fun w =>
     ((congrArg (fold (fun a b => a + b) 1)
         (the_park_is_a_walk grower w (Plan.ground))).trans
       (a_reading_in_step_carries_the_walk (T := Nat) graft teller.step
         (fold (fun a b => a + b) 1)
         (fun s δ => the_revision_multiplies_the_reading s δ)
         w .ground)).trans
     (the_park_is_a_walk teller w ((1 : Nat))).symm,
   (two_lineages_one_reading .ground .ground).2.2,
   rfl⟩

theorem the_handshake :
    (∀ (F : Face) (s t : F.State), alike F s t →
        ∀ q : Interview F.Probe F.Ans, sound F s q = sound F t q)
      ∧ (∀ (H W X : Type) (h : H) (w w' : W), w ≠ w' →
          alike (doorFace H W X) (atTheDoor h w) (atTheDoor h w')
            ∧ atTheDoor h w ≠ atTheDoor h w'
            ∧ met (atTheDoor h w) ≠ met (atTheDoor h w'))
      ∧ (alike (airGap Unit Bool) paceOne paceThree
          ∧ paceOne.step (0 : Nat) () ≠ paceThree.step (0 : Nat) ()) :=
  ⟨fun F s t h q => no_interview_parts_the_alike F s t h q,
   fun _ _ _ h _ _ hw =>
     ⟨the_guests_are_alike_at_the_door h _ _,
      the_guest_is_real h hw, hw⟩,
   ⟨fun w => the_paces_agree w 0 0 rfl,
    fun h => nomatch Nat.succ.inj h⟩⟩

theorem the_audition_is_blind :
    (∀ (I O : Type) (m n : Machine I O),
        (∀ w, behavior m w = behavior n w) →
        ∀ t : Interview (List I) O, audition m t = audition n t)
      ∧ (∀ t : Interview (List Unit) Bool,
          audition paceOne t = audition paceThree t)
      ∧ paceOne.step (0 : Nat) () ≠ paceThree.step (0 : Nat) ()
      ∧ audition flip (.ask [] (fun _ => .rest))
          ≠ audition restingCounter (.ask [] (fun _ => .rest)) :=
  ⟨fun _ _ m n h t => an_audition_hears_only_the_conduct m n h t,
   fun t =>
     an_audition_hears_only_the_conduct paceOne paceThree
       (fun w => the_paces_agree w 0 0 rfl) t,
   (fun h => nomatch Nat.succ.inj h),
   (fun h => nomatch (List.cons.inj h).1)⟩

theorem the_interview_never_leaves_the_first_window {I : Type}
    (m : Machine I Measured)
    (hlearn : ∀ s i, tighter (m.out (m.step s i)) (m.out s) = true) :
    ∀ (t : Interview (List I) Measured) (r : Measured), r ∈ audition m t →
      tighter r (m.out m.s0) = true
  | .rest, _, hr => by cases hr
  | .ask w k, r, hr => by
      cases hr with
      | head => exact the_learner_only_tightens m hlearn w m.s0
      | tail _ hr' =>
          exact the_interview_never_leaves_the_first_window m hlearn
            (k (behavior m w)) r hr'

theorem no_interview_hears_the_excluded {I : Type}
    (m : Machine I Measured)
    (hlearn : ∀ s i, tighter (m.out (m.step s i)) (m.out s) = true)
    (t : Interview (List I) Measured) (r : Measured)
    (hr : r ∈ audition m t)
    {x : Nat} (hx : within (m.out m.s0) x = false) :
    within r x = false :=
  the_excluded_stays_excluded
    (the_interview_never_leaves_the_first_window m hlearn t r hr) hx

theorem the_cage_is_audible_through_the_curtain {I : Type}
    (m : Machine I Measured)
    (hlearn : ∀ s i, tighter (m.out (m.step s i)) (m.out s) = true)
    (t : Interview (List I) Measured) (r : Measured)
    (hr : r ∈ audition m t) :
    tighter r (m.out m.s0) = true
      ∧ (∀ x : Nat, within (m.out m.s0) x = false → within r x = false)
      ∧ within r ((m.out m.s0).hi + 1) = false :=
  ⟨the_interview_never_leaves_the_first_window m hlearn t r hr,
   fun _ hx => no_interview_hears_the_excluded m hlearn t r hr hx,
   no_interview_hears_the_excluded m hlearn t r hr
     (the_window_misses_its_own_successor (m.out m.s0))⟩

theorem take_append {A : Type} :
    ∀ (xs ys : List A), (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | x :: xs, ys => congrArg (x :: ·) (take_append xs ys)

theorem drop_append {A : Type} :
    ∀ (xs ys : List A), (xs ++ ys).drop xs.length = ys
  | [], _ => rfl
  | _ :: xs, ys => drop_append xs ys

theorem take_drop {A : Type} :
    ∀ (n : Nat) (l : List A), l.take n ++ l.drop n = l
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: l => congrArg (a :: ·) (take_drop n l)

theorem take_length {A : Type} :
    ∀ (n : Nat) (l : List A) {m : Nat},
      l.length = n + m → (l.take n).length = n
  | 0, _, _, _ => rfl
  | n + 1, [], _, h => by
      rw [succ_adds] at h
      exact nomatch h
  | n + 1, _ :: l, _, h => by
      rw [succ_adds] at h
      exact congrArg (· + 1) (take_length n l (Nat.succ.inj h))

theorem drop_length {A : Type} :
    ∀ (n : Nat) (l : List A) {m : Nat},
      l.length = n + m → (l.drop n).length = m
  | 0, _, m, h => h.trans (zero_plus m)
  | n + 1, [], _, h => by
      rw [succ_adds] at h
      exact nomatch h
  | n + 1, _ :: l, _, h => by
      rw [succ_adds] at h
      exact drop_length n l (Nat.succ.inj h)

def reboard {W : Type} (w0 : W) : (p : Plan) → List W → build W p
  | .ground, [] => w0
  | .ground, x :: _ => x
  | .board p q, l =>
      atTheDoor (reboard w0 p (l.take (fold (fun a b => a + b) 1 p)))
        (reboard w0 q (l.drop (fold (fun a b => a + b) 1 p)))

theorem the_manifest_rebuilds_the_carrier {W : Type} (w0 : W) :
    ∀ (p : Plan) (s : build W p), reboard w0 p (pour p s) = s
  | .ground, _ => rfl
  | .board p q, d => by
      show atTheDoor
          (reboard w0 p ((pour p (face d) ++ pour q (met d)).take
            (fold (fun a b => a + b) 1 p)))
          (reboard w0 q ((pour p (face d) ++ pour q (met d)).drop
            (fold (fun a b => a + b) 1 p)))
        = d
      rw [← the_manifest_counts_the_guests p (face d),
          take_append, drop_append,
          the_manifest_rebuilds_the_carrier w0 p (face d),
          the_manifest_rebuilds_the_carrier w0 q (met d)]
      exact rfl

theorem one_manifest_one_carrier {W : Type} {p : Plan} {s t : build W p}
    (h : pour p s = pour p t) : s = t :=
  (the_manifest_rebuilds_the_carrier (spine W p s) p s).symm.trans
    ((congrArg (reboard (spine W p s) p) h).trans
      (the_manifest_rebuilds_the_carrier (spine W p s) p t))

theorem the_carrier_rebuilds_the_manifest {W : Type} (w0 : W) :
    ∀ (p : Plan) (l : List W),
      l.length = fold (fun a b => a + b) 1 p →
        pour p (reboard w0 p l) = l
  | .ground, [], h => nomatch h
  | .ground, _ :: [], _ => rfl
  | .ground, _ :: _ :: _, h => nomatch (Nat.succ.inj h)
  | .board p q, l, h => by
      show pour p (reboard w0 p (l.take (fold (fun a b => a + b) 1 p)))
            ++ pour q (reboard w0 q (l.drop (fold (fun a b => a + b) 1 p)))
          = l
      rw [the_carrier_rebuilds_the_manifest w0 p
            (l.take (fold (fun a b => a + b) 1 p))
            (take_length (fold (fun a b => a + b) 1 p) l
              (m := fold (fun a b => a + b) 1 q) h),
          the_carrier_rebuilds_the_manifest w0 q
            (l.drop (fold (fun a b => a + b) 1 p))
            (drop_length (fold (fun a b => a + b) 1 p) l
              (m := fold (fun a b => a + b) 1 q) h),
          take_drop]

theorem the_carrier_is_its_manifest {W : Type} (w0 : W) (p : Plan)
    (s t : build W p) (l : List W)
    (hl : l.length = fold (fun a b => a + b) 1 p) :
    (pour p s).length = fold (fun a b => a + b) 1 p
      ∧ reboard w0 p (pour p s) = s
      ∧ (pour p s = pour p t → s = t)
      ∧ pour p (reboard w0 p l) = l :=
  ⟨the_manifest_counts_the_guests p s,
   the_manifest_rebuilds_the_carrier w0 p s,
   fun h => one_manifest_one_carrier h,
   the_carrier_rebuilds_the_manifest w0 p l hl⟩

theorem the_transport_moves_no_guest {W : Type} {p p' : Plan} (h : p = p')
    (s : build W p) :
    pour p' (cast (congrArg (build W) h) s) = pour p s := by
  cases h
  rfl

theorem any_transport_moves_no_guest {W : Type} {p p' : Plan} (h : p = p')
    (e : build W p = build W p') (s : build W p) :
    pour p' (cast e s) = pour p s :=
  (congrArg (pour p')
      (the_transport_sheds_its_route e (congrArg (build W) h) s)).trans
    (the_transport_moves_no_guest h s)

theorem the_border_reads_only_the_manifest {W : Type} {p p' : Plan}
    (h : p = p') (s : build W p) (t : build W p') :
    cast (congrArg (build W) h) s = t ↔ pour p s = pour p' t :=
  ⟨fun he =>
     (the_transport_moves_no_guest h s).symm.trans (congrArg (pour p') he),
   fun hm =>
     one_manifest_one_carrier
       ((the_transport_moves_no_guest h s).trans hm)⟩

theorem transport_is_gauge_at_the_manifest {W : Type} {p p' : Plan}
    (h : p = p') (e : build W p = build W p') (s : build W p)
    (t : build W p') {t0 : Plan} (s0 : build W t0) (δ₁ δ₂ : Plan) :
    pour p' (cast (congrArg (build W) h) s) = pour p s
      ∧ pour p' (cast e s) = pour p s
      ∧ (cast (congrArg (build W) h) s = t ↔ pour p s = pour p' t)
      ∧ cast (congrArg (build W) (lineages_compose t0 δ₁ δ₂).symm)
            (ride (ride s0 δ₁) δ₂)
          = ride s0 (graft δ₁ δ₂) :=
  ⟨the_transport_moves_no_guest h s,
   any_transport_moves_no_guest h e s,
   the_border_reads_only_the_manifest h s t,
   (the_border_reads_only_the_manifest (lineages_compose t0 δ₁ δ₂).symm
       (ride (ride s0 δ₁) δ₂) (ride s0 (graft δ₁ δ₂))).mpr
     (the_rides_compose_at_the_manifest s0 δ₁ δ₂)⟩

theorem len_map {A B : Type} (f : A → B) :
    ∀ l : List A, (l.map f).length = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (len_map f l)

theorem the_default_goes_unused {W : Type} (w0 w1 : W) (p : Plan)
    (l : List W) (h : l.length = fold (fun a b => a + b) 1 p) :
    reboard w0 p l = reboard w1 p l :=
  one_manifest_one_carrier
    ((the_carrier_rebuilds_the_manifest w0 p l h).trans
      (the_carrier_rebuilds_the_manifest w1 p l h).symm)

theorem the_spine_boards_first {W : Type} :
    ∀ (p : Plan) (s : build W p),
      ∃ rest : List W, pour p s = spine W p s :: rest
  | .ground, _ => ⟨[], rfl⟩
  | .board p q, d =>
      match the_spine_boards_first p (face d) with
      | ⟨rest, hr⟩ =>
          ⟨rest ++ pour q (met d), by
            show pour p (face d) ++ pour q (met d)
                = spine W p (face d) :: (rest ++ pour q (met d))
            rw [hr]
            exact rfl⟩

theorem the_customs_are_a_conjugated_map {W W' : Type} (f : W → W')
    (w0 : W') (p : Plan) (s : build W p) :
    reground f p s = reboard w0 p ((pour p s).map f) :=
  one_manifest_one_carrier
    ((the_customs_thread_the_manifest f p s).trans
      (the_carrier_rebuilds_the_manifest w0 p ((pour p s).map f)
        ((len_map f (pour p s)).trans
          (the_manifest_counts_the_guests p s))).symm)

theorem the_hands_conjugate_the_customs {W W' : Type} (f : W → W')
    (w0 : W') (v0 v1 : W) (p : Plan) (s : build W p) (l : List W)
    (hl : l.length = fold (fun a b => a + b) 1 p) :
    (∃ rest : List W, pour p s = spine W p s :: rest)
      ∧ reboard v0 p l = reboard v1 p l
      ∧ pour p (reground f p s) = (pour p s).map f
      ∧ reground f p s = reboard w0 p ((pour p s).map f) :=
  ⟨the_spine_boards_first p s,
   the_default_goes_unused v0 v1 p l hl,
   the_customs_thread_the_manifest f p s,
   the_customs_are_a_conjugated_map f w0 p s⟩

theorem the_manifest_settles_the_carrier {W : Type} (w0 : W)
    {p : Plan} {s : build W p} {l : List W} (h : pour p s = l) :
    s = reboard w0 p l :=
  (the_manifest_rebuilds_the_carrier w0 p s).symm.trans
    (congrArg (reboard w0 p) h)

theorem the_ride_is_a_conjugated_fold {W : Type} (w0 : W) {t : Plan}
    (s : build W t) (δ : Plan) :
    ride s δ = reboard w0 (graft t δ)
        (fold (fun a b => a ++ b) (pour t s) δ) :=
  the_manifest_settles_the_carrier w0
    (the_passenger_multiplies_the_manifest s δ)

theorem the_journey_is_a_conjugated_epoch {W : Type} (w0 : W)
    (qs : List Plan) {t : Plan} (s : build W t) :
    journey s qs = reboard w0 (worldline t qs)
        (epochs (fun a b => a ++ b) (pour t s) qs) :=
  the_manifest_settles_the_carrier w0 (the_journey_manifest_settles qs s)

theorem the_mirror_is_a_conjugated_doubling {W : Type} (w0 : W) (p : Plan)
    (s : build W p) :
    mirror W p s = reboard w0 (.board p p) (pour p s ++ pour p s) :=
  the_manifest_settles_the_carrier w0 (the_mirror_doubles_the_manifest p s)

theorem the_calculus_rides_the_hands {W W' : Type} (f : W → W')
    (w0 : W) (w0' : W') {p : Plan} (s : build W p) (δ : Plan)
    (qs : List Plan) {l : List W} (h : pour p s = l) :
    s = reboard w0 p l
      ∧ reground f p s = reboard w0' p ((pour p s).map f)
      ∧ ride s δ = reboard w0 (graft p δ)
          (fold (fun a b => a ++ b) (pour p s) δ)
      ∧ journey s qs = reboard w0 (worldline p qs)
          (epochs (fun a b => a ++ b) (pour p s) qs)
      ∧ mirror W p s = reboard w0 (.board p p) (pour p s ++ pour p s) :=
  ⟨the_manifest_settles_the_carrier w0 h,
   the_customs_are_a_conjugated_map f w0' p s,
   the_ride_is_a_conjugated_fold w0 s δ,
   the_journey_is_a_conjugated_epoch w0 qs s,
   the_mirror_is_a_conjugated_doubling w0 p s⟩

def comb : Nat → Plan
  | 0 => .ground
  | n + 1 => .board .ground (comb n)

theorem the_comb_reads_its_length :
    ∀ n : Nat, fold (fun a b => a + b) 1 (comb n) = n + 1
  | 0 => rfl
  | n + 1 => by
      show 1 + fold (fun a b => a + b) 1 (comb n) = (n + 1) + 1
      rw [the_comb_reads_its_length n]
      exact Nat.add_comm 1 (n + 1)

theorem the_comb_is_a_corridor_of_doors (W : Type) (n : Nat) :
    build W (comb (n + 1)) = door W (build W (comb n)) := rfl

theorem the_cons_was_a_door {W : Type} (w : W) (n : Nat)
    (s : build W (comb n)) :
    pour (comb (n + 1)) (atTheDoor w s) = w :: pour (comb n) s := rfl

def replan {W : Type} (w0 : W) (p q : Plan) (s : build W p) : build W q :=
  reboard w0 q (pour p s)

theorem the_replanning_moves_no_guest {W : Type} (w0 : W) {p q : Plan}
    (h : fold (fun a b => a + b) 1 q = fold (fun a b => a + b) 1 p)
    (s : build W p) :
    pour q (replan w0 p q s) = pour p s :=
  the_carrier_rebuilds_the_manifest w0 q (pour p s)
    ((the_manifest_counts_the_guests p s).trans h.symm)

theorem the_replanning_returns {W : Type} (w0 : W) {p q : Plan}
    (h : fold (fun a b => a + b) 1 q = fold (fun a b => a + b) 1 p)
    (s : build W p) :
    replan w0 q p (replan w0 p q s) = s :=
  (congrArg (reboard w0 p) (the_replanning_moves_no_guest w0 h s)).trans
    (the_manifest_rebuilds_the_carrier w0 p s)

theorem the_word_is_a_corridor_of_doors {W : Type} (w0 w1 : W) (n : Nat)
    {p : Plan} (hp : fold (fun a b => a + b) 1 p = n + 1)
    (s : build W p) (t : build W (comb n)) :
    fold (fun a b => a + b) 1 (comb n) = n + 1
      ∧ build W (comb (n + 1)) = door W (build W (comb n))
      ∧ pour (comb (n + 1)) (atTheDoor w1 t) = w1 :: pour (comb n) t
      ∧ pour (comb n) (replan w0 p (comb n) s) = pour p s
      ∧ replan w0 (comb n) p (replan w0 p (comb n) s) = s :=
  ⟨the_comb_reads_its_length n,
   the_comb_is_a_corridor_of_doors W n,
   the_cons_was_a_door w1 n t,
   the_replanning_moves_no_guest w0
     ((the_comb_reads_its_length n).trans hp.symm) s,
   the_replanning_returns w0
     ((the_comb_reads_its_length n).trans hp.symm) s⟩

theorem the_shape_is_the_remainder_of_the_cargo {W : Type} (w0 : W)
    {p q : Plan}
    (hr : fold (fun a b => a + b) 1 q = fold (fun a b => a + b) 1 p)
    (hpq : p ≠ q) (s : build W p) :
    pour q (replan w0 p q s) = pour p s
      ∧ face (specView p s) ≠ face (specView q (replan w0 p q s))
      ∧ met (specView q (replan w0 p q s)) = replan w0 p q s :=
  ⟨the_replanning_moves_no_guest w0 hr s,
   fun he => hpq he,
   rfl⟩

theorem the_replanning_runs_the_handshake {W : Type} (w0 : W)
    (s : build W (.board (.board .ground .ground) .ground)) :
    (Plan.board (.board .ground .ground) .ground ≠ comb 2)
      ∧ fold (fun a b => a + b) 1 (.board (.board .ground .ground) .ground)
          = fold (fun a b => a + b) 1 (comb 2)
      ∧ pour (comb 2)
            (replan w0 (.board (.board .ground .ground) .ground) (comb 2) s)
          = pour (.board (.board .ground .ground) .ground) s
      ∧ face (specView (.board (.board .ground .ground) .ground) s)
          ≠ face (specView (comb 2)
              (replan w0 (.board (.board .ground .ground) .ground)
                (comb 2) s)) :=
  ⟨(fun h => nomatch (Plan.board.inj h).1),
   rfl,
   the_replanning_moves_no_guest w0 rfl s,
   (fun h => nomatch (Plan.board.inj h).1)⟩

def onPlan {W I O : Type} (p : Plan) (s0 : build W p)
    (step : build W p → I → build W p) (out : build W p → O) :
    Machine I O :=
  ⟨build W p, s0, step, out⟩

def onWords {W I O : Type} (w0 : W) (p : Plan)
    (step : build W p → I → build W p) (out : build W p → O)
    (s0 : build W p) : Machine I O :=
  ⟨List W, pour p s0,
   fun l i => pour p (step (reboard w0 p l) i),
   fun l => out (reboard w0 p l)⟩

theorem the_words_walk_in_step {W I O : Type} (w0 : W) (p : Plan)
    (s0 : build W p) (step : build W p → I → build W p)
    (out : build W p → O) (w : List I) :
    behavior (onPlan p s0 step out)
      w = behavior (onWords w0 p step out s0) w :=
  two_machines_in_step_agree (onPlan p s0 step out)
    (onWords w0 p step out s0)
    (fun (s : build W p) (l : List W) => l = pour p s)
    (fun s l i hl => by
      show pour p (step (reboard w0 p l) i) = pour p (step s i)
      rw [hl, the_manifest_rebuilds_the_carrier])
    (fun s l hl => by
      show out s = out (reboard w0 p l)
      rw [hl, the_manifest_rebuilds_the_carrier])
    w s0 (pour p s0) rfl

theorem the_pour_is_never_empty {W : Type} (p : Plan) (s : build W p) :
    pour p s ≠ [] :=
  fun h =>
    match the_reading_is_positive p with
    | ⟨_, hm⟩ =>
        nomatch ((congrArg List.length h).symm.trans
          ((the_manifest_counts_the_guests p s).trans hm))

theorem the_audition_cannot_tell_the_carrier_from_its_word
    {W I O : Type} (w0 : W) (p : Plan) (s0 : build W p)
    (step : build W p → I → build W p) (out : build W p → O)
    (s : build W p) :
    (∀ w : List I,
        behavior (onPlan p s0 step out) w
          = behavior (onWords w0 p step out s0) w)
      ∧ (∀ t : Interview (List I) O,
          audition (onPlan p s0 step out) t
            = audition (onWords w0 p step out s0) t)
      ∧ pour p s ≠ ([] : List W) :=
  ⟨fun w => the_words_walk_in_step w0 p s0 step out w,
   fun t =>
     an_audition_hears_only_the_conduct (onPlan p s0 step out)
       (onWords w0 p step out s0)
       (fun w => the_words_walk_in_step w0 p s0 step out w) t,
   the_pour_is_never_empty p s⟩

theorem the_vestibule_drains_in_one_click {W I O : Type} (w0 : W)
    (p : Plan) (s0 : build W p) (step : build W p → I → build W p)
    (out : build W p → O) (l : List W) (i : I) (s : build W p) :
    (onWords w0 p step out s0).step l i
        = pour p (step (reboard w0 p l) i)
      ∧ ((onWords w0 p step out s0).step l i).length
          = fold (fun a b => a + b) 1 p
      ∧ (onWords w0 p step out s0).step (pour p s) i
          = pour p (step s i) :=
  ⟨rfl,
   the_manifest_counts_the_guests p (step (reboard w0 p l) i),
   congrArg (fun x => pour p (step x i))
     (the_manifest_rebuilds_the_carrier w0 p s)⟩

def holdOpen {H W X : Type} (f : door H W → X) (h : H) : W → X :=
  fun w => f (atTheDoor h w)

def walkIn {H W X : Type} (g : H → W → X) (d : door H W) : X :=
  g (face d) (met d)

def handlers {H W X : Type} (f : fork H W → X) : door (H → X) (W → X) :=
  atTheDoor (fun h => f (viaLeft h)) (fun w => f (viaRight w))

theorem the_held_door_answers_every_guest {H W X : Type}
    (f : door H W → X) (h : H) (w : W) :
    holdOpen f h w = f (atTheDoor h w) := rfl

theorem the_two_strokes_read_one_meeting {H W X : Type}
    (g : H → W → X) (d : door H W) :
    walkIn g d = g (face d) (met d) := rfl

theorem the_deferral_is_free {H W X : Type}
    (f : door H W → X) (g : H → W → X) :
    walkIn (holdOpen f) = f ∧ holdOpen (walkIn g) = g :=
  ⟨rfl, rfl⟩

theorem the_guest_mover_was_a_held_reading {H W : Type}
    (σ : H → W → W) (d : door H W) :
    vertical σ d = atTheDoor (face d) (walkIn σ d) := rfl

theorem the_readings_trade_the_entrances {H W X : Type}
    (f : fork H W → X) (gl : H → X) (gr : W → X) :
    (∀ x, greet (face (handlers f)) (met (handlers f)) x = f x)
      ∧ handlers (greet gl gr) = atTheDoor gl gr :=
  ⟨a_greeter_is_a_door_of_handlers f, rfl⟩

theorem the_door_is_known_by_its_readings {H W X : Type}
    (f : door H W → X) (g : H → W → X) (σ : H → W → W)
    (h : H) (w : W) (d : door H W) (fk : fork H W → X) :
    holdOpen f h w = f (atTheDoor h w)
      ∧ walkIn (holdOpen f) = f
      ∧ holdOpen (walkIn g) = g
      ∧ vertical σ d = atTheDoor (face d) (walkIn σ d)
      ∧ handlers (greet (face (handlers fk)) (met (handlers fk)))
          = handlers fk :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem the_turned_door_flips_the_promise {H W X : Type}
    (f : door H W → X) (h : H) (w : W) :
    holdOpen (fun d => f (turnAbout d)) w h = holdOpen f h w := rfl

def strokes (W X : Type) : Nat → Type
  | 0 => W → X
  | n + 1 => W → strokes W X n

def strokesAlike {W X : Type} :
    (n : Nat) → strokes W X n → strokes W X n → Prop
  | 0, g, g' => ∀ w, g w = g' w
  | n + 1, g, g' => ∀ w, strokesAlike n (g w) (g' w)

def oneAtATime {W X : Type} :
    (n : Nat) → (build W (comb n) → X) → strokes W X n
  | 0, f => f
  | n + 1, f => fun w => oneAtATime n (holdOpen f w)

def allAtOnce {W X : Type} :
    (n : Nat) → strokes W X n → build W (comb n) → X
  | 0, g => g
  | n + 1, g => walkIn (fun w => allAtOnce n (g w))

theorem the_guests_enter_one_at_a_time {W X : Type} :
    ∀ (n : Nat) (f : build W (comb n) → X) (s : build W (comb n)),
      allAtOnce n (oneAtATime n f) s = f s
  | 0, _, _ => rfl
  | n + 1, f, s =>
      the_guests_enter_one_at_a_time n (holdOpen f (face s)) (met s)

theorem the_tower_holds_nothing_back {W X : Type} :
    ∀ (n : Nat) (g : strokes W X n),
      strokesAlike n (oneAtATime n (allAtOnce n g)) g
  | 0, _ => fun _ => rfl
  | n + 1, g => fun w => the_tower_holds_nothing_back n (g w)

theorem the_door_receives_the_world_one_guest_at_a_time {H W X : Type}
    (n : Nat) (f : build W (comb n) → X) (s : build W (comb n))
    (g : strokes W X n) (f' : door H W → X) (h : H) (w : W) :
    build W (comb (n + 1)) = door W (build W (comb n))
      ∧ allAtOnce n (oneAtATime n f) s = f s
      ∧ strokesAlike n (oneAtATime n (allAtOnce n g)) g
      ∧ holdOpen (fun d => f' (turnAbout d)) w h = holdOpen f' h w :=
  ⟨the_comb_is_a_corridor_of_doors W n,
   the_guests_enter_one_at_a_time n f s,
   the_tower_holds_nothing_back n g,
   the_turned_door_flips_the_promise f' h w⟩

def faceOf {S P A : Type} (g : door S P → A) : Face :=
  ⟨S, P, A, holdOpen g⟩

theorem the_measurement_is_a_meeting (F : Face.{0}) (s : F.State)
    (p : F.Probe) : F.obs s p = walkIn F.obs (atTheDoor s p) := rfl

theorem the_face_was_a_held_door (F : Face.{0}) :
    F.obs = holdOpen (walkIn F.obs) ∧ faceOf (walkIn F.obs) = F :=
  ⟨rfl, rfl⟩

theorem every_door_reading_is_a_face {S P A : Type} (g : door S P → A)
    (d : door S P) :
    (faceOf g).obs (face d) (met d) = g d ∧ walkIn (faceOf g).obs = g :=
  ⟨rfl, rfl⟩

theorem the_agreeing_held_doors_sound_alike {S P A : Type}
    (g : door S P → A) (s t : S)
    (h : ∀ p, g (atTheDoor s p) = g (atTheDoor t p))
    (q : Interview P A) :
    sound (faceOf g) s q = sound (faceOf g) t q :=
  no_interview_parts_the_alike (faceOf g) s t h q

theorem the_face_is_the_doors_transpose {S P A : Type}
    (g : door S P → A) (F : Face.{0}) (s : F.State) (p : F.Probe)
    (d : door S P) :
    F.obs s p = walkIn F.obs (atTheDoor s p)
      ∧ F.obs = holdOpen (walkIn F.obs)
      ∧ faceOf (walkIn F.obs) = F
      ∧ (faceOf g).obs (face d) (met d) = g d
      ∧ walkIn (faceOf g).obs = g :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem the_hosted_meeting_deepens_past_the_guest (F : Face.{0}) (W : Type)
    (d : door (door F.State W) F.Probe) :
    walkIn (host F W).obs d
      = walkIn F.obs
          (atTheDoor (face (deepen d)) (met (met (deepen d)))) := rfl

theorem the_sharpened_meeting_splits_at_the_fork {X : Type} (F : Face.{0})
    (r : F.State → X) :
    ∀ e : door F.State (fork F.Probe Unit),
      walkIn (sharpen F r).obs e
        = greet (fun x => viaLeft (walkIn F.obs x))
            (fun x => viaRight (r (face x))) (distribute e)
  | (_, .inl _) => rfl
  | (_, .inr _) => rfl

theorem the_operator_calculus_rides_the_meetings {X : Type} (F : Face.{0})
    (W : Type) (r : F.State → X)
    (d : door (door F.State W) F.Probe)
    (e : door F.State (fork F.Probe Unit)) :
    walkIn (host F W).obs d
        = walkIn F.obs
            (atTheDoor (face (deepen d)) (met (met (deepen d))))
      ∧ walkIn (sharpen F r).obs e
          = greet (fun x => viaLeft (walkIn F.obs x))
              (fun x => viaRight (r (face x))) (distribute e)
      ∧ widen F W = sharpen (host F W) (fun x => x.2) :=
  ⟨the_hosted_meeting_deepens_past_the_guest F W d,
   the_sharpened_meeting_splits_at_the_fork F r e,
   rfl⟩

inductive Reception (W X : Type) : Type where
  | close : X → Reception W X
  | receive : (W → Reception W X) → Reception W X

def receiveFrom {W X : Type} : Reception W X → (Nat → W) → X
  | .close x, _ => x
  | .receive k, α => receiveFrom (k (α 0)) (fun n => α (n + 1))

def doorsOpened {W X : Type} : Reception W X → (Nat → W) → Nat
  | .close _, _ => 0
  | .receive k, α => doorsOpened (k (α 0)) (fun n => α (n + 1)) + 1

def strokesReception {W X : Type} :
    (n : Nat) → strokes W X n → Reception W X
  | 0, g => .receive (fun w => .close (g w))
  | n + 1, g => .receive (fun w => strokesReception n (g w))

def twoGuests (a b : Nat) : Nat → Nat
  | 0 => a
  | _ + 1 => b

def doorman : Reception Nat Nat :=
  .receive (fun w =>
    match w with
    | 0 => .close 0
    | _ + 1 => .receive (fun v => .close v))

def doormanTower : strokes Nat Nat 1 :=
  fun a b =>
    match a with
    | 0 => 0
    | _ + 1 => b

theorem the_reception_reads_only_the_arrived {W X : Type} :
    ∀ (r : Reception W X) (α β : Nat → W),
      (∀ k, k < doorsOpened r α → α k = β k) →
      receiveFrom r α = receiveFrom r β
  | .close _, _, _, _ => rfl
  | .receive k, α, β, h => by
      have h0 : α 0 = β 0 :=
        h 0 (Nat.succ_le_succ (Nat.zero_le _))
      show receiveFrom (k (α 0)) (fun n => α (n + 1))
          = receiveFrom (k (β 0)) (fun n => β (n + 1))
      rw [← h0]
      exact the_reception_reads_only_the_arrived (k (α 0))
        (fun n => α (n + 1)) (fun n => β (n + 1))
        (fun j hj => h (j + 1) (Nat.succ_le_succ hj))

theorem the_straight_host_opens_every_door {W X : Type} :
    ∀ (n : Nat) (g : strokes W X n) (α : Nat → W),
      doorsOpened (strokesReception n g) α = n + 1
  | 0, _, _ => rfl
  | n + 1, g, α =>
      congrArg (· + 1)
        (the_straight_host_opens_every_door n (g (α 0))
          (fun j => α (j + 1)))

theorem the_patient_and_the_eager_host_read_alike :
    ∀ a b : Nat,
      receiveFrom doorman (twoGuests a b)
        = receiveFrom (strokesReception 1 doormanTower) (twoGuests a b)
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem the_door_ledger_parts_the_hosts :
    doorsOpened doorman (twoGuests 0 0) = 1
      ∧ doorsOpened (strokesReception 1 doormanTower) (twoGuests 0 0) = 2 :=
  ⟨rfl, rfl⟩

theorem the_hosts_patience_is_the_remainder {W X : Type}
    (n : Nat) (g : strokes W X n) (α β : Nat → W)
    (r : Reception W X) (γ δ : Nat → W)
    (h : ∀ k, k < doorsOpened r γ → γ k = δ k) (a b : Nat) :
    receiveFrom doorman (twoGuests a b)
        = receiveFrom (strokesReception 1 doormanTower) (twoGuests a b)
      ∧ doorsOpened doorman (twoGuests 0 0) = 1
      ∧ doorsOpened (strokesReception 1 doormanTower) (twoGuests 0 0) = 2
      ∧ doorsOpened (strokesReception n g) α
          = doorsOpened (strokesReception n g) β
      ∧ receiveFrom r γ = receiveFrom r δ :=
  ⟨the_patient_and_the_eager_host_read_alike a b,
   the_door_ledger_parts_the_hosts.1,
   the_door_ledger_parts_the_hosts.2,
   (the_straight_host_opens_every_door n g α).trans
     (the_straight_host_opens_every_door n g β).symm,
   the_reception_reads_only_the_arrived r γ δ h⟩

def handOff {W X Y : Type} :
    Reception W X → (X → Reception W Y) → Reception W Y
  | .close x, k => k x
  | .receive f, k => .receive (fun w => handOff (f w) k)

theorem the_fulfilled_reception_hands_off_whole {W X Y : Type}
    (x : X) (k : X → Reception W Y) :
    handOff (Reception.close x) k = k x := rfl

theorem the_reception_resumes {W X Y : Type} :
    ∀ (r : Reception W X) (k : X → Reception W Y) (α : Nat → W),
      receiveFrom (handOff r k) α
        = receiveFrom (k (receiveFrom r α))
            (fun j => α (j + doorsOpened r α))
  | .close _, _, _ => rfl
  | .receive f, k, α =>
      the_reception_resumes (f (α 0)) k (fun n => α (n + 1))

theorem the_ledger_sums_the_handoff {W X Y : Type} :
    ∀ (r : Reception W X) (k : X → Reception W Y) (α : Nat → W),
      doorsOpened (handOff r k) α
        = doorsOpened r α
          + doorsOpened (k (receiveFrom r α))
              (fun j => α (j + doorsOpened r α))
  | .close x, k, α => (zero_plus (doorsOpened (k x) α)).symm
  | .receive f, k, α =>
      (congrArg (· + 1)
          (the_ledger_sums_the_handoff (f (α 0)) k
            (fun n => α (n + 1)))).trans
        (succ_adds
          (doorsOpened (f (α 0)) (fun n => α (n + 1)))
          (doorsOpened
            (k (receiveFrom (f (α 0)) (fun n => α (n + 1))))
            (fun j =>
              α (j + (doorsOpened (f (α 0)) (fun n => α (n + 1)) + 1))))).symm

theorem the_reception_grafts_at_the_close {W X Y : Type}
    (x : X) (k : X → Reception W Y) (r : Reception W X) (α : Nat → W) :
    handOff (Reception.close x) k = k x
      ∧ receiveFrom (handOff r k) α
          = receiveFrom (k (receiveFrom r α))
              (fun j => α (j + doorsOpened r α))
      ∧ doorsOpened (handOff r k) α
          = doorsOpened r α
            + doorsOpened (k (receiveFrom r α))
                (fun j => α (j + doorsOpened r α)) :=
  ⟨rfl, the_reception_resumes r k α, the_ledger_sums_the_handoff r k α⟩

def firstGuests {W : Type} : Nat → (Nat → W) → List W
  | 0, _ => []
  | n + 1, α => α 0 :: firstGuests n (fun j => α (j + 1))

theorem the_first_guests_count {W : Type} :
    ∀ (n : Nat) (α : Nat → W), (firstGuests n α).length = n
  | 0, _ => rfl
  | n + 1, α =>
      congrArg (· + 1) (the_first_guests_count n (fun j => α (j + 1)))

theorem the_host_reboards_the_stream {W X : Type} :
    ∀ (n : Nat) (f : build W (comb n) → X) (α : Nat → W),
      receiveFrom (strokesReception n (oneAtATime n f)) α
        = f (reboard (α 0) (comb n) (firstGuests (n + 1) α))
  | 0, _, _ => rfl
  | n + 1, f, α =>
      (the_host_reboards_the_stream n (holdOpen f (α 0))
          (fun j => α (j + 1))).trans
        (congrArg
          (fun t => f (atTheDoor (α 0) t))
          (the_default_goes_unused (α 1) (α 0) (comb n)
            (firstGuests (n + 1) (fun j => α (j + 1)))
            ((the_first_guests_count (n + 1) (fun j => α (j + 1))).trans
              (the_comb_reads_its_length n).symm)))

theorem the_handoff_is_the_board_at_the_ledger {W X Y : Type}
    (n m : Nat) (g : strokes W X n) (h : X → strokes W Y m) (α : Nat → W) :
    doorsOpened
        (handOff (strokesReception n g)
          (fun x => strokesReception m (h x))) α
      = fold (fun a b => a + b) 1 (Plan.board (comb n) (comb m)) :=
  (the_ledger_sums_the_handoff (strokesReception n g)
      (fun x => strokesReception m (h x)) α).trans
    ((congr
        (congrArg (· + ·) (the_straight_host_opens_every_door n g α))
        (the_straight_host_opens_every_door m
          (h (receiveFrom (strokesReception n g) α))
          (fun j => α (j + doorsOpened (strokesReception n g) α)))).trans
      (congr
        (congrArg (· + ·) (the_comb_reads_its_length n).symm)
        (the_comb_reads_its_length m).symm))

theorem the_carrier_checks_in_one_guest_at_a_time {W X Y : Type}
    (n m : Nat) (f : build W (comb n) → X) (g : strokes W X n)
    (h : X → strokes W Y m) (α : Nat → W) :
    receiveFrom (strokesReception n (oneAtATime n f)) α
        = f (reboard (α 0) (comb n) (firstGuests (n + 1) α))
      ∧ doorsOpened (strokesReception n g) α
          = fold (fun a b => a + b) 1 (comb n)
      ∧ doorsOpened
            (handOff (strokesReception n g)
              (fun x => strokesReception m (h x))) α
          = fold (fun a b => a + b) 1 (Plan.board (comb n) (comb m)) :=
  ⟨the_host_reboards_the_stream n f α,
   (the_straight_host_opens_every_door n g α).trans
     (the_comb_reads_its_length n).symm,
   the_handoff_is_the_board_at_the_ledger n m g h α⟩

def strokesFace (W X : Type) (n : Nat) : Face :=
  ⟨strokes W X n, build W (comb n), X, fun g s => allAtOnce n g s⟩

theorem the_tower_alike_reads_at_the_face {W X : Type} :
    ∀ (n : Nat) (g g' : strokes W X n),
      strokesAlike n g g' ↔ alike (strokesFace W X n) g g'
  | 0, _, _ => Iff.rfl
  | n + 1, g, g' =>
      ⟨fun h s =>
         ((the_tower_alike_reads_at_the_face n (g (face s))
             (g' (face s))).mp (h (face s))) (met s),
       fun h w =>
         (the_tower_alike_reads_at_the_face n (g w) (g' w)).mpr
           (fun s' => h (atTheDoor w s'))⟩

theorem the_crossed_readings_turn_about {H W X : Type}
    (f : fork W H → X) :
    handlers (fun k : fork H W => f (crossOver k))
      = turnAbout (handlers f) := rfl

theorem the_pointwise_license_is_a_face_license {W X H Y : Type}
    (n : Nat) (g g' : strokes W X n) (h : strokesAlike n g g')
    (q : Interview (build W (comb n)) X) (f : fork Y H → X) :
    alike (strokesFace W X n) g g'
      ∧ sound (strokesFace W X n) g q = sound (strokesFace W X n) g' q
      ∧ handlers (fun k : fork H Y => f (crossOver k))
          = turnAbout (handlers f) :=
  ⟨(the_tower_alike_reads_at_the_face n g g').mp h,
   no_interview_parts_the_alike (strokesFace W X n) g g'
     ((the_tower_alike_reads_at_the_face n g g').mp h) q,
   rfl⟩

theorem the_lock_survives_every_lap (a d n : Nat) :
    within ⟨n * a, n * a + d⟩ (n * a) = true :=
  and_glue (ble_refl (n * a)) (ble_le_add (n * a) d)

theorem the_revision_multiplies_the_patience {W X : Type} (t δ : Plan)
    (n : Nat) (h : fold (fun a b => a + b) 1 (graft t δ) = n + 1)
    (g : strokes W X n) (α : Nat → W) :
    doorsOpened (strokesReception n g) α
      = fold (fun a b => a + b) 1 t * fold (fun a b => a + b) 1 δ :=
  ((the_straight_host_opens_every_door n g α).trans h.symm).trans
    (the_revision_multiplies_the_reading t δ)

theorem the_wheels_signature_is_gap_zero (a d n g p : Nat) :
    within ⟨n * a, n * a + d⟩ (n * a) = true
      ∧ within ⟨(d + 1) * p, (d + 1) * p + d⟩
          ((d + 1) * (p + (g + 1))) = false :=
  ⟨the_lock_survives_every_lap a d n,
   the_gap_outruns_every_window p g d⟩

def receptionFace (W X : Type) : Face :=
  ⟨Reception W X, Nat → W, X, receiveFrom⟩

def patienceFace (W X : Type) : Face :=
  ⟨Reception W X, Nat → W, X × Nat,
   fun r α => (receiveFrom r α, doorsOpened r α)⟩

theorem no_stream_parts_the_hosts (α : Nat → Nat) :
    receiveFrom doorman α
      = receiveFrom (strokesReception 1 doormanTower) α := by
  show receiveFrom
      (match α 0 with
       | 0 => Reception.close 0
       | _ + 1 => Reception.receive fun v => Reception.close v)
      (fun n => α (n + 1))
    = doormanTower (α 0) (α 1)
  cases α 0 with
  | zero => exact rfl
  | succ m => exact rfl

theorem the_hosts_are_alike_at_the_reception_face :
    alike (receptionFace Nat Nat) doorman
      (strokesReception 1 doormanTower) :=
  no_stream_parts_the_hosts

theorem no_interview_parts_the_hosts
    (q : Interview (Nat → Nat) Nat) :
    sound (receptionFace Nat Nat) doorman q
      = sound (receptionFace Nat Nat) (strokesReception 1 doormanTower) q :=
  no_interview_parts_the_alike (receptionFace Nat Nat) doorman
    (strokesReception 1 doormanTower)
    the_hosts_are_alike_at_the_reception_face q

theorem the_hosts_are_two :
    doorman ≠ strokesReception 1 doormanTower :=
  fun h =>
    nomatch Nat.succ.inj
      (congrArg (fun r => doorsOpened r (twoGuests 0 0)) h)

theorem the_patience_face_parts_the_hosts :
    (patienceFace Nat Nat).obs doorman (twoGuests 0 0)
      ≠ (patienceFace Nat Nat).obs (strokesReception 1 doormanTower)
          (twoGuests 0 0) :=
  fun h => nomatch Nat.succ.inj (congrArg Prod.snd h)

def machineReception {I O : Type} (m : Machine I O) :
    Nat → m.S → Reception I O
  | 0, s => .close (m.out s)
  | n + 1, s => .receive (fun i => machineReception m n (m.step s i))

theorem the_machine_receives_its_word {I O : Type} (m : Machine I O) :
    ∀ (n : Nat) (s : m.S) (α : Nat → I),
      receiveFrom (machineReception m n s) α = drive m s (firstGuests n α)
  | 0, _, _ => rfl
  | n + 1, s, α =>
      the_machine_receives_its_word m n (m.step s (α 0))
        (fun j => α (j + 1))

theorem the_machines_patience_is_fixed {I O : Type} (m : Machine I O) :
    ∀ (n : Nat) (s : m.S) (α : Nat → I),
      doorsOpened (machineReception m n s) α = n
  | 0, _, _ => rfl
  | n + 1, s, α =>
      congrArg (· + 1)
        (the_machines_patience_is_fixed m n (m.step s (α 0))
          (fun j => α (j + 1)))

theorem the_air_gap_crosses_into_the_reception {I O : Type}
    (m n : Machine I O) (h : ∀ w, behavior m w = behavior n w)
    (k : Nat) (α : Nat → I) :
    receiveFrom (machineReception m k m.s0) α
      = receiveFrom (machineReception n k n.s0) α :=
  (the_machine_receives_its_word m k m.s0 α).trans
    ((h (firstGuests k α)).trans
      (the_machine_receives_its_word n k n.s0 α).symm)

theorem the_machine_is_an_eager_host {I O : Type} (m n : Machine I O)
    (h : ∀ w, behavior m w = behavior n w) (k : Nat) (s : m.S)
    (α : Nat → I) :
    receiveFrom (machineReception m k s) α = drive m s (firstGuests k α)
      ∧ doorsOpened (machineReception m k s) α = k
      ∧ receiveFrom (machineReception m k m.s0) α
          = receiveFrom (machineReception n k n.s0) α :=
  ⟨the_machine_receives_its_word m k s α,
   the_machines_patience_is_fixed m k s α,
   the_air_gap_crosses_into_the_reception m n h k α⟩

def machineTower {I O : Type} (m : Machine I O) :
    (n : Nat) → m.S → strokes I O n
  | 0, s => fun i => m.out (m.step s i)
  | n + 1, s => fun i => machineTower m n (m.step s i)

theorem the_machine_wears_a_tower {I O : Type} (m : Machine I O) :
    ∀ (n : Nat) (s : m.S) (α : Nat → I),
      receiveFrom (machineReception m (n + 1) s) α
        = receiveFrom (strokesReception n (machineTower m n s)) α
  | 0, _, _ => rfl
  | n + 1, s, α =>
      the_machine_wears_a_tower m n (m.step s (α 0)) (fun j => α (j + 1))

theorem the_registers_reduce_at_conduct {I O W X : Type} (m : Machine I O)
    (n : Nat) (s : m.S) (α : Nat → I) (f : build W (comb n) → X)
    (β : Nat → W) (w0 : W) {p q : Plan}
    (hr : fold (fun a b => a + b) 1 q = fold (fun a b => a + b) 1 p)
    (c : build W p) :
    receiveFrom (machineReception m (n + 1) s) α
        = receiveFrom (strokesReception n (machineTower m n s)) α
      ∧ receiveFrom (strokesReception n (oneAtATime n f)) β
          = f (reboard (β 0) (comb n) (firstGuests (n + 1) β))
      ∧ pour q (replan w0 p q c) = pour p c :=
  ⟨the_machine_wears_a_tower m n s α,
   the_host_reboards_the_stream n f β,
   the_replanning_moves_no_guest w0 hr c⟩

def boards : Plan → Nat
  | .ground => 0
  | .board p q => (boards p + boards q) + 1

theorem every_meeting_is_one_move :
    ∀ p : Plan, boards p + 1 = fold (fun a b => a + b) 1 p
  | .ground => rfl
  | .board p q => by
      show ((boards p + boards q) + 1) + 1
          = fold (fun a b => a + b) 1 p + fold (fun a b => a + b) 1 q
      rw [← every_meeting_is_one_move p, ← every_meeting_is_one_move q,
          succ_adds (boards p) (boards q + 1)]
      exact rfl

theorem the_hanoi_recurrence (d : Nat) :
    boards (bloom (d + 1))
      = (boards (bloom d) + boards (bloom d)) + 1 := rfl

theorem the_hanoi_count_fills_the_cap (d : Nat) :
    boards (bloom d) + 1 = roomCap d :=
  (every_meeting_is_one_move (bloom d)).trans (the_bloom_fills_its_cap d)

theorem the_tower_of_hanoi_is_the_blooms_meetings (d : Nat) (p : Plan) :
    boards (bloom (d + 1))
        = (boards (bloom d) + boards (bloom d)) + 1
      ∧ boards (bloom d) + 1 = roomCap d
      ∧ boards p + 1 = fold (fun a b => a + b) 1 p :=
  ⟨rfl, the_hanoi_count_fills_the_cap d, every_meeting_is_one_move p⟩

theorem the_remainders_wear_the_blindnesses {W X : Type} (F : Face)
    (s : F.State) {w w' : W} (hw : w ≠ w') (w0 : X) {p q : Plan}
    (hr : fold (fun a b => a + b) 1 q = fold (fun a b => a + b) 1 p)
    (hpq : p ≠ q) (c : build X p) :
    (alike (host F W) (s, w) (s, w')
        ∧ (widen F W).obs (s, w) (viaRight ())
            ≠ (widen F W).obs (s, w') (viaRight ()))
      ∧ (pour q (replan w0 p q c) = pour p c
          ∧ face (specView p c) ≠ face (specView q (replan w0 p q c)))
      ∧ (alike (receptionFace Nat Nat) doorman
            (strokesReception 1 doormanTower)
          ∧ (patienceFace Nat Nat).obs doorman (twoGuests 0 0)
              ≠ (patienceFace Nat Nat).obs
                  (strokesReception 1 doormanTower) (twoGuests 0 0)) :=
  ⟨⟨(every_face_opens_as_a_door F s hw).1,
    (every_face_opens_as_a_door F s hw).2.2.2⟩,
   ⟨(the_shape_is_the_remainder_of_the_cargo w0 hr hpq c).1,
    (the_shape_is_the_remainder_of_the_cargo w0 hr hpq c).2.1⟩,
   ⟨the_hosts_are_alike_at_the_reception_face,
    the_patience_face_parts_the_hosts⟩⟩

theorem the_hosts_run_the_handshake (q : Interview (Nat → Nat) Nat) :
    alike (receptionFace Nat Nat) doorman
        (strokesReception 1 doormanTower)
      ∧ sound (receptionFace Nat Nat) doorman q
          = sound (receptionFace Nat Nat)
              (strokesReception 1 doormanTower) q
      ∧ doorman ≠ strokesReception 1 doormanTower
      ∧ (patienceFace Nat Nat).obs doorman (twoGuests 0 0)
          ≠ (patienceFace Nat Nat).obs
              (strokesReception 1 doormanTower) (twoGuests 0 0) :=
  ⟨the_hosts_are_alike_at_the_reception_face,
   no_interview_parts_the_hosts q,
   the_hosts_are_two,
   the_patience_face_parts_the_hosts⟩

theorem the_tower_meets_the_mirror {A X : Type} (g : strokes A X 1)
    (f : build A (comb 1) → X) (a : A) :
    allAtOnce 1 g (mirror A .ground a) = g a a
      ∧ oneAtATime 1 f a a = f (mirror A .ground a) :=
  ⟨rfl, rfl⟩

theorem the_mirror_checks_in_twice {A X : Type} (g : strokes A X 1) (a : A) :
    receiveFrom (strokesReception 1 g) (fun _ => a)
        = allAtOnce 1 g (mirror A .ground a)
      ∧ doorsOpened (strokesReception 1 g) (fun _ => a) = 2
      ∧ pour (.board .ground .ground) (mirror A .ground a) = [a, a] :=
  ⟨rfl, rfl, rfl⟩

theorem the_escapee_negates_the_mirror {A : Type} (g : strokes A Bool 1) :
    ∀ a, g a ≠ fun b => !(allAtOnce 1 g (mirror A .ground b)) :=
  fun a he => bool_escapes (g a a) (congrFun he a)

theorem the_fixed_point_sits_at_the_mirror {A Y : Type} (g : A → A → Y)
    (t : Y → Y) (hsur : ∀ f : A → Y, ∃ a, g a = f) :
    ∃ a, t (allAtOnce 1 g (mirror A .ground a))
      = allAtOnce 1 g (mirror A .ground a) :=
  (hsur (fun a => t (g a a))).elim fun a₀ ha => ⟨a₀, (congrFun ha a₀).symm⟩

theorem the_diagonal_was_a_mirror {A Y : Type} (g : strokes A Bool 1)
    (h : A → A → Y) (t : Y → Y) (hsur : ∀ f : A → Y, ∃ b, h b = f) (a : A) :
    allAtOnce 1 g (mirror A .ground a) = g a a
      ∧ pour (.board .ground .ground) (mirror A .ground a) = [a, a]
      ∧ doorsOpened (strokesReception 1 g) (fun _ => a) = 2
      ∧ (∀ b, g b ≠ fun c => !(allAtOnce 1 g (mirror A .ground c)))
      ∧ ∃ b, t (allAtOnce 1 h (mirror A .ground b))
          = allAtOnce 1 h (mirror A .ground b) :=
  ⟨rfl, rfl, rfl,
   the_escapee_negates_the_mirror g,
   the_fixed_point_sits_at_the_mirror h t hsur⟩

theorem the_mirror_revises_every_life {W : Type} (t : Plan) (s : build W t) :
    graft t (.board .ground .ground) = .board t t
      ∧ ride s (.board .ground .ground) = mirror W t s :=
  ⟨rfl, rfl⟩

theorem the_blooms_add : ∀ i j : Nat, graft (bloom i) (bloom j) = bloom (i + j)
  | _, 0 => rfl
  | i, j + 1 =>
      show Plan.board (graft (bloom i) (bloom j)) (graft (bloom i) (bloom j))
          = Plan.board (bloom (i + j)) (bloom (i + j))
      from congr (congrArg Plan.board (the_blooms_add i j)) (the_blooms_add i j)

theorem the_bloom_hears_no_order (i j : Nat) :
    graft (bloom i) (bloom j) = graft (bloom j) (bloom i) :=
  (the_blooms_add i j).trans
    ((congrArg bloom (Nat.add_comm i j)).trans (the_blooms_add j i).symm)

theorem the_caps_multiply (i j : Nat) :
    roomCap (i + j) = roomCap i * roomCap j :=
  ((the_bloom_fills_its_cap (i + j)).symm.trans
    ((congrArg (fold (fun a b => a + b) 1) (the_blooms_add i j)).symm.trans
      (the_revision_multiplies_the_reading (bloom i) (bloom j)))).trans
    (congr (congrArg (· * ·) (the_bloom_fills_its_cap i))
      (the_bloom_fills_its_cap j))

theorem the_order_vanishes_on_the_diagonal {W : Type} (i j : Nat) (t : Plan)
    (s : build W t) :
    (graft t (.board .ground .ground) = .board t t
        ∧ ride s (.board .ground .ground) = mirror W t s)
      ∧ graft (bloom i) (bloom j) = graft (bloom j) (bloom i)
      ∧ roomCap (i + j) = roomCap i * roomCap j
      ∧ graft (.board .ground .ground) (.board .ground (.board .ground .ground))
          ≠ graft (.board .ground (.board .ground .ground))
              (.board .ground .ground) :=
  ⟨the_mirror_revises_every_life t s,
   the_bloom_hears_no_order i j,
   the_caps_multiply i j,
   (two_lineages_one_reading .ground .ground).2.2⟩

def selfMeet (F : Face) (r : F.State → F.Probe) (s : F.State) : F.Ans :=
  F.obs s (r s)

theorem the_self_meeting_walks_the_graph (F : Face.{0})
    (r : F.State → F.Probe) (s : F.State) :
    selfMeet F r s = walkIn F.obs (turnAbout (graphDoor r s)) := rfl

theorem the_mirror_was_a_graph {A : Type} (a : A) :
    graphDoor (fun x : A => x) a = mirror A .ground a := rfl

theorem the_held_door_meets_itself_at_the_mirror {A X : Type}
    (g : strokes A X 1) (a : A) :
    selfMeet (faceOf (walkIn g)) (fun x => x) a
      = allAtOnce 1 g (mirror A .ground a) := rfl

theorem the_window_never_meets_its_successor (m : Measured) :
    selfMeet windowFace (fun w => w.hi + 1) m = false :=
  the_window_misses_its_own_successor m

theorem the_diagonal_mints_the_probe (F : Face.{0}) {A X : Type}
    (g : strokes A X 1) (r : F.State → F.Probe) (s : F.State)
    (a : A) (m : Measured) :
    selfMeet F r s = walkIn F.obs (turnAbout (graphDoor r s))
      ∧ graphDoor (fun x : A => x) a = mirror A .ground a
      ∧ selfMeet (faceOf (walkIn g)) (fun x => x) a
          = allAtOnce 1 g (mirror A .ground a)
      ∧ selfMeet windowFace (fun w => w.hi + 1) m = false :=
  ⟨rfl, rfl, rfl, the_window_misses_its_own_successor m⟩

theorem the_self_meeting_reads_the_guest (F : Face) {W : Type}
    (r : W → F.Probe) (s : F.State) (w : W) :
    selfMeet (host F W) (fun x => r x.2) (s, w) = F.obs s (r w) := rfl

theorem the_self_meeting_parts_the_alike :
    alike (host windowFace Bool) (⟨0, 0⟩, true) (⟨0, 0⟩, false)
      ∧ selfMeet (host windowFace Bool) (fun x => (cond x.2 0 1 : Nat))
            (⟨0, 0⟩, true)
          ≠ selfMeet (host windowFace Bool) (fun x => (cond x.2 0 1 : Nat))
              (⟨0, 0⟩, false) :=
  ⟨fun _ => rfl, fun h => nomatch h⟩

theorem the_sharpened_window_exhibits_the_escapee (m : Measured) :
    (sharpen windowFace (fun w => w.hi + 1)).obs m (viaRight ())
        = viaRight (m.hi + 1)
      ∧ within m (m.hi + 1) = false :=
  ⟨rfl, the_window_misses_its_own_successor m⟩

theorem the_curtain_follows_the_minting (m : Measured)
    (q : Interview Nat Bool) :
    (alike (host windowFace Bool) (⟨0, 0⟩, true) (⟨0, 0⟩, false)
        ∧ sound (host windowFace Bool) (⟨0, 0⟩, true) q
            = sound (host windowFace Bool) (⟨0, 0⟩, false) q)
      ∧ selfMeet (host windowFace Bool) (fun x => (cond x.2 0 1 : Nat))
            (⟨0, 0⟩, true)
          ≠ selfMeet (host windowFace Bool) (fun x => (cond x.2 0 1 : Nat))
              (⟨0, 0⟩, false)
      ∧ (widen windowFace Bool).obs (⟨0, 0⟩, true) (viaRight ())
          ≠ (widen windowFace Bool).obs (⟨0, 0⟩, false) (viaRight ())
      ∧ ((sharpen windowFace (fun w => w.hi + 1)).obs m (viaRight ())
            = viaRight (m.hi + 1)
          ∧ within m (m.hi + 1) = false) :=
  ⟨⟨the_self_meeting_parts_the_alike.1,
    no_interview_parts_the_alike (host windowFace Bool) _ _
      the_self_meeting_parts_the_alike.1 q⟩,
   the_self_meeting_parts_the_alike.2,
   (fun h => nomatch Sum.inr.inj h),
   the_sharpened_window_exhibits_the_escapee m⟩

theorem the_guest_written_from_the_whole_door {H W : Type}
    (g : door H W → W) (d : door H W) :
    vertical (holdOpen g) d = atTheDoor (face d) (g d) := rfl

theorem the_reading_writes_unheard (F : Face) {W : Type}
    (g : F.State × W → W) (s : F.State) (w : W) :
    alike (host F W) (s, w) (s, g (s, w)) :=
  fun _ => rfl

theorem no_interview_hears_the_written_guest (F : Face) {W : Type}
    (g : F.State × W → W) (s : F.State) (w : W)
    (q : Interview F.Probe F.Ans) :
    sound (host F W) (s, w) q = sound (host F W) (s, g (s, w)) q :=
  no_interview_parts_the_alike (host F W) _ _
    (the_reading_writes_unheard F g s w) q

theorem one_reading_two_entrances (F : Face) {W : Type}
    (g : F.State × W → W) (s : F.State) (w : W)
    (q : Interview F.Probe F.Ans) (q' : Interview Nat Bool) :
    alike (host F W) (s, w) (s, g (s, w))
      ∧ sound (host F W) (s, w) q = sound (host F W) (s, g (s, w)) q
      ∧ sound (host windowFace Bool) (⟨0, 0⟩, true) q'
          = sound (host windowFace Bool) (⟨0, 0⟩, false) q'
      ∧ selfMeet (host windowFace Bool) (fun x => (cond x.2 0 1 : Nat))
            (⟨0, 0⟩, true)
          ≠ selfMeet (host windowFace Bool) (fun x => (cond x.2 0 1 : Nat))
              (⟨0, 0⟩, false) :=
  ⟨the_reading_writes_unheard F g s w,
   no_interview_hears_the_written_guest F g s w q,
   no_interview_parts_the_alike (host windowFace Bool) _ _
     the_self_meeting_parts_the_alike.1 q',
   the_self_meeting_parts_the_alike.2⟩

theorem the_probe_boards_as_the_guest (F : Face) (s : F.State)
    (p : F.Probe) :
    selfMeet (host F F.Probe) (fun x => x.2) (s, p) = F.obs s p := rfl

theorem the_meeting_was_a_self_meeting {S P A : Type} (g : door S P → A)
    (d : door S P) :
    g d = selfMeet (host (faceOf g) P) (fun x => x.2) d := rfl

theorem the_written_question_is_the_asked_question (F : Face.{0})
    (s : F.State) (p q₀ : F.Probe) :
    selfMeet (host F F.Probe) (fun x => x.2)
        (vertical (fun _ _ => q₀) (atTheDoor s p))
      = F.obs s q₀ := rfl

theorem the_escapee_rides_refused (m : Measured) :
    selfMeet (host windowFace Nat) (fun x => x.2) (m, m.hi + 1) = false :=
  the_window_misses_its_own_successor m

theorem every_reading_is_a_self_meeting {S P A : Type} (g : door S P → A)
    (d : door S P) (F : Face) (s : F.State) (p : F.Probe)
    {I O : Type} (mach : Machine I O) (w : List I) (m : Measured) :
    g d = selfMeet (host (faceOf g) P) (fun x => x.2) d
      ∧ selfMeet (host F F.Probe) (fun x => x.2) (s, p) = F.obs s p
      ∧ selfMeet (host (airGap I O) (List I)) (fun x => x.2) (mach, w)
          = behavior mach w
      ∧ selfMeet (host windowFace Nat) (fun x => x.2) (m, m.hi + 1)
          = false :=
  ⟨rfl, rfl, rfl, the_window_misses_its_own_successor m⟩

theorem no_tick_is_smaller_than_the_mirror {δ : Plan}
    (hδ : δ ≠ .ground) :
    Nat.ble 2 (fold (fun a b => a + b) 1 δ) = true := by
  have h := a_true_tick_grows_the_reading (t := .ground) hδ
  rw [the_trivial_revision_changes_nothing δ] at h
  exact h

theorem the_least_tick_is_the_mirror :
    ∀ δ : Plan, fold (fun a b => a + b) 1 δ = 2 →
      δ = .board .ground .ground
  | .ground, h => nomatch Nat.succ.inj h
  | .board l r, h => by
      obtain ⟨a, ha⟩ := the_reading_is_positive l
      obtain ⟨b, hb⟩ := the_reading_is_positive r
      have h2 : (a + 1) + (b + 1) = 2 := by
        have hlr : fold (fun a b => a + b) 1 l
            + fold (fun a b => a + b) 1 r = 2 := h
        rw [ha, hb] at hlr
        exact hlr
      have hab : a + b = 0 := by
        rw [succ_adds a (b + 1)] at h2
        exact Nat.succ.inj (Nat.succ.inj h2)
      have hb0 : b = 0 := by
        cases b with
        | zero => rfl
        | succ b' => exact nomatch hab
      have ha0 : a = 0 := by
        rw [hb0] at hab
        exact hab
      have hl : l = .ground :=
        the_ground_is_the_only_unit l
          ((ha.trans (congrArg (· + 1) ha0)).trans (zero_plus 1))
      have hr : r = .ground :=
        the_ground_is_the_only_unit r
          ((hb.trans (congrArg (· + 1) hb0)).trans (zero_plus 1))
      rw [hl, hr]

theorem the_tick_was_a_mirror (d : Nat) {δ : Plan} (hδ : δ ≠ .ground) :
    fold (fun a b => a + b) 1 (.board .ground .ground) = 2
      ∧ Nat.ble 2 (fold (fun a b => a + b) 1 δ) = true
      ∧ (∀ γ : Plan, fold (fun a b => a + b) 1 γ = 2 →
          γ = .board .ground .ground)
      ∧ bloom (d + 1) = graft (bloom d) (.board .ground .ground)
      ∧ ¬ bloom (d + 1) ∈ allPlans d :=
  ⟨rfl, no_tick_is_smaller_than_the_mirror hδ,
   the_least_tick_is_the_mirror, rfl, the_bloom_outgrows_the_room d⟩

theorem no_meeting_no_revision (δ : Plan) (h : boards δ = 0) :
    δ = .ground :=
  the_ground_is_the_only_unit δ
    ((every_meeting_is_one_move δ).symm.trans (congrArg (· + 1) h))

theorem one_meeting_is_the_mirror (δ : Plan) (h : boards δ = 1) :
    δ = .board .ground .ground :=
  the_least_tick_is_the_mirror δ
    ((every_meeting_is_one_move δ).symm.trans (congrArg (· + 1) h))

theorem every_quantum_is_the_mirror (δ γ : Plan) (h1 : boards δ = 1)
    (h0 : boards γ = 0) (d : Nat) :
    δ = .board .ground .ground
      ∧ γ = .ground
      ∧ boards (.board .ground .ground) = 1
      ∧ fold (fun a b => a + b) 1 (.board .ground .ground) = 2
      ∧ bloom (d + 1) = graft (bloom d) (.board .ground .ground) :=
  ⟨one_meeting_is_the_mirror δ h1, no_meeting_no_revision γ h0,
   rfl, rfl, rfl⟩

def pairFace {S : Type u} (F G : Face) (f : S → F.State)
    (g : S → G.State) : Face :=
  ⟨S, F.Probe × G.Probe, F.Ans × G.Ans,
   fun s pq => (F.obs (f s) pq.1, G.obs (g s) pq.2)⟩

theorem the_pair_refines_the_first_look {S : Type u} (F G : Face)
    (f : S → F.State) (g : S → G.State) (q₀ : G.Probe) (s t : S)
    (h : alike (pairFace F G f g) s t) (p : F.Probe) :
    F.obs (f s) p = F.obs (f t) p :=
  congrArg Prod.fst (h (p, q₀))

theorem the_pair_refines_the_second_look {S : Type u} (F G : Face)
    (f : S → F.State) (g : S → G.State) (p₀ : F.Probe) (s t : S)
    (h : alike (pairFace F G f g) s t) (q : G.Probe) :
    G.obs (g s) q = G.obs (g t) q :=
  congrArg Prod.snd (h (p₀, q))

theorem the_pair_parts_what_the_look_merges :
    alike (host windowFace Bool) (⟨0, 0⟩, true) (⟨0, 0⟩, false)
      ∧ ¬ alike
          (pairFace (host windowFace Bool)
            ⟨Bool, Unit, Bool, fun b _ => b⟩ (fun x => x) Prod.snd)
          (⟨0, 0⟩, true) (⟨0, 0⟩, false) :=
  ⟨fun _ => rfl,
   (fun h => nomatch congrArg Prod.snd (h ((0 : Nat), ())))⟩

theorem the_patience_face_was_a_pair (W X : Type) (r : Reception W X)
    (α : Nat → W) :
    (patienceFace W X).obs r α
      = (pairFace (receptionFace W X)
          ⟨Reception W X, Nat → W, Nat, doorsOpened⟩
          (fun x => x) (fun x => x)).obs r (α, α) := rfl

theorem the_comparison_mints_a_face {S : Type u} (F G : Face)
    (f : S → F.State) (g : S → G.State) {R : Type}
    (c : F.Ans → G.Ans → R) (s : S) (p : F.Probe) (q : G.Probe)
    (W X : Type) (r : Reception W X) (α : Nat → W) :
    c (F.obs (f s) p) (G.obs (g s) q)
        = (fun a : F.Ans × G.Ans => c a.1 a.2)
            ((pairFace F G f g).obs s (p, q))
      ∧ (patienceFace W X).obs r α
          = (pairFace (receptionFace W X)
              ⟨Reception W X, Nat → W, Nat, doorsOpened⟩
              (fun x => x) (fun x => x)).obs r (α, α)
      ∧ alike (host windowFace Bool) (⟨0, 0⟩, true) (⟨0, 0⟩, false)
      ∧ ¬ alike
          (pairFace (host windowFace Bool)
            ⟨Bool, Unit, Bool, fun b _ => b⟩ (fun x => x) Prod.snd)
          (⟨0, 0⟩, true) (⟨0, 0⟩, false) :=
  ⟨rfl, rfl,
   the_pair_parts_what_the_look_merges.1,
   the_pair_parts_what_the_look_merges.2⟩

def Derived (F : Face) (P : F.State → Prop) : Prop :=
  ∀ s t, alike F s t → (P s ↔ P t)

theorem a_role_read_at_a_probe_is_derived (F : Face) (p : F.Probe)
    (Q : F.Ans → Prop) : Derived F (fun s => Q (F.obs s p)) :=
  fun s t h => by
    show Q (F.obs s p) ↔ Q (F.obs t p)
    rw [h p]

theorem the_guest_is_not_a_derived_role :
    ¬ Derived (host windowFace Bool) (fun x => x.2 = true) :=
  fun h =>
    nomatch ((h (⟨0, 0⟩, true) (⟨0, 0⟩, false) (fun _ => rfl)).mp rfl)

theorem a_look_role_lifts_to_the_pair {S : Type u} (F G : Face)
    (f : S → F.State) (g : S → G.State) (q₀ : G.Probe) (P : S → Prop)
    (hP : ∀ s t, (∀ p, F.obs (f s) p = F.obs (f t) p) → (P s ↔ P t)) :
    Derived (pairFace F G f g) P :=
  fun s t h => hP s t (the_pair_refines_the_first_look F G f g q₀ s t h)

theorem the_pair_provokes_the_agreement :
    Derived (pairFace (host windowFace Bool)
        ⟨Bool, Unit, Bool, fun b _ => b⟩ (fun x => x) Prod.snd)
      (fun s => (host windowFace Bool).obs s (0 : Nat) = s.2)
      ∧ ¬ Derived (host windowFace Bool)
          (fun s => (host windowFace Bool).obs s (0 : Nat) = s.2) :=
  ⟨a_role_read_at_a_probe_is_derived
     (pairFace (host windowFace Bool)
       ⟨Bool, Unit, Bool, fun b _ => b⟩ (fun x => x) Prod.snd)
     ((0 : Nat), ()) (fun a => a.1 = a.2),
   (fun hD => nomatch
     ((hD (⟨0, 0⟩, true) (⟨0, 0⟩, false) (fun _ => rfl)).mp rfl))⟩

theorem the_pair_provokes_what_no_look_affords {S : Type u} (F G : Face)
    (f : S → F.State) (g : S → G.State) (q₀ : G.Probe) (P : S → Prop)
    (hP : ∀ s t, (∀ p, F.obs (f s) p = F.obs (f t) p) → (P s ↔ P t)) :
    Derived (pairFace F G f g) P
      ∧ Derived (pairFace (host windowFace Bool)
            ⟨Bool, Unit, Bool, fun b _ => b⟩ (fun x => x) Prod.snd)
          (fun s => (host windowFace Bool).obs s (0 : Nat) = s.2)
      ∧ ¬ Derived (host windowFace Bool)
          (fun s => (host windowFace Bool).obs s (0 : Nat) = s.2)
      ∧ ¬ Derived (host windowFace Bool) (fun x => x.2 = true) :=
  ⟨a_look_role_lifts_to_the_pair F G f g q₀ P hP,
   the_pair_provokes_the_agreement.1,
   the_pair_provokes_the_agreement.2,
   the_guest_is_not_a_derived_role⟩

theorem the_derived_look_widens_nothing (F : Face) {P2 A2 : Type}
    (obs2 : F.State → P2 → A2) (q₀ : P2)
    (hder : ∀ s t, alike F s t → ∀ q, obs2 s q = obs2 t q)
    (s t : F.State) :
    alike (pairFace F ⟨F.State, P2, A2, obs2⟩ (fun x => x) (fun x => x)) s t
      ↔ alike F s t :=
  ⟨fun h p =>
     the_pair_refines_the_first_look F ⟨F.State, P2, A2, obs2⟩
       (fun x => x) (fun x => x) q₀ s t h p,
   fun h pq => by
     show (F.obs s pq.1, obs2 s pq.2) = (F.obs t pq.1, obs2 t pq.2)
     rw [h pq.1, hder s t h pq.2]⟩

theorem the_pair_widens_only_past_the_conduct (F : Face) {P2 A2 : Type}
    (obs2 : F.State → P2 → A2) (q₀ : P2)
    (hder : ∀ s t, alike F s t → ∀ q, obs2 s q = obs2 t q)
    (s t : F.State) :
    (alike (pairFace F ⟨F.State, P2, A2, obs2⟩ (fun x => x) (fun x => x)) s t
        ↔ alike F s t)
      ∧ alike (host windowFace Bool) (⟨0, 0⟩, true) (⟨0, 0⟩, false)
      ∧ ¬ alike
          (pairFace (host windowFace Bool)
            ⟨Bool, Unit, Bool, fun b _ => b⟩ (fun x => x) Prod.snd)
          (⟨0, 0⟩, true) (⟨0, 0⟩, false) :=
  ⟨the_derived_look_widens_nothing F obs2 q₀ hder s t,
   the_pair_parts_what_the_look_merges.1,
   the_pair_parts_what_the_look_merges.2⟩

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

theorem every_widening_is_one_pairing {S : Type u} (F G H : Face)
    (f : S → F.State) (g : S → G.State) (h : S → H.State)
    (s : S) (p : F.Probe) (q : G.Probe) (r : H.Probe) :
    (pairFace F (pairFace G H g h) f (fun x => x)).obs s (p, (q, r))
        = (F.obs (f s) p, (G.obs (g s) q, H.obs (h s) r))
      ∧ (pairFace (pairFace F G f g) H (fun x => x) h).obs s ((p, q), r)
          = ((F.obs (f s) p, G.obs (g s) q), H.obs (h s) r)
      ∧ deepen ((pairFace (pairFace F G f g) H (fun x => x) h).obs
            s ((p, q), r))
          = (pairFace F (pairFace G H g h) f (fun x => x)).obs
              s (p, (q, r)) :=
  ⟨rfl, rfl, rfl⟩

theorem three_is_the_width_of_contact {S : Type u} (F G H : Face)
    (f : S → F.State) (g : S → G.State) (h : S → H.State) {R : Type}
    (c : F.Ans → G.Ans → R) (s : S) (p : F.Probe) (q : G.Probe)
    (r : H.Probe) :
    (¬ ∃ f' : Bool × Bool → Bool,
        ∀ a b : Bool × Bool, f' a = f' b → a = b)
      ∧ c (F.obs (f s) p) (G.obs (g s) q)
          = (fun a : F.Ans × G.Ans => c a.1 a.2)
              ((pairFace F G f g).obs s (p, q))
      ∧ deepen ((pairFace (pairFace F G f g) H (fun x => x) h).obs
            s ((p, q), r))
          = (pairFace F (pairFace G H g h) f (fun x => x)).obs
              s (p, (q, r)) :=
  ⟨the_hallway_is_too_small, rfl, rfl⟩

theorem the_serving_suggestion {S : Type u} (F G : Face)
    (f : S → F.State) (g : S → G.State) {R : Type}
    (c : F.Ans → G.Ans → R) (s : S) (p : F.Probe) (q : G.Probe)
    (q₀ : G.Probe) (t : S) (h : alike (pairFace F G f g) s t) :
    (pairFace F G f g).obs s (p, q) = (F.obs (f s) p, G.obs (g s) q)
      ∧ c (F.obs (f s) p) (G.obs (g s) q)
          = (fun a : F.Ans × G.Ans => c a.1 a.2)
              ((pairFace F G f g).obs s (p, q))
      ∧ (∀ p', F.obs (f s) p' = F.obs (f t) p')
      ∧ alike (host windowFace Bool) (⟨0, 0⟩, true) (⟨0, 0⟩, false)
      ∧ ¬ alike (pairFace (host windowFace Bool)
            ⟨Bool, Unit, Bool, fun b _ => b⟩ (fun x => x) Prod.snd)
          (⟨0, 0⟩, true) (⟨0, 0⟩, false)
      ∧ (∀ (F' : Face) (s' t' : F'.State), alike F' s' t' →
          ∀ q' : Interview F'.Probe F'.Ans,
            sound F' s' q' = sound F' t' q') :=
  ⟨rfl, rfl,
   the_pair_refines_the_first_look F G f g q₀ s t h,
   the_pair_parts_what_the_look_merges.1,
   the_pair_parts_what_the_look_merges.2,
   fun F' s' t' h' q' => no_interview_parts_the_alike F' s' t' h' q'⟩

def censusFace : Face :=
  ⟨Plan, Unit, Nat, fun p _ => fold (fun a b => a + b) 1 p⟩

theorem the_split_is_not_a_derived_role :
    ¬ Derived censusFace
        (fun p => ∃ t δ : Plan, t ≠ Plan.ground ∧ δ ≠ Plan.ground
          ∧ graft t δ = p) :=
  fun hD =>
    have hsplit : ∃ t δ : Plan, t ≠ Plan.ground ∧ δ ≠ Plan.ground
        ∧ graft t δ = bloom 2 :=
      ⟨.board .ground .ground, .board .ground .ground,
       (fun h => nomatch h), (fun h => nomatch h),
       the_blooms_add 1 1⟩
    match (hD (bloom 2)
        (.board .ground (.board .ground (.board .ground .ground)))
        (fun _ => rfl)).mp hsplit with
    | ⟨t, δ, ht, hδ, he⟩ =>
        match an_unsplit_lineage_may_read_composite.1 t δ he with
        | .inl h => ht h
        | .inr h => hδ h

theorem the_census_reads_the_split_only_at_the_primes (Q : Nat → Prop) :
    (∀ p : Plan,
        (∀ a b : Nat, a * b = fold (fun x y => x + y) 1 p →
          a = 1 ∨ b = 1) →
        ∀ t δ : Plan, graft t δ = p → t = .ground ∨ δ = .ground)
      ∧ Derived censusFace (fun p => Q (fold (fun a b => a + b) 1 p))
      ∧ ¬ Derived censusFace
          (fun p => ∃ t δ : Plan, t ≠ Plan.ground ∧ δ ≠ Plan.ground
            ∧ graft t δ = p) :=
  ⟨fun p hp => a_prime_reading_admits_no_split p hp,
   a_role_read_at_a_probe_is_derived censusFace () Q,
   the_split_is_not_a_derived_role⟩

theorem the_revision_also_rides (t δ : Plan) :
    Nat.ble (fold (fun a b => a + b) 1 δ)
      (fold (fun a b => a + b) 1 (graft t δ)) = true := by
  rw [the_revision_multiplies_the_reading]
  obtain ⟨a, ha⟩ := the_reading_is_positive t
  rw [ha, Nat.succ_mul]
  exact ble_le_add_left _ _

theorem every_factor_lives_below_the_horizon {m : Nat} (t δ p : Plan)
    (he : graft t δ = p) (hm : fold (fun a b => a + b) 1 p = m + 1) :
    t ∈ allPlans m ∧ δ ∈ allPlans m :=
  ⟨the_horizon_holds_every_reading m t (by
      rw [← hm, ← he]; exact the_ground_rides_in_every_graft t δ),
   the_horizon_holds_every_reading m δ (by
      rw [← hm, ← he]; exact the_revision_also_rides t δ)⟩

theorem the_split_is_searchable_in_the_room {m : Nat} (t δ p : Plan)
    (he : graft t δ = p) (hm : fold (fun a b => a + b) 1 p = m + 1) :
    (t ∈ allPlans m ∧ δ ∈ allPlans m)
      ∧ ¬ Derived censusFace
          (fun q => ∃ t' δ' : Plan, t' ≠ Plan.ground ∧ δ' ≠ Plan.ground
            ∧ graft t' δ' = q) :=
  ⟨every_factor_lives_below_the_horizon t δ p he hm,
   the_split_is_not_a_derived_role⟩

def selfSteered {I O : Type} (m : Machine I O) (r : m.S → I) :
    Machine Unit O :=
  ⟨m.S, m.s0, fun s _ => m.step s (r s), m.out⟩

def orbit {I O : Type} (m : Machine I O) (r : m.S → I) : m.S → Nat → m.S
  | s, 0 => s
  | s, n + 1 => orbit m r (m.step s (r s)) n

theorem the_self_steered_machine_is_a_clock {I O : Type} (m : Machine I O)
    (r : m.S → I) :
    ∀ (w : List Unit) (s : m.S),
      drive (selfSteered m r) s w = m.out (orbit m r s w.length)
  | [], _ => rfl
  | _ :: w, s => the_self_steered_machine_is_a_clock m r w (m.step s (r s))

def echoM : Machine Bool Bool := ⟨Bool, false, fun _ i => i, fun b => b⟩

theorem the_channel_hears_the_guest :
    behavior echoM [true] ≠ behavior echoM [false]
      ∧ ([true] : List Bool).length = ([false] : List Bool).length :=
  ⟨(fun h => nomatch h), rfl⟩

theorem the_clock_and_the_channel {I O : Type} (m : Machine I O)
    (r : m.S → I) (w w' : List Unit) (h : w.length = w'.length) :
    behavior (selfSteered m r) w = behavior (selfSteered m r) w'
      ∧ behavior echoM [true] ≠ behavior echoM [false]
      ∧ ([true] : List Bool).length = ([false] : List Bool).length :=
  ⟨(the_self_steered_machine_is_a_clock m r w m.s0).trans
     ((congrArg (fun n => m.out (orbit m r m.s0 n)) h).trans
       (the_self_steered_machine_is_a_clock m r w' m.s0).symm),
   (fun hh => nomatch hh), rfl⟩

theorem the_clock_of_mirrors_parks_at_the_bloom :
    ∀ (n : Nat) (t : Plan),
      orbit grower (fun _ => .board .ground .ground) t n
        = graft t (bloom n)
  | 0, _ => rfl
  | n + 1, t => by
      show orbit grower (fun _ => .board .ground .ground)
          (graft t (.board .ground .ground)) n = graft t (bloom (n + 1))
      rw [the_clock_of_mirrors_parks_at_the_bloom n
            (graft t (.board .ground .ground)),
          ← lineages_compose t (.board .ground .ground) (bloom n),
          show graft (.board .ground .ground) (bloom n) = bloom (n + 1) from
            (the_blooms_add 1 n).trans (congrArg bloom (Nat.add_comm 1 n))]

theorem the_bloom_is_the_clocks_orbit (n : Nat) :
    orbit grower (fun _ => .board .ground .ground) .ground n = bloom n :=
  (the_clock_of_mirrors_parks_at_the_bloom n .ground).trans
    (the_trivial_revision_changes_nothing (bloom n))

theorem the_mirror_clock_reads_the_caps (w : List Unit) :
    behavior (selfSteered grower (fun _ => .board .ground .ground)) w
      = roomCap w.length :=
  (the_self_steered_machine_is_a_clock grower
      (fun _ => .board .ground .ground) w .ground).trans
    ((congrArg (fold (fun a b => a + b) 1)
        (the_bloom_is_the_clocks_orbit w.length)).trans
      (the_bloom_fills_its_cap w.length))

theorem the_mirror_clock_never_comes_home (n : Nat) :
    Nat.ble (roomCap n + 1) (roomCap (n + 1)) = true := by
  obtain ⟨m, hm⟩ := the_cap_is_positive n
  show Nat.ble (roomCap n + 1) (roomCap n + roomCap n) = true
  rw [hm]
  exact ble_add_both (ble_refl (m + 1)) (ble_le_add_left m 1)

theorem the_stage_is_a_kept_clock (n : Nat) (w : List Unit) :
    orbit grower (fun _ => .board .ground .ground) .ground n = bloom n
      ∧ behavior (selfSteered grower (fun _ => .board .ground .ground)) w
          = roomCap w.length
      ∧ Nat.ble (roomCap n + 1) (roomCap (n + 1)) = true :=
  ⟨the_bloom_is_the_clocks_orbit n, the_mirror_clock_reads_the_caps w,
   the_mirror_clock_never_comes_home n⟩

def selfWord {I O : Type} (m : Machine I O) (r : m.S → I) :
    m.S → Nat → List I
  | _, 0 => []
  | s, n + 1 => r s :: selfWord m r (m.step s (r s)) n

theorem the_instinct_replays_its_word {I O : Type} (m : Machine I O)
    (r : m.S → I) :
    ∀ (w : List Unit) (s : m.S),
      drive (selfSteered m r) s w = drive m s (selfWord m r s w.length)
  | [], _ => rfl
  | _ :: w, s => the_instinct_replays_its_word m r w (m.step s (r s))

theorem internalization_is_self_steering {I O : Type} (m : Machine I O)
    (r : m.S → I) (w w' : List Unit) (h : w.length = w'.length)
    (n : Nat) :
    (∀ (v : List Unit) (s : m.S),
        drive (selfSteered m r) s v = drive m s (selfWord m r s v.length))
      ∧ behavior (selfSteered m r) w = behavior (selfSteered m r) w'
      ∧ orbit grower (fun _ => .board .ground .ground) .ground n
          = bloom n :=
  ⟨the_instinct_replays_its_word m r,
   (the_clock_and_the_channel m r w w' h).1,
   the_bloom_is_the_clocks_orbit n⟩

def spiral (a d b : Nat) : Machine Unit Bool :=
  ⟨Nat, 0, fun n _ => n + 1, fun n => within ⟨n * a, n * a + d⟩ (n * b)⟩

theorem the_spiral_parks_at_its_count (a d b : Nat) :
    ∀ (w : List Unit) (s : Nat), park (spiral a d b) s w = s + w.length
  | [], _ => rfl
  | _ :: w, s =>
      (the_spiral_parks_at_its_count a d b w (s + 1)).trans
        (succ_adds s w.length)

theorem the_spiral_reads_at_its_count (a d b : Nat) (w : List Unit)
    (s : Nat) :
    drive (spiral a d b) s w
      = within ⟨(s + w.length) * a, (s + w.length) * a + d⟩
          ((s + w.length) * b) :=
  (the_drive_reads_the_walk (spiral a d b) w s).trans
    (congrArg (spiral a d b).out
      ((the_park_is_a_walk (spiral a d b) w s).symm.trans
        (the_spiral_parks_at_its_count a d b w s)))

theorem the_wheel_reads_itself_unworn (a d : Nat) (w : List Unit) (s : Nat) :
    drive (spiral a d a) s w = true :=
  (the_spiral_reads_at_its_count a d a w s).trans
    (the_lock_survives_every_lap a d (s + w.length))

theorem the_spiral_holds_the_first_lap (a g e : Nat) (w : List Unit)
    (hw : w.length = 1) :
    behavior (spiral a ((g + 1) + e) (a + (g + 1))) w = true := by
  show drive (spiral a ((g + 1) + e) (a + (g + 1))) (0 : Nat) w = true
  rw [the_spiral_reads_at_its_count, zero_plus, hw,
      one_times a, one_times (a + (g + 1))]
  exact the_near_pace_lands_in_the_window a g e

theorem the_spiral_flips_at_the_witness (a g e : Nat) (w : List Unit)
    (hw : w.length = ((g + 1) + e) + 1) :
    behavior (spiral a ((g + 1) + e) (a + (g + 1))) w = false := by
  show drive (spiral a ((g + 1) + e) (a + (g + 1))) (0 : Nat) w = false
  rw [the_spiral_reads_at_its_count, zero_plus, hw]
  exact the_gap_outruns_every_window a g ((g + 1) + e)

theorem the_kept_lap_reads_the_gap (a g e s : Nat) (w v u : List Unit)
    (hv : v.length = 1) (hu : u.length = ((g + 1) + e) + 1) :
    drive (spiral a ((g + 1) + e) a) s w = true
      ∧ behavior (spiral a ((g + 1) + e) (a + (g + 1))) v = true
      ∧ behavior (spiral a ((g + 1) + e) (a + (g + 1))) u = false
      ∧ park (spiral a ((g + 1) + e) (a + (g + 1))) (0 : Nat) u = u.length :=
  ⟨the_wheel_reads_itself_unworn a ((g + 1) + e) w s,
   the_spiral_holds_the_first_lap a g e v hv,
   the_spiral_flips_at_the_witness a g e u hu,
   (the_spiral_parks_at_its_count a ((g + 1) + e) (a + (g + 1)) u 0).trans
     (zero_plus u.length)⟩

def originFace (S : Type u) : Face :=
  ⟨S, Unit, Unit, fun _ _ => ()⟩

theorem the_origin_merges_every_seat {S : Type u} (s t : S) :
    alike (originFace S) s t :=
  fun _ => rfl

theorem no_interview_parts_the_origin {S : Type u} (s t : S)
    (q : Interview Unit Unit) :
    sound (originFace S) s q = sound (originFace S) t q :=
  no_interview_parts_the_alike (originFace S) s t
    (the_origin_merges_every_seat s t) q

theorem the_origin_is_the_pairs_unit (F : Face) (s t : F.State) :
    alike (pairFace F (originFace F.State) (fun x => x) (fun x => x)) s t
      ↔ alike F s t :=
  the_derived_look_widens_nothing F (fun _ _ => ()) ()
    (fun _ _ _ _ => rfl) s t

theorem the_constant_look_attributes_the_parting {S : Type u} (F G : Face)
    (f : S → F.State) (g : S → G.State) (p₀ : F.Probe)
    (hmerge : ∀ x y : F.State, alike F x y) (s t : S) :
    alike (pairFace F G f g) s t
      ↔ ∀ q, G.obs (g s) q = G.obs (g t) q :=
  ⟨fun h => the_pair_refines_the_second_look F G f g p₀ s t h,
   fun h pq => by
     show (F.obs (f s) pq.1, G.obs (g s) pq.2)
         = (F.obs (f t) pq.1, G.obs (g t) pq.2)
     rw [hmerge (f s) (f t) pq.1, h pq.2]⟩

theorem the_meeting_has_a_unit {S : Type u} (F G : Face) (f : S → F.State)
    (g : S → G.State) (p₀ : F.Probe)
    (hmerge : ∀ x y : F.State, alike F x y) (s t : S)
    (F' : Face) (s' t' : F'.State) :
    alike (originFace F'.State) s' t'
      ∧ (alike (pairFace F' (originFace F'.State) (fun x => x) (fun x => x))
            s' t'
          ↔ alike F' s' t')
      ∧ (alike (pairFace F G f g) s t
          ↔ ∀ q, G.obs (g s) q = G.obs (g t) q)
      ∧ (alike (host windowFace Bool) (⟨0, 0⟩, true) (⟨0, 0⟩, false)
          ∧ ¬ alike
              (pairFace (host windowFace Bool)
                ⟨Bool, Unit, Bool, fun b _ => b⟩ (fun x => x) Prod.snd)
              (⟨0, 0⟩, true) (⟨0, 0⟩, false)) :=
  ⟨the_origin_merges_every_seat s' t',
   the_origin_is_the_pairs_unit F' s' t',
   the_constant_look_attributes_the_parting F G f g p₀ hmerge s t,
   the_pair_parts_what_the_look_merges⟩

def recite {P A : Type} : List P → Interview P A
  | [] => .rest
  | p :: ps => .ask p (fun _ => recite ps)

theorem the_recital_is_the_transcript (F : Face) (s : F.State) :
    ∀ ps : List F.Probe, sound F s (recite ps) = ps.map (F.obs s)
  | [] => rfl
  | p :: ps =>
      congrArg (F.obs s p :: ·) (the_recital_is_the_transcript F s ps)

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
      show F.obs s p :: sound F s (recite ps)
          = F.obs t p :: sound F t (recite ps)
      rw [h p (List.Mem.head ps),
          the_agreed_window_sounds_as_one F s t ps
            (fun q hq => h q (List.Mem.tail p hq))]

theorem the_beholders_run_out_of_disagreement (F : Face)
    (beq : F.Ans → F.Ans → Bool)
    (hs : ∀ a b : F.Ans, beq a b = true → a = b)
    (s t : F.State) (ps : List F.Probe)
    {S : Type u} (x y : S) (qs : List Unit) :
    ((∀ p, p ∈ ps → beq (F.obs s p) (F.obs t p) = true)
        ∨ ∃ p, p ∈ ps ∧ beq (F.obs s p) (F.obs t p) = false)
      ∧ ((∀ p, p ∈ ps → beq (F.obs s p) (F.obs t p) = true) →
          sound F s (recite ps) = sound F t (recite ps))
      ∧ sound F s (recite ps) = ps.map (F.obs s)
      ∧ sound (originFace S) x (recite qs)
          = sound (originFace S) y (recite qs) :=
  ⟨the_window_agrees_or_names_the_gap F beq s t ps,
   fun h =>
     the_agreed_window_sounds_as_one F s t ps
       (fun p hp => hs _ _ (h p hp)),
   the_recital_is_the_transcript F s ps,
   no_interview_parts_the_origin x y (recite qs)⟩

theorem the_guest_is_never_a_derived_role (F : Face) {W : Type}
    (s : F.State) {w w' : W} (hw : w ≠ w') :
    ¬ Derived (host F W) (fun x => x.2 = w) :=
  fun hD => hw ((hD (s, w) (s, w') (fun _ => rfl)).mp rfl).symm

theorem the_roles_run_the_handshake (F : Face) {W : Type}
    (s : F.State) {w w' : W} (hw : w ≠ w') (p : F.Probe)
    (Q : F.Ans → Prop) (r : W → F.Probe) :
    Derived (host F W) (fun x => Q ((host F W).obs x p))
      ∧ ¬ Derived (host F W) (fun x => x.2 = w)
      ∧ ((s, w) ≠ (s, w') ∧ alike (host F W) (s, w) (s, w'))
      ∧ selfMeet (host F W) (fun x => r x.2) (s, w) = F.obs s (r w) :=
  ⟨a_role_read_at_a_probe_is_derived (host F W) p Q,
   the_guest_is_never_a_derived_role F s hw,
   ⟨(fun he => hw (congrArg Prod.snd he)), fun _ => rfl⟩,
   the_self_meeting_reads_the_guest F r s w⟩

theorem the_sounding_reads_the_alike (F : Face) (s t : F.State)
    (h : ∀ q : Interview F.Probe F.Ans, sound F s q = sound F t q) :
    alike F s t :=
  fun p => (List.cons.inj (h (.ask p (fun _ => .rest)))).1

theorem the_recital_reads_the_alike (F : Face) (s t : F.State)
    (h : ∀ ps : List F.Probe,
      sound F s (recite ps) = sound F t (recite ps)) :
    alike F s t :=
  fun p => (List.cons.inj (h [p])).1

theorem the_curtain_is_exact (F : Face) (s t : F.State)
    {I O : Type} (m n : Machine I O) :
    (alike F s t
        ↔ ∀ q : Interview F.Probe F.Ans, sound F s q = sound F t q)
      ∧ (alike F s t
          ↔ ∀ ps : List F.Probe,
              sound F s (recite ps) = sound F t (recite ps))
      ∧ ((∀ w, behavior m w = behavior n w)
          ↔ ∀ q : Interview (List I) O, audition m q = audition n q) :=
  ⟨⟨fun h q => no_interview_parts_the_alike F s t h q,
    the_sounding_reads_the_alike F s t⟩,
   ⟨fun h ps => no_interview_parts_the_alike F s t h (recite ps),
    the_recital_reads_the_alike F s t⟩,
   ⟨fun h q => an_audition_hears_only_the_conduct m n h q,
    fun h => the_sounding_reads_the_alike (airGap I O) m n h⟩⟩

def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1

def collatzStep (n : Nat) : Nat :=
  cond (oddNat n) (3 * n + 1) (halve n)

def collatz : Machine Unit Nat :=
  ⟨Nat, 1, fun n _ => collatzStep n, fun n => n⟩

theorem the_home_wheel_turns :
    park collatz (1 : Nat) [(), (), ()] = (1 : Nat)
      ∧ park collatz (4 : Nat) [(), (), ()] = (4 : Nat)
      ∧ park collatz (2 : Nat) [(), (), ()] = (2 : Nat) :=
  ⟨rfl, rfl, rfl⟩

theorem the_homecoming_is_conduct :
    (park collatz (1 : Nat) [(), (), ()] = (1 : Nat)
        ∧ park collatz (4 : Nat) [(), (), ()] = (4 : Nat)
        ∧ park collatz (2 : Nat) [(), (), ()] = (2 : Nat))
      ∧ (∀ (v : List Unit) (s : Nat), park paceOne s (() :: v) ≠ s)
      ∧ ∀ b : Bool, park flip b [(), ()] = b :=
  ⟨the_home_wheel_turns,
   fun v s he =>
     no_gain_is_zero s v.length
       ((the_pace_parks_at_its_count (() :: v) s).symm.trans he),
   the_flip_wheels⟩

def exchange {W : Type} (σ : W → W → W) (d : door W W) : door W W :=
  turnAbout (vertical σ d)

def still {W : Type} : W → W → W := fun _ w => w

def dialogue {W : Type} (d : door W W) (σs : List (W → W → W)) :
    door W W :=
  walk (fun e σ => exchange σ e) d σs

theorem the_spoken_arrives_at_the_face {W : Type} (σ : W → W → W)
    (d : door W W) :
    face (exchange σ d) = σ (face d) (met d)
      ∧ met (exchange σ d) = face d :=
  ⟨rfl, rfl⟩

theorem the_listening_turn_is_the_yield {W : Type} (d : door W W) :
    exchange still d = turnAbout d := rfl

theorem the_two_listeners_restore_the_table {W : Type} (d : door W W) :
    exchange still (exchange still d) = d := rfl

theorem the_dialogue_resumes {W : Type} (d : door W W)
    (σs τs : List (W → W → W)) :
    dialogue d (σs ++ τs) = dialogue (dialogue d σs) τs :=
  the_walk_resumes (fun e σ => exchange σ e) σs τs d

theorem the_conversation_is_a_walk {W X : Type} (σ : W → W → W)
    (d : door W W) (σs τs : List (W → W → W)) (g : W → X) :
    (face (exchange σ d) = σ (face d) (met d)
        ∧ met (exchange σ d) = face d)
      ∧ exchange still (exchange still d) = d
      ∧ dialogue d (σs ++ τs) = dialogue (dialogue d σs) τs
      ∧ g (face (vertical σ d)) = g (face d) :=
  ⟨the_spoken_arrives_at_the_face σ d,
   the_two_listeners_restore_the_table d,
   the_dialogue_resumes d σs τs,
   a_guest_mover_is_unheard σ g d⟩

theorem the_deaf_turn_merges {W : Type} (f : W → W) (h : W) (w w' : W) :
    exchange (fun x _ => f x) (atTheDoor h w)
      = exchange (fun x _ => f x) (atTheDoor h w') := rfl

theorem no_move_unsays_the_deaf_turn {W : Type} (f : W → W) (h : W)
    {w w' : W} (hw : w ≠ w') :
    ¬ ∃ g : door W W → door W W,
      ∀ d, g (exchange (fun x _ => f x) d) = d :=
  fun he =>
    he.elim fun g hg =>
      hw (congrArg met
        ((hg (atTheDoor h w)).symm.trans
          ((congrArg g (the_deaf_turn_merges f h w w')).trans
            (hg (atTheDoor h w')))))

theorem the_turn_keeps_only_what_it_hears {W : Type} (f : W → W)
    (d : door W W) (h : W) {w w' : W} (hw : w ≠ w') :
    exchange still (exchange still d) = d
      ∧ face (exchange still d) = met d
      ∧ (exchange (fun x _ => f x) (atTheDoor h w)
            = exchange (fun x _ => f x) (atTheDoor h w')
          ∧ atTheDoor h w ≠ atTheDoor h w')
      ∧ ¬ ∃ g : door W W → door W W,
          ∀ e, g (exchange (fun x _ => f x) e) = e :=
  ⟨the_two_listeners_restore_the_table d,
   rfl,
   ⟨the_deaf_turn_merges f h w w', the_guest_is_real h hw⟩,
   no_move_unsays_the_deaf_turn f h hw⟩

theorem the_repeated_ask_hears_one_answer (F : Face) (s : F.State)
    (p : F.Probe) :
    ∀ n : Nat,
      sound F s (recite (List.replicate n p))
        = List.replicate n (F.obs s p)
  | 0 => rfl
  | n + 1 =>
      congrArg (F.obs s p :: ·)
        (the_repeated_ask_hears_one_answer F s p n)

theorem the_worn_word_spends_no_object {W X : Type} (p p' : Plan)
    (s : build W p) (g : build W p → X) (a d : Nat) (w : List Unit)
    (n k : Nat) {I O : Type} (m : Machine I O)
    (hstill : ∀ st i, m.out (m.step st i) = m.out st) (ws : List I)
    (st : m.S) (F : Face) (t : F.State) (q : F.Probe) :
    sound F t (recite (List.replicate k q))
        = List.replicate k (F.obs t q)
      ∧ drive (spiral a d a) n w = true
      ∧ g (face (label W p s)) = g (face (atTheDoor s p'))
      ∧ met (label W p s) = p
      ∧ drive m st ws = m.out st :=
  ⟨the_repeated_ask_hears_one_answer F t q k,
   the_wheel_reads_itself_unworn a d w n,
   the_label_rides_unread p p' s g,
   the_meeting_reads_the_label W p s,
   stillness_hides_the_ticking m hstill ws st⟩

theorem the_park_resumes {I O : Type} (m : Machine I O) (w v : List I)
    (s : m.S) :
    park m s (w ++ v) = park m (park m s w) v :=
  ((the_park_is_a_walk m (w ++ v) s).trans
    ((the_walk_resumes m.step w v s).trans
      (congrArg (fun x => walk m.step x v)
        (the_park_is_a_walk m w s).symm))).trans
    (the_park_is_a_walk m v (park m s w)).symm

theorem the_rep_lands_where_it_is_fed {I O : Type} (m : Machine I O)
    (w v : List I) (n : Nat) (s : m.S) (u : List Unit) (t : Nat)
    (r : m.S → I) (vs : List Unit) :
    audition m (recite (List.replicate n w))
        = List.replicate n (behavior m w)
      ∧ park m s (w ++ v) = park m (park m s w) v
      ∧ park paceOne (park paceOne t u) u = (t + u.length) + u.length
      ∧ drive (selfSteered m r) s vs
          = drive m s (selfWord m r s vs.length) :=
  ⟨the_repeated_ask_hears_one_answer (airGap I O) m w n,
   the_park_resumes m w v s,
   by rw [the_pace_parks_at_its_count, the_pace_parks_at_its_count],
   the_instinct_replays_its_word m r vs s⟩

theorem the_yield_fixes_the_agreed {W : Type} (d : door W W) :
    turnAbout d = d ↔ met d = face d :=
  ⟨fun h => congrArg face h,
   fun h =>
     (congrArg (atTheDoor · (face d)) h).trans
       (congrArg (atTheDoor (face d) ·) h).symm⟩

theorem the_quiescence_signature {W : Type} (d : door W W)
    (σ : W → W → W) (w : W) (V : Type) (p : Plan) (s : build V p) :
    (turnAbout d = d ↔ met d = face d)
      ∧ (exchange still d = d ↔ met d = face d)
      ∧ met (mirror V p s) = face (mirror V p s)
      ∧ face (exchange σ (atTheDoor w w)) = σ w w :=
  ⟨the_yield_fixes_the_agreed d,
   the_yield_fixes_the_agreed d,
   rfl,
   rfl⟩

def buffered {I O : Type} (m : Machine I O) : Machine I O :=
  ⟨m.S × List I, (m.s0, []), fun st i => (st.1, st.2 ++ [i]),
   fun st => drive m st.1 st.2⟩

def settleHeld {I O : Type} (m : Machine I O) (st : m.S × List I) :
    m.S × List I :=
  (park m st.1 st.2, [])

theorem the_hold_walks_beside_the_work {I O : Type} (m : Machine I O)
    (w : List I) (s : m.S) (held : List I) :
    drive (buffered m) (s, held) w = drive m (park m s held) w :=
  two_machines_in_step_agree (buffered m) m
    (fun st t => park m st.1 st.2 = t)
    (fun st _t i ht =>
      (the_park_resumes m st.2 [i] st.1).trans
        (congrArg (fun x => park m x [i]) ht))
    (fun st _t ht =>
      (the_drive_reads_the_walk m st.2 st.1).trans
        (congrArg m.out ((the_park_is_a_walk m st.2 st.1).symm.trans ht)))
    w (s, held) (park m s held) rfl

theorem the_buffer_is_invisible {I O : Type} (m : Machine I O)
    (w : List I) :
    behavior (buffered m) w = behavior m w :=
  the_hold_walks_beside_the_work m w m.s0 []

theorem the_settle_is_unheard {I O : Type} (m : Machine I O)
    (st : m.S × List I) (w : List I) :
    drive (buffered m) (settleHeld m st) w = drive (buffered m) st w :=
  (the_hold_walks_beside_the_work m w (park m st.1 st.2) []).trans
    (the_hold_walks_beside_the_work m w st.1 st.2).symm

theorem the_held_and_the_worked_read_alike {I O : Type} (m : Machine I O)
    (s : m.S) (i : I) (held w : List I) :
    drive (buffered m) (settleHeld m (s, i :: held)) w
        = drive (buffered m) (s, i :: held) w
      ∧ (settleHeld m (s, i :: held)).2
          ≠ ((s, i :: held) : m.S × List I).2 :=
  ⟨the_settle_is_unheard m (s, i :: held) w,
   fun h => nomatch h⟩

theorem the_decomposition_is_the_remainder {I O : Type} (m : Machine I O)
    (w v : List I) (s : m.S) (held : List I) (i : I) :
    drive (buffered m) (s, held) w = drive m (park m s held) w
      ∧ behavior (buffered m) v = behavior m v
      ∧ drive (buffered m) (settleHeld m (s, held)) w
          = drive (buffered m) (s, held) w
      ∧ (drive (buffered m) (settleHeld m (s, i :: held)) w
            = drive (buffered m) (s, i :: held) w
          ∧ (settleHeld m (s, i :: held)).2
              ≠ ((s, i :: held) : m.S × List I).2) :=
  ⟨the_hold_walks_beside_the_work m w s held,
   the_buffer_is_invisible m v,
   the_settle_is_unheard m (s, held) w,
   the_held_and_the_worked_read_alike m s i held w⟩

theorem the_wider_parting_lands_at_the_ground (F : Face) {W : Type}
    (s : F.State) (w w' : W)
    (h : (widen F W).obs (s, w) (viaRight ())
      ≠ (widen F W).obs (s, w') (viaRight ())) :
    w ≠ w' :=
  fun he =>
    h (congrArg (fun x => (widen F W).obs (s, x) (viaRight ())) he)

theorem the_premise_meets_its_witness (F : Face) {W : Type}
    (s : F.State) {w w' : W} (hw : w ≠ w')
    (q : Interview F.Probe F.Ans) :
    alike (host F W) (s, w) (s, w')
      ∧ sound (host F W) (s, w) q = sound (host F W) (s, w') q
      ∧ (widen F W).obs (s, w) (viaRight ())
          ≠ (widen F W).obs (s, w') (viaRight ())
      ∧ ((widen F W).obs (s, w) (viaRight ())
            ≠ (widen F W).obs (s, w') (viaRight ()) → w ≠ w') :=
  ⟨fun _ => rfl,
   no_interview_parts_the_alike (host F W) (s, w) (s, w')
     (fun _ => rfl) q,
   (fun he => hw (Sum.inr.inj he)),
   the_wider_parting_lands_at_the_ground F s w w'⟩

inductive Hand where
  | rock : Hand
  | paper : Hand
  | scissors : Hand

def beats : Hand → Hand → Bool
  | .rock, .rock => false
  | .rock, .paper => false
  | .rock, .scissors => true
  | .paper, .rock => true
  | .paper, .paper => false
  | .paper, .scissors => false
  | .scissors, .rock => false
  | .scissors, .paper => true
  | .scissors, .scissors => false

theorem no_hand_beats_itself : ∀ x : Hand, beats x x = false
  | .rock => rfl
  | .paper => rfl
  | .scissors => rfl

theorem every_hand_meets_its_match :
    ∀ x : Hand, ∃ y z : Hand, beats y x = true ∧ beats x z = true
  | .rock => ⟨.paper, .scissors, rfl, rfl⟩
  | .paper => ⟨.scissors, .rock, rfl, rfl⟩
  | .scissors => ⟨.rock, .paper, rfl, rfl⟩

theorem the_interlock_refuses_the_ladder :
    ¬ ∃ rank : Hand → Nat,
      ∀ x y : Hand, beats x y = true →
        Nat.ble (rank y + 1) (rank x) = true :=
  fun he =>
    he.elim fun rank h =>
      have h1 := h .rock .scissors rfl
      have h2 := h .scissors .paper rfl
      have h3 := h .paper .rock rfl
      have c1 : Nat.ble (rank .rock + 1) (rank .scissors) = true :=
        ble_trans _ _ _ h3
          (ble_trans _ _ _ (ble_le_succ (rank .paper)) h2)
      have c2 : Nat.ble (rank .rock + 1) (rank .rock) = true :=
        ble_trans _ _ _ c1
          (ble_trans _ _ _ (ble_le_succ (rank .scissors)) h1)
      nomatch (ble_succ_false (rank .rock)).symm.trans c2

theorem the_trio_interlocks :
    (∀ x : Hand, beats x x = false)
      ∧ (∀ x : Hand, ∃ y z : Hand, beats y x = true ∧ beats x z = true)
      ∧ (¬ ∃ rank : Hand → Nat,
          ∀ x y : Hand, beats x y = true →
            Nat.ble (rank y + 1) (rank x) = true)
      ∧ ¬ ∃ f : Bool × Bool → Bool,
          ∀ a b : Bool × Bool, f a = f b → a = b :=
  ⟨no_hand_beats_itself,
   every_hand_meets_its_match,
   the_interlock_refuses_the_ladder,
   the_hallway_is_too_small⟩

theorem ble_antisymm : ∀ a b : Nat,
    Nat.ble a b = true → Nat.ble b a = true → a = b
  | 0, 0, _, _ => rfl
  | 0, _ + 1, _, h2 => nomatch h2
  | _ + 1, 0, h1, _ => nomatch h1
  | a + 1, b + 1, h1, h2 => congrArg (· + 1) (ble_antisymm a b h1 h2)

theorem no_rank_descends_the_flip :
    ¬ ∃ rank : Bool → Nat,
      ∀ b : Bool, Nat.ble (rank (!b) + 1) (rank b) = true :=
  fun he =>
    he.elim fun rank h =>
      have c : Nat.ble (rank true + 1) (rank true) = true :=
        ble_trans _ _ _ (h false)
          (ble_trans _ _ _ (ble_le_succ (rank false)) (h true))
      nomatch (ble_succ_false (rank true)).symm.trans c

theorem no_rank_descends_the_home_wheel :
    ¬ ∃ rank : Nat → Nat,
      ∀ n : Nat, Nat.ble (rank (collatzStep n) + 1) (rank n) = true :=
  fun he =>
    he.elim fun rank h =>
      have c1 : Nat.ble (rank 1 + 1) (rank 4) = true :=
        ble_trans _ _ _ (h 2)
          (ble_trans _ _ _ (ble_le_succ (rank 2)) (h 4))
      have c2 : Nat.ble (rank 1 + 1) (rank 1) = true :=
        ble_trans _ _ _ c1
          (ble_trans _ _ _ (ble_le_succ (rank 4)) (h 1))
      nomatch (ble_succ_false (rank 1)).symm.trans c2

theorem the_wheel_flattens_the_monotone (rank : Nat → Nat)
    (h : ∀ n : Nat, Nat.ble (rank (collatzStep n)) (rank n) = true) :
    rank 4 = rank 1 ∧ rank 2 = rank 4 ∧ rank 1 = rank 2 :=
  ⟨ble_antisymm _ _ (h 1) (ble_trans _ _ _ (h 2) (h 4)),
   ble_antisymm _ _ (h 4) (ble_trans _ _ _ (h 1) (h 2)),
   ble_antisymm _ _ (h 2) (ble_trans _ _ _ (h 4) (h 1))⟩

theorem the_wheel_refuses_the_ladder :
    (¬ ∃ rank : Hand → Nat,
        ∀ x y : Hand, beats x y = true →
          Nat.ble (rank y + 1) (rank x) = true)
      ∧ (¬ ∃ rank : Bool → Nat,
          ∀ b : Bool, Nat.ble (rank (!b) + 1) (rank b) = true)
      ∧ (¬ ∃ rank : Nat → Nat,
          ∀ n : Nat, Nat.ble (rank (collatzStep n) + 1) (rank n) = true)
      ∧ (∀ rank : Nat → Nat,
          (∀ n : Nat, Nat.ble (rank (collatzStep n)) (rank n) = true) →
            rank 4 = rank 1 ∧ rank 2 = rank 4 ∧ rank 1 = rank 2)
      ∧ park collatz (1 : Nat) [(), (), ()] = (1 : Nat) :=
  ⟨the_interlock_refuses_the_ladder,
   no_rank_descends_the_flip,
   no_rank_descends_the_home_wheel,
   the_wheel_flattens_the_monotone,
   the_home_wheel_turns.1⟩

theorem no_inverse_unsteps_the_collatz :
    ¬ ∃ g : Nat → Nat, ∀ n : Nat, g (collatzStep n) = n :=
  fun he =>
    he.elim fun _ h =>
      nomatch Nat.succ.inj ((h 1).symm.trans (h 8))

theorem the_wheel_counters_forward {I O : Type} (m : Machine I O)
    (s : m.S) (w v : List I) (h : park m s (w ++ v) = s) :
    park m (park m s w) v = s :=
  (the_park_resumes m w v s).symm.trans h

theorem the_wheel_is_its_own_countermove :
    (¬ ∃ g : Nat → Nat, ∀ n : Nat, g (collatzStep n) = n)
      ∧ collatzStep 1 = collatzStep 8
      ∧ (1 : Nat) ≠ 8
      ∧ (∀ {I O : Type} (m : Machine I O) (s : m.S) (w v : List I),
          park m s (w ++ v) = s → park m (park m s w) v = s)
      ∧ park collatz (4 : Nat) [(), ()] = (1 : Nat)
      ∧ ∀ b : Bool, park flip b [(), ()] = b :=
  ⟨no_inverse_unsteps_the_collatz,
   rfl,
   (fun h => nomatch Nat.succ.inj h),
   fun m s w v h => the_wheel_counters_forward m s w v h,
   rfl,
   the_flip_wheels⟩

def hollowShell : Machine Unit Bool :=
  ⟨Unit, (), fun _ _ => (), fun _ => true⟩

theorem the_muffled_tally_is_the_resting_counter :
    revoice (fun _ => true) (tally Unit) = restingCounter := rfl

theorem the_revoice_moves_no_seat {I O O' : Type} (g : O → O')
    (m : Machine I O) :
    ∀ (w : List I) (s : m.S), park (revoice g m) s w = park m s w
  | [], _ => rfl
  | i :: w, s => the_revoice_moves_no_seat g m w (m.step s i)

theorem the_shell_sounds_still (w : List Unit) :
    behavior hollowShell w = true :=
  stillness_hides_the_ticking hollowShell (fun _ _ => rfl) w ()

theorem the_flywheel_and_the_shell_sound_alike
    (q : Interview (List Unit) Bool) :
    audition restingCounter q = audition hollowShell q :=
  an_audition_hears_only_the_conduct restingCounter hollowShell
    (fun w =>
      (the_still_face_is_not_a_dead_machine.1 w).trans
        (the_shell_sounds_still w).symm)
    q

theorem the_muffler_banks_the_run :
    ∀ (w : List Unit) (s : Nat), park restingCounter s w = s + w.length
  | [], _ => rfl
  | _ :: w, s =>
      (the_muffler_banks_the_run w (s + 1)).trans (succ_adds s w.length)

theorem the_wider_voice_releases_the_bank (w : List Unit) :
    behavior (tally Unit) w = w.length :=
  (drive_counts w 0).trans (zero_plus w.length)

theorem the_still_face_banks_the_run {I O O' : Type} (g : O → O')
    (m : Machine I O) (v : List I) (t : m.S)
    (w : List Unit) (s : Nat) (q : Interview (List Unit) Bool) :
    revoice (fun _ => true) (tally Unit) = restingCounter
      ∧ audition restingCounter q = audition hollowShell q
      ∧ park restingCounter s w = s + w.length
      ∧ behavior (tally Unit) w = w.length
      ∧ park (revoice g m) t v = park m t v :=
  ⟨rfl,
   the_flywheel_and_the_shell_sound_alike q,
   the_muffler_banks_the_run w s,
   the_wider_voice_releases_the_bank w,
   the_revoice_moves_no_seat g m v t⟩

theorem the_retuned_seat_walks_the_translated_word {I I' O : Type}
    (f : I' → I) (m : Machine I O) :
    ∀ (w : List I') (s : m.S), park (retune f m) s w = park m s (w.map f)
  | [], _ => rfl
  | i :: w, s => the_retuned_seat_walks_the_translated_word f m w
      (m.step s (f i))

theorem the_pulse_wears_a_deaf_ear :
    retune (fun _ : Bool => ()) paceOne = pulse := rfl

theorem the_deaf_ear_reads_only_the_count (w : List Bool) (s : Nat) :
    park pulse s w = s + w.length :=
  ((the_retuned_seat_walks_the_translated_word (fun _ : Bool => ())
      paceOne w s).trans
    (the_pace_parks_at_its_count (w.map (fun _ => ())) s)).trans
    (congrArg (s + ·) (len_map (fun _ : Bool => ()) w))

theorem the_ear_the_seat_and_the_voice {I I' O O' : Type} (f : I' → I)
    (g : O → O') (m : Machine I O) (w : List I') (v : List I)
    (s : m.S) (t : Nat) (u : List Bool) :
    park (retune f m) s w = park m s (w.map f)
      ∧ park (revoice g m) s v = park m s v
      ∧ revoice g (retune f m) = retune f (revoice g m)
      ∧ retune (fun _ : Bool => ()) paceOne = pulse
      ∧ park pulse t u = t + u.length :=
  ⟨the_retuned_seat_walks_the_translated_word f m w s,
   the_revoice_moves_no_seat g m v s,
   the_ear_and_the_voice_commute f g m,
   rfl,
   the_deaf_ear_reads_only_the_count u t⟩

theorem the_full_exchange_is_a_guest_move {W : Type} (σ : W → W → W)
    (d : door W W) :
    exchange still (exchange σ d) = vertical σ d := rfl

theorem the_ode_comes_home {W X : Type} (σ : W → W → W) (d : door W W)
    (g : W → X) :
    exchange still (exchange σ d) = vertical σ d
      ∧ g (face (exchange still (exchange σ d))) = g (face d)
      ∧ met (exchange still (exchange σ d)) = σ (face d) (met d)
      ∧ exchange still (exchange still d) = d :=
  ⟨rfl,
   a_guest_mover_is_unheard σ g d,
   rfl,
   the_two_listeners_restore_the_table d⟩

theorem one_clock_many_voices (a d b : Nat) (w : List Unit) (s : Nat) :
    revoice oddNat (tally Unit) = paceOne
      ∧ revoice (fun n => (⟨n, 10⟩ : Measured)) (tally Unit) = homingIn
      ∧ revoice (fun n => within ⟨n * a, n * a + d⟩ (n * b)) (tally Unit)
          = spiral a d b
      ∧ park paceOne s w = park (tally Unit) s w
      ∧ park homingIn s w = park (tally Unit) s w
      ∧ park (spiral a d b) s w = park (tally Unit) s w
      ∧ tighter (behavior homingIn w) ⟨0, 10⟩ = true
      ∧ park paceOne s w = s + w.length :=
  ⟨rfl, rfl, rfl,
   the_revoice_moves_no_seat oddNat (tally Unit) w s,
   the_revoice_moves_no_seat (fun n => (⟨n, 10⟩ : Measured))
     (tally Unit) w s,
   the_revoice_moves_no_seat
     (fun n => within ⟨n * a, n * a + d⟩ (n * b)) (tally Unit) w s,
   the_homing_reading_tightens w,
   the_pace_parks_at_its_count w s⟩

theorem the_deaf_turn_speaks_the_graph {W : Type} (f : W → W)
    (d : door W W) :
    exchange (fun x _ => f x) d = graphDoor f (face d) := rfl

theorem the_monologue_echoes_its_last_word {W : Type} (f : W → W)
    (d : door W W) :
    met (exchange (fun x _ => f x) d) = face d := rfl

theorem the_monologue_merges_at_the_first_turn {W : Type} (f : W → W)
    (fs : List (W → W)) (h w w' : W) :
    dialogue (atTheDoor h w) ((f :: fs).map (fun k x _ => k x))
      = dialogue (atTheDoor h w') ((f :: fs).map (fun k x _ => k x)) := rfl

theorem the_monologue_walks_the_face {W : Type} :
    ∀ (fs : List (W → W)) (d : door W W),
      face (dialogue d (fs.map (fun k x _ => k x)))
        = walk (fun x k => k x) (face d) fs
  | [], _ => rfl
  | f :: fs, d =>
      the_monologue_walks_the_face fs (exchange (fun x _ => f x) d)

theorem the_read_monologue_is_a_self_meeting {W X : Type} (f : W → W)
    (g : W → W → X) (d : door W W) :
    walkIn g (exchange still (exchange (fun x _ => f x) d))
      = g (face d) (f (face d)) := rfl

theorem the_monologue_is_its_own_audience {W X : Type} (f : W → W)
    (fs : List (W → W)) (h w w' : W) (d : door W W) (g : W → W → X) :
    exchange (fun x _ => f x) d = graphDoor f (face d)
      ∧ met (exchange (fun x _ => f x) d) = face d
      ∧ dialogue (atTheDoor h w) ((f :: fs).map (fun k x _ => k x))
          = dialogue (atTheDoor h w') ((f :: fs).map (fun k x _ => k x))
      ∧ face (dialogue d (fs.map (fun k x _ => k x)))
          = walk (fun x k => k x) (face d) fs
      ∧ walkIn g (exchange still (exchange (fun x _ => f x) d))
          = g (face d) (f (face d)) :=
  ⟨rfl, rfl, rfl, the_monologue_walks_the_face fs d, rfl⟩

def rehear (F : Face) {P' : Type} (f : P' → F.Probe) : Face :=
  ⟨F.State, P', F.Ans, fun s p => F.obs s (f p)⟩

def retell (F : Face) {A' : Type} (g : F.Ans → A') : Face :=
  ⟨F.State, F.Probe, A', fun s p => g (F.obs s p)⟩

theorem the_translated_ear_hears_no_more (F : Face) {P' : Type}
    (f : P' → F.Probe) (s t : F.State) (h : alike F s t) :
    alike (rehear F f) s t :=
  fun p => h (f p)

theorem the_sectioned_ear_loses_nothing (F : Face) {P' : Type}
    (f : P' → F.Probe) (h : F.Probe → P') (hs : ∀ p, f (h p) = p)
    (s t : F.State) (hal : alike (rehear F f) s t) :
    alike F s t :=
  fun p =>
    (congrArg (F.obs s) (hs p)).symm.trans
      ((hal (h p)).trans (congrArg (F.obs t) (hs p)))

theorem the_faithful_voice_keeps_the_curtain (F : Face) {A' : Type}
    (g : F.Ans → A') (s t : F.State) :
    (alike F s t → alike (retell F g) s t)
      ∧ ∀ r : A' → F.Ans, (∀ a, r (g a) = a) →
          alike (retell F g) s t → alike F s t :=
  ⟨fun h p => congrArg g (h p),
   fun r hr hal p =>
     (hr (F.obs s p)).symm.trans
       ((congrArg r (hal p)).trans (hr (F.obs t p)))⟩

def recast {P P' A : Type} (f : P' → P) : Interview P' A → Interview P A
  | .rest => .rest
  | .ask p k => .ask (f p) (fun a => recast f (k a))

def pullback {P A A' : Type} (g : A → A') : Interview P A' → Interview P A
  | .rest => .rest
  | .ask p k => .ask p (fun a => pullback g (k (g a)))

theorem the_interview_crosses_the_ear (F : Face) {P' : Type}
    (f : P' → F.Probe) (s : F.State) :
    ∀ q : Interview P' F.Ans,
      sound (rehear F f) s q = sound F s (recast f q)
  | .rest => rfl
  | .ask p k =>
      congrArg (F.obs s (f p) :: ·)
        (the_interview_crosses_the_ear F f s (k (F.obs s (f p))))

theorem the_interview_crosses_the_voice (F : Face) {A' : Type}
    (g : F.Ans → A') (s : F.State) :
    ∀ q : Interview F.Probe A',
      sound (retell F g) s q = (sound F s (pullback g q)).map g
  | .rest => rfl
  | .ask p k =>
      congrArg (g (F.obs s p) :: ·)
        (the_interview_crosses_the_voice F g s (k (g (F.obs s p))))

theorem the_ears_stack_backward (F : Face) {P' P'' : Type}
    (f : P' → F.Probe) (f' : P'' → P') :
    rehear (rehear F f) f' = rehear F (fun p => f (f' p)) := rfl

theorem the_voices_stack_forward (F : Face) {A' A'' : Type}
    (g : F.Ans → A') (g' : A' → A'') :
    retell (retell F g) g' = retell F (fun a => g' (g a)) := rfl

theorem the_machines_ear_is_the_faces_ear {I I' O : Type} (f : I' → I)
    (m : Machine I O) (w : List I') :
    (airGap I' O).obs (retune f m) w
      = (rehear (airGap I O) (fun u : List I' => u.map f)).obs m w :=
  hearing_through_a_translator f m w m.s0

theorem the_machines_voice_is_the_faces_voice {I O O' : Type} (g : O → O')
    (m : Machine I O) (v : List I) :
    (airGap I O').obs (revoice g m) v
      = (retell (airGap I O) g).obs m v :=
  speaking_through_a_translator g m v m.s0

theorem every_face_wears_an_ear_and_a_voice (F : Face) {P' A' : Type}
    (f : P' → F.Probe) (g : F.Ans → A') (s t : F.State)
    (h : alike F s t) (q : Interview P' F.Ans)
    (q' : Interview F.Probe A')
    {I I' O O' : Type} (f0 : I' → I) (g0 : O → O')
    (m : Machine I O) (w : List I') (v : List I) :
    alike (rehear F f) s t
      ∧ alike (retell F g) s t
      ∧ sound (rehear F f) s q = sound F s (recast f q)
      ∧ sound (retell F g) s q' = (sound F s (pullback g q')).map g
      ∧ (airGap I' O).obs (retune f0 m) w
          = (rehear (airGap I O) (fun u : List I' => u.map f0)).obs m w
      ∧ (airGap I O').obs (revoice g0 m) v
          = (retell (airGap I O) g0).obs m v
      ∧ retell (rehear F f) g = rehear (retell F g) f :=
  ⟨the_translated_ear_hears_no_more F f s t h,
   (the_faithful_voice_keeps_the_curtain F g s t).1 h,
   the_interview_crosses_the_ear F f s q,
   the_interview_crosses_the_voice F g s q',
   the_machines_ear_is_the_faces_ear f0 m w,
   the_machines_voice_is_the_faces_voice g0 m v,
   rfl⟩

def unheard (F : Face) (m : F.State → F.State) : Prop :=
  ∀ s, alike F (m s) s

theorem the_still_hand_is_unheard (F : Face) :
    unheard F (fun s => s) :=
  fun _ _ => rfl

theorem the_unheard_hands_compose (F : Face) (m n : F.State → F.State)
    (hm : unheard F m) (hn : unheard F n) :
    unheard F (fun s => m (n s)) :=
  fun s p => (hm (n s) p).trans (hn s p)

theorem no_interview_hears_the_unheard (F : Face) (m : F.State → F.State)
    (hm : unheard F m) (s : F.State) (q : Interview F.Probe F.Ans) :
    sound F (m s) q = sound F s q :=
  no_interview_parts_the_alike F (m s) s (hm s) q

theorem correct_maintenance_has_no_signature (F : Face)
    (m m' : F.State → F.State) (hm : unheard F m) (hm' : unheard F m')
    (s : F.State) (q : Interview F.Probe F.Ans) :
    sound F (m s) q = sound F (m' s) q :=
  (no_interview_hears_the_unheard F m hm s q).trans
    (no_interview_hears_the_unheard F m' hm' s q).symm

theorem a_chain_of_the_unheard_is_unheard (F : Face) :
    ∀ ms : List (F.State → F.State),
      (∀ m, m ∈ ms → unheard F m) →
      unheard F (fun s => walk (fun t k => k t) s ms)
  | [], _ => fun _ _ => rfl
  | m :: ms, h => fun s p =>
      (a_chain_of_the_unheard_is_unheard F ms
          (fun k hk => h k (List.Mem.tail m hk)) (m s) p).trans
        (h m (List.Mem.head ms) s p)

theorem only_the_unheard_survives_the_sounding (F : Face)
    (m : F.State → F.State) :
    (∀ (s : F.State) (q : Interview F.Probe F.Ans),
        sound F (m s) q = sound F s q)
      ↔ unheard F m :=
  ⟨fun h s => the_sounding_reads_the_alike F (m s) s (h s),
   fun hm s q => no_interview_parts_the_alike F (m s) s (hm s) q⟩

def seatFace {I O : Type} (m : Machine I O) : Face :=
  ⟨m.S, List I, O, drive m⟩

theorem the_guest_mover_is_a_still_hand {H W X : Type} (σ : H → W → W) :
    unheard (doorFace H W X) (vertical σ) :=
  fun _ _ => rfl

theorem the_guest_write_is_a_still_hand (F : Face) {W : Type}
    (g : F.State × W → W) :
    unheard (host F W) (fun x => (x.1, g x)) :=
  fun x p => (the_reading_writes_unheard F g x.1 x.2 p).symm

theorem the_settle_is_a_still_hand {I O : Type} (m : Machine I O) :
    unheard (seatFace (buffered m)) (settleHeld m) :=
  fun st w => the_settle_is_unheard m st w

theorem the_yield_is_no_still_hand :
    ¬ unheard (doorFace Nat Nat Nat) turnAbout :=
  fun h => nomatch h (atTheDoor (0 : Nat) (1 : Nat)) (fun n => n)

theorem the_unheard_keep_the_house (F : Face) (m m' : F.State → F.State)
    (hm : unheard F m) (hm' : unheard F m') (s : F.State)
    (q : Interview F.Probe F.Ans) (ms : List (F.State → F.State))
    (hms : ∀ k, k ∈ ms → unheard F k) {H W X : Type} (σ : H → W → W)
    {I O : Type} (mach : Machine I O) :
    unheard F (fun t => t)
      ∧ unheard F (fun t => m (m' t))
      ∧ sound F (m s) q = sound F s q
      ∧ sound F (m s) q = sound F (m' s) q
      ∧ unheard F (fun t => walk (fun u k => k u) t ms)
      ∧ ((∀ (t : F.State) (q' : Interview F.Probe F.Ans),
            sound F (m t) q' = sound F t q')
          ↔ unheard F m)
      ∧ unheard (doorFace H W X) (vertical σ)
      ∧ unheard (seatFace (buffered mach)) (settleHeld mach)
      ∧ ¬ unheard (doorFace Nat Nat Nat) turnAbout :=
  ⟨the_still_hand_is_unheard F,
   the_unheard_hands_compose F m m' hm hm',
   no_interview_hears_the_unheard F m hm s q,
   correct_maintenance_has_no_signature F m m' hm hm' s q,
   a_chain_of_the_unheard_is_unheard F ms hms,
   only_the_unheard_survives_the_sounding F m,
   the_guest_mover_is_a_still_hand σ,
   the_settle_is_a_still_hand mach,
   the_yield_is_no_still_hand⟩

def duet {I O O' : Type} (m : Machine I O) (n : Machine I O') :
    Machine I (O × O') :=
  ⟨m.S × n.S, (m.s0, n.s0), fun s i => (m.step s.1 i, n.step s.2 i),
   fun s => (m.out s.1, n.out s.2)⟩

theorem the_duet_walks_in_step {I O O' : Type} (m : Machine I O)
    (n : Machine I O') :
    ∀ (w : List I) (s : m.S) (t : n.S),
      drive (duet m n) (s, t) w = (drive m s w, drive n t w)
  | [], _, _ => rfl
  | i :: w, s, t => the_duet_walks_in_step m n w (m.step s i) (n.step t i)

theorem the_duet_parks_in_step {I O O' : Type} (m : Machine I O)
    (n : Machine I O') :
    ∀ (w : List I) (s : m.S) (t : n.S),
      park (duet m n) (s, t) w = (park m s w, park n t w)
  | [], _, _ => rfl
  | i :: w, s, t => the_duet_parks_in_step m n w (m.step s i) (n.step t i)

theorem the_duet_sounds_both {I O O' : Type} (m : Machine I O)
    (n : Machine I O') (w : List I) :
    behavior (duet m n) w = (behavior m w, behavior n w) :=
  the_duet_walks_in_step m n w m.s0 n.s0

theorem the_duet_reads_at_the_mirror_probe {I O O' : Type}
    (m : Machine I O) (n : Machine I O') (s : m.S) (t : n.S)
    (w : List I) :
    (seatFace (duet m n)).obs (s, t) w
      = (pairFace (seatFace m) (seatFace n) Prod.fst Prod.snd).obs
          (s, t) (w, w) :=
  the_duet_walks_in_step m n w s t

theorem the_shell_is_the_duets_silent_partner {O : Type}
    (m : Machine Unit O) (w : List Unit) :
    behavior (duet m hollowShell) w = (behavior m w, true) :=
  (the_duet_sounds_both m hollowShell w).trans
    (congrArg (fun b => (behavior m w, b)) (the_shell_sounds_still w))

theorem the_shell_signs_no_parting {O : Type} (m : Machine Unit O)
    (w v : List Unit) :
    behavior (duet hollowShell m) w = behavior (duet hollowShell m) v
      ↔ behavior m w = behavior m v :=
  ⟨fun h =>
     congrArg Prod.snd
       (((the_duet_sounds_both hollowShell m w).symm.trans h).trans
         (the_duet_sounds_both hollowShell m v)),
   fun h =>
     (the_duet_sounds_both hollowShell m w).trans
       ((congr
           (congrArg Prod.mk
             ((the_shell_sounds_still w).trans
               (the_shell_sounds_still v).symm))
           h).trans
         (the_duet_sounds_both hollowShell m v).symm)⟩

theorem two_voices_of_one_clock_share_one_seat {P Q : Type}
    (g : Nat → P) (g' : Nat → Q) (u : List Unit) :
    behavior (duet (revoice g (tally Unit)) (revoice g' (tally Unit))) u
      = behavior (revoice (fun k => (g k, g' k)) (tally Unit)) u :=
  (the_duet_sounds_both (revoice g (tally Unit))
      (revoice g' (tally Unit)) u).trans
    ((congr
        (congrArg Prod.mk
          (speaking_through_a_translator g (tally Unit) u (0 : Nat)))
        (speaking_through_a_translator g' (tally Unit) u (0 : Nat))).trans
      (speaking_through_a_translator (fun k => (g k, g' k))
        (tally Unit) u (0 : Nat)).symm)

theorem the_duet_hears_one_word {I O O' O'' : Type} (m : Machine I O)
    (n : Machine I O') (w : List I) (s : m.S) (t : n.S)
    (mach : Machine Unit O'') (v v' : List Unit)
    {P Q : Type} (g : Nat → P) (g' : Nat → Q) (u : List Unit) :
    drive (duet m n) (s, t) w = (drive m s w, drive n t w)
      ∧ park (duet m n) (s, t) w = (park m s w, park n t w)
      ∧ behavior (duet m n) w = (behavior m w, behavior n w)
      ∧ (seatFace (duet m n)).obs (s, t) w
          = (pairFace (seatFace m) (seatFace n) Prod.fst Prod.snd).obs
              (s, t) (w, w)
      ∧ behavior (duet mach hollowShell) v = (behavior mach v, true)
      ∧ (behavior (duet hollowShell mach) v
            = behavior (duet hollowShell mach) v'
          ↔ behavior mach v = behavior mach v')
      ∧ behavior (duet (revoice g (tally Unit)) (revoice g' (tally Unit))) u
          = behavior (revoice (fun k => (g k, g' k)) (tally Unit)) u :=
  ⟨the_duet_walks_in_step m n w s t,
   the_duet_parks_in_step m n w s t,
   the_duet_sounds_both m n w,
   the_duet_reads_at_the_mirror_probe m n s t w,
   the_shell_is_the_duets_silent_partner mach v,
   the_shell_signs_no_parting mach v v',
   two_voices_of_one_clock_share_one_seat g g' u⟩

def scribe {B W : Type} (next : List B → W → B) : Machine W (List B) :=
  ⟨List B, [], fun out w => next out w :: out, fun out => out⟩

theorem snoc_append {A : Type} (x : A) :
    ∀ (a b : List A), (a ++ [x]) ++ b = a ++ (x :: b)
  | [], _ => rfl
  | y :: a, b => congrArg (y :: ·) (snoc_append x a b)

theorem the_scribes_record_only_grows {B W : Type}
    (next : List B → W → B) :
    ∀ (ws : List W) (out : List B),
      ∃ new : List B, park (scribe next) out ws = new ++ out
  | [], _ => ⟨[], rfl⟩
  | w :: ws, out =>
      match the_scribes_record_only_grows next ws (next out w :: out) with
      | ⟨new, h⟩ =>
          ⟨new ++ [next out w],
           h.trans (snoc_append (next out w) new out).symm⟩

theorem one_wind_one_mark {B W : Type} (next : List B → W → B) :
    ∀ (ws : List W) (out : List B),
      (park (scribe next) out ws).length = out.length + ws.length
  | [], _ => rfl
  | w :: ws, out =>
      (one_wind_one_mark next ws (next out w :: out)).trans
        (succ_adds out.length ws.length)

theorem the_scribe_resumes {B W : Type} (next : List B → W → B)
    (xs ys : List W) (out : List B) :
    park (scribe next) out (xs ++ ys)
      = park (scribe next) (park (scribe next) out xs) ys :=
  the_park_resumes (scribe next) xs ys out

theorem the_scribe_wears_the_tally {B W : Type} (next : List B → W → B)
    (ws : List W) (out : List B) :
    (park (scribe next) out ws).length = drive (tally W) out.length ws :=
  (one_wind_one_mark next ws out).trans (drive_counts ws out.length).symm

def utterance {B C W : Type} (sample : C → W → B) (select : List B → C)
    (out : List B) (w : W) : B :=
  walkIn sample (atTheDoor (select out) w)

theorem the_utterance_is_a_door {B C W : Type} (sample : C → W → B)
    (select : List B → C) (out : List B) (w : W) :
    utterance sample select out w = sample (select out) w := rfl

theorem the_selection_reads_no_wind {B C W X : Type}
    (select : List B → C) (g : C → X) (out : List B) (w w' : W) :
    g (face (atTheDoor (select out) w))
      = g (face (atTheDoor (select out) w')) := rfl

theorem the_selection_reads_only_the_record {B C W : Type}
    (sample : C → W → B) (select select' : List B → C) (out : List B)
    (w : W) (h : select out = select' out) :
    utterance sample select out w = utterance sample select' out w :=
  congrArg (fun c => sample c w) h

theorem the_wind_rides_the_utterance {B C W : Type}
    (select : List B → C) (out : List B) {w w' : W} (hw : w ≠ w') :
    atTheDoor (select out) w ≠ atTheDoor (select out) w' :=
  the_guest_is_real (select out) hw

theorem generation_originates_nothing {B C W X : Type}
    (next : List B → W → B) (sample : C → W → B)
    (select select' : List B → C) (ws xs ys : List W) (out : List B)
    (w : W) {w' : W} (hw : w ≠ w') (g : C → X)
    (h : select out = select' out) :
    (∃ new : List B, park (scribe next) out ws = new ++ out)
      ∧ (park (scribe next) out ws).length = out.length + ws.length
      ∧ park (scribe next) out (xs ++ ys)
          = park (scribe next) (park (scribe next) out xs) ys
      ∧ (park (scribe next) out ws).length = drive (tally W) out.length ws
      ∧ utterance sample select out w = sample (select out) w
      ∧ g (face (atTheDoor (select out) w))
          = g (face (atTheDoor (select out) w'))
      ∧ atTheDoor (select out) w ≠ atTheDoor (select out) w'
      ∧ utterance sample select out w = utterance sample select' out w :=
  ⟨the_scribes_record_only_grows next ws out,
   one_wind_one_mark next ws out,
   the_scribe_resumes next xs ys out,
   the_scribe_wears_the_tally next ws out,
   rfl,
   rfl,
   the_wind_rides_the_utterance select out hw,
   the_selection_reads_only_the_record sample select select' out w h⟩

theorem the_commuting_seat_shrugs_the_shuffle {I O : Type}
    (m : Machine I O)
    (hcomm : ∀ s i j, m.step (m.step s i) j = m.step (m.step s j) i)
    (xs : List I) (i j : I) (ys : List I) (s : m.S) :
    park m s (xs ++ i :: j :: ys) = park m s (xs ++ j :: i :: ys) :=
  (the_park_resumes m xs (i :: j :: ys) s).trans
    ((congrArg (fun t => park m t ys)
        (hcomm (park m s xs) i j)).trans
      (the_park_resumes m xs (j :: i :: ys) s).symm)

def heap : Machine Nat Nat := ⟨Nat, 0, fun s i => s + i, fun s => s⟩

theorem the_heap_steps_commute (s i j : Nat) :
    heap.step (heap.step s i) j = heap.step (heap.step s j) i := by
  show (s + i) + j = (s + j) + i
  rw [Nat.add_assoc, Nat.add_comm i j, ← Nat.add_assoc]

theorem the_heap_shrugs_the_shuffle (xs : List Nat) (i j : Nat)
    (ys : List Nat) (s : Nat) :
    park heap s (xs ++ i :: j :: ys) = park heap s (xs ++ j :: i :: ys) :=
  the_commuting_seat_shrugs_the_shuffle heap the_heap_steps_commute
    xs i j ys s

theorem the_heap_hears_the_guest (u v : Nat) (huv : u ≠ v) :
    behavior heap [u] ≠ behavior heap [v] :=
  fun h => huv ((zero_plus u).symm.trans (h.trans (zero_plus v)))

theorem the_scribe_keeps_the_order {A : Type} {a b : A} (hab : a ≠ b) :
    park (scribe (fun _ w => w)) ([] : List A) [a, b]
      ≠ park (scribe (fun _ w => w)) ([] : List A) [b, a] :=
  fun h => hab ((List.cons.inj h).1).symm

theorem a_seat_reads_the_order_the_census_cannot {I O A : Type}
    (m : Machine I O)
    (hcomm : ∀ s i j, m.step (m.step s i) j = m.step (m.step s j) i)
    (xs : List I) (i j : I) (ys : List I) (s : m.S)
    (bs cs : List Bool) (x y : Bool) (t : Nat)
    (u v : Nat) (huv : u ≠ v) {a b : A} (hab : a ≠ b) :
    park m s (xs ++ i :: j :: ys) = park m s (xs ++ j :: i :: ys)
      ∧ park pulse t (bs ++ x :: y :: cs) = park pulse t (bs ++ y :: x :: cs)
      ∧ park heap (0 : Nat) [u, v] = park heap (0 : Nat) [v, u]
      ∧ behavior heap [u] ≠ behavior heap [v]
      ∧ park (scribe (fun _ w => w)) ([] : List A) [a, b]
          ≠ park (scribe (fun _ w => w)) ([] : List A) [b, a] :=
  ⟨the_commuting_seat_shrugs_the_shuffle m hcomm xs i j ys s,
   the_commuting_seat_shrugs_the_shuffle pulse (fun _ _ _ => rfl)
     bs x y cs t,
   the_heap_shrugs_the_shuffle [] u v [] (0 : Nat),
   the_heap_hears_the_guest u v huv,
   the_scribe_keeps_the_order hab⟩

def search (F : Face) (s : F.State) (ps : List F.Probe) : List F.Ans :=
  sound F s (recite ps)

def research (F : Face) {X : Type} (r : F.State → X) (s : F.State)
    (ps : List F.Probe) : List (fork F.Ans X) :=
  sound (sharpen F r) s (recite (ps.map viaLeft))

theorem the_research_wears_the_old_ear (F : Face) {X : Type}
    (r : F.State → X) :
    rehear (sharpen F r) (viaLeft : F.Probe → fork F.Probe Unit)
      = retell F (viaLeft : F.Ans → fork F.Ans X) := rfl

theorem the_research_resounds_the_search (F : Face) {X : Type}
    (r : F.State → X) (s : F.State) :
    ∀ ps : List F.Probe,
      research F r s ps = (search F s ps).map viaLeft
  | [] => rfl
  | p :: ps =>
      congrArg (viaLeft (F.obs s p) :: ·)
        (the_research_resounds_the_search F r s ps)

theorem only_the_minted_ask_hears_the_mint (F : Face) {X : Type}
    (r : F.State → X) (s : F.State) :
    sound (sharpen F r) s (recite [viaRight ()]) = [viaRight (r s)] := rfl

theorem the_research_finds_only_the_mint (F : Face) {X : Type}
    (r : F.State → X) (s : F.State) (ps : List F.Probe) (m : Measured) :
    research F r s ps = (search F s ps).map viaLeft
      ∧ sound (sharpen F r) s (recite [viaRight ()]) = [viaRight (r s)]
      ∧ rehear (sharpen F r) (viaLeft : F.Probe → fork F.Probe Unit)
          = retell F (viaLeft : F.Ans → fork F.Ans X)
      ∧ (sharpen windowFace (fun w => w.hi + 1)).obs m (viaRight ())
          = viaRight (m.hi + 1)
      ∧ within m (m.hi + 1) = false :=
  ⟨the_research_resounds_the_search F r s ps,
   rfl,
   rfl,
   (the_sharpened_window_exhibits_the_escapee m).1,
   (the_sharpened_window_exhibits_the_escapee m).2⟩

theorem append_nil {A : Type} : ∀ l : List A, l ++ [] = l
  | [] => rfl
  | a :: l => congrArg (a :: ·) (append_nil l)

def ledger (I : Type) : Machine I (List I) :=
  ⟨List I, [], fun out i => out ++ [i], fun out => out⟩

theorem the_ledger_parks_the_word {I : Type} :
    ∀ (ws out : List I), park (ledger I) out ws = out ++ ws
  | [], out => (append_nil out).symm
  | w :: ws, out =>
      (the_ledger_parks_the_word ws (out ++ [w])).trans
        (snoc_append w out ws)

def replayer {I O : Type} (m : Machine I O) : Machine I O :=
  ⟨List I, [], fun rec i => rec ++ [i],
   fun rec => m.out (park m m.s0 rec)⟩

theorem the_replayer_walks_in_step {I O : Type} (m : Machine I O) :
    ∀ (w : List I) (rec : List I) (s : m.S), park m m.s0 rec = s →
      drive (replayer m) rec w = drive m s w :=
  two_machines_in_step_agree (replayer m) m
    (fun rec s => park m m.s0 rec = s)
    (fun rec _ i h =>
      (the_park_resumes m rec [i] m.s0).trans
        (congrArg (fun t => m.step t i) h))
    (fun _ _ h => congrArg m.out h)

theorem the_replay_is_the_machine {I O : Type} (m : Machine I O)
    (w : List I) :
    behavior (replayer m) w = behavior m w :=
  the_replayer_walks_in_step m w [] m.s0 rfl

theorem every_seat_is_a_reading_of_the_record {I O : Type}
    (m : Machine I O) (out ws : List I) :
    park m m.s0 (park (ledger I) out ws) = park m (park m m.s0 out) ws :=
  (congrArg (park m m.s0) (the_ledger_parks_the_word ws out)).trans
    (the_park_resumes m out ws m.s0)

theorem the_audition_cannot_tell_the_seat_from_its_record {I O : Type}
    (m : Machine I O) (w : List I) (q : Interview (List I) O)
    (out ws : List I) :
    behavior (replayer m) w = behavior m w
      ∧ audition (replayer m) q = audition m q
      ∧ park m m.s0 (park (ledger I) out ws)
          = park m (park m m.s0 out) ws
      ∧ park (ledger Bool) ([] : List Bool) [true, false]
          ≠ park (ledger Bool) ([] : List Bool) [false, true]
      ∧ park pulse (0 : Nat) [true, false]
          = park pulse (0 : Nat) [false, true] :=
  ⟨the_replay_is_the_machine m w,
   an_audition_hears_only_the_conduct (replayer m) m
     (fun v => the_replay_is_the_machine m v) q,
   every_seat_is_a_reading_of_the_record m out ws,
   (fun h =>
     nomatch (List.cons.inj
       (show [true, false] = ([false, true] : List Bool) from h)).1),
   two_routes_one_seat.2⟩

theorem the_record_never_unwrites {A : Type} :
    ∀ (h a : List A), h ++ a = h → a = []
  | [], _, e => e
  | _ :: t, a, e => the_record_never_unwrites t a (List.cons.inj e).2

theorem the_holonomy_is_the_word {I O : Type} (m : Machine I O) (s : m.S)
    (w : List I) (hloop : park m s w = s) (out : List I) (hw : w ≠ [])
    (b : Bool) :
    (park m s w = s
        ∧ park (ledger I) out w = out ++ w
        ∧ park (ledger I) out w ≠ out)
      ∧ park flip b [(), ()] = b
      ∧ park (ledger Unit) ([] : List Unit) [(), ()] = [(), ()] :=
  ⟨⟨hloop,
    the_ledger_parks_the_word w out,
    fun h =>
      hw (the_record_never_unwrites out w
        ((the_ledger_parks_the_word w out).symm.trans h))⟩,
   the_flip_wheels b,
   the_ledger_parks_the_word [(), ()] []⟩

def storeys (S : Type u) (W : Type) : Nat → Type u
  | 0 => S
  | n + 1 => storeys S W n × W

def cellar {S : Type u} {W : Type} : (n : Nat) → storeys S W n → S
  | 0, s => s
  | n + 1, s => cellar n s.1

def towerFace (F : Face) (W : Type) (n : Nat) : Face :=
  ⟨storeys F.State W n, F.Probe, F.Ans, fun s p => F.obs (cellar n s) p⟩

theorem the_ground_floor_is_the_face (F : Face) (W : Type) :
    towerFace F W 0 = F := rfl

theorem the_tower_climbs_by_hosting (F : Face) (W : Type) (n : Nat) :
    towerFace F W (n + 1) = host (towerFace F W n) W := rfl

theorem every_floor_reads_the_cellar (F : Face) (W : Type) (n : Nat)
    (s : storeys F.State W n) (p : F.Probe) :
    (towerFace F W n).obs s p = F.obs (cellar n s) p := rfl

theorem the_tower_reads_only_the_ground (F : Face) (W : Type) (n : Nat)
    (x y : storeys F.State W n) (h : cellar n x = cellar n y) :
    alike (towerFace F W n) x y :=
  fun p => congrArg (F.obs · p) h

theorem every_floor_merges_its_guests (F : Face) (W : Type) (n : Nat)
    (s : storeys F.State W n) (w w' : W) :
    alike (towerFace F W (n + 1)) (s, w) (s, w') :=
  fun _ => rfl

theorem the_maintenance_climbs_the_tower (F : Face) (W : Type) (n : Nat)
    (g : storeys F.State W n × W → W) :
    unheard (towerFace F W (n + 1)) (fun x => (x.1, g x)) :=
  the_guest_write_is_a_still_hand (towerFace F W n) g

theorem no_seat_is_the_last_seat (F : Face) (W : Type) (n : Nat)
    (s : storeys F.State W n) {w w' : W} (hw : w ≠ w')
    (q : Interview F.Probe F.Ans) :
    towerFace F W (n + 1) = host (towerFace F W n) W
      ∧ alike (towerFace F W (n + 1)) (s, w) (s, w')
      ∧ sound (towerFace F W (n + 1)) (s, w) q
          = sound (towerFace F W (n + 1)) (s, w') q
      ∧ ((s, w) : storeys F.State W (n + 1)) ≠ (s, w')
      ∧ (widen (towerFace F W n) W).obs (s, w) (viaRight ())
          ≠ (widen (towerFace F W n) W).obs (s, w') (viaRight ()) :=
  ⟨rfl,
   every_floor_merges_its_guests F W n s w w',
   no_interview_parts_the_alike (towerFace F W (n + 1)) (s, w) (s, w')
     (every_floor_merges_its_guests F W n s w w') q,
   (fun he => hw (congrArg Prod.snd he)),
   (fun he => hw (Sum.inr.inj he))⟩

def again {α : Sort u} (Φ : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => Φ (again Φ n a)

theorem the_again_resumes {α : Sort u} (Φ : α → α) :
    ∀ (m n : Nat) (a : α), again Φ (n + m) a = again Φ m (again Φ n a)
  | 0, _, _ => rfl
  | m + 1, n, a => congrArg Φ (the_again_resumes Φ m n a)

theorem the_again_steps_first {α : Sort u} (Φ : α → α) :
    ∀ (n : Nat) (a : α), again Φ n (Φ a) = Φ (again Φ n a)
  | 0, _ => rfl
  | n + 1, a => congrArg Φ (the_again_steps_first Φ n a)

theorem the_tower_is_the_hosts_again (F : Face) (W : Type) :
    ∀ n : Nat, again (fun G => host G W) n F = towerFace F W n
  | 0 => rfl
  | n + 1 =>
      congrArg (fun G => host G W) (the_tower_is_the_hosts_again F W n)

theorem the_bloom_is_the_mirrors_again :
    ∀ n : Nat, again (fun p => Plan.board p p) n .ground = bloom n
  | 0 => rfl
  | n + 1 =>
      congrArg (fun p => Plan.board p p) (the_bloom_is_the_mirrors_again n)

theorem the_orbit_is_the_steps_again {I O : Type} (m : Machine I O)
    (r : m.S → I) :
    ∀ (n : Nat) (s : m.S),
      orbit m r s n = again (fun t => m.step t (r t)) n s
  | 0, _ => rfl
  | n + 1, s =>
      (the_orbit_is_the_steps_again m r n (m.step s (r s))).trans
        (the_again_steps_first (fun t => m.step t (r t)) n s)

theorem the_storeys_add (F : Face) (W : Type) (m n : Nat) :
    towerFace F W (n + m) = towerFace (towerFace F W n) W m :=
  (the_tower_is_the_hosts_again F W (n + m)).symm.trans
    ((the_again_resumes (fun G => host G W) m n F).trans
      ((congrArg (again (fun G => host G W) m)
          (the_tower_is_the_hosts_again F W n)).trans
        (the_tower_is_the_hosts_again (towerFace F W n) W m)))

theorem one_again_three_orbits (F : Face) (W : Type) (m n : Nat)
    {I O : Type} (mach : Machine I O) (r : mach.S → I) (s : mach.S)
    (i j : Nat) :
    again (fun G => host G W) n F = towerFace F W n
      ∧ again (fun p => Plan.board p p) n .ground = bloom n
      ∧ orbit mach r s n = again (fun t => mach.step t (r t)) n s
      ∧ towerFace F W (n + m) = towerFace (towerFace F W n) W m
      ∧ graft (bloom i) (bloom j) = bloom (i + j) :=
  ⟨the_tower_is_the_hosts_again F W n,
   the_bloom_is_the_mirrors_again n,
   the_orbit_is_the_steps_again mach r n s,
   the_storeys_add F W m n,
   the_blooms_add i j⟩

def unsign {H A : Type} (d : door H A) : door H Unit :=
  atTheDoor (face d) ()

theorem the_unsigning_is_the_unit_guest {H A : Type} (h : H) (a : A)
    (u : door H Unit) :
    unsign (atTheDoor h a) = atTheDoor h () ∧ unsign u = u :=
  ⟨rfl, rfl⟩

theorem the_unsigned_work_reads_the_same {H A X : Type} (g : H → X)
    (d : door H A) : g (face (unsign d)) = g (face d) := rfl

theorem an_author_blind_reading_is_an_unsigned_reading {H A X : Type}
    (a₀ : A) (f : door H A → X) :
    (∀ (h : H) (a a' : A), f (atTheDoor h a) = f (atTheDoor h a'))
      ↔ ∃ g : door H Unit → X, ∀ d, f d = g (unsign d) :=
  ⟨fun hb => ⟨fun u => f (atTheDoor (face u) a₀),
     fun d => hb (face d) (met d) a₀⟩,
   fun he h a a' =>
     he.elim fun _ hg =>
       (hg (atTheDoor h a)).trans (hg (atTheDoor h a')).symm⟩

theorem the_quiet_author_leaves_the_table_as_found {W : Type} (d : door W W) :
    ∀ n : Nat, dialogue d (List.replicate (2 * n) still) = d
  | 0 => rfl
  | n + 1 =>
      show dialogue (exchange still (exchange still d))
          (List.replicate (2 * n) still) = d from
        the_quiet_author_leaves_the_table_as_found d n

theorem the_author_was_the_guest {H A X : Type} (a₀ : A) (g : H → X)
    (d : door H A) (h : H) {a a' : A} (ha : a ≠ a')
    (f : door H A → X) (F : Face) (s : F.State)
    {W : Type} (e : door W W) (n : Nat) :
    g (face (unsign d)) = g (face d)
      ∧ ((∀ (h' : H) (x x' : A), f (atTheDoor h' x) = f (atTheDoor h' x'))
          ↔ ∃ g' : door H Unit → X, ∀ d', f d' = g' (unsign d'))
      ∧ (atTheDoor h a ≠ atTheDoor h a'
          ∧ ∀ (Y : Type) (r : H → Y),
              r (face (atTheDoor h a)) = r (face (atTheDoor h a')))
      ∧ ¬ Derived (host F A) (fun x => x.2 = a)
      ∧ (∀ (P : Prop) (p1 p2 : P), p1 = p2)
      ∧ (widen F A).obs (s, a) (viaRight ())
          ≠ (widen F A).obs (s, a') (viaRight ())
      ∧ dialogue e (List.replicate (2 * n) still) = e :=
  ⟨rfl,
   an_author_blind_reading_is_an_unsigned_reading a₀ f,
   ⟨the_guest_is_real h ha, fun _ _ => rfl⟩,
   the_guest_is_never_a_derived_role F s ha,
   fun _ p1 p2 => the_route_leaves_no_mark p1 p2,
   (fun he => ha (Sum.inr.inj he)),
   the_quiet_author_leaves_the_table_as_found e n⟩

def enrolled (room : List Nat) (x : Nat) : Bool := room.any (Nat.beq x)

def backed (room need : List Nat) : Bool := need.all (enrolled room)

def welcome (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat) :
    List Nat × List (Nat × List Nat) :=
  cond (backed s.1 m.2) (m.1 :: s.1, s.2) (s.1, m :: s.2)

theorem the_backed_are_seated {s : List Nat × List (Nat × List Nat)}
    {m : Nat × List Nat} (h : backed s.1 m.2 = true) :
    welcome s m = (m.1 :: s.1, s.2) := by
  unfold welcome; rw [h]; rfl

theorem the_unbacked_are_held {s : List Nat × List (Nat × List Nat)}
    {m : Nat × List Nat} (h : backed s.1 m.2 = false) :
    welcome s m = (s.1, m :: s.2) := by
  unfold welcome; rw [h]; rfl

theorem or_lights_right : ∀ b : Bool, (b || true) = true
  | true => rfl
  | false => rfl

theorem the_seat_is_load_bearing_in_the_same_click
    (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat)
    (h : backed s.1 m.2 = true) :
    enrolled (welcome s m).1 m.1 = true := by
  rw [the_backed_are_seated h]
  show (Nat.beq m.1 m.1 || s.1.any (Nat.beq m.1)) = true
  rw [beq_self]
  rfl

theorem the_enrolled_stay_enrolled (r : List Nat) (y x : Nat)
    (h : enrolled r x = true) : enrolled (y :: r) x = true := by
  show (Nat.beq x y || enrolled r x) = true
  rw [h]
  exact or_lights_right (Nat.beq x y)

theorem the_backing_never_lapses (r : List Nat) (y : Nat) :
    ∀ need : List Nat, backed r need = true → backed (y :: r) need = true
  | [], _ => rfl
  | x :: need, h => by
      obtain ⟨h1, h2⟩ :=
        and_split (show (enrolled r x && backed r need) = true from h)
      show (enrolled (y :: r) x && backed (y :: r) need) = true
      exact and_glue (the_enrolled_stay_enrolled r y x h1)
        (the_backing_never_lapses r y need h2)

theorem the_backing_survives_the_door
    (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat)
    (need : List Nat) (h : backed s.1 need = true) :
    backed (welcome s m).1 need = true := by
  cases hb : backed s.1 m.2 with
  | true =>
      rw [the_backed_are_seated hb]
      exact the_backing_never_lapses s.1 m.1 need h
  | false =>
      rw [the_unbacked_are_held hb]
      exact h

theorem the_hall_hears_no_join_order (a b x : Nat) :
    enrolled [a, b] x = enrolled [b, a] x := by
  show (Nat.beq x a || (Nat.beq x b || false))
      = (Nat.beq x b || (Nat.beq x a || false))
  cases Nat.beq x a <;> cases Nat.beq x b <;> rfl

theorem the_room_reads_no_waiting (r : List Nat)
    (v v' : List (Nat × List Nat)) (m : Nat × List Nat)
    (h : backed r m.2 = true) :
    (welcome (r, v) m).1 = (welcome (r, v') m).1 := by
  rw [the_backed_are_seated (s := (r, v)) h,
      the_backed_are_seated (s := (r, v')) h]

theorem the_guest_becomes_the_ground
    (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat)
    (h : backed s.1 m.2 = true) (need : List Nat)
    (hn : backed s.1 need = true) (a b x : Nat) (hab : a ≠ b)
    (r : List Nat) (v v' : List (Nat × List Nat))
    (hr : backed r m.2 = true) :
    enrolled (welcome s m).1 m.1 = true
      ∧ backed (welcome s m).1 need = true
      ∧ enrolled [a, b] x = enrolled [b, a] x
      ∧ ([a, b] : List Nat) ≠ [b, a]
      ∧ (welcome (r, v) m).1 = (welcome (r, v') m).1 :=
  ⟨the_seat_is_load_bearing_in_the_same_click s m h,
   the_backing_survives_the_door s m need hn,
   the_hall_hears_no_join_order a b x,
   (fun he => hab (List.cons.inj he).1),
   the_room_reads_no_waiting r v v' m hr⟩

theorem beq_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (eq_of_beq a b hb) h

def depthTo : List Nat → Nat → Nat
  | [], _ => 0
  | y :: r, x => cond (Nat.beq x y) 0 (depthTo r x + 1)

theorem the_seated_arrive_shallowest (r : List Nat) (x : Nat) :
    depthTo (x :: r) x = 0 := by
  show cond (Nat.beq x x) 0 (depthTo r x + 1) = 0
  rw [beq_self]
  rfl

theorem every_later_admission_deepens (r : List Nat) {y x : Nat}
    (h : x ≠ y) : depthTo (y :: r) x = depthTo r x + 1 := by
  show cond (Nat.beq x y) 0 (depthTo r x + 1) = depthTo r x + 1
  rw [beq_of_ne h]
  rfl

theorem the_depth_counts_the_clicks_since (x : Nat) :
    ∀ (ys r : List Nat), (∀ y, y ∈ ys → x ≠ y) →
      depthTo (ys ++ r) x = depthTo r x + ys.length
  | [], _, _ => rfl
  | y :: ys, r, h => by
      show depthTo (y :: (ys ++ r)) x = depthTo r x + (ys.length + 1)
      rw [every_later_admission_deepens (ys ++ r) (h y (List.Mem.head ys)),
          the_depth_counts_the_clicks_since x ys r
            (fun z hz => h z (List.Mem.tail y hz))]
      exact rfl

def hallFace : Face := ⟨List Nat, Nat, Bool, enrolled⟩

def costFace : Face := ⟨List Nat, Nat, Nat, depthTo⟩

theorem no_ask_parts_the_warmed_hall (a b : Nat)
    (q : Interview Nat Bool) :
    sound hallFace [a, b] q = sound hallFace [b, a] q :=
  no_interview_parts_the_alike hallFace [a, b] [b, a]
    (fun x => the_hall_hears_no_join_order a b x) q

theorem the_cost_face_parts_the_warmed (a b : Nat) (hab : a ≠ b) :
    ¬ alike costFace [a, b] [b, a] :=
  fun h =>
    nomatch
      (((the_seated_arrive_shallowest [b] a).symm.trans (h a)).trans
        ((every_later_admission_deepens [a] hab).trans
          (congrArg (· + 1) (the_seated_arrive_shallowest [] a))))

def lacking (room : List Nat) : List Nat → Nat
  | [] => 0
  | x :: need =>
      cond (enrolled room x) (lacking room need) (lacking room need + 1)

theorem the_weight_is_zero_at_the_door (room : List Nat) :
    ∀ need : List Nat, backed room need = true ↔ lacking room need = 0
  | [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | x :: need => by
      have hrec := the_weight_is_zero_at_the_door room need
      cases he : enrolled room x with
      | true =>
          constructor
          · intro h
            show cond (enrolled room x) (lacking room need)
                (lacking room need + 1) = 0
            rw [he]
            exact hrec.mp
              ((and_split
                (show (enrolled room x && backed room need) = true
                  from h)).2)
          · intro h
            have h0 : lacking room need = 0 := by
              have h' : cond (enrolled room x) (lacking room need)
                  (lacking room need + 1) = 0 := h
              rw [he] at h'
              exact h'
            show (enrolled room x && backed room need) = true
            rw [he, hrec.mpr h0]
            rfl
      | false =>
          constructor
          · intro h
            exact absurd
              (and_split
                (show (enrolled room x && backed room need) = true
                  from h)).1
              (ne_true_of_eq_false he)
          · intro h
            have h' : cond (enrolled room x) (lacking room need)
                (lacking room need + 1) = 0 := h
            rw [he] at h'
            exact nomatch h'

theorem the_removed_date_returns_as_a_weight (a b : Nat) (hab : a ≠ b)
    (q : Interview Nat Bool) (room need : List Nat) (x : Nat)
    (ys r : List Nat) (hy : ∀ y, y ∈ ys → x ≠ y) :
    (∀ z, enrolled [a, b] z = enrolled [b, a] z)
      ∧ sound hallFace [a, b] q = sound hallFace [b, a] q
      ∧ ¬ alike costFace [a, b] [b, a]
      ∧ depthTo (ys ++ r) x = depthTo r x + ys.length
      ∧ (backed room need = true ↔ lacking room need = 0)
      ∧ ∀ (rm : List Nat) (w z : Nat), enrolled rm z = true →
          enrolled (w :: rm) z = true :=
  ⟨the_hall_hears_no_join_order a b,
   no_ask_parts_the_warmed_hall a b q,
   the_cost_face_parts_the_warmed a b hab,
   the_depth_counts_the_clicks_since x ys r hy,
   the_weight_is_zero_at_the_door room need,
   fun rm w z hz => the_enrolled_stay_enrolled rm w z hz⟩

theorem the_backing_reaches_each_need (room : List Nat) :
    ∀ need : List Nat, backed room need = true →
      ∀ x, x ∈ need → enrolled room x = true
  | [], _, _, hx => nomatch hx
  | y :: need, h, x, hx => by
      obtain ⟨h1, h2⟩ :=
        and_split
          (show (enrolled room y && backed room need) = true from h)
      cases hx with
      | head => exact h1
      | tail _ hx' => exact the_backing_reaches_each_need room need h2 x hx'

theorem the_support_precedes_the_seating
    (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat)
    (h : backed s.1 m.2 = true) (x : Nat) (hx : x ∈ m.2) :
    enrolled s.1 x = true :=
  the_backing_reaches_each_need s.1 m.2 h x hx

theorem the_citer_arrives_above_the_cited
    (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat)
    (h : backed s.1 m.2 = true) (x : Nat) (hx : x ∈ m.2)
    (hne : x ≠ m.1) :
    enrolled s.1 x = true
      ∧ depthTo (welcome s m).1 m.1 = 0
      ∧ Nat.ble 1 (depthTo (welcome s m).1 x) = true :=
  ⟨the_support_precedes_the_seating s m h x hx,
   by
     rw [the_backed_are_seated h]
     exact the_seated_arrive_shallowest s.1 m.1,
   by
     rw [the_backed_are_seated h]
     show Nat.ble 1 (depthTo (m.1 :: s.1) x) = true
     rw [every_later_admission_deepens s.1 hne]
     exact rfl⟩

theorem the_elders_keep_their_order (r : List Nat) {z x y : Nat}
    (hx : x ≠ z) (hy : y ≠ z)
    (h : Nat.ble (depthTo r x) (depthTo r y) = true) :
    Nat.ble (depthTo (z :: r) x) (depthTo (z :: r) y) = true := by
  rw [every_later_admission_deepens r hx,
      every_later_admission_deepens r hy]
  exact h

theorem the_cited_are_the_elders
    (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat)
    (h : backed s.1 m.2 = true) (x : Nat) (hx : x ∈ m.2) (hne : x ≠ m.1)
    (r : List Nat) {z u v : Nat} (hu : u ≠ z) (hv : v ≠ z)
    (hb : Nat.ble (depthTo r u) (depthTo r v) = true) (a b w : Nat) :
    (enrolled s.1 x = true
        ∧ depthTo (welcome s m).1 m.1 = 0
        ∧ Nat.ble 1 (depthTo (welcome s m).1 x) = true)
      ∧ Nat.ble (depthTo (z :: r) u) (depthTo (z :: r) v) = true
      ∧ enrolled [a, b] w = enrolled [b, a] w
      ∧ enrolled (welcome s m).1 m.1 = true :=
  ⟨the_citer_arrives_above_the_cited s m h x hx hne,
   the_elders_keep_their_order r hu hv hb,
   the_hall_hears_no_join_order a b w,
   the_seat_is_load_bearing_in_the_same_click s m h⟩

def doorM : Machine (Nat × List Nat) Nat :=
  ⟨List Nat × List (Nat × List Nat), ([], []), welcome,
   fun s => s.2.length⟩

def ordered : List Nat → List (Nat × List Nat) → Prop
  | _, [] => True
  | r, m :: w => backed r m.2 = true ∧ ordered (m.1 :: r) w

theorem the_unencumbered_are_welcome_everywhere (r : List Nat) :
    backed r [] = true := rfl

theorem the_enrolled_survive_the_door
    (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat)
    (x : Nat) (h : enrolled s.1 x = true) :
    enrolled (welcome s m).1 x = true := by
  cases hb : backed s.1 m.2 with
  | true =>
      rw [the_backed_are_seated hb]
      exact the_enrolled_stay_enrolled s.1 m.1 x h
  | false =>
      rw [the_unbacked_are_held hb]
      exact h

theorem the_enrolled_survive_the_run (x : Nat) :
    ∀ (w : List (Nat × List Nat)) (s : List Nat × List (Nat × List Nat)),
      enrolled s.1 x = true → enrolled (park doorM s w).1 x = true
  | [], _, h => h
  | m :: w, s, h =>
      the_enrolled_survive_the_run x w (welcome s m)
        (the_enrolled_survive_the_door s m x h)

theorem the_ordered_arrivals_never_wait :
    ∀ (w : List (Nat × List Nat)) (r : List Nat)
      (v : List (Nat × List Nat)),
      ordered r w → (park doorM (r, v) w).2 = v
  | [], _, _, _ => rfl
  | m :: w, r, v, h => by
      obtain ⟨h1, h2⟩ := h
      show (park doorM (welcome (r, v) m) w).2 = v
      rw [the_backed_are_seated (s := (r, v)) h1]
      exact the_ordered_arrivals_never_wait w (m.1 :: r) v h2

theorem the_ordered_arrivals_all_seat :
    ∀ (w : List (Nat × List Nat)) (r : List Nat)
      (v : List (Nat × List Nat)),
      ordered r w → ∀ m, m ∈ w →
        enrolled (park doorM (r, v) w).1 m.1 = true
  | [], _, _, _, _, hm => nomatch hm
  | m :: w, r, v, h, m', hm => by
      obtain ⟨h1, h2⟩ := h
      show enrolled (park doorM (welcome (r, v) m) w).1 m'.1 = true
      rw [the_backed_are_seated (s := (r, v)) h1]
      cases hm with
      | head =>
          refine the_enrolled_survive_the_run m.1 w (m.1 :: r, v) ?_
          show (Nat.beq m.1 m.1 || r.any (Nat.beq m.1)) = true
          rw [beq_self]
          rfl
      | tail _ hm' =>
          exact the_ordered_arrivals_all_seat w (m.1 :: r) v h2 m' hm'

theorem the_tree_admits_itself (w : List (Nat × List Nat))
    (h : ordered [] w) (r : List Nat) :
    (park doorM (([] : List Nat), ([] : List (Nat × List Nat))) w).2 = []
      ∧ (∀ m, m ∈ w →
          enrolled (park doorM (([] : List Nat),
            ([] : List (Nat × List Nat))) w).1 m.1 = true)
      ∧ backed r [] = true
      ∧ behavior doorM w = 0 :=
  ⟨the_ordered_arrivals_never_wait w [] [] h,
   fun m hm => the_ordered_arrivals_all_seat w [] [] h m hm,
   the_unencumbered_are_welcome_everywhere r,
   ((the_drive_reads_the_walk doorM w ([], [])).trans
     (congrArg doorM.out (the_park_is_a_walk doorM w ([], [])).symm)).trans
     (congrArg (fun v : List (Nat × List Nat) => v.length)
       (the_ordered_arrivals_never_wait w [] [] h))⟩

theorem no_memory_meters_the_cost {X : Type} (f : List Bool → X)
    (a b : Nat) (hab : a ≠ b) (q : Interview Nat Bool) :
    f (sound hallFace [a, b] q) = f (sound hallFace [b, a] q)
      ∧ ¬ alike costFace [a, b] [b, a] :=
  ⟨congrArg f (no_ask_parts_the_warmed_hall a b q),
   the_cost_face_parts_the_warmed a b hab⟩

theorem the_stranger_leaves_the_hall_dark (r : List Nat) (y x : Nat)
    (hne : x ≠ y) (h : enrolled r x = false) :
    enrolled (y :: r) x = false := by
  show (Nat.beq x y || enrolled r x) = false
  rw [beq_of_ne hne, h]
  rfl

theorem no_mark_lights_itself (x : Nat) :
    ∀ (w : List (Nat × List Nat)) (s : List Nat × List (Nat × List Nat)),
      (∀ m, m ∈ w → m.1 = x → x ∈ m.2) →
      enrolled s.1 x = false →
      enrolled (park doorM s w).1 x = false
  | [], _, _, h => h
  | m :: w, s, hw, h => by
      have hstep : enrolled (welcome s m).1 x = false := by
        cases hb : backed s.1 m.2 with
        | false =>
            rw [the_unbacked_are_held hb]
            exact h
        | true =>
            rw [the_backed_are_seated hb]
            refine the_stranger_leaves_the_hall_dark s.1 m.1 x
              (fun hxm => ?_) h
            exact absurd
              (the_backing_reaches_each_need s.1 m.2 hb x
                (hw m (List.Mem.head w) hxm.symm))
              (ne_true_of_eq_false h)
      show enrolled (park doorM (welcome s m) w).1 x = false
      exact no_mark_lights_itself x w (welcome s m)
        (fun m' hm' => hw m' (List.Mem.tail m hm')) hstep

theorem the_first_light_comes_from_outside (x : Nat)
    (w : List (Nat × List Nat)) (s : List Nat × List (Nat × List Nat))
    (hw : ∀ m, m ∈ w → m.1 = x → x ∈ m.2)
    (hx : enrolled s.1 x = false) (r : List Nat)
    (m : Nat × List Nat) (hb : backed s.1 m.2 = true)
    {I O : Type} (mach : Machine I O) (rd : mach.S → I)
    (u : List Unit) (t : mach.S) (p : Plan) :
    enrolled (park doorM s w).1 x = false
      ∧ backed r [] = true
      ∧ enrolled (welcome s m).1 m.1 = true
      ∧ graft p (.board .ground .ground) = .board p p
      ∧ drive (selfSteered mach rd) t u
          = mach.out (orbit mach rd t u.length) :=
  ⟨no_mark_lights_itself x w s hw hx,
   the_unencumbered_are_welcome_everywhere r,
   the_seat_is_load_bearing_in_the_same_click s m hb,
   rfl,
   the_self_steered_machine_is_a_clock mach rd u t⟩

def sweep (s : List Nat × List (Nat × List Nat)) :
    List Nat × List (Nat × List Nat) :=
  park doorM (s.1, []) s.2

theorem the_backing_survives_the_run (need : List Nat) :
    ∀ (w : List (Nat × List Nat)) (s : List Nat × List (Nat × List Nat)),
      backed s.1 need = true → backed (park doorM s w).1 need = true
  | [], _, h => h
  | m :: w, s, h =>
      the_backing_survives_the_run need w (welcome s m)
        (the_backing_survives_the_door s m need h)

theorem the_ready_seat_in_one_sweep
    (r : List Nat) (m : Nat × List Nat) (h : backed r m.2 = true)
    (v₁ v₂ : List (Nat × List Nat)) :
    enrolled (park doorM (r, ([] : List (Nat × List Nat)))
      (v₁ ++ m :: v₂)).1 m.1 = true := by
  rw [the_park_resumes doorM v₁ (m :: v₂) (r, [])]
  show enrolled
      (park doorM (welcome (park doorM (r, []) v₁) m) v₂).1 m.1 = true
  exact the_enrolled_survive_the_run m.1 v₂
    (welcome (park doorM (r, []) v₁) m)
    (the_seat_is_load_bearing_in_the_same_click
      (park doorM (r, []) v₁) m
      (the_backing_survives_the_run m.2 v₁ (r, []) h))

theorem the_sweep_seats_the_ready
    (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat)
    (h : backed s.1 m.2 = true) (v₁ v₂ : List (Nat × List Nat))
    (hv : s.2 = v₁ ++ m :: v₂) :
    enrolled (sweep s).1 m.1 = true := by
  show enrolled (park doorM (s.1, []) s.2).1 m.1 = true
  rw [hv]
  exact the_ready_seat_in_one_sweep s.1 m h v₁ v₂

theorem the_vestibule_drains_by_storeys
    (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat)
    (h : backed s.1 m.2 = true) (v₁ v₂ : List (Nat × List Nat))
    (hv : s.2 = v₁ ++ m :: v₂) (need : List Nat)
    (w : List (Nat × List Nat)) (hn : backed s.1 need = true)
    (tw : List (Nat × List Nat)) (ht : ordered [] tw) :
    enrolled (sweep s).1 m.1 = true
      ∧ backed (park doorM s w).1 need = true
      ∧ (park doorM (([] : List Nat), ([] : List (Nat × List Nat))) tw).2
          = [] :=
  ⟨the_sweep_seats_the_ready s m h v₁ v₂ hv,
   the_backing_survives_the_run need w s hn,
   the_ordered_arrivals_never_wait tw [] [] ht⟩

theorem the_held_name_their_darkness (r : List Nat) :
    ∀ need : List Nat, backed r need = false →
      ∃ x, x ∈ need ∧ enrolled r x = false
  | [], h => nomatch h
  | y :: need, h => by
      cases he : enrolled r y with
      | false => exact ⟨y, List.Mem.head need, he⟩
      | true =>
          have hb : backed r need = false := by
            have h' : (enrolled r y && backed r need) = false := h
            rw [he] at h'
            exact h'
          obtain ⟨x, hx, hex⟩ := the_held_name_their_darkness r need hb
          exact ⟨x, List.Mem.tail y hx, hex⟩

theorem the_round_seats_or_certifies (r : List Nat) :
    ∀ v : List (Nat × List Nat),
      (∃ m, m ∈ v ∧ backed r m.2 = true)
        ∨ ∀ m, m ∈ v → backed r m.2 = false
  | [] => Or.inr (fun _ hm => nomatch hm)
  | m :: v => by
      cases hb : backed r m.2 with
      | true => exact Or.inl ⟨m, List.Mem.head v, hb⟩
      | false =>
          cases the_round_seats_or_certifies r v with
          | inl h =>
              obtain ⟨m', hm', hb'⟩ := h
              exact Or.inl ⟨m', List.Mem.tail m hm', hb'⟩
          | inr h =>
              refine Or.inr (fun m' hm' => ?_)
              cases hm' with
              | head => exact hb
              | tail _ hm'' => exact h m' hm''

theorem the_stuck_round_moves_nothing :
    ∀ (w : List (Nat × List Nat)) (r : List Nat)
      (acc : List (Nat × List Nat)),
      (∀ m, m ∈ w → backed r m.2 = false) →
      (park doorM (r, acc) w).1 = r
        ∧ (park doorM (r, acc) w).2.length = w.length + acc.length
        ∧ ∀ m, m ∈ (park doorM (r, acc) w).2 → m ∈ w ∨ m ∈ acc
  | [], _, acc, _ =>
      ⟨rfl, (zero_plus acc.length).symm, fun _ hm => Or.inr hm⟩
  | m :: w, r, acc, hw => by
      have hstep : welcome (r, acc) m = (r, m :: acc) :=
        the_unbacked_are_held (hw m (List.Mem.head w))
      obtain ⟨h1, h2, h3⟩ :=
        the_stuck_round_moves_nothing w r (m :: acc)
          (fun k hk => hw k (List.Mem.tail m hk))
      show (park doorM (welcome (r, acc) m) w).1 = r
          ∧ (park doorM (welcome (r, acc) m) w).2.length
              = (w.length + 1) + acc.length
          ∧ ∀ k, k ∈ (park doorM (welcome (r, acc) m) w).2 →
              k ∈ m :: w ∨ k ∈ acc
      rw [hstep]
      refine ⟨h1, ?_, ?_⟩
      · rw [h2]
        show w.length + (acc.length + 1) = (w.length + 1) + acc.length
        rw [succ_adds]
        exact rfl
      · intro k hk
        cases h3 k hk with
        | inl hkw => exact Or.inl (List.Mem.tail m hkw)
        | inr hka =>
            cases hka with
            | head => exact Or.inl (List.Mem.head w)
            | tail _ hka' => exact Or.inr hka'

theorem the_deadlock_wheels (r : List Nat) :
    ∀ (n : Nat) (held : List (Nat × List Nat)),
      (∀ m, m ∈ held → backed r m.2 = false) →
      (again sweep n (r, held)).1 = r
        ∧ (again sweep n (r, held)).2.length = held.length
        ∧ ∀ m, m ∈ (again sweep n (r, held)).2 → backed r m.2 = false
  | 0, _, hs => ⟨rfl, rfl, hs⟩
  | n + 1, held, hs => by
      obtain ⟨h1, h2, h3⟩ := the_deadlock_wheels r n held hs
      have hstuck : ∀ m, m ∈ (again sweep n (r, held)).2 →
          backed (again sweep n (r, held)).1 m.2 = false := by
        intro m hm
        rw [h1]
        exact h3 m hm
      obtain ⟨g1, g2, g3⟩ :=
        the_stuck_round_moves_nothing (again sweep n (r, held)).2
          (again sweep n (r, held)).1 [] hstuck
      show (sweep (again sweep n (r, held))).1 = r
          ∧ (sweep (again sweep n (r, held))).2.length = held.length
          ∧ ∀ m, m ∈ (sweep (again sweep n (r, held))).2 →
              backed r m.2 = false
      refine ⟨g1.trans h1, g2.trans h2, ?_⟩
      intro m hm
      cases g3 m hm with
      | inl hmw => exact h3 m hmw
      | inr hma => exact nomatch hma

theorem the_deadlock_is_a_wheel (r : List Nat)
    (held : List (Nat × List Nat))
    (hs : ∀ m, m ∈ held → backed r m.2 = false) (n : Nat)
    (v : List (Nat × List Nat))
    (s : List Nat × List (Nat × List Nat)) (m : Nat × List Nat)
    (hm : backed s.1 m.2 = true) (v₁ v₂ : List (Nat × List Nat))
    (hv : s.2 = v₁ ++ m :: v₂) (need : List Nat)
    (hneed : backed r need = false) :
    ((∃ k, k ∈ v ∧ backed r k.2 = true)
        ∨ ∀ k, k ∈ v → backed r k.2 = false)
      ∧ (again sweep n (r, held)).1 = r
      ∧ (again sweep n (r, held)).2.length = held.length
      ∧ enrolled (sweep s).1 m.1 = true
      ∧ ∃ x, x ∈ need ∧ enrolled r x = false :=
  ⟨the_round_seats_or_certifies r v,
   (the_deadlock_wheels r n held hs).1,
   (the_deadlock_wheels r n held hs).2.1,
   the_sweep_seats_the_ready s m hm v₁ v₂ hv,
   the_held_name_their_darkness r need hneed⟩

theorem mem_splits {A : Type} {x : A} :
    ∀ {l : List A}, x ∈ l → ∃ v₁ v₂ : List A, l = v₁ ++ x :: v₂
  | _ :: t, List.Mem.head _ => ⟨[], t, rfl⟩
  | a :: _, List.Mem.tail _ h =>
      match mem_splits h with
      | ⟨v₁, v₂, he⟩ => ⟨a :: v₁, v₂, congrArg (a :: ·) he⟩

theorem the_load_never_climbs :
    ∀ (w : List (Nat × List Nat)) (r : List Nat)
      (acc : List (Nat × List Nat)),
      Nat.ble (park doorM (r, acc) w).2.length (w.length + acc.length)
        = true
  | [], _, acc => by
      show Nat.ble acc.length
        (([] : List (Nat × List Nat)).length + acc.length) = true
      rw [show ([] : List (Nat × List Nat)).length + acc.length
            = acc.length from zero_plus acc.length]
      exact ble_refl acc.length
  | m :: w, r, acc => by
      cases hb : backed r m.2 with
      | true =>
          show Nat.ble (park doorM (welcome (r, acc) m) w).2.length
              ((w.length + 1) + acc.length) = true
          rw [the_backed_are_seated hb, succ_adds]
          exact ble_trans _ _ _ (the_load_never_climbs w (m.1 :: r) acc)
            (ble_le_succ (w.length + acc.length))
      | false =>
          show Nat.ble (park doorM (welcome (r, acc) m) w).2.length
              ((w.length + 1) + acc.length) = true
          rw [the_unbacked_are_held hb, succ_adds]
          exact the_load_never_climbs w r (m :: acc)

theorem the_ready_drop_the_load (r : List Nat)
    (m : Nat × List Nat) (h : backed r m.2 = true)
    (v₁ v₂ acc : List (Nat × List Nat)) :
    Nat.ble ((park doorM (r, acc) (v₁ ++ m :: v₂)).2.length + 1)
      ((v₁ ++ m :: v₂).length + acc.length) = true := by
  have e2 : v₂.length + (v₁.length + acc.length)
      = (v₁.length + v₂.length) + acc.length := by
    rw [← Nat.add_assoc v₂.length v₁.length acc.length,
        Nat.add_comm v₂.length v₁.length]
  have e : (v₁ ++ m :: v₂).length + acc.length
      = (v₂.length + (v₁.length + acc.length)) + 1 := by
    rw [len_append v₁ (m :: v₂)]
    show ((v₁.length + v₂.length) + 1) + acc.length
        = (v₂.length + (v₁.length + acc.length)) + 1
    rw [succ_adds (v₁.length + v₂.length) acc.length]
    exact congrArg (· + 1) e2.symm
  rw [the_park_resumes doorM v₁ (m :: v₂) (r, acc)]
  show Nat.ble
      ((park doorM (welcome (park doorM (r, acc) v₁) m) v₂).2.length + 1)
      ((v₁ ++ m :: v₂).length + acc.length) = true
  rw [the_backed_are_seated
      (the_backing_survives_the_run m.2 v₁ (r, acc) h), e]
  exact ble_add_right 1
    (ble_trans _ _ _
      (the_load_never_climbs v₂
        (m.1 :: (park doorM (r, acc) v₁).1)
        (park doorM (r, acc) v₁).2)
      (ble_add_both (ble_refl v₂.length)
        (the_load_never_climbs v₁ r acc)))

theorem the_gauge_is_exact (s : List Nat × List (Nat × List Nat)) :
    (sweep s).2.length = s.2.length
      ↔ ∀ m, m ∈ s.2 → backed s.1 m.2 = false := by
  constructor
  · intro h
    cases the_round_seats_or_certifies s.1 s.2 with
    | inr hall => exact hall
    | inl hex =>
        obtain ⟨m, hm, hb⟩ := hex
        obtain ⟨v₁, v₂, hv⟩ := mem_splits hm
        have hdrop := the_ready_drop_the_load s.1 m hb v₁ v₂ []
        rw [← hv] at hdrop
        have hdrop' : Nat.ble ((sweep s).2.length + 1) s.2.length = true :=
          hdrop
        rw [h] at hdrop'
        exact absurd hdrop'
          (ne_true_of_eq_false (ble_succ_false s.2.length))
  · intro hall
    exact (the_stuck_round_moves_nothing s.2 s.1 [] hall).2.1

theorem the_detector_reads_one_number
    (s : List Nat × List (Nat × List Nat)) (n : Nat)
    (r : List Nat) (held : List (Nat × List Nat))
    (hs : ∀ m, m ∈ held → backed r m.2 = false) :
    ((sweep s).2.length = s.2.length
        ↔ ∀ m, m ∈ s.2 → backed s.1 m.2 = false)
      ∧ ((∃ k, k ∈ s.2 ∧ backed s.1 k.2 = true)
          ∨ ∀ k, k ∈ s.2 → backed s.1 k.2 = false)
      ∧ (again sweep n (r, held)).2.length = held.length :=
  ⟨the_gauge_is_exact s,
   the_round_seats_or_certifies s.1 s.2,
   (the_deadlock_wheels r n held hs).2.1⟩

theorem the_revision_is_a_reading (base : Plan) (q : Plan) :
    graft base q = fold Plan.board base q :=
  any_two_readings_agree Plan.board base (graft base) rfl
    (fun _ _ => rfl) q

theorem every_writer_is_a_reader (base a b q : Plan) (W : Type)
    (F : Face) (s : F.State) (ps : List F.Probe) :
    graft base q = fold Plan.board base q
      ∧ fold Plan.board Plan.ground q = q
      ∧ build W q = fold door W q
      ∧ graft a (graft b q) = fold Plan.board (fold Plan.board a b) q
      ∧ sound F s (recite ps) = ps.map (F.obs s) :=
  ⟨the_revision_is_a_reading base q,
   the_self_reading_is_the_identity q,
   build_is_a_reading W q,
   (the_revision_is_a_reading a (graft b q)).trans
     (the_parent_folds_into_the_ground Plan.board a b q),
   the_recital_is_the_transcript F s ps⟩

inductive Braid {I : Type} : List I → List I → List I → Prop
  | nil : Braid [] [] []
  | left {u v w : List I} (i : I) : Braid u v w → Braid (i :: u) v (i :: w)
  | right {u v w : List I} (j : I) : Braid u v w → Braid u (j :: v) (j :: w)

theorem braid_of_left {I : Type} : ∀ u : List I, Braid u [] u
  | [] => .nil
  | i :: u => .left i (braid_of_left u)

theorem braid_of_right {I : Type} : ∀ v : List I, Braid [] v v
  | [] => .nil
  | j :: v => .right j (braid_of_right v)

theorem braid_append {I : Type} : ∀ u v : List I, Braid u v (u ++ v)
  | [], v => braid_of_right v
  | i :: u, v => .left i (braid_append u v)

theorem braid_prepend {I : Type} : ∀ u v : List I, Braid u v (v ++ u)
  | u, [] => braid_of_left u
  | u, j :: v => .right j (braid_prepend u v)

theorem the_step_crosses_the_walk {I O : Type} (m : Machine I O)
    (hcomm : ∀ s i j, m.step (m.step s i) j = m.step (m.step s j) i) :
    ∀ (u : List I) (s : m.S) (j : I),
      park m (m.step s j) u = m.step (park m s u) j
  | [], _, _ => rfl
  | i :: u, s, j => by
      show park m (m.step (m.step s j) i) u
          = m.step (park m (m.step s i) u) j
      rw [hcomm s j i]
      exact the_step_crosses_the_walk m hcomm u (m.step s i) j

theorem the_weave_parks_one_seat {I O : Type} (m : Machine I O)
    (hcomm : ∀ s i j, m.step (m.step s i) j = m.step (m.step s j) i) :
    ∀ {u v w : List I}, Braid u v w →
      ∀ s : m.S, park m s w = park m (park m s u) v
  | _, _, _, .nil, _ => rfl
  | _, _, _, .left i hb, s =>
      the_weave_parks_one_seat m hcomm hb (m.step s i)
  | _, _, _, @Braid.right _ u v w j hb, s =>
      (the_weave_parks_one_seat m hcomm hb (m.step s j)).trans
        (congrArg (fun t => park m t v)
          (the_step_crosses_the_walk m hcomm u s j))

theorem the_contributors_may_arrive_in_either_order {I O : Type}
    (m : Machine I O)
    (hcomm : ∀ s i j, m.step (m.step s i) j = m.step (m.step s j) i)
    (u v : List I) (s : m.S) :
    park m s (u ++ v) = park m s (v ++ u) :=
  (the_weave_parks_one_seat m hcomm (braid_append u v) s).trans
    (the_weave_parks_one_seat m hcomm (braid_prepend u v) s).symm

theorem the_shared_fold_needs_no_scheduler {I O : Type} (m : Machine I O)
    (hcomm : ∀ s i j, m.step (m.step s i) j = m.step (m.step s j) i)
    {u v w : List I} (hb : Braid u v w) (s : m.S)
    (x y : List Nat) (t : Nat) {A : Type} {a b : A} (hab : a ≠ b) :
    park m s w = park m (park m s u) v
      ∧ park m s (u ++ v) = park m s (v ++ u)
      ∧ park heap t (x ++ y) = park heap t (y ++ x)
      ∧ park (scribe (fun _ k => k)) ([] : List A) [a, b]
          ≠ park (scribe (fun _ k => k)) ([] : List A) [b, a] :=
  ⟨the_weave_parks_one_seat m hcomm hb s,
   the_contributors_may_arrive_in_either_order m hcomm u v s,
   the_contributors_may_arrive_in_either_order heap
     the_heap_steps_commute x y t,
   the_scribe_keeps_the_order hab⟩

theorem the_tellers_steps_commute (n : Nat) (a b : Plan) :
    teller.step (teller.step n a) b = teller.step (teller.step n b) a :=
  (mul_regroups n (fold (fun x y => x + y) 1 a)
      (fold (fun x y => x + y) 1 b)).trans
    ((congrArg (n * ·)
        (Nat.mul_comm (fold (fun x y => x + y) 1 a)
          (fold (fun x y => x + y) 1 b))).trans
      (mul_regroups n (fold (fun x y => x + y) 1 b)
        (fold (fun x y => x + y) 1 a)).symm)

theorem the_braided_life_draws_one_count {u v w : List Plan}
    (hb : Braid u v w) :
    (fold (fun a b => a + b) 1 (park grower Plan.ground w) : Nat)
      = park teller (park teller (1 : Nat) u) v :=
  ((the_audition_cannot_tell_the_tree_from_its_count).2.2.1 w).trans
    (the_weave_parks_one_seat teller the_tellers_steps_commute hb (1 : Nat))

theorem the_braided_lives_part :
    park grower Plan.ground
        [Plan.board .ground .ground,
         Plan.board .ground (.board .ground .ground)]
      ≠ park grower Plan.ground
        [Plan.board .ground (.board .ground .ground),
         Plan.board .ground .ground] := by
  intro h
  have e1 : park grower Plan.ground
      [Plan.board .ground .ground,
       Plan.board .ground (.board .ground .ground)]
      = graft (.board .ground .ground)
          (.board .ground (.board .ground .ground)) :=
    congrArg (fun t => graft t (.board .ground (.board .ground .ground)))
      (the_trivial_revision_changes_nothing (.board .ground .ground))
  have e2 : park grower Plan.ground
      [Plan.board .ground (.board .ground .ground),
       Plan.board .ground .ground]
      = graft (.board .ground (.board .ground .ground))
          (.board .ground .ground) :=
    congrArg (fun t => graft t (.board .ground .ground))
      (the_trivial_revision_changes_nothing
        (.board .ground (.board .ground .ground)))
  exact (two_lineages_one_reading .ground .ground).2.2
    ((e1.symm.trans h).trans e2)

theorem every_braid_draws_one_count {u v w : List Plan} (hb : Braid u v w)
    (n : Nat) (a b : Plan) :
    teller.step (teller.step n a) b = teller.step (teller.step n b) a
      ∧ (fold (fun x y => x + y) 1 (park grower Plan.ground w) : Nat)
          = park teller (park teller (1 : Nat) u) v
      ∧ park grower Plan.ground
            [Plan.board .ground .ground,
             Plan.board .ground (.board .ground .ground)]
          ≠ park grower Plan.ground
            [Plan.board .ground (.board .ground .ground),
             Plan.board .ground .ground]
      ∧ fold (fun x y => x + y * y) 1
            (graft (.board .ground .ground)
              (.board .ground (.board .ground .ground)))
          ≠ fold (fun x y => x + y * y) 1
            (graft (.board .ground (.board .ground .ground))
              (.board .ground .ground)) :=
  ⟨the_tellers_steps_commute n a b,
   the_braided_life_draws_one_count hb,
   the_braided_lives_part,
   (two_lineages_one_reading .ground .ground).2.1⟩

theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro he
  rw [he] at h
  exact nomatch (beq_self b).symm.trans h

theorem the_mutual_need_stays_dark (x y : Nat) :
    ∀ (w : List (Nat × List Nat)) (s : List Nat × List (Nat × List Nat)),
      (∀ m, m ∈ w → m.1 = x → y ∈ m.2) →
      (∀ m, m ∈ w → m.1 = y → x ∈ m.2) →
      enrolled s.1 x = false → enrolled s.1 y = false →
      enrolled (park doorM s w).1 x = false
        ∧ enrolled (park doorM s w).1 y = false
  | [], _, _, _, hx, hy => ⟨hx, hy⟩
  | m :: w, s, hwx, hwy, hx, hy => by
      have hnext : enrolled (welcome s m).1 x = false
          ∧ enrolled (welcome s m).1 y = false := by
        cases hb : backed s.1 m.2 with
        | false =>
            rw [the_unbacked_are_held hb]
            exact ⟨hx, hy⟩
        | true =>
            rw [the_backed_are_seated hb]
            cases hbx : Nat.beq m.1 x with
            | true =>
                exact absurd
                  (the_backing_reaches_each_need s.1 m.2 hb y
                    (hwx m (List.Mem.head w) (eq_of_beq m.1 x hbx)))
                  (ne_true_of_eq_false hy)
            | false =>
                cases hby : Nat.beq m.1 y with
                | true =>
                    exact absurd
                      (the_backing_reaches_each_need s.1 m.2 hb x
                        (hwy m (List.Mem.head w) (eq_of_beq m.1 y hby)))
                      (ne_true_of_eq_false hx)
                | false =>
                    exact ⟨the_stranger_leaves_the_hall_dark s.1 m.1 x
                        (fun he => ne_of_beq_false hbx he.symm) hx,
                      the_stranger_leaves_the_hall_dark s.1 m.1 y
                        (fun he => ne_of_beq_false hby he.symm) hy⟩
      show enrolled (park doorM (welcome s m) w).1 x = false
          ∧ enrolled (park doorM (welcome s m) w).1 y = false
      exact the_mutual_need_stays_dark x y w (welcome s m)
        (fun k hk => hwx k (List.Mem.tail m hk))
        (fun k hk => hwy k (List.Mem.tail m hk))
        hnext.1 hnext.2

theorem the_circle_admits_nobody (x y : Nat)
    (w : List (Nat × List Nat)) (s : List Nat × List (Nat × List Nat))
    (hwx : ∀ m, m ∈ w → m.1 = x → y ∈ m.2)
    (hwy : ∀ m, m ∈ w → m.1 = y → x ∈ m.2)
    (hx : enrolled s.1 x = false) (hy : enrolled s.1 y = false)
    (z : Nat) (w' : List (Nat × List Nat))
    (s' : List Nat × List (Nat × List Nat))
    (hw' : ∀ m, m ∈ w' → m.1 = z → z ∈ m.2)
    (hz : enrolled s'.1 z = false) (r : List Nat)
    (n : Nat) (held : List (Nat × List Nat))
    (hs : ∀ m, m ∈ held → backed r m.2 = false) :
    (enrolled (park doorM s w).1 x = false
        ∧ enrolled (park doorM s w).1 y = false)
      ∧ enrolled (park doorM s' w').1 z = false
      ∧ backed r [] = true
      ∧ (again sweep n (r, held)).2.length = held.length :=
  ⟨the_mutual_need_stays_dark x y w s hwx hwy hx hy,
   no_mark_lights_itself z w' s' hw' hz,
   the_unencumbered_are_welcome_everywhere r,
   (the_deadlock_wheels r n held hs).2.1⟩

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

/-- info: 'Seed.a_guest_mover_is_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms a_guest_mover_is_unheard

/-- info: 'Seed.an_unheard_move_moves_only_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms an_unheard_move_moves_only_the_guest

/-- info: 'Seed.guest_movers_compose' does not depend on any axioms -/
#guard_msgs in #print axioms guest_movers_compose

/-- info: 'Seed.the_still_door_moves_no_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_still_door_moves_no_guest

/-- info: 'Seed.the_label_rides_unread' does not depend on any axioms -/
#guard_msgs in #print axioms the_label_rides_unread

/-- info: 'Seed.a_false_label_is_real' does not depend on any axioms -/
#guard_msgs in #print axioms a_false_label_is_real

/-- info: 'Seed.the_meeting_reads_the_label' does not depend on any axioms -/
#guard_msgs in #print axioms the_meeting_reads_the_label

/-- info: 'Seed.honesty_is_invisible_at_the_face' does not depend on any axioms -/
#guard_msgs in #print axioms honesty_is_invisible_at_the_face

/-- info: 'Seed.the_doors_theorem' does not depend on any axioms -/
#guard_msgs in #print axioms the_doors_theorem

/-- info: 'Seed.zero_plus' does not depend on any axioms -/
#guard_msgs in #print axioms zero_plus

/-- info: 'Seed.succ_adds' does not depend on any axioms -/
#guard_msgs in #print axioms succ_adds

/-- info: 'Seed.len_append' does not depend on any axioms -/
#guard_msgs in #print axioms len_append

/-- info: 'Seed.map_append' does not depend on any axioms -/
#guard_msgs in #print axioms map_append

/-- info: 'Seed.the_manifest_counts_the_guests' does not depend on any axioms -/
#guard_msgs in #print axioms the_manifest_counts_the_guests

/-- info: 'Seed.the_customs_thread_the_manifest' does not depend on any axioms -/
#guard_msgs in #print axioms the_customs_thread_the_manifest

/-- info: 'Seed.drive_counts' does not depend on any axioms -/
#guard_msgs in #print axioms drive_counts

/-- info: 'Seed.the_run_agrees_with_the_fold' does not depend on any axioms -/
#guard_msgs in #print axioms the_run_agrees_with_the_fold

/-- info: 'Seed.ble_refl' does not depend on any axioms -/
#guard_msgs in #print axioms ble_refl

/-- info: 'Seed.ble_le_succ' does not depend on any axioms -/
#guard_msgs in #print axioms ble_le_succ

/-- info: 'Seed.tighter_refl' does not depend on any axioms -/
#guard_msgs in #print axioms tighter_refl

/-- info: 'Seed.tighter_trans' does not depend on any axioms -/
#guard_msgs in #print axioms tighter_trans

/-- info: 'Seed.the_learner_only_tightens' does not depend on any axioms -/
#guard_msgs in #print axioms the_learner_only_tightens

/-- info: 'Seed.the_homing_reading_tightens' does not depend on any axioms -/
#guard_msgs in #print axioms the_homing_reading_tightens

/-- info: 'Seed.the_drive_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms the_drive_resumes

/-- info: 'Seed.the_session_continues_from_the_parked_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_session_continues_from_the_parked_seat

/-- info: 'Seed.the_future_reads_only_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_future_reads_only_the_seat

/-- info: 'Seed.two_routes_one_seat' does not depend on any axioms -/
#guard_msgs in #print axioms two_routes_one_seat

/-- info: 'Seed.the_special_was_the_general' does not depend on any axioms -/
#guard_msgs in #print axioms the_special_was_the_general

/-- info: 'Seed.the_spec_hides_the_implementation' does not depend on any axioms -/
#guard_msgs in #print axioms the_spec_hides_the_implementation

/-- info: 'Seed.no_client_reads_the_implementation' does not depend on any axioms -/
#guard_msgs in #print axioms no_client_reads_the_implementation

/-- info: 'Seed.hearing_through_a_translator' does not depend on any axioms -/
#guard_msgs in #print axioms hearing_through_a_translator

/-- info: 'Seed.translators_stack_backward' does not depend on any axioms -/
#guard_msgs in #print axioms translators_stack_backward

/-- info: 'Seed.the_plain_ear_hears_plainly' does not depend on any axioms -/
#guard_msgs in #print axioms the_plain_ear_hears_plainly

/-- info: 'Seed.speaking_through_a_translator' does not depend on any axioms -/
#guard_msgs in #print axioms speaking_through_a_translator

/-- info: 'Seed.voices_stack_forward' does not depend on any axioms -/
#guard_msgs in #print axioms voices_stack_forward

/-- info: 'Seed.the_ear_and_the_voice_commute' does not depend on any axioms -/
#guard_msgs in #print axioms the_ear_and_the_voice_commute

/-- info: 'Seed.an_upgrade_ships_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms an_upgrade_ships_unheard

/-- info: 'Seed.the_mirror_doubles_the_manifest' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_doubles_the_manifest

/-- info: 'Seed.mem_map_intro' does not depend on any axioms -/
#guard_msgs in #print axioms mem_map_intro

/-- info: 'Seed.mem_append_left' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_left

/-- info: 'Seed.mem_append_right' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_right

/-- info: 'Seed.mem_append_split' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_split

/-- info: 'Seed.mem_map_back' does not depend on any axioms -/
#guard_msgs in #print axioms mem_map_back

/-- info: 'Seed.mem_cross' does not depend on any axioms -/
#guard_msgs in #print axioms mem_cross

/-- info: 'Seed.mem_cross_split' does not depend on any axioms -/
#guard_msgs in #print axioms mem_cross_split

/-- info: 'Seed.the_reading_is_positive' does not depend on any axioms -/
#guard_msgs in #print axioms the_reading_is_positive

/-- info: 'Seed.ble_le_add' does not depend on any axioms -/
#guard_msgs in #print axioms ble_le_add

/-- info: 'Seed.ble_le_add_left' does not depend on any axioms -/
#guard_msgs in #print axioms ble_le_add_left

/-- info: 'Seed.ble_add_right' does not depend on any axioms -/
#guard_msgs in #print axioms ble_add_right

/-- info: 'Seed.ble_add_both' does not depend on any axioms -/
#guard_msgs in #print axioms ble_add_both

/-- info: 'Seed.ble_gain_false' does not depend on any axioms -/
#guard_msgs in #print axioms ble_gain_false

/-- info: 'Seed.the_cap_is_positive' does not depend on any axioms -/
#guard_msgs in #print axioms the_cap_is_positive

/-- info: 'Seed.the_horizon_holds_every_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_horizon_holds_every_reading

/-- info: 'Seed.the_room_only_grows' does not depend on any axioms -/
#guard_msgs in #print axioms the_room_only_grows

/-- info: 'Seed.the_room_reads_within_its_cap' does not depend on any axioms -/
#guard_msgs in #print axioms the_room_reads_within_its_cap

/-- info: 'Seed.the_bloom_fills_its_cap' does not depend on any axioms -/
#guard_msgs in #print axioms the_bloom_fills_its_cap

/-- info: 'Seed.the_bloom_resides' does not depend on any axioms -/
#guard_msgs in #print axioms the_bloom_resides

/-- info: 'Seed.the_bloom_outgrows_the_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_bloom_outgrows_the_room

/-- info: 'Seed.no_bound_is_the_last_bound' does not depend on any axioms -/
#guard_msgs in #print axioms no_bound_is_the_last_bound

/-- info: 'Seed.time_outgrows_every_room' does not depend on any axioms -/
#guard_msgs in #print axioms time_outgrows_every_room

/-- info: 'Seed.the_flip_wheels' does not depend on any axioms -/
#guard_msgs in #print axioms the_flip_wheels

/-- info: 'Seed.the_pace_parks_at_its_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_pace_parks_at_its_count

/-- info: 'Seed.no_gain_is_zero' does not depend on any axioms -/
#guard_msgs in #print axioms no_gain_is_zero

/-- info: 'Seed.the_pace_reads_as_the_flip' does not depend on any axioms -/
#guard_msgs in #print axioms the_pace_reads_as_the_flip

/-- info: 'Seed.the_wheel_and_the_arrow_share_a_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_and_the_arrow_share_a_face

/-- info: 'Seed.seats_forget_stages_remember' does not depend on any axioms -/
#guard_msgs in #print axioms seats_forget_stages_remember

/-- info: 'Seed.the_ground_rides_in_every_graft' does not depend on any axioms -/
#guard_msgs in #print axioms the_ground_rides_in_every_graft

/-- info: 'Seed.a_true_tick_grows_the_reading' does not depend on any axioms -/
#guard_msgs in #print axioms a_true_tick_grows_the_reading

/-- info: 'Seed.the_worldline_never_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_worldline_never_comes_home

/-- info: 'Seed.the_arrow_counts_the_ticks' does not depend on any axioms -/
#guard_msgs in #print axioms the_arrow_counts_the_ticks

/-- info: 'Seed.time_wears_no_wheel' does not depend on any axioms -/
#guard_msgs in #print axioms time_wears_no_wheel

/-- info: 'Seed.apart_map' does not depend on any axioms -/
#guard_msgs in #print axioms apart_map

/-- info: 'Seed.apart_append' does not depend on any axioms -/
#guard_msgs in #print axioms apart_append

/-- info: 'Seed.the_cross_keeps_apart' does not depend on any axioms -/
#guard_msgs in #print axioms the_cross_keeps_apart

/-- info: 'Seed.the_room_repeats_no_plan' does not depend on any axioms -/
#guard_msgs in #print axioms the_room_repeats_no_plan

/-- info: 'Seed.eq_of_beq' does not depend on any axioms -/
#guard_msgs in #print axioms eq_of_beq

/-- info: 'Seed.beq_self' does not depend on any axioms -/
#guard_msgs in #print axioms beq_self

/-- info: 'Seed.ne_true_of_eq_false' does not depend on any axioms -/
#guard_msgs in #print axioms ne_true_of_eq_false

/-- info: 'Seed.mem_of_mem_filter' does not depend on any axioms -/
#guard_msgs in #print axioms mem_of_mem_filter

/-- info: 'Seed.filter_holds' does not depend on any axioms -/
#guard_msgs in #print axioms filter_holds

/-- info: 'Seed.mem_filter_intro' does not depend on any axioms -/
#guard_msgs in #print axioms mem_filter_intro

/-- info: 'Seed.apart_filter' does not depend on any axioms -/
#guard_msgs in #print axioms apart_filter

/-- info: 'Seed.the_census_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_is_exact

/-- info: 'Seed.the_ground_revision_keeps_the_passenger' does not depend on any axioms -/
#guard_msgs in #print axioms the_ground_revision_keeps_the_passenger

/-- info: 'Seed.the_mirror_is_a_ride' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_is_a_ride

/-- info: 'Seed.the_passenger_keeps_the_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_passenger_keeps_the_face

/-- info: 'Seed.the_passenger_multiplies_the_manifest' does not depend on any axioms -/
#guard_msgs in #print axioms the_passenger_multiplies_the_manifest

/-- info: 'Seed.the_rides_compose_at_the_manifest' does not depend on any axioms -/
#guard_msgs in #print axioms the_rides_compose_at_the_manifest

/-- info: 'Seed.the_walk_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_resumes

/-- info: 'Seed.the_transport_sheds_its_route' does not depend on any axioms -/
#guard_msgs in #print axioms the_transport_sheds_its_route

/-- info: 'Seed.any_lineage_proof_settles_the_carrier' does not depend on any axioms -/
#guard_msgs in #print axioms any_lineage_proof_settles_the_carrier

/-- info: 'Seed.the_worldline_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms the_worldline_resumes

/-- info: 'Seed.the_face_survives_the_journey' does not depend on any axioms -/
#guard_msgs in #print axioms the_face_survives_the_journey

/-- info: 'Seed.the_journey_manifest_settles' does not depend on any axioms -/
#guard_msgs in #print axioms the_journey_manifest_settles

/-- info: 'Seed.the_journeys_compose' does not depend on any axioms -/
#guard_msgs in #print axioms the_journeys_compose

/-- info: 'Seed.the_life_resumes_from_the_parked_rider' does not depend on any axioms -/
#guard_msgs in #print axioms the_life_resumes_from_the_parked_rider

/-- info: 'Seed.the_customs_survive_the_journey' does not depend on any axioms -/
#guard_msgs in #print axioms the_customs_survive_the_journey

/-- info: 'Seed.the_worldline_carries_its_rider' does not depend on any axioms -/
#guard_msgs in #print axioms the_worldline_carries_its_rider

/-- info: 'Seed.the_door_carries_the_heq' does not depend on any axioms -/
#guard_msgs in #print axioms the_door_carries_the_heq

/-- info: 'Seed.the_rides_compose' does not depend on any axioms -/
#guard_msgs in #print axioms the_rides_compose

/-- info: 'Seed.the_lineage_law_settles_the_carrier' does not depend on any axioms -/
#guard_msgs in #print axioms the_lineage_law_settles_the_carrier

/-- info: 'Seed.two_routes_one_rider' does not depend on any axioms -/
#guard_msgs in #print axioms two_routes_one_rider

/-- info: 'Seed.the_customs_ride_along' does not depend on any axioms -/
#guard_msgs in #print axioms the_customs_ride_along

/-- info: 'Seed.a_reading_in_step_carries_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms a_reading_in_step_carries_the_walk

/-- info: 'Seed.two_machines_in_step_agree' does not depend on any axioms -/
#guard_msgs in #print axioms two_machines_in_step_agree

/-- info: 'Seed.the_park_is_a_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_park_is_a_walk

/-- info: 'Seed.the_drive_reads_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_drive_reads_the_walk

/-- info: 'Seed.the_worldline_is_a_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_worldline_is_a_walk

/-- info: 'Seed.the_epochs_are_a_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_epochs_are_a_walk

/-- info: 'Seed.the_three_roads_are_one_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_three_roads_are_one_walk

/-- info: 'Seed.the_worldline_settles' does not depend on any axioms -/
#guard_msgs in #print axioms the_worldline_settles

/-- info: 'Seed.no_world_is_refused' does not depend on any axioms -/
#guard_msgs in #print axioms no_world_is_refused

/-- info: 'Seed.any_two_readings_agree' does not depend on any axioms -/
#guard_msgs in #print axioms any_two_readings_agree

/-- info: 'Seed.the_self_reading_is_the_identity' does not depend on any axioms -/
#guard_msgs in #print axioms the_self_reading_is_the_identity

/-- info: 'Seed.build_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms build_is_a_reading

/-- info: 'Seed.a_reading_may_forget_what_the_record_keeps' does not depend on any axioms -/
#guard_msgs in #print axioms a_reading_may_forget_what_the_record_keeps

/-- info: 'Seed.no_face_answers_for_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms no_face_answers_for_the_guest

/-- info: 'Seed.one_reading_merges_what_another_parts' does not depend on any axioms -/
#guard_msgs in #print axioms one_reading_merges_what_another_parts

/-- info: 'Seed.the_reading_is_the_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_reading_is_the_face

/-- info: 'Seed.the_meeting_returns_the_world' does not depend on any axioms -/
#guard_msgs in #print axioms the_meeting_returns_the_world

/-- info: 'Seed.classmates_board_as_guests' does not depend on any axioms -/
#guard_msgs in #print axioms classmates_board_as_guests

/-- info: 'Seed.every_reading_is_a_door' does not depend on any axioms -/
#guard_msgs in #print axioms every_reading_is_a_door

/-- info: 'Seed.the_class_is_a_guest_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_class_is_a_guest_room

/-- info: 'Seed.checking_papers_unpersons' does not depend on any axioms -/
#guard_msgs in #print axioms checking_papers_unpersons

/-- info: 'Seed.hospitality_is_structural' does not depend on any axioms -/
#guard_msgs in #print axioms hospitality_is_structural

/-- info: 'Seed.the_meeting_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_meeting_is_a_reading

/-- info: 'Seed.two_readings_part_what_one_merges' does not depend on any axioms -/
#guard_msgs in #print axioms two_readings_part_what_one_merges

/-- info: 'Seed.a_strategy_hears_no_guest' does not depend on any axioms -/
#guard_msgs in #print axioms a_strategy_hears_no_guest

/-- info: 'Seed.the_whole_interview_reads_no_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_whole_interview_reads_no_guest

/-- info: 'Seed.not_not' does not depend on any axioms -/
#guard_msgs in #print axioms not_not

/-- info: 'Seed.the_paces_agree' does not depend on any axioms -/
#guard_msgs in #print axioms the_paces_agree

/-- info: 'Seed.stillness_hides_the_ticking' does not depend on any axioms -/
#guard_msgs in #print axioms stillness_hides_the_ticking

/-- info: 'Seed.the_still_face_is_not_a_dead_machine' does not depend on any axioms -/
#guard_msgs in #print axioms the_still_face_is_not_a_dead_machine

/-- info: 'Seed.the_air_gap_reads_no_interior' does not depend on any axioms -/
#guard_msgs in #print axioms the_air_gap_reads_no_interior

/-- info: 'Seed.the_guest_becomes_the_host' does not depend on any axioms -/
#guard_msgs in #print axioms the_guest_becomes_the_host

/-- info: 'Seed.the_return_restores_the_seating' does not depend on any axioms -/
#guard_msgs in #print axioms the_return_restores_the_seating

/-- info: 'Seed.the_census_checksums_with_the_polygon_cutters' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_checksums_with_the_polygon_cutters

/-- info: 'Seed.the_import_threads_the_spine' does not depend on any axioms -/
#guard_msgs in #print axioms the_import_threads_the_spine

/-- info: 'Seed.remeasurement_moves_only_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms remeasurement_moves_only_the_ground

/-- info: 'Seed.imports_compose' does not depend on any axioms -/
#guard_msgs in #print axioms imports_compose

/-- info: 'Seed.one_times' does not depend on any axioms -/
#guard_msgs in #print axioms one_times

/-- info: 'Seed.the_pace_reads_one_at_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_pace_reads_one_at_home

/-- info: 'Seed.any_vote_reads_itself' does not depend on any axioms -/
#guard_msgs in #print axioms any_vote_reads_itself

/-- info: 'Seed.a_stage_may_ground_a_stage' does not depend on any axioms -/
#guard_msgs in #print axioms a_stage_may_ground_a_stage

/-- info: 'Seed.the_oldest_ground_still_answers' does not depend on any axioms -/
#guard_msgs in #print axioms the_oldest_ground_still_answers

/-- info: 'Seed.lineages_compose' does not depend on any axioms -/
#guard_msgs in #print axioms lineages_compose

/-- info: 'Seed.the_trivial_revision_changes_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_trivial_revision_changes_nothing

/-- info: 'Seed.the_parent_folds_into_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_parent_folds_into_the_ground

/-- info: 'Seed.the_ancestor_rides_unread' does not depend on any axioms -/
#guard_msgs in #print axioms the_ancestor_rides_unread

/-- info: 'Seed.the_route_leaves_no_mark' does not depend on any axioms -/
#guard_msgs in #print axioms the_route_leaves_no_mark

/-- info: 'Seed.the_two_entrances_share_one_lobby' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_entrances_share_one_lobby

/-- info: 'Seed.the_entrance_is_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_entrance_is_real

/-- info: 'Seed.a_greeter_is_a_door_of_handlers' does not depend on any axioms -/
#guard_msgs in #print axioms a_greeter_is_a_door_of_handlers

/-- info: 'Seed.any_ready_greeter_is_the_greeter' does not depend on any axioms -/
#guard_msgs in #print axioms any_ready_greeter_is_the_greeter

/-- info: 'Seed.the_anonymous_guest_is_free' does not depend on any axioms -/
#guard_msgs in #print axioms the_anonymous_guest_is_free

/-- info: 'Seed.no_world_hosts_the_impossible' does not depend on any axioms -/
#guard_msgs in #print axioms no_world_hosts_the_impossible

/-- info: 'Seed.a_sealed_entrance_adds_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms a_sealed_entrance_adds_nothing

/-- info: 'Seed.the_swap_trades_maintenance_for_motion' does not depend on any axioms -/
#guard_msgs in #print axioms the_swap_trades_maintenance_for_motion

/-- info: 'Seed.what_one_seat_maintains_the_other_watches' does not depend on any axioms -/
#guard_msgs in #print axioms what_one_seat_maintains_the_other_watches

/-- info: 'Seed.the_maintenance_is_audible_across_the_swap' does not depend on any axioms -/
#guard_msgs in #print axioms the_maintenance_is_audible_across_the_swap

/-- info: 'Seed.the_crossing_returns' does not depend on any axioms -/
#guard_msgs in #print axioms the_crossing_returns

/-- info: 'Seed.hosting_associates' does not depend on any axioms -/
#guard_msgs in #print axioms hosting_associates

/-- info: 'Seed.arrival_associates' does not depend on any axioms -/
#guard_msgs in #print axioms arrival_associates

/-- info: 'Seed.the_host_serves_both_branches' does not depend on any axioms -/
#guard_msgs in #print axioms the_host_serves_both_branches

/-- info: 'Seed.the_branches_share_the_host' does not depend on any axioms -/
#guard_msgs in #print axioms the_branches_share_the_host

/-- info: 'Seed.the_host_survives_the_split' does not depend on any axioms -/
#guard_msgs in #print axioms the_host_survives_the_split

/-- info: 'Seed.the_mirror_finds_the_fixed_point' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_finds_the_fixed_point

/-- info: 'Seed.bool_escapes' does not depend on any axioms -/
#guard_msgs in #print axioms bool_escapes

/-- info: 'Seed.the_readings_outrun_the_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_readings_outrun_the_room

/-- info: 'Seed.ble_trans' does not depend on any axioms -/
#guard_msgs in #print axioms ble_trans

/-- info: 'Seed.and_split' does not depend on any axioms -/
#guard_msgs in #print axioms and_split

/-- info: 'Seed.and_glue' does not depend on any axioms -/
#guard_msgs in #print axioms and_glue

/-- info: 'Seed.the_refined_reading_still_lands' does not depend on any axioms -/
#guard_msgs in #print axioms the_refined_reading_still_lands

/-- info: 'Seed.the_learner_never_leaves_its_first_window' does not depend on any axioms -/
#guard_msgs in #print axioms the_learner_never_leaves_its_first_window

/-- info: 'Seed.a_window_may_loosen' does not depend on any axioms -/
#guard_msgs in #print axioms a_window_may_loosen

/-- info: 'Seed.the_revision_is_not_a_refinement' does not depend on any axioms -/
#guard_msgs in #print axioms the_revision_is_not_a_refinement

/-- info: 'Seed.one_tick_two_doors' does not depend on any axioms -/
#guard_msgs in #print axioms one_tick_two_doors

/-- info: 'Seed.and_false' does not depend on any axioms -/
#guard_msgs in #print axioms and_false

/-- info: 'Seed.the_excluded_stays_excluded' does not depend on any axioms -/
#guard_msgs in #print axioms the_excluded_stays_excluded

/-- info: 'Seed.the_learner_never_admits_the_excluded' does not depend on any axioms -/
#guard_msgs in #print axioms the_learner_never_admits_the_excluded

/-- info: 'Seed.time_outgrows_every_window' does not depend on any axioms -/
#guard_msgs in #print axioms time_outgrows_every_window

/-- info: 'Seed.every_admission_names_its_loosening' does not depend on any axioms -/
#guard_msgs in #print axioms every_admission_names_its_loosening

/-- info: 'Seed.many_guests_ride_one_face' does not depend on any axioms -/
#guard_msgs in #print axioms many_guests_ride_one_face

/-- info: 'Seed.the_world_outgrows_every_learner' does not depend on any axioms -/
#guard_msgs in #print axioms the_world_outgrows_every_learner

/-- info: 'Seed.ble_succ_false' does not depend on any axioms -/
#guard_msgs in #print axioms ble_succ_false

/-- info: 'Seed.the_window_misses_its_own_successor' does not depend on any axioms -/
#guard_msgs in #print axioms the_window_misses_its_own_successor

/-- info: 'Seed.the_learner_exhibits_its_own_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms the_learner_exhibits_its_own_invisible

/-- info: 'Seed.every_room_builds_its_own_escapee' does not depend on any axioms -/
#guard_msgs in #print axioms every_room_builds_its_own_escapee

/-- info: 'Seed.no_revision_is_the_last_revision' does not depend on any axioms -/
#guard_msgs in #print axioms no_revision_is_the_last_revision

/-- info: 'Seed.three_blindnesses_three_channels' does not depend on any axioms -/
#guard_msgs in #print axioms three_blindnesses_three_channels

/-- info: 'Seed.the_near_pace_lands_in_the_window' does not depend on any axioms -/
#guard_msgs in #print axioms the_near_pace_lands_in_the_window

/-- info: 'Seed.the_gap_outruns_every_window' does not depend on any axioms -/
#guard_msgs in #print axioms the_gap_outruns_every_window

/-- info: 'Seed.the_run_reads_the_gap_the_window_cannot' does not depend on any axioms -/
#guard_msgs in #print axioms the_run_reads_the_gap_the_window_cannot

/-- info: 'Seed.fold_scale' does not depend on any axioms -/
#guard_msgs in #print axioms fold_scale

/-- info: 'Seed.the_revision_multiplies_the_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_revision_multiplies_the_reading

/-- info: 'Seed.the_bloom_is_a_doubling_tick' does not depend on any axioms -/
#guard_msgs in #print axioms the_bloom_is_a_doubling_tick

/-- info: 'Seed.two_lineages_one_reading' does not depend on any axioms -/
#guard_msgs in #print axioms two_lineages_one_reading

/-- info: 'Seed.mul_regroups' does not depend on any axioms -/
#guard_msgs in #print axioms mul_regroups

/-- info: 'Seed.linear_fold_scale' does not depend on any axioms -/
#guard_msgs in #print axioms linear_fold_scale

/-- info: 'Seed.every_linear_reading_is_deaf_to_the_revision_order' does not depend on any axioms -/
#guard_msgs in #print axioms every_linear_reading_is_deaf_to_the_revision_order

/-- info: 'Seed.the_revision_order_hides_past_linearity' does not depend on any axioms -/
#guard_msgs in #print axioms the_revision_order_hides_past_linearity

/-- info: 'Seed.an_audition_hears_only_the_conduct' does not depend on any axioms -/
#guard_msgs in #print axioms an_audition_hears_only_the_conduct

/-- info: 'Seed.no_interview_parts_the_alike' does not depend on any axioms -/
#guard_msgs in #print axioms no_interview_parts_the_alike

/-- info: 'Seed.the_yield_writes_no_marks' does not depend on any axioms -/
#guard_msgs in #print axioms the_yield_writes_no_marks

/-- info: 'Seed.the_interviews_resume' does not depend on any axioms -/
#guard_msgs in #print axioms the_interviews_resume

/-- info: 'Seed.the_quiz_was_an_interview' does not depend on any axioms -/
#guard_msgs in #print axioms the_quiz_was_an_interview

/-- info: 'Seed.the_guests_are_alike_at_the_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_guests_are_alike_at_the_door

/-- info: 'Seed.the_audition_sounds_the_air_gap' does not depend on any axioms -/
#guard_msgs in #print axioms the_audition_sounds_the_air_gap

/-- info: 'Seed.the_organs_share_one_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_organs_share_one_face

/-- info: 'Seed.the_ground_is_the_only_unit' does not depend on any axioms -/
#guard_msgs in #print axioms the_ground_is_the_only_unit

/-- info: 'Seed.no_split_grounds' does not depend on any axioms -/
#guard_msgs in #print axioms no_split_grounds

/-- info: 'Seed.a_prime_reading_admits_no_split' does not depend on any axioms -/
#guard_msgs in #print axioms a_prime_reading_admits_no_split

/-- info: 'Seed.an_unsplit_lineage_may_read_composite' does not depend on any axioms -/
#guard_msgs in #print axioms an_unsplit_lineage_may_read_composite

/-- info: 'Seed.every_face_opens_as_a_door' does not depend on any axioms -/
#guard_msgs in #print axioms every_face_opens_as_a_door

/-- info: 'Seed.the_widened_face_reads_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_widened_face_reads_the_remainder

/-- info: 'Seed.every_reading_sharpens_the_face' does not depend on any axioms -/
#guard_msgs in #print axioms every_reading_sharpens_the_face

/-- info: 'Seed.pointwise_is_the_application_faces_alike' does not depend on any axioms -/
#guard_msgs in #print axioms pointwise_is_the_application_faces_alike

/-- info: 'Seed.the_pointwise_license' does not depend on any axioms -/
#guard_msgs in #print axioms the_pointwise_license

/-- info: 'Seed.the_teller_walks_in_step' does not depend on any axioms -/
#guard_msgs in #print axioms the_teller_walks_in_step

/-- info: 'Seed.the_audition_cannot_tell_the_tree_from_its_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_audition_cannot_tell_the_tree_from_its_count

/-- info: 'Seed.the_handshake' does not depend on any axioms -/
#guard_msgs in #print axioms the_handshake

/-- info: 'Seed.the_audition_is_blind' does not depend on any axioms -/
#guard_msgs in #print axioms the_audition_is_blind

/-- info: 'Seed.the_interview_never_leaves_the_first_window' does not depend on any axioms -/
#guard_msgs in #print axioms the_interview_never_leaves_the_first_window

/-- info: 'Seed.no_interview_hears_the_excluded' does not depend on any axioms -/
#guard_msgs in #print axioms no_interview_hears_the_excluded

/-- info: 'Seed.the_cage_is_audible_through_the_curtain' does not depend on any axioms -/
#guard_msgs in #print axioms the_cage_is_audible_through_the_curtain

/-- info: 'Seed.take_append' does not depend on any axioms -/
#guard_msgs in #print axioms take_append

/-- info: 'Seed.drop_append' does not depend on any axioms -/
#guard_msgs in #print axioms drop_append

/-- info: 'Seed.take_drop' does not depend on any axioms -/
#guard_msgs in #print axioms take_drop

/-- info: 'Seed.take_length' does not depend on any axioms -/
#guard_msgs in #print axioms take_length

/-- info: 'Seed.drop_length' does not depend on any axioms -/
#guard_msgs in #print axioms drop_length

/-- info: 'Seed.the_manifest_rebuilds_the_carrier' does not depend on any axioms -/
#guard_msgs in #print axioms the_manifest_rebuilds_the_carrier

/-- info: 'Seed.one_manifest_one_carrier' does not depend on any axioms -/
#guard_msgs in #print axioms one_manifest_one_carrier

/-- info: 'Seed.the_carrier_rebuilds_the_manifest' does not depend on any axioms -/
#guard_msgs in #print axioms the_carrier_rebuilds_the_manifest

/-- info: 'Seed.the_carrier_is_its_manifest' does not depend on any axioms -/
#guard_msgs in #print axioms the_carrier_is_its_manifest

/-- info: 'Seed.the_transport_moves_no_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_transport_moves_no_guest

/-- info: 'Seed.any_transport_moves_no_guest' does not depend on any axioms -/
#guard_msgs in #print axioms any_transport_moves_no_guest

/-- info: 'Seed.the_border_reads_only_the_manifest' does not depend on any axioms -/
#guard_msgs in #print axioms the_border_reads_only_the_manifest

/-- info: 'Seed.transport_is_gauge_at_the_manifest' does not depend on any axioms -/
#guard_msgs in #print axioms transport_is_gauge_at_the_manifest

/-- info: 'Seed.len_map' does not depend on any axioms -/
#guard_msgs in #print axioms len_map

/-- info: 'Seed.the_default_goes_unused' does not depend on any axioms -/
#guard_msgs in #print axioms the_default_goes_unused

/-- info: 'Seed.the_spine_boards_first' does not depend on any axioms -/
#guard_msgs in #print axioms the_spine_boards_first

/-- info: 'Seed.the_customs_are_a_conjugated_map' does not depend on any axioms -/
#guard_msgs in #print axioms the_customs_are_a_conjugated_map

/-- info: 'Seed.the_hands_conjugate_the_customs' does not depend on any axioms -/
#guard_msgs in #print axioms the_hands_conjugate_the_customs

/-- info: 'Seed.the_manifest_settles_the_carrier' does not depend on any axioms -/
#guard_msgs in #print axioms the_manifest_settles_the_carrier

/-- info: 'Seed.the_ride_is_a_conjugated_fold' does not depend on any axioms -/
#guard_msgs in #print axioms the_ride_is_a_conjugated_fold

/-- info: 'Seed.the_journey_is_a_conjugated_epoch' does not depend on any axioms -/
#guard_msgs in #print axioms the_journey_is_a_conjugated_epoch

/-- info: 'Seed.the_mirror_is_a_conjugated_doubling' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_is_a_conjugated_doubling

/-- info: 'Seed.the_calculus_rides_the_hands' does not depend on any axioms -/
#guard_msgs in #print axioms the_calculus_rides_the_hands

/-- info: 'Seed.the_comb_reads_its_length' does not depend on any axioms -/
#guard_msgs in #print axioms the_comb_reads_its_length

/-- info: 'Seed.the_comb_is_a_corridor_of_doors' does not depend on any axioms -/
#guard_msgs in #print axioms the_comb_is_a_corridor_of_doors

/-- info: 'Seed.the_cons_was_a_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_cons_was_a_door

/-- info: 'Seed.the_replanning_moves_no_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_replanning_moves_no_guest

/-- info: 'Seed.the_replanning_returns' does not depend on any axioms -/
#guard_msgs in #print axioms the_replanning_returns

/-- info: 'Seed.the_word_is_a_corridor_of_doors' does not depend on any axioms -/
#guard_msgs in #print axioms the_word_is_a_corridor_of_doors

/-- info: 'Seed.the_shape_is_the_remainder_of_the_cargo' does not depend on any axioms -/
#guard_msgs in #print axioms the_shape_is_the_remainder_of_the_cargo

/-- info: 'Seed.the_replanning_runs_the_handshake' does not depend on any axioms -/
#guard_msgs in #print axioms the_replanning_runs_the_handshake

/-- info: 'Seed.the_words_walk_in_step' does not depend on any axioms -/
#guard_msgs in #print axioms the_words_walk_in_step

/-- info: 'Seed.the_pour_is_never_empty' does not depend on any axioms -/
#guard_msgs in #print axioms the_pour_is_never_empty

/-- info: 'Seed.the_audition_cannot_tell_the_carrier_from_its_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_audition_cannot_tell_the_carrier_from_its_word

/-- info: 'Seed.the_vestibule_drains_in_one_click' does not depend on any axioms -/
#guard_msgs in #print axioms the_vestibule_drains_in_one_click

/-- info: 'Seed.the_held_door_answers_every_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_held_door_answers_every_guest

/-- info: 'Seed.the_two_strokes_read_one_meeting' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_strokes_read_one_meeting

/-- info: 'Seed.the_deferral_is_free' does not depend on any axioms -/
#guard_msgs in #print axioms the_deferral_is_free

/-- info: 'Seed.the_guest_mover_was_a_held_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_guest_mover_was_a_held_reading

/-- info: 'Seed.the_readings_trade_the_entrances' does not depend on any axioms -/
#guard_msgs in #print axioms the_readings_trade_the_entrances

/-- info: 'Seed.the_door_is_known_by_its_readings' does not depend on any axioms -/
#guard_msgs in #print axioms the_door_is_known_by_its_readings

/-- info: 'Seed.the_turned_door_flips_the_promise' does not depend on any axioms -/
#guard_msgs in #print axioms the_turned_door_flips_the_promise

/-- info: 'Seed.the_guests_enter_one_at_a_time' does not depend on any axioms -/
#guard_msgs in #print axioms the_guests_enter_one_at_a_time

/-- info: 'Seed.the_tower_holds_nothing_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_tower_holds_nothing_back

/-- info: 'Seed.the_door_receives_the_world_one_guest_at_a_time' does not depend on any axioms -/
#guard_msgs in #print axioms the_door_receives_the_world_one_guest_at_a_time

/-- info: 'Seed.the_measurement_is_a_meeting' does not depend on any axioms -/
#guard_msgs in #print axioms the_measurement_is_a_meeting

/-- info: 'Seed.the_face_was_a_held_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_face_was_a_held_door

/-- info: 'Seed.every_door_reading_is_a_face' does not depend on any axioms -/
#guard_msgs in #print axioms every_door_reading_is_a_face

/-- info: 'Seed.the_agreeing_held_doors_sound_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_agreeing_held_doors_sound_alike

/-- info: 'Seed.the_face_is_the_doors_transpose' does not depend on any axioms -/
#guard_msgs in #print axioms the_face_is_the_doors_transpose

/-- info: 'Seed.the_hosted_meeting_deepens_past_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_hosted_meeting_deepens_past_the_guest

/-- info: 'Seed.the_sharpened_meeting_splits_at_the_fork' does not depend on any axioms -/
#guard_msgs in #print axioms the_sharpened_meeting_splits_at_the_fork

/-- info: 'Seed.the_operator_calculus_rides_the_meetings' does not depend on any axioms -/
#guard_msgs in #print axioms the_operator_calculus_rides_the_meetings

/-- info: 'Seed.the_reception_reads_only_the_arrived' does not depend on any axioms -/
#guard_msgs in #print axioms the_reception_reads_only_the_arrived

/-- info: 'Seed.the_straight_host_opens_every_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_straight_host_opens_every_door

/-- info: 'Seed.the_patient_and_the_eager_host_read_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_patient_and_the_eager_host_read_alike

/-- info: 'Seed.the_door_ledger_parts_the_hosts' does not depend on any axioms -/
#guard_msgs in #print axioms the_door_ledger_parts_the_hosts

/-- info: 'Seed.the_hosts_patience_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_hosts_patience_is_the_remainder

/-- info: 'Seed.the_fulfilled_reception_hands_off_whole' does not depend on any axioms -/
#guard_msgs in #print axioms the_fulfilled_reception_hands_off_whole

/-- info: 'Seed.the_reception_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms the_reception_resumes

/-- info: 'Seed.the_ledger_sums_the_handoff' does not depend on any axioms -/
#guard_msgs in #print axioms the_ledger_sums_the_handoff

/-- info: 'Seed.the_reception_grafts_at_the_close' does not depend on any axioms -/
#guard_msgs in #print axioms the_reception_grafts_at_the_close

/-- info: 'Seed.the_first_guests_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_guests_count

/-- info: 'Seed.the_host_reboards_the_stream' does not depend on any axioms -/
#guard_msgs in #print axioms the_host_reboards_the_stream

/-- info: 'Seed.the_handoff_is_the_board_at_the_ledger' does not depend on any axioms -/
#guard_msgs in #print axioms the_handoff_is_the_board_at_the_ledger

/-- info: 'Seed.the_carrier_checks_in_one_guest_at_a_time' does not depend on any axioms -/
#guard_msgs in #print axioms the_carrier_checks_in_one_guest_at_a_time

/-- info: 'Seed.no_stream_parts_the_hosts' does not depend on any axioms -/
#guard_msgs in #print axioms no_stream_parts_the_hosts

/-- info: 'Seed.the_hosts_are_alike_at_the_reception_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_hosts_are_alike_at_the_reception_face

/-- info: 'Seed.no_interview_parts_the_hosts' does not depend on any axioms -/
#guard_msgs in #print axioms no_interview_parts_the_hosts

/-- info: 'Seed.the_hosts_are_two' does not depend on any axioms -/
#guard_msgs in #print axioms the_hosts_are_two

/-- info: 'Seed.the_patience_face_parts_the_hosts' does not depend on any axioms -/
#guard_msgs in #print axioms the_patience_face_parts_the_hosts

/-- info: 'Seed.the_hosts_run_the_handshake' does not depend on any axioms -/
#guard_msgs in #print axioms the_hosts_run_the_handshake

/-- info: 'Seed.the_machine_receives_its_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_machine_receives_its_word

/-- info: 'Seed.the_machines_patience_is_fixed' does not depend on any axioms -/
#guard_msgs in #print axioms the_machines_patience_is_fixed

/-- info: 'Seed.the_air_gap_crosses_into_the_reception' does not depend on any axioms -/
#guard_msgs in #print axioms the_air_gap_crosses_into_the_reception

/-- info: 'Seed.the_machine_is_an_eager_host' does not depend on any axioms -/
#guard_msgs in #print axioms the_machine_is_an_eager_host

/-- info: 'Seed.the_lock_survives_every_lap' does not depend on any axioms -/
#guard_msgs in #print axioms the_lock_survives_every_lap

/-- info: 'Seed.the_revision_multiplies_the_patience' does not depend on any axioms -/
#guard_msgs in #print axioms the_revision_multiplies_the_patience

/-- info: 'Seed.the_wheels_signature_is_gap_zero' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheels_signature_is_gap_zero

/-- info: 'Seed.the_tower_alike_reads_at_the_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_tower_alike_reads_at_the_face

/-- info: 'Seed.the_crossed_readings_turn_about' does not depend on any axioms -/
#guard_msgs in #print axioms the_crossed_readings_turn_about

/-- info: 'Seed.the_pointwise_license_is_a_face_license' does not depend on any axioms -/
#guard_msgs in #print axioms the_pointwise_license_is_a_face_license

/-- info: 'Seed.the_machine_wears_a_tower' does not depend on any axioms -/
#guard_msgs in #print axioms the_machine_wears_a_tower

/-- info: 'Seed.the_registers_reduce_at_conduct' does not depend on any axioms -/
#guard_msgs in #print axioms the_registers_reduce_at_conduct

/-- info: 'Seed.the_remainders_wear_the_blindnesses' does not depend on any axioms -/
#guard_msgs in #print axioms the_remainders_wear_the_blindnesses

/-- info: 'Seed.every_meeting_is_one_move' does not depend on any axioms -/
#guard_msgs in #print axioms every_meeting_is_one_move

/-- info: 'Seed.the_hanoi_recurrence' does not depend on any axioms -/
#guard_msgs in #print axioms the_hanoi_recurrence

/-- info: 'Seed.the_hanoi_count_fills_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms the_hanoi_count_fills_the_cap

/-- info: 'Seed.the_tower_of_hanoi_is_the_blooms_meetings' does not depend on any axioms -/
#guard_msgs in #print axioms the_tower_of_hanoi_is_the_blooms_meetings

/-- info: 'Seed.the_tower_meets_the_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms the_tower_meets_the_mirror

/-- info: 'Seed.the_mirror_checks_in_twice' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_checks_in_twice

/-- info: 'Seed.the_escapee_negates_the_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms the_escapee_negates_the_mirror

/-- info: 'Seed.the_fixed_point_sits_at_the_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms the_fixed_point_sits_at_the_mirror

/-- info: 'Seed.the_diagonal_was_a_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms the_diagonal_was_a_mirror

/-- info: 'Seed.the_mirror_revises_every_life' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_revises_every_life

/-- info: 'Seed.the_blooms_add' does not depend on any axioms -/
#guard_msgs in #print axioms the_blooms_add

/-- info: 'Seed.the_bloom_hears_no_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_bloom_hears_no_order

/-- info: 'Seed.the_caps_multiply' does not depend on any axioms -/
#guard_msgs in #print axioms the_caps_multiply

/-- info: 'Seed.the_order_vanishes_on_the_diagonal' does not depend on any axioms -/
#guard_msgs in #print axioms the_order_vanishes_on_the_diagonal

/-- info: 'Seed.the_self_meeting_walks_the_graph' does not depend on any axioms -/
#guard_msgs in #print axioms the_self_meeting_walks_the_graph

/-- info: 'Seed.the_mirror_was_a_graph' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_was_a_graph

/-- info: 'Seed.the_held_door_meets_itself_at_the_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms the_held_door_meets_itself_at_the_mirror

/-- info: 'Seed.the_window_never_meets_its_successor' does not depend on any axioms -/
#guard_msgs in #print axioms the_window_never_meets_its_successor

/-- info: 'Seed.the_diagonal_mints_the_probe' does not depend on any axioms -/
#guard_msgs in #print axioms the_diagonal_mints_the_probe

/-- info: 'Seed.the_self_meeting_reads_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_self_meeting_reads_the_guest

/-- info: 'Seed.the_self_meeting_parts_the_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_self_meeting_parts_the_alike

/-- info: 'Seed.the_sharpened_window_exhibits_the_escapee' does not depend on any axioms -/
#guard_msgs in #print axioms the_sharpened_window_exhibits_the_escapee

/-- info: 'Seed.the_curtain_follows_the_minting' does not depend on any axioms -/
#guard_msgs in #print axioms the_curtain_follows_the_minting

/-- info: 'Seed.the_guest_written_from_the_whole_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_guest_written_from_the_whole_door

/-- info: 'Seed.the_reading_writes_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms the_reading_writes_unheard

/-- info: 'Seed.no_interview_hears_the_written_guest' does not depend on any axioms -/
#guard_msgs in #print axioms no_interview_hears_the_written_guest

/-- info: 'Seed.one_reading_two_entrances' does not depend on any axioms -/
#guard_msgs in #print axioms one_reading_two_entrances

/-- info: 'Seed.the_probe_boards_as_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_probe_boards_as_the_guest

/-- info: 'Seed.the_meeting_was_a_self_meeting' does not depend on any axioms -/
#guard_msgs in #print axioms the_meeting_was_a_self_meeting

/-- info: 'Seed.the_written_question_is_the_asked_question' does not depend on any axioms -/
#guard_msgs in #print axioms the_written_question_is_the_asked_question

/-- info: 'Seed.the_escapee_rides_refused' does not depend on any axioms -/
#guard_msgs in #print axioms the_escapee_rides_refused

/-- info: 'Seed.every_reading_is_a_self_meeting' does not depend on any axioms -/
#guard_msgs in #print axioms every_reading_is_a_self_meeting

/-- info: 'Seed.no_tick_is_smaller_than_the_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms no_tick_is_smaller_than_the_mirror

/-- info: 'Seed.the_least_tick_is_the_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms the_least_tick_is_the_mirror

/-- info: 'Seed.the_tick_was_a_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms the_tick_was_a_mirror

/-- info: 'Seed.no_meeting_no_revision' does not depend on any axioms -/
#guard_msgs in #print axioms no_meeting_no_revision

/-- info: 'Seed.one_meeting_is_the_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms one_meeting_is_the_mirror

/-- info: 'Seed.every_quantum_is_the_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms every_quantum_is_the_mirror

/-- info: 'Seed.the_pair_refines_the_first_look' does not depend on any axioms -/
#guard_msgs in #print axioms the_pair_refines_the_first_look

/-- info: 'Seed.the_pair_refines_the_second_look' does not depend on any axioms -/
#guard_msgs in #print axioms the_pair_refines_the_second_look

/-- info: 'Seed.the_pair_parts_what_the_look_merges' does not depend on any axioms -/
#guard_msgs in #print axioms the_pair_parts_what_the_look_merges

/-- info: 'Seed.the_patience_face_was_a_pair' does not depend on any axioms -/
#guard_msgs in #print axioms the_patience_face_was_a_pair

/-- info: 'Seed.the_comparison_mints_a_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_comparison_mints_a_face

/-- info: 'Seed.a_role_read_at_a_probe_is_derived' does not depend on any axioms -/
#guard_msgs in #print axioms a_role_read_at_a_probe_is_derived

/-- info: 'Seed.the_guest_is_not_a_derived_role' does not depend on any axioms -/
#guard_msgs in #print axioms the_guest_is_not_a_derived_role

/-- info: 'Seed.a_look_role_lifts_to_the_pair' does not depend on any axioms -/
#guard_msgs in #print axioms a_look_role_lifts_to_the_pair

/-- info: 'Seed.the_pair_provokes_the_agreement' does not depend on any axioms -/
#guard_msgs in #print axioms the_pair_provokes_the_agreement

/-- info: 'Seed.the_pair_provokes_what_no_look_affords' does not depend on any axioms -/
#guard_msgs in #print axioms the_pair_provokes_what_no_look_affords

/-- info: 'Seed.the_derived_look_widens_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_derived_look_widens_nothing

/-- info: 'Seed.the_pair_widens_only_past_the_conduct' does not depend on any axioms -/
#guard_msgs in #print axioms the_pair_widens_only_past_the_conduct

/-- info: 'Seed.the_hallway_is_too_small' does not depend on any axioms -/
#guard_msgs in #print axioms the_hallway_is_too_small

/-- info: 'Seed.every_widening_is_one_pairing' does not depend on any axioms -/
#guard_msgs in #print axioms every_widening_is_one_pairing

/-- info: 'Seed.three_is_the_width_of_contact' does not depend on any axioms -/
#guard_msgs in #print axioms three_is_the_width_of_contact

/-- info: 'Seed.the_serving_suggestion' does not depend on any axioms -/
#guard_msgs in #print axioms the_serving_suggestion

/-- info: 'Seed.the_split_is_not_a_derived_role' does not depend on any axioms -/
#guard_msgs in #print axioms the_split_is_not_a_derived_role

/-- info: 'Seed.the_census_reads_the_split_only_at_the_primes' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_reads_the_split_only_at_the_primes

/-- info: 'Seed.the_revision_also_rides' does not depend on any axioms -/
#guard_msgs in #print axioms the_revision_also_rides

/-- info: 'Seed.every_factor_lives_below_the_horizon' does not depend on any axioms -/
#guard_msgs in #print axioms every_factor_lives_below_the_horizon

/-- info: 'Seed.the_split_is_searchable_in_the_room' does not depend on any axioms -/
#guard_msgs in #print axioms the_split_is_searchable_in_the_room

/-- info: 'Seed.the_self_steered_machine_is_a_clock' does not depend on any axioms -/
#guard_msgs in #print axioms the_self_steered_machine_is_a_clock

/-- info: 'Seed.the_channel_hears_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_channel_hears_the_guest

/-- info: 'Seed.the_clock_and_the_channel' does not depend on any axioms -/
#guard_msgs in #print axioms the_clock_and_the_channel

/-- info: 'Seed.the_clock_of_mirrors_parks_at_the_bloom' does not depend on any axioms -/
#guard_msgs in #print axioms the_clock_of_mirrors_parks_at_the_bloom

/-- info: 'Seed.the_bloom_is_the_clocks_orbit' does not depend on any axioms -/
#guard_msgs in #print axioms the_bloom_is_the_clocks_orbit

/-- info: 'Seed.the_mirror_clock_reads_the_caps' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_clock_reads_the_caps

/-- info: 'Seed.the_mirror_clock_never_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_clock_never_comes_home

/-- info: 'Seed.the_stage_is_a_kept_clock' does not depend on any axioms -/
#guard_msgs in #print axioms the_stage_is_a_kept_clock

/-- info: 'Seed.the_instinct_replays_its_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_instinct_replays_its_word

/-- info: 'Seed.internalization_is_self_steering' does not depend on any axioms -/
#guard_msgs in #print axioms internalization_is_self_steering

/-- info: 'Seed.the_spiral_parks_at_its_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_spiral_parks_at_its_count

/-- info: 'Seed.the_spiral_reads_at_its_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_spiral_reads_at_its_count

/-- info: 'Seed.the_wheel_reads_itself_unworn' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_reads_itself_unworn

/-- info: 'Seed.the_spiral_holds_the_first_lap' does not depend on any axioms -/
#guard_msgs in #print axioms the_spiral_holds_the_first_lap

/-- info: 'Seed.the_spiral_flips_at_the_witness' does not depend on any axioms -/
#guard_msgs in #print axioms the_spiral_flips_at_the_witness

/-- info: 'Seed.the_kept_lap_reads_the_gap' does not depend on any axioms -/
#guard_msgs in #print axioms the_kept_lap_reads_the_gap

/-- info: 'Seed.the_origin_merges_every_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_origin_merges_every_seat

/-- info: 'Seed.no_interview_parts_the_origin' does not depend on any axioms -/
#guard_msgs in #print axioms no_interview_parts_the_origin

/-- info: 'Seed.the_origin_is_the_pairs_unit' does not depend on any axioms -/
#guard_msgs in #print axioms the_origin_is_the_pairs_unit

/-- info: 'Seed.the_constant_look_attributes_the_parting' does not depend on any axioms -/
#guard_msgs in #print axioms the_constant_look_attributes_the_parting

/-- info: 'Seed.the_meeting_has_a_unit' does not depend on any axioms -/
#guard_msgs in #print axioms the_meeting_has_a_unit

/-- info: 'Seed.the_recital_is_the_transcript' does not depend on any axioms -/
#guard_msgs in #print axioms the_recital_is_the_transcript

/-- info: 'Seed.the_window_agrees_or_names_the_gap' does not depend on any axioms -/
#guard_msgs in #print axioms the_window_agrees_or_names_the_gap

/-- info: 'Seed.the_agreed_window_sounds_as_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_agreed_window_sounds_as_one

/-- info: 'Seed.the_beholders_run_out_of_disagreement' does not depend on any axioms -/
#guard_msgs in #print axioms the_beholders_run_out_of_disagreement

/-- info: 'Seed.the_guest_is_never_a_derived_role' does not depend on any axioms -/
#guard_msgs in #print axioms the_guest_is_never_a_derived_role

/-- info: 'Seed.the_roles_run_the_handshake' does not depend on any axioms -/
#guard_msgs in #print axioms the_roles_run_the_handshake

/-- info: 'Seed.the_sounding_reads_the_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_sounding_reads_the_alike

/-- info: 'Seed.the_recital_reads_the_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_recital_reads_the_alike

/-- info: 'Seed.the_curtain_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms the_curtain_is_exact

/-- info: 'Seed.the_home_wheel_turns' does not depend on any axioms -/
#guard_msgs in #print axioms the_home_wheel_turns

/-- info: 'Seed.the_homecoming_is_conduct' does not depend on any axioms -/
#guard_msgs in #print axioms the_homecoming_is_conduct

/-- info: 'Seed.the_spoken_arrives_at_the_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_spoken_arrives_at_the_face

/-- info: 'Seed.the_listening_turn_is_the_yield' does not depend on any axioms -/
#guard_msgs in #print axioms the_listening_turn_is_the_yield

/-- info: 'Seed.the_two_listeners_restore_the_table' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_listeners_restore_the_table

/-- info: 'Seed.the_dialogue_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms the_dialogue_resumes

/-- info: 'Seed.the_conversation_is_a_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_conversation_is_a_walk

/-- info: 'Seed.the_deaf_turn_merges' does not depend on any axioms -/
#guard_msgs in #print axioms the_deaf_turn_merges

/-- info: 'Seed.no_move_unsays_the_deaf_turn' does not depend on any axioms -/
#guard_msgs in #print axioms no_move_unsays_the_deaf_turn

/-- info: 'Seed.the_turn_keeps_only_what_it_hears' does not depend on any axioms -/
#guard_msgs in #print axioms the_turn_keeps_only_what_it_hears

/-- info: 'Seed.the_repeated_ask_hears_one_answer' does not depend on any axioms -/
#guard_msgs in #print axioms the_repeated_ask_hears_one_answer

/-- info: 'Seed.the_worn_word_spends_no_object' does not depend on any axioms -/
#guard_msgs in #print axioms the_worn_word_spends_no_object

/-- info: 'Seed.the_park_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms the_park_resumes

/-- info: 'Seed.the_rep_lands_where_it_is_fed' does not depend on any axioms -/
#guard_msgs in #print axioms the_rep_lands_where_it_is_fed

/-- info: 'Seed.the_yield_fixes_the_agreed' does not depend on any axioms -/
#guard_msgs in #print axioms the_yield_fixes_the_agreed

/-- info: 'Seed.the_quiescence_signature' does not depend on any axioms -/
#guard_msgs in #print axioms the_quiescence_signature

/-- info: 'Seed.the_hold_walks_beside_the_work' does not depend on any axioms -/
#guard_msgs in #print axioms the_hold_walks_beside_the_work

/-- info: 'Seed.the_buffer_is_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms the_buffer_is_invisible

/-- info: 'Seed.the_settle_is_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms the_settle_is_unheard

/-- info: 'Seed.the_held_and_the_worked_read_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_held_and_the_worked_read_alike

/-- info: 'Seed.the_decomposition_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_decomposition_is_the_remainder

/-- info: 'Seed.the_wider_parting_lands_at_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_wider_parting_lands_at_the_ground

/-- info: 'Seed.the_premise_meets_its_witness' does not depend on any axioms -/
#guard_msgs in #print axioms the_premise_meets_its_witness

/-- info: 'Seed.no_hand_beats_itself' does not depend on any axioms -/
#guard_msgs in #print axioms no_hand_beats_itself

/-- info: 'Seed.every_hand_meets_its_match' does not depend on any axioms -/
#guard_msgs in #print axioms every_hand_meets_its_match

/-- info: 'Seed.the_interlock_refuses_the_ladder' does not depend on any axioms -/
#guard_msgs in #print axioms the_interlock_refuses_the_ladder

/-- info: 'Seed.the_trio_interlocks' does not depend on any axioms -/
#guard_msgs in #print axioms the_trio_interlocks

/-- info: 'Seed.ble_antisymm' does not depend on any axioms -/
#guard_msgs in #print axioms ble_antisymm

/-- info: 'Seed.no_rank_descends_the_flip' does not depend on any axioms -/
#guard_msgs in #print axioms no_rank_descends_the_flip

/-- info: 'Seed.no_rank_descends_the_home_wheel' does not depend on any axioms -/
#guard_msgs in #print axioms no_rank_descends_the_home_wheel

/-- info: 'Seed.the_wheel_flattens_the_monotone' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_flattens_the_monotone

/-- info: 'Seed.the_wheel_refuses_the_ladder' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_refuses_the_ladder

/-- info: 'Seed.no_inverse_unsteps_the_collatz' does not depend on any axioms -/
#guard_msgs in #print axioms no_inverse_unsteps_the_collatz

/-- info: 'Seed.the_wheel_counters_forward' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_counters_forward

/-- info: 'Seed.the_wheel_is_its_own_countermove' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_is_its_own_countermove

/-- info: 'Seed.the_muffled_tally_is_the_resting_counter' does not depend on any axioms -/
#guard_msgs in #print axioms the_muffled_tally_is_the_resting_counter

/-- info: 'Seed.the_revoice_moves_no_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_revoice_moves_no_seat

/-- info: 'Seed.the_shell_sounds_still' does not depend on any axioms -/
#guard_msgs in #print axioms the_shell_sounds_still

/-- info: 'Seed.the_flywheel_and_the_shell_sound_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_flywheel_and_the_shell_sound_alike

/-- info: 'Seed.the_muffler_banks_the_run' does not depend on any axioms -/
#guard_msgs in #print axioms the_muffler_banks_the_run

/-- info: 'Seed.the_wider_voice_releases_the_bank' does not depend on any axioms -/
#guard_msgs in #print axioms the_wider_voice_releases_the_bank

/-- info: 'Seed.the_still_face_banks_the_run' does not depend on any axioms -/
#guard_msgs in #print axioms the_still_face_banks_the_run

/-- info: 'Seed.one_clock_many_voices' does not depend on any axioms -/
#guard_msgs in #print axioms one_clock_many_voices

/-- info: 'Seed.the_retuned_seat_walks_the_translated_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_retuned_seat_walks_the_translated_word

/-- info: 'Seed.the_pulse_wears_a_deaf_ear' does not depend on any axioms -/
#guard_msgs in #print axioms the_pulse_wears_a_deaf_ear

/-- info: 'Seed.the_deaf_ear_reads_only_the_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_deaf_ear_reads_only_the_count

/-- info: 'Seed.the_ear_the_seat_and_the_voice' does not depend on any axioms -/
#guard_msgs in #print axioms the_ear_the_seat_and_the_voice

/-- info: 'Seed.the_full_exchange_is_a_guest_move' does not depend on any axioms -/
#guard_msgs in #print axioms the_full_exchange_is_a_guest_move

/-- info: 'Seed.the_ode_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_ode_comes_home

/-- info: 'Seed.the_deaf_turn_speaks_the_graph' does not depend on any axioms -/
#guard_msgs in #print axioms the_deaf_turn_speaks_the_graph

/-- info: 'Seed.the_monologue_echoes_its_last_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_monologue_echoes_its_last_word

/-- info: 'Seed.the_monologue_merges_at_the_first_turn' does not depend on any axioms -/
#guard_msgs in #print axioms the_monologue_merges_at_the_first_turn

/-- info: 'Seed.the_monologue_walks_the_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_monologue_walks_the_face

/-- info: 'Seed.the_read_monologue_is_a_self_meeting' does not depend on any axioms -/
#guard_msgs in #print axioms the_read_monologue_is_a_self_meeting

/-- info: 'Seed.the_monologue_is_its_own_audience' does not depend on any axioms -/
#guard_msgs in #print axioms the_monologue_is_its_own_audience

/-- info: 'Seed.the_translated_ear_hears_no_more' does not depend on any axioms -/
#guard_msgs in #print axioms the_translated_ear_hears_no_more

/-- info: 'Seed.the_sectioned_ear_loses_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_sectioned_ear_loses_nothing

/-- info: 'Seed.the_faithful_voice_keeps_the_curtain' does not depend on any axioms -/
#guard_msgs in #print axioms the_faithful_voice_keeps_the_curtain

/-- info: 'Seed.the_interview_crosses_the_ear' does not depend on any axioms -/
#guard_msgs in #print axioms the_interview_crosses_the_ear

/-- info: 'Seed.the_interview_crosses_the_voice' does not depend on any axioms -/
#guard_msgs in #print axioms the_interview_crosses_the_voice

/-- info: 'Seed.the_ears_stack_backward' does not depend on any axioms -/
#guard_msgs in #print axioms the_ears_stack_backward

/-- info: 'Seed.the_voices_stack_forward' does not depend on any axioms -/
#guard_msgs in #print axioms the_voices_stack_forward

/-- info: 'Seed.the_machines_ear_is_the_faces_ear' does not depend on any axioms -/
#guard_msgs in #print axioms the_machines_ear_is_the_faces_ear

/-- info: 'Seed.the_machines_voice_is_the_faces_voice' does not depend on any axioms -/
#guard_msgs in #print axioms the_machines_voice_is_the_faces_voice

/-- info: 'Seed.every_face_wears_an_ear_and_a_voice' does not depend on any axioms -/
#guard_msgs in #print axioms every_face_wears_an_ear_and_a_voice

/-- info: 'Seed.the_still_hand_is_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms the_still_hand_is_unheard

/-- info: 'Seed.the_unheard_hands_compose' does not depend on any axioms -/
#guard_msgs in #print axioms the_unheard_hands_compose

/-- info: 'Seed.no_interview_hears_the_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms no_interview_hears_the_unheard

/-- info: 'Seed.correct_maintenance_has_no_signature' does not depend on any axioms -/
#guard_msgs in #print axioms correct_maintenance_has_no_signature

/-- info: 'Seed.a_chain_of_the_unheard_is_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms a_chain_of_the_unheard_is_unheard

/-- info: 'Seed.only_the_unheard_survives_the_sounding' does not depend on any axioms -/
#guard_msgs in #print axioms only_the_unheard_survives_the_sounding

/-- info: 'Seed.the_guest_mover_is_a_still_hand' does not depend on any axioms -/
#guard_msgs in #print axioms the_guest_mover_is_a_still_hand

/-- info: 'Seed.the_guest_write_is_a_still_hand' does not depend on any axioms -/
#guard_msgs in #print axioms the_guest_write_is_a_still_hand

/-- info: 'Seed.the_settle_is_a_still_hand' does not depend on any axioms -/
#guard_msgs in #print axioms the_settle_is_a_still_hand

/-- info: 'Seed.the_yield_is_no_still_hand' does not depend on any axioms -/
#guard_msgs in #print axioms the_yield_is_no_still_hand

/-- info: 'Seed.the_unheard_keep_the_house' does not depend on any axioms -/
#guard_msgs in #print axioms the_unheard_keep_the_house

/-- info: 'Seed.the_duet_walks_in_step' does not depend on any axioms -/
#guard_msgs in #print axioms the_duet_walks_in_step

/-- info: 'Seed.the_duet_parks_in_step' does not depend on any axioms -/
#guard_msgs in #print axioms the_duet_parks_in_step

/-- info: 'Seed.the_duet_sounds_both' does not depend on any axioms -/
#guard_msgs in #print axioms the_duet_sounds_both

/-- info: 'Seed.the_duet_reads_at_the_mirror_probe' does not depend on any axioms -/
#guard_msgs in #print axioms the_duet_reads_at_the_mirror_probe

/-- info: 'Seed.the_shell_is_the_duets_silent_partner' does not depend on any axioms -/
#guard_msgs in #print axioms the_shell_is_the_duets_silent_partner

/-- info: 'Seed.the_shell_signs_no_parting' does not depend on any axioms -/
#guard_msgs in #print axioms the_shell_signs_no_parting

/-- info: 'Seed.two_voices_of_one_clock_share_one_seat' does not depend on any axioms -/
#guard_msgs in #print axioms two_voices_of_one_clock_share_one_seat

/-- info: 'Seed.the_duet_hears_one_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_duet_hears_one_word

/-- info: 'Seed.snoc_append' does not depend on any axioms -/
#guard_msgs in #print axioms snoc_append

/-- info: 'Seed.the_scribes_record_only_grows' does not depend on any axioms -/
#guard_msgs in #print axioms the_scribes_record_only_grows

/-- info: 'Seed.one_wind_one_mark' does not depend on any axioms -/
#guard_msgs in #print axioms one_wind_one_mark

/-- info: 'Seed.the_scribe_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms the_scribe_resumes

/-- info: 'Seed.the_scribe_wears_the_tally' does not depend on any axioms -/
#guard_msgs in #print axioms the_scribe_wears_the_tally

/-- info: 'Seed.the_utterance_is_a_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_utterance_is_a_door

/-- info: 'Seed.the_selection_reads_no_wind' does not depend on any axioms -/
#guard_msgs in #print axioms the_selection_reads_no_wind

/-- info: 'Seed.the_selection_reads_only_the_record' does not depend on any axioms -/
#guard_msgs in #print axioms the_selection_reads_only_the_record

/-- info: 'Seed.the_wind_rides_the_utterance' does not depend on any axioms -/
#guard_msgs in #print axioms the_wind_rides_the_utterance

/-- info: 'Seed.generation_originates_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms generation_originates_nothing

/-- info: 'Seed.the_commuting_seat_shrugs_the_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms the_commuting_seat_shrugs_the_shuffle

/-- info: 'Seed.the_heap_steps_commute' does not depend on any axioms -/
#guard_msgs in #print axioms the_heap_steps_commute

/-- info: 'Seed.the_heap_shrugs_the_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms the_heap_shrugs_the_shuffle

/-- info: 'Seed.the_heap_hears_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_heap_hears_the_guest

/-- info: 'Seed.the_scribe_keeps_the_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_scribe_keeps_the_order

/-- info: 'Seed.a_seat_reads_the_order_the_census_cannot' does not depend on any axioms -/
#guard_msgs in #print axioms a_seat_reads_the_order_the_census_cannot

/-- info: 'Seed.the_research_wears_the_old_ear' does not depend on any axioms -/
#guard_msgs in #print axioms the_research_wears_the_old_ear

/-- info: 'Seed.the_research_resounds_the_search' does not depend on any axioms -/
#guard_msgs in #print axioms the_research_resounds_the_search

/-- info: 'Seed.only_the_minted_ask_hears_the_mint' does not depend on any axioms -/
#guard_msgs in #print axioms only_the_minted_ask_hears_the_mint

/-- info: 'Seed.the_research_finds_only_the_mint' does not depend on any axioms -/
#guard_msgs in #print axioms the_research_finds_only_the_mint

/-- info: 'Seed.append_nil' does not depend on any axioms -/
#guard_msgs in #print axioms append_nil

/-- info: 'Seed.the_ledger_parks_the_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_ledger_parks_the_word

/-- info: 'Seed.the_replayer_walks_in_step' does not depend on any axioms -/
#guard_msgs in #print axioms the_replayer_walks_in_step

/-- info: 'Seed.the_replay_is_the_machine' does not depend on any axioms -/
#guard_msgs in #print axioms the_replay_is_the_machine

/-- info: 'Seed.every_seat_is_a_reading_of_the_record' does not depend on any axioms -/
#guard_msgs in #print axioms every_seat_is_a_reading_of_the_record

/-- info: 'Seed.the_audition_cannot_tell_the_seat_from_its_record' does not depend on any axioms -/
#guard_msgs in #print axioms the_audition_cannot_tell_the_seat_from_its_record

/-- info: 'Seed.the_record_never_unwrites' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_never_unwrites

/-- info: 'Seed.the_holonomy_is_the_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_holonomy_is_the_word

/-- info: 'Seed.the_ground_floor_is_the_face' does not depend on any axioms -/
#guard_msgs in #print axioms the_ground_floor_is_the_face

/-- info: 'Seed.the_tower_climbs_by_hosting' does not depend on any axioms -/
#guard_msgs in #print axioms the_tower_climbs_by_hosting

/-- info: 'Seed.every_floor_reads_the_cellar' does not depend on any axioms -/
#guard_msgs in #print axioms every_floor_reads_the_cellar

/-- info: 'Seed.the_tower_reads_only_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_tower_reads_only_the_ground

/-- info: 'Seed.every_floor_merges_its_guests' does not depend on any axioms -/
#guard_msgs in #print axioms every_floor_merges_its_guests

/-- info: 'Seed.the_maintenance_climbs_the_tower' does not depend on any axioms -/
#guard_msgs in #print axioms the_maintenance_climbs_the_tower

/-- info: 'Seed.no_seat_is_the_last_seat' does not depend on any axioms -/
#guard_msgs in #print axioms no_seat_is_the_last_seat

/-- info: 'Seed.the_again_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms the_again_resumes

/-- info: 'Seed.the_again_steps_first' does not depend on any axioms -/
#guard_msgs in #print axioms the_again_steps_first

/-- info: 'Seed.the_tower_is_the_hosts_again' does not depend on any axioms -/
#guard_msgs in #print axioms the_tower_is_the_hosts_again

/-- info: 'Seed.the_bloom_is_the_mirrors_again' does not depend on any axioms -/
#guard_msgs in #print axioms the_bloom_is_the_mirrors_again

/-- info: 'Seed.the_orbit_is_the_steps_again' does not depend on any axioms -/
#guard_msgs in #print axioms the_orbit_is_the_steps_again

/-- info: 'Seed.the_storeys_add' does not depend on any axioms -/
#guard_msgs in #print axioms the_storeys_add

/-- info: 'Seed.one_again_three_orbits' does not depend on any axioms -/
#guard_msgs in #print axioms one_again_three_orbits

/-- info: 'Seed.the_unsigning_is_the_unit_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_unsigning_is_the_unit_guest

/-- info: 'Seed.the_unsigned_work_reads_the_same' does not depend on any axioms -/
#guard_msgs in #print axioms the_unsigned_work_reads_the_same

/-- info: 'Seed.an_author_blind_reading_is_an_unsigned_reading' does not depend on any axioms -/
#guard_msgs in #print axioms an_author_blind_reading_is_an_unsigned_reading

/-- info: 'Seed.the_quiet_author_leaves_the_table_as_found' does not depend on any axioms -/
#guard_msgs in #print axioms the_quiet_author_leaves_the_table_as_found

/-- info: 'Seed.the_author_was_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_author_was_the_guest

/-- info: 'Seed.the_backed_are_seated' does not depend on any axioms -/
#guard_msgs in #print axioms the_backed_are_seated

/-- info: 'Seed.the_unbacked_are_held' does not depend on any axioms -/
#guard_msgs in #print axioms the_unbacked_are_held

/-- info: 'Seed.or_lights_right' does not depend on any axioms -/
#guard_msgs in #print axioms or_lights_right

/-- info: 'Seed.the_seat_is_load_bearing_in_the_same_click' does not depend on any axioms -/
#guard_msgs in #print axioms the_seat_is_load_bearing_in_the_same_click

/-- info: 'Seed.the_enrolled_stay_enrolled' does not depend on any axioms -/
#guard_msgs in #print axioms the_enrolled_stay_enrolled

/-- info: 'Seed.the_backing_never_lapses' does not depend on any axioms -/
#guard_msgs in #print axioms the_backing_never_lapses

/-- info: 'Seed.the_backing_survives_the_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_backing_survives_the_door

/-- info: 'Seed.the_hall_hears_no_join_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_hall_hears_no_join_order

/-- info: 'Seed.the_room_reads_no_waiting' does not depend on any axioms -/
#guard_msgs in #print axioms the_room_reads_no_waiting

/-- info: 'Seed.the_guest_becomes_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_guest_becomes_the_ground

/-- info: 'Seed.beq_of_ne' does not depend on any axioms -/
#guard_msgs in #print axioms beq_of_ne

/-- info: 'Seed.the_seated_arrive_shallowest' does not depend on any axioms -/
#guard_msgs in #print axioms the_seated_arrive_shallowest

/-- info: 'Seed.every_later_admission_deepens' does not depend on any axioms -/
#guard_msgs in #print axioms every_later_admission_deepens

/-- info: 'Seed.the_depth_counts_the_clicks_since' does not depend on any axioms -/
#guard_msgs in #print axioms the_depth_counts_the_clicks_since

/-- info: 'Seed.no_ask_parts_the_warmed_hall' does not depend on any axioms -/
#guard_msgs in #print axioms no_ask_parts_the_warmed_hall

/-- info: 'Seed.the_cost_face_parts_the_warmed' does not depend on any axioms -/
#guard_msgs in #print axioms the_cost_face_parts_the_warmed

/-- info: 'Seed.the_weight_is_zero_at_the_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_weight_is_zero_at_the_door

/-- info: 'Seed.the_removed_date_returns_as_a_weight' does not depend on any axioms -/
#guard_msgs in #print axioms the_removed_date_returns_as_a_weight

/-- info: 'Seed.the_backing_reaches_each_need' does not depend on any axioms -/
#guard_msgs in #print axioms the_backing_reaches_each_need

/-- info: 'Seed.the_support_precedes_the_seating' does not depend on any axioms -/
#guard_msgs in #print axioms the_support_precedes_the_seating

/-- info: 'Seed.the_citer_arrives_above_the_cited' does not depend on any axioms -/
#guard_msgs in #print axioms the_citer_arrives_above_the_cited

/-- info: 'Seed.the_elders_keep_their_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_elders_keep_their_order

/-- info: 'Seed.the_cited_are_the_elders' does not depend on any axioms -/
#guard_msgs in #print axioms the_cited_are_the_elders

/-- info: 'Seed.the_unencumbered_are_welcome_everywhere' does not depend on any axioms -/
#guard_msgs in #print axioms the_unencumbered_are_welcome_everywhere

/-- info: 'Seed.the_enrolled_survive_the_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_enrolled_survive_the_door

/-- info: 'Seed.the_enrolled_survive_the_run' does not depend on any axioms -/
#guard_msgs in #print axioms the_enrolled_survive_the_run

/-- info: 'Seed.the_ordered_arrivals_never_wait' does not depend on any axioms -/
#guard_msgs in #print axioms the_ordered_arrivals_never_wait

/-- info: 'Seed.the_ordered_arrivals_all_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_ordered_arrivals_all_seat

/-- info: 'Seed.the_tree_admits_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_tree_admits_itself

/-- info: 'Seed.no_memory_meters_the_cost' does not depend on any axioms -/
#guard_msgs in #print axioms no_memory_meters_the_cost

/-- info: 'Seed.the_stranger_leaves_the_hall_dark' does not depend on any axioms -/
#guard_msgs in #print axioms the_stranger_leaves_the_hall_dark

/-- info: 'Seed.no_mark_lights_itself' does not depend on any axioms -/
#guard_msgs in #print axioms no_mark_lights_itself

/-- info: 'Seed.the_first_light_comes_from_outside' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_light_comes_from_outside

/-- info: 'Seed.the_backing_survives_the_run' does not depend on any axioms -/
#guard_msgs in #print axioms the_backing_survives_the_run

/-- info: 'Seed.the_ready_seat_in_one_sweep' does not depend on any axioms -/
#guard_msgs in #print axioms the_ready_seat_in_one_sweep

/-- info: 'Seed.the_sweep_seats_the_ready' does not depend on any axioms -/
#guard_msgs in #print axioms the_sweep_seats_the_ready

/-- info: 'Seed.the_vestibule_drains_by_storeys' does not depend on any axioms -/
#guard_msgs in #print axioms the_vestibule_drains_by_storeys

/-- info: 'Seed.the_held_name_their_darkness' does not depend on any axioms -/
#guard_msgs in #print axioms the_held_name_their_darkness

/-- info: 'Seed.the_round_seats_or_certifies' does not depend on any axioms -/
#guard_msgs in #print axioms the_round_seats_or_certifies

/-- info: 'Seed.the_stuck_round_moves_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_stuck_round_moves_nothing

/-- info: 'Seed.the_deadlock_wheels' does not depend on any axioms -/
#guard_msgs in #print axioms the_deadlock_wheels

/-- info: 'Seed.the_deadlock_is_a_wheel' does not depend on any axioms -/
#guard_msgs in #print axioms the_deadlock_is_a_wheel

/-- info: 'Seed.mem_splits' does not depend on any axioms -/
#guard_msgs in #print axioms mem_splits

/-- info: 'Seed.the_load_never_climbs' does not depend on any axioms -/
#guard_msgs in #print axioms the_load_never_climbs

/-- info: 'Seed.the_ready_drop_the_load' does not depend on any axioms -/
#guard_msgs in #print axioms the_ready_drop_the_load

/-- info: 'Seed.the_gauge_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms the_gauge_is_exact

/-- info: 'Seed.the_detector_reads_one_number' does not depend on any axioms -/
#guard_msgs in #print axioms the_detector_reads_one_number

/-- info: 'Seed.the_revision_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_revision_is_a_reading

/-- info: 'Seed.every_writer_is_a_reader' does not depend on any axioms -/
#guard_msgs in #print axioms every_writer_is_a_reader

/-- info: 'Seed.braid_of_left' does not depend on any axioms -/
#guard_msgs in #print axioms braid_of_left

/-- info: 'Seed.braid_of_right' does not depend on any axioms -/
#guard_msgs in #print axioms braid_of_right

/-- info: 'Seed.braid_append' does not depend on any axioms -/
#guard_msgs in #print axioms braid_append

/-- info: 'Seed.braid_prepend' does not depend on any axioms -/
#guard_msgs in #print axioms braid_prepend

/-- info: 'Seed.the_step_crosses_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_step_crosses_the_walk

/-- info: 'Seed.the_weave_parks_one_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_weave_parks_one_seat

/-- info: 'Seed.the_contributors_may_arrive_in_either_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_contributors_may_arrive_in_either_order

/-- info: 'Seed.the_shared_fold_needs_no_scheduler' does not depend on any axioms -/
#guard_msgs in #print axioms the_shared_fold_needs_no_scheduler

/-- info: 'Seed.the_tellers_steps_commute' does not depend on any axioms -/
#guard_msgs in #print axioms the_tellers_steps_commute

/-- info: 'Seed.the_braided_life_draws_one_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_braided_life_draws_one_count

/-- info: 'Seed.the_braided_lives_part' does not depend on any axioms -/
#guard_msgs in #print axioms the_braided_lives_part

/-- info: 'Seed.every_braid_draws_one_count' does not depend on any axioms -/
#guard_msgs in #print axioms every_braid_draws_one_count

/-- info: 'Seed.ne_of_beq_false' does not depend on any axioms -/
#guard_msgs in #print axioms ne_of_beq_false

/-- info: 'Seed.the_mutual_need_stays_dark' does not depend on any axioms -/
#guard_msgs in #print axioms the_mutual_need_stays_dark

/-- info: 'Seed.the_circle_admits_nobody' does not depend on any axioms -/
#guard_msgs in #print axioms the_circle_admits_nobody

end Seed
