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

/-- info: 'Seed.the_audition_is_blind' does not depend on any axioms -/
#guard_msgs in #print axioms the_audition_is_blind

/-- info: 'Seed.the_interview_never_leaves_the_first_window' does not depend on any axioms -/
#guard_msgs in #print axioms the_interview_never_leaves_the_first_window

/-- info: 'Seed.no_interview_hears_the_excluded' does not depend on any axioms -/
#guard_msgs in #print axioms no_interview_hears_the_excluded

/-- info: 'Seed.the_cage_is_audible_through_the_curtain' does not depend on any axioms -/
#guard_msgs in #print axioms the_cage_is_audible_through_the_curtain

end Seed
