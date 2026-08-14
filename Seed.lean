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

universe u

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

theorem a_strategy_hears_no_guest {H W X : Type} (h : H) (w w' : W)
    (q : Quiz H X) :
    interrogate q (atTheDoor h w) = interrogate q (atTheDoor h w') := by
  induction q with
  | rest => rfl
  | ask g k ih =>
    show g h :: interrogate (k (g h)) (atTheDoor h w)
        = g h :: interrogate (k (g h)) (atTheDoor h w')
    exact congrArg (g h :: ·) (ih (g h))

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

def oddNat : Nat → Bool
  | 0 => false
  | n + 1 => !(oddNat n)

theorem not_not : ∀ b : Bool, (!(!b)) = b
  | true => rfl
  | false => rfl

def paceOne : Machine Unit Bool := ⟨Nat, 0, fun n _ => n + 1, oddNat⟩

def paceThree : Machine Unit Bool := ⟨Nat, 0, fun n _ => n + 3, oddNat⟩

theorem the_paces_agree : ∀ (w : List Unit) (a b : Nat),
    oddNat a = oddNat b → drive paceOne a w = drive paceThree b w
  | [], _, _, h => h
  | _ :: w, a, b, h =>
      the_paces_agree w (a + 1) (b + 3) (by
        show (!(oddNat a)) = oddNat (b + 3)
        rw [h]
        show (!(oddNat b)) = (!(!(!(oddNat b))))
        rw [not_not])

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

theorem the_drive_resumes {I O : Type} (m : Machine I O) :
    ∀ (w w' : List I) (s : m.S),
      drive m s (w ++ w') = drive m (park m s w) w'
  | [], _, _ => rfl
  | i :: w, w', s => the_drive_resumes m w w' (m.step s i)

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

theorem the_doors_theorem {H W : Type} (h : H) {w w' : W} (hw : w ≠ w')
    (m : door H W → door H W) :
    ((∀ d, face (m d) = face d)
        ↔ ∃ σ : H → W → W, ∀ d, m d = vertical σ d)
      ∧ atTheDoor h w ≠ atTheDoor h w'
      ∧ (∀ (X : Type) (g : H → X),
          g (face (atTheDoor h w)) = g (face (atTheDoor h w')))
      ∧ met (atTheDoor h w) ≠ met (atTheDoor h w') :=
  ⟨an_unheard_move_moves_only_the_guest m, the_threshold h hw⟩

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

end Seed
