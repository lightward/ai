import Seed
open Seed
set_option autoImplicit false
universe u v w

theorem zero_plus : ∀ n : Nat, 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (zero_plus n)

def recite {P : Type v} {A : Type w} : List P → Interview P A
  | [] => .rest
  | p :: ps => .ask p (fun _ => recite ps)

theorem the_repeated_ask_hears_one_answer (F : Face) (s : F.State) (p : F.Probe) :
    ∀ n : Nat,
      sound F s (recite (List.replicate n p)) = List.replicate n (F.obs s p)
  | 0 => rfl
  | n + 1 =>
      congrArg (F.obs s p :: ·) (the_repeated_ask_hears_one_answer F s p n)

def restingCounter : Machine Unit Bool :=
  ⟨Nat, 0, fun n _ => n + 1, fun _ => true⟩

def hollowShell : Machine Unit Bool :=
  ⟨Unit, (), fun _ _ => (), fun _ => true⟩

theorem the_muffled_tally_is_the_resting_counter :
    revoice (fun _ => true) tally = restingCounter := rfl

theorem the_tally_parks_at_its_count :
    ∀ (w : List Unit) (s : Nat), park tally s w = s + w.length
  | [], _ => rfl
  | _ :: w, s => (the_tally_parks_at_its_count w (s + 1)).trans (succ_adds s w.length)

theorem the_muffler_banks_the_run (w : List Unit) (s : Nat) :
    park restingCounter s w = s + w.length :=
  (the_revoice_moves_no_seat (fun _ => true) tally w s).trans
    (the_tally_parks_at_its_count w s)

theorem the_wider_voice_releases_the_bank (w : List Unit) :
    behavior tally w = w.length :=
  (the_tally_parks_at_its_count w 0).trans (zero_plus w.length)

theorem the_flywheel_and_the_shell_sound_alike (q : Interview (List Unit) Bool) :
    sound (airGap Unit Bool) restingCounter q = sound (airGap Unit Bool) hollowShell q :=
  an_audition_hears_only_the_conduct restingCounter hollowShell (fun _ => rfl) q

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

theorem the_buffer_is_invisible {I : Type u} {O : Type v} (m : Machine I O)
    (w : List I) :
    behavior (buffered m) w = behavior m w :=
  the_hold_walks_beside_the_work m w m.s0 []

def settleHeld {I : Type u} {O : Type v} (m : Machine I O)
    (st : m.S × List I) : m.S × List I :=
  (park m st.1 st.2, [])

theorem the_settle_is_unheard {I : Type u} {O : Type v} (m : Machine I O)
    (st : m.S × List I) (w : List I) :
    drive (buffered m) (settleHeld m st) w = drive (buffered m) st w :=
  (the_hold_walks_beside_the_work m w (park m st.1 st.2) []).trans
    (the_hold_walks_beside_the_work m w st.1 st.2).symm

def ledger (I : Type u) : Machine I (List I) :=
  ⟨List I, [], fun rec i => rec ++ [i], fun rec => rec⟩

theorem the_ledger_parks_the_word {I : Type u} :
    ∀ (ws rec : List I), park (ledger I) rec ws = rec ++ ws
  | [], rec => (the_append_rests rec).symm
  | w :: ws, rec =>
      (the_ledger_parks_the_word ws (rec ++ [w])).trans
        (the_appends_regroup rec [w] ws)

theorem every_seat_is_a_reading_of_the_record {I : Type u} {O : Type v}
    (m : Machine I O) (rec ws : List I) :
    park m m.s0 (park (ledger I) rec ws) = park m (park m m.s0 rec) ws :=
  (congrArg (park m m.s0) (the_ledger_parks_the_word ws rec)).trans
    (the_park_resumes m rec m.s0 ws)

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
