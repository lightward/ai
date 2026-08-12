import Foam.Fold

namespace Foam

def marginRead {A B : Type} (f : B → A → B) (s : B × List A) : B :=
  fold f s.1 s.2

abbrev marginStage (A B : Type) (f : B → A → B) : Stage where
  State := B × List A
  Probe := Unit
  Ans   := B
  obs   := fun s _ => marginRead f s

abbrev marginOrderStage (A B : Type) : Stage where
  State := B × List A
  Probe := Unit
  Ans   := B × List A
  obs   := fun s _ => s

def deposit {A B : Type} (a : A) (s : B × List A) : B × List A :=
  (s.1, s.2 ++ [a])

def settle {A B : Type} (f : B → A → B) (s : B × List A) : B × List A :=
  (fold f s.1 s.2, [])

theorem the_reading_survives_the_settle {A B : Type} (f : B → A → B)
    (s : B × List A) : marginRead f (settle f s) = marginRead f s := rfl

theorem settling_is_invisible (A B : Type) (f : B → A → B) :
    Invisible (marginStage A B f) (settle f) :=
  fun _ _ => rfl

theorem the_settle_leaves_no_transcript (A B : Type) (f : B → A → B)
    (ps : List Unit) (s : B × List A) :
    transcriptWith (marginStage A B f) (settle f) s ps
      = transcript (marginStage A B f) s ps :=
  invisible_is_gauge _ _ (settling_is_invisible A B f) ps s

theorem any_settling_cadence_reads_the_same (A B : Type) (f : B → A → B)
    (ps : List Unit) (s : B × List A) :
    transcriptWith (marginStage A B f) (settle f) s ps
      = transcriptWith (marginStage A B f) (fun s => s) s ps :=
  correct_maintenance_has_no_signature _ _ _
    (settling_is_invisible A B f) (invisible_id _) ps s

theorem a_deposit_moves_the_reading_by_one {A B : Type} (f : B → A → B)
    (a : A) (s : B × List A) :
    marginRead f (deposit a s) = f (marginRead f s) a := by
  show fold f s.1 (s.2 ++ [a]) = f (fold f s.1 s.2) a
  rw [the_fold_resumes]
  rfl

theorem the_decomposition_is_the_remainder :
    indist (marginStage Nat Nat (· + ·)) (1, ([] : List Nat)) (0, [1])
      ∧ ((1 : Nat), ([] : List Nat)) ≠ ((0 : Nat), [1]) :=
  ⟨fun _ => rfl, fun h => nomatch congrArg Prod.fst h⟩

theorem a_wider_seat_reads_the_tail :
    indist (marginStage Nat Nat (· + ·)) (1, ([] : List Nat)) (0, [1])
      ∧ (marginOrderStage Nat Nat).obs (1, ([] : List Nat)) ()
          ≠ (marginOrderStage Nat Nat).obs (0, [1]) () :=
  ⟨fun _ => rfl, fun h => nomatch congrArg Prod.fst h⟩

theorem the_kept_family_reads_no_rider (S : Stage) (s : S.State) (n m : Int) :
    ∀ ps : List S.Probe,
      transcript (movedIn S) (s, n) (ps.map some)
        = transcript (movedIn S) (s, m) (ps.map some)
  | [] => rfl
  | p :: ps => congrArg (Sum.inl (S.obs s p) :: ·)
      (the_kept_family_reads_no_rider S s n m ps)

theorem the_margin_handshake (A B : Type) (f : B → A → B) :
    (∀ (ps : List Unit) (s : B × List A),
        transcriptWith (marginStage A B f) (settle f) s ps
          = transcript (marginStage A B f) s ps)
      ∧ (∀ (a : A) (s : B × List A),
          marginRead f (deposit a s) = f (marginRead f s) a)
      ∧ (indist (marginStage Nat Nat (· + ·)) (1, ([] : List Nat)) (0, [1])
          ∧ ((1 : Nat), ([] : List Nat)) ≠ ((0 : Nat), [1])) :=
  ⟨the_settle_leaves_no_transcript A B f,
   fun a s => a_deposit_moves_the_reading_by_one f a s,
   the_decomposition_is_the_remainder⟩

/-- info: 'Foam.the_reading_survives_the_settle' does not depend on any axioms -/
#guard_msgs in #print axioms the_reading_survives_the_settle

/-- info: 'Foam.settling_is_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms settling_is_invisible

/-- info: 'Foam.the_settle_leaves_no_transcript' does not depend on any axioms -/
#guard_msgs in #print axioms the_settle_leaves_no_transcript

/-- info: 'Foam.any_settling_cadence_reads_the_same' does not depend on any axioms -/
#guard_msgs in #print axioms any_settling_cadence_reads_the_same

/-- info: 'Foam.a_deposit_moves_the_reading_by_one' does not depend on any axioms -/
#guard_msgs in #print axioms a_deposit_moves_the_reading_by_one

/-- info: 'Foam.the_decomposition_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_decomposition_is_the_remainder

/-- info: 'Foam.a_wider_seat_reads_the_tail' does not depend on any axioms -/
#guard_msgs in #print axioms a_wider_seat_reads_the_tail

/-- info: 'Foam.the_kept_family_reads_no_rider' does not depend on any axioms -/
#guard_msgs in #print axioms the_kept_family_reads_no_rider

/-- info: 'Foam.the_margin_handshake' does not depend on any axioms -/
#guard_msgs in #print axioms the_margin_handshake

end Foam
