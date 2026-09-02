import Foam

namespace Foam

theorem the_probe_settles_or_points {A X : Type} (inst : DecidableEq X)
    (c : A → X) (a : A) :
    ∀ L : List A,
      (∀ m, List.Mem m L → c a = c m) ∨ (∃ m, List.Mem m L ∧ c a ≠ c m)
  | [] => Or.inl (fun _ hm => nomatch hm)
  | b :: L =>
      match inst (c a) (c b) with
      | .isTrue h =>
          match the_probe_settles_or_points inst c a L with
          | .inl hall => Or.inl (fun m hm =>
              match hm with
              | .head _ => h
              | .tail _ hm' => hall m hm')
          | .inr ⟨m, hm, hne⟩ => Or.inr ⟨m, .tail _ hm, hne⟩
      | .isFalse h => Or.inr ⟨b, .head _, h⟩

theorem the_window_agrees_or_names_the_gap (A X : Type)
    (inst : DecidableEq X) (c : A → X) :
    ∀ L : List A,
      (∀ n, List.Mem n L → ∀ m, List.Mem m L → c n = c m)
        ∨ (∃ n, List.Mem n L ∧ ∃ m, List.Mem m L ∧ c n ≠ c m)
  | [] => Or.inl (fun _ hn => nomatch hn)
  | a :: L =>
      match the_probe_settles_or_points inst c a L with
      | .inr ⟨m, hm, hne⟩ => Or.inr ⟨a, .head _, m, .tail _ hm, hne⟩
      | .inl hall =>
          match the_window_agrees_or_names_the_gap A X inst c L with
          | .inr ⟨n, hn, m, hm, hne⟩ =>
              Or.inr ⟨n, .tail _ hn, m, .tail _ hm, hne⟩
          | .inl hLL =>
              Or.inl (by
                intro n hn m hm
                cases hn with
                | head =>
                    cases hm with
                    | head => rfl
                    | tail _ hm' => exact hall m hm'
                | tail _ hn' =>
                    cases hm with
                    | head => exact (hall n hn').symm
                    | tail _ hm' => exact hLL n hn' m hm')

/-- info: 'Foam.the_probe_settles_or_points' does not depend on any axioms -/
#guard_msgs in #print axioms the_probe_settles_or_points

/-- info: 'Foam.the_window_agrees_or_names_the_gap' does not depend on any axioms -/
#guard_msgs in #print axioms the_window_agrees_or_names_the_gap

end Foam
