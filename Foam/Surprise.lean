import Foam

namespace Foam

inductive Path {H : Type} (q : List (H × H)) : H → H → Type where
  | nil (a : H) : Path q a a
  | cons {a c : H} (b : H) (e : (a, b) ∈ q) (rest : Path q b c) : Path q a c

def Path.edges {H : Type} {q : List (H × H)} :
    {x y : H} → Path q x y → List (H × H)
  | _, _, .nil _ => []
  | x, _, .cons b _ rest => (x, b) :: rest.edges

def Path.widen {H : Type} {q : List (H × H)} (e' : H × H) :
    {x y : H} → Path q x y → Path (e' :: q) x y
  | _, _, .nil a => .nil a
  | _, _, .cons b e rest => .cons b (List.Mem.tail e' e) (rest.widen e')

theorem a_fresh_edge_rides_no_path {H : Type} {q : List (H × H)}
    {a b : H} (hfresh : (a, b) ∉ q) :
    ∀ {x y : H} (p : Path q x y), (a, b) ∉ p.edges
  | _, _, .nil _, hm => nomatch hm
  | x, _, .cons c e rest, hm => by
      have hm' : (a, b) ∈ (x, c) :: rest.edges := hm
      cases hm' with
      | head => exact hfresh e
      | tail _ hm'' => exact a_fresh_edge_rides_no_path hfresh rest hm''

theorem the_known_edge_already_reaches {H : Type} {q : List (H × H)}
    {a b : H} (h : (a, b) ∈ q) : Nonempty (Path q a b) :=
  ⟨.cons b h (.nil b)⟩

theorem old_reach_survives_the_deposit {H : Type} {q : List (H × H)}
    (e' : H × H) {x y : H} (h : Nonempty (Path q x y)) :
    Nonempty (Path (e' :: q) x y) :=
  h.elim fun p => ⟨p.widen e'⟩

theorem the_deposit_writes_one_mark {H : Type} (q : List (H × H))
    (e : H × H) : (e :: q).length = q.length + 1 := rfl

theorem only_surprise_extends_reach {H : Type} (q : List (H × H))
    (a b : H) (hfresh : (a, b) ∉ q) :
    (∀ {x y : H} (p : Path q x y), (a, b) ∉ p.edges)
      ∧ Nonempty (Path ((a, b) :: q) a b) :=
  ⟨a_fresh_edge_rides_no_path hfresh,
   ⟨.cons b (List.Mem.head q) (.nil b)⟩⟩

/-- info: 'Foam.a_fresh_edge_rides_no_path' does not depend on any axioms -/
#guard_msgs in #print axioms a_fresh_edge_rides_no_path

/-- info: 'Foam.the_known_edge_already_reaches' does not depend on any axioms -/
#guard_msgs in #print axioms the_known_edge_already_reaches

/-- info: 'Foam.old_reach_survives_the_deposit' does not depend on any axioms -/
#guard_msgs in #print axioms old_reach_survives_the_deposit

/-- info: 'Foam.the_deposit_writes_one_mark' does not depend on any axioms -/
#guard_msgs in #print axioms the_deposit_writes_one_mark

/-- info: 'Foam.only_surprise_extends_reach' does not depend on any axioms -/
#guard_msgs in #print axioms only_surprise_extends_reach

def Path.append {H : Type} {q : List (H × H)} :
    {x y z : H} → Path q x y → Path q y z → Path q x z
  | _, _, _, .nil _, p2 => p2
  | _, _, _, .cons b e rest, p2 => .cons b e (Path.append rest p2)

theorem the_derivable_edge_reroutes {H : Type} {q : List (H × H)}
    {a b : H} (hab : Path q a b) :
    ∀ {x y : H}, Path ((a, b) :: q) x y → Nonempty (Path q x y)
  | _, _, .nil c => ⟨.nil c⟩
  | _, _, .cons c hm rest =>
      match the_derivable_edge_reroutes hab rest with
      | ⟨rest'⟩ =>
        match hm with
        | .head _ => ⟨hab.append rest'⟩
        | .tail _ hm' => ⟨.cons c hm' rest'⟩

theorem a_derivable_edge_adds_no_reach {H : Type} {q : List (H × H)}
    {a b : H} (hab : Nonempty (Path q a b)) (x y : H) :
    Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y) :=
  ⟨fun h => h.elim fun p => hab.elim fun pab => the_derivable_edge_reroutes pab p,
   fun h => old_reach_survives_the_deposit (a, b) h⟩

theorem the_shortcut_pays_only_its_mark {H : Type} (q : List (H × H))
    (a b : H) (hfresh : (a, b) ∉ q) (hab : Nonempty (Path q a b)) :
    (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
      ∧ ((a, b) :: q).length = q.length + 1
      ∧ ∀ x y : H, Nonempty (Path ((a, b) :: q) x y) ↔ Nonempty (Path q x y) :=
  ⟨fun _ _ p => a_fresh_edge_rides_no_path hfresh p,
   the_deposit_writes_one_mark q (a, b),
   fun x y => a_derivable_edge_adds_no_reach hab x y⟩

theorem the_known_edge_reroutes {H : Type} {q : List (H × H)} {e : H × H}
    (he : e ∈ q) : ∀ {x y : H}, Path (e :: q) x y → Nonempty (Path q x y)
  | _, _, .nil a => ⟨.nil a⟩
  | _, _, .cons b hm rest =>
      match the_known_edge_reroutes he rest with
      | ⟨rest'⟩ =>
        match hm with
        | .head _ => ⟨.cons b he rest'⟩
        | .tail _ hm' => ⟨.cons b hm' rest'⟩

theorem a_known_edge_adds_no_reach {H : Type} {q : List (H × H)} {e : H × H}
    (he : e ∈ q) (x y : H) :
    Nonempty (Path (e :: q) x y) ↔ Nonempty (Path q x y) :=
  ⟨fun h => h.elim fun p => the_known_edge_reroutes he p,
   fun h => old_reach_survives_the_deposit e h⟩

/-- info: 'Foam.the_derivable_edge_reroutes' does not depend on any axioms -/
#guard_msgs in #print axioms the_derivable_edge_reroutes

/-- info: 'Foam.a_derivable_edge_adds_no_reach' does not depend on any axioms -/
#guard_msgs in #print axioms a_derivable_edge_adds_no_reach

/-- info: 'Foam.the_shortcut_pays_only_its_mark' does not depend on any axioms -/
#guard_msgs in #print axioms the_shortcut_pays_only_its_mark

/-- info: 'Foam.the_known_edge_reroutes' does not depend on any axioms -/
#guard_msgs in #print axioms the_known_edge_reroutes

/-- info: 'Foam.a_known_edge_adds_no_reach' does not depend on any axioms -/
#guard_msgs in #print axioms a_known_edge_adds_no_reach

end Foam
