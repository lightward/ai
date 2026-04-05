/-
# FTPG — Toward the Fundamental Theorem of Projective Geometry

A complemented modular atomistic lattice has the structure of a
projective geometry. This file builds the incidence geometry from
the lattice axioms alone: atoms are points, joins of atom pairs
are lines, and the modular law forces Veblen-Young (two lines in
a plane meet).

The target: prove that such a lattice (with irreducibility and
height ≥ 4) is isomorphic to the subspace lattice of a vector
space over a division ring. This would replace the axiom in
Bridge.lean with a theorem.

## What's here

1. Atom structure: disjointness, covering by joins
2. Line structure: height 2, determined by any two points
3. Plane structure: covers lines
4. Veblen-Young: two lines in a plane meet (from modularity)
5. Central projection: well-defined, gives atoms

## What's needed

- Desargues' theorem (automatic from height ≥ 4)
- Coordinatization: lattice ops → division ring
- The isomorphism: L ≃o Sub(D, V)
-/

import Mathlib.Order.ModularLattice
import Mathlib.Order.Atoms
import Mathlib.Order.KrullDimension
import Mathlib.Order.Height
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projectivization.Basic

namespace Foam.FTPGExplore

universe u

/-!
## The statement

The precise hypotheses for FTPG: complemented, modular, atomistic,
irreducible (any two atoms span a line with a third point),
and height ≥ 4 (chains of length ≥ 4 exist).
-/

/-- The fundamental theorem of projective geometry (lattice form). -/
def ftpg_statement : Prop :=
  ∀ (L : Type u) [Lattice L] [BoundedOrder L]
    [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]
    (h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (h_height : ∃ (a b c d : L), ⊥ < a ∧ a < b ∧ b < c ∧ c < d),
    ∃ (D : Type u) (_ : DivisionRing D)
      (V : Type u) (_ : AddCommGroup V) (_ : Module D V),
    Nonempty (L ≃o Submodule D V)

/-!
## Incidence geometry from the modular law
-/

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

-- § Atoms

/-- Distinct atoms are disjoint. -/
theorem atoms_disjoint {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    a ⊓ b = ⊥ := by
  rcases ha.le_iff.mp inf_le_left with h | h
  · exact h
  · exfalso; apply hab
    have hab' : a ≤ b := h ▸ inf_le_right
    exact le_antisymm hab' (hb.le_iff.mp hab' |>.resolve_left ha.1 ▸ le_refl b)

/-- Distinct atoms: each is covered by their join. -/
theorem atom_covBy_join {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    a ⋖ a ⊔ b := by
  have h_meet : a ⊓ b = ⊥ := atoms_disjoint ha hb hab
  exact covBy_sup_of_inf_covBy_of_inf_covBy_left (h_meet ▸ ha.bot_covBy) (h_meet ▸ hb.bot_covBy)

/-- Irreducibility gives a third atom on every line, and that atom
    generates the same line. -/
theorem third_atom_on_line {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b ∧ a ⊔ b = a ⊔ c := by
  obtain ⟨c, hc_atom, hc_le, hc_ne_a, hc_ne_b⟩ := h_irred a b ha hb hab
  refine ⟨c, hc_atom, hc_le, hc_ne_a, hc_ne_b, ?_⟩
  have h_cov := atom_covBy_join ha hb hab
  have h_c_not_le_a : ¬ c ≤ a := by
    intro hle
    exact hc_ne_a (le_antisymm hle (ha.le_iff.mp hle |>.resolve_left hc_atom.1 ▸ le_refl a))
  have h_a_lt_ac : a < a ⊔ c := lt_of_le_of_ne le_sup_left (by
    intro heq; exact h_c_not_le_a (heq ▸ le_sup_right))
  have h_ac_le_ab : a ⊔ c ≤ a ⊔ b := sup_le le_sup_left hc_le
  exact ((h_cov.eq_or_eq h_a_lt_ac.le h_ac_le_ab).resolve_left (ne_of_gt h_a_lt_ac)).symm

-- § Lines

/-- Any atom on a line is covered by that line. -/
theorem line_covers_its_atoms {a b c : L}
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (hc : IsAtom c) (hc_le : c ≤ a ⊔ b) :
    c ⋖ a ⊔ b := by
  by_cases hca : c = a
  · subst hca; exact atom_covBy_join hc hb hab
  by_cases hcb : c = b
  · subst hcb; rw [sup_comm]; exact atom_covBy_join hc ha (Ne.symm hab)
  · have h_cov_ab := atom_covBy_join ha hb hab
    have h_c_not_le_a : ¬ c ≤ a := by
      intro hle; exact hca (le_antisymm hle (ha.le_iff.mp hle |>.resolve_left hc.1 ▸ le_refl a))
    have h_a_lt_ac : a < a ⊔ c := lt_of_le_of_ne le_sup_left (by
      intro heq; exact h_c_not_le_a (heq ▸ le_sup_right))
    have h_eq : a ⊔ b = a ⊔ c :=
      ((h_cov_ab.eq_or_eq h_a_lt_ac.le (sup_le le_sup_left hc_le)).resolve_left
        (ne_of_gt h_a_lt_ac)).symm
    have hac : a ≠ c := fun h => hca h.symm
    have h_cov_ca := atom_covBy_join hc ha hac.symm
    rwa [sup_comm c a, ← h_eq] at h_cov_ca

/-- Lines are determined by any two of their points. -/
theorem line_eq_of_atom_le {a b c : L}
    (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hc_le : c ≤ a ⊔ b) :
    a ⊔ b = a ⊔ c := by
  have h_cov := atom_covBy_join ha hb hab
  have h_c_not_le_a : ¬ c ≤ a := by
    intro hle; exact hac.symm (le_antisymm hle (ha.le_iff.mp hle |>.resolve_left hc.1 ▸ le_refl a))
  have h_a_lt_ac : a < a ⊔ c := lt_of_le_of_ne le_sup_left (by
    intro heq; exact h_c_not_le_a (heq ▸ le_sup_right))
  exact ((h_cov.eq_or_eq h_a_lt_ac.le (sup_le le_sup_left hc_le)).resolve_left
    (ne_of_gt h_a_lt_ac)).symm

/-- Lines have height 2: anything strictly between ⊥ and a line is an atom. -/
theorem line_height_two {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    {x : L} (hx_pos : ⊥ < x) (hx_lt : x < a ⊔ b) :
    IsAtom x := by
  obtain ⟨s, hs_lub, hs_atoms⟩ := IsAtomistic.isLUB_atoms x
  have hs_ne : s.Nonempty := by
    by_contra hs_empty
    simp only [Set.not_nonempty_iff_eq_empty] at hs_empty
    subst hs_empty
    have : x ≤ ⊥ := hs_lub.2 (fun _ hx => (Set.mem_empty_iff_false _).mp hx |>.elim)
    exact ne_of_gt hx_pos (le_antisymm this bot_le)
  obtain ⟨p, hp_mem⟩ := hs_ne
  have hp_atom := hs_atoms p hp_mem
  have hp_le_x : p ≤ x := hs_lub.1 hp_mem
  have hp_cov := line_covers_its_atoms ha hb hab hp_atom (le_trans hp_le_x hx_lt.le)
  rcases hp_cov.eq_or_eq hp_le_x hx_lt.le with h | h
  · exact h ▸ hp_atom
  · exact absurd h (ne_of_lt hx_lt)

-- § Planes

/-- A line and an off-line atom form a plane that covers the line. -/
theorem line_covBy_plane {a b c : L}
    (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h_not_collinear : ¬ c ≤ a ⊔ b) :
    a ⊔ b ⋖ a ⊔ b ⊔ c := by
  have h_meet : c ⊓ (a ⊔ b) = ⊥ := by
    rcases hc.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) h_not_collinear
  have h1 := covBy_sup_of_inf_covBy_left (h_meet ▸ hc.bot_covBy)
  rw [show c ⊔ (a ⊔ b) = a ⊔ b ⊔ c from sup_comm _ _] at h1
  exact h1

/-- Two lines through a common atom: the modular law gives their meet. -/
theorem modular_intersection {a b c : L}
    (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h_not_collinear : ¬ c ≤ a ⊔ b) :
    (a ⊔ b) ⊓ (a ⊔ c) = a := by
  rw [sup_inf_assoc_of_le b (le_sup_left : a ≤ a ⊔ c)]
  have : b ⊓ (a ⊔ c) = ⊥ := by
    rcases hb.le_iff.mp inf_le_left with h | h
    · exact h
    · exfalso; apply h_not_collinear
      have hb_le : b ≤ a ⊔ c := h ▸ inf_le_right
      exact (line_eq_of_atom_le ha hc hb hac hab hbc.symm hb_le) ▸ le_sup_right
  rw [this, sup_bot_eq]

-- § Veblen-Young

/-- Abstract core: if x ⋖ z, y ≤ z, y ≰ x, and x ⊓ y = ⊥, then ⊥ ⋖ y. -/
theorem covBy_inf_disjoint_atom {x y z : L}
    (h_cov : x ⋖ z) (hy_le : y ≤ z) (hy_not_le : ¬ y ≤ x) (h_disj : x ⊓ y = ⊥) :
    ⊥ ⋖ y := by
  have h_join : x ⊔ y = z := by
    have h_lt : x < x ⊔ y := lt_of_le_of_ne le_sup_left
      (fun h => hy_not_le (le_trans le_sup_right (ge_of_eq h)))
    exact (h_cov.eq_or_eq h_lt.le (sup_le h_cov.le hy_le)).resolve_left (ne_of_gt h_lt)
  have h_inf_cov : x ⊓ y ⋖ y := by
    rw [← h_join] at h_cov
    exact IsLowerModularLattice.inf_covBy_of_covBy_sup h_cov
  rwa [h_disj] at h_inf_cov

/-- Two lines in a plane meet (assuming the second is a genuine line). -/
theorem lines_meet_if_coplanar {l₁ l₂ z : L}
    (h_cov : l₁ ⋖ z) (hl₂_le : l₂ ≤ z) (hl₂_not : ¬ l₂ ≤ l₁)
    {p : L} (hp : IsAtom p) (hp_lt : p < l₂) :
    l₁ ⊓ l₂ ≠ ⊥ := by
  intro h_disj
  exact (covBy_inf_disjoint_atom h_cov hl₂_le hl₂_not h_disj).2 hp.bot_lt hp_lt

/-- **Veblen-Young.** Two lines in a plane have non-trivial intersection. -/
theorem veblen_young {a b c d : L}
    (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c) (hd : IsAtom d)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d)
    (h_nc : ¬ c ≤ a ⊔ b)
    (hd_le : d ≤ a ⊔ b ⊔ c)
    (hd_not_bc : ¬ d ≤ b ⊔ c) :
    (b ⊔ c) ⊓ (a ⊔ d) ≠ ⊥ := by
  have ha_not_bc : ¬ a ≤ b ⊔ c := by
    intro hle; apply h_nc
    calc c ≤ b ⊔ c := le_sup_right
      _ = b ⊔ a := line_eq_of_atom_le hb hc ha hbc hab.symm hac.symm hle
      _ = a ⊔ b := sup_comm b a
  have ha_meet_bc : a ⊓ (b ⊔ c) = ⊥ := by
    rcases ha.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) ha_not_bc
  have h_plane_covers_bc : b ⊔ c ⋖ a ⊔ (b ⊔ c) :=
    covBy_sup_of_inf_covBy_left (ha_meet_bc ▸ ha.bot_covBy)
  have h_ad_le_plane : a ⊔ d ≤ a ⊔ b ⊔ c :=
    sup_le (le_sup_of_le_left le_sup_left) hd_le
  have h_join_le : (b ⊔ c) ⊔ (a ⊔ d) ≤ a ⊔ (b ⊔ c) := by
    rw [(sup_assoc a b c).symm]
    exact sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right) h_ad_le_plane
  have h_bc_lt_join : b ⊔ c < (b ⊔ c) ⊔ (a ⊔ d) :=
    lt_of_le_of_ne le_sup_left (fun h => ha_not_bc
      (le_trans le_sup_left (le_trans le_sup_right (ge_of_eq h))))
  have h_join_eq : (b ⊔ c) ⊔ (a ⊔ d) = a ⊔ (b ⊔ c) :=
    (h_plane_covers_bc.eq_or_eq h_bc_lt_join.le h_join_le).resolve_left
      (ne_of_gt h_bc_lt_join)
  intro h_disjoint
  rw [← h_join_eq] at h_plane_covers_bc
  have h_cov_ad : (b ⊔ c) ⊓ (a ⊔ d) ⋖ (a ⊔ d) :=
    IsLowerModularLattice.inf_covBy_of_covBy_sup h_plane_covers_bc
  rw [h_disjoint] at h_cov_ad
  exact h_cov_ad.2
    (show ⊥ < a from ha.bot_lt)
    (show a < a ⊔ d from lt_of_le_of_ne le_sup_left (by
      intro heq
      exact had (le_antisymm (ha.le_iff.mp (heq ▸ le_sup_right) |>.resolve_left hd.1 ▸ le_refl a)
        (heq ▸ le_sup_right))))

/-- Meet of two distinct lines (when nonzero) is an atom. -/
theorem meet_of_lines_is_atom {a b c d : L}
    (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c) (hd : IsAtom d)
    (hab : a ≠ b) (hcd : c ≠ d)
    (h_not_le : ¬ a ⊔ b ≤ c ⊔ d)
    (h_meet_ne : (a ⊔ b) ⊓ (c ⊔ d) ≠ ⊥) :
    IsAtom ((a ⊔ b) ⊓ (c ⊔ d)) :=
  line_height_two ha hb hab
    (bot_lt_iff_ne_bot.mpr h_meet_ne)
    (lt_of_le_of_ne inf_le_left (fun heq => h_not_le (heq ▸ inf_le_right)))

-- § Central projection

/-- Project a point through a center onto a target line. -/
noncomputable def project (c p l : L) : L := (p ⊔ c) ⊓ l

/-- Central projection gives an atom on the target line. -/
theorem project_is_atom {c p a b : L}
    (hc : IsAtom c) (hp : IsAtom p) (hcp : c ≠ p)
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (hc_not_l : ¬ c ≤ a ⊔ b) (hp_not_l : ¬ p ≤ a ⊔ b)
    (h_coplanar : p ⊔ c ≤ (a ⊔ b) ⊔ c) :
    IsAtom (project c p (a ⊔ b)) := by
  unfold project
  have hc_meet : c ⊓ (a ⊔ b) = ⊥ := by
    rcases hc.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hc_not_l
  have h_plane_cov : (a ⊔ b) ⋖ (a ⊔ b) ⊔ c := by
    rw [show (a ⊔ b) ⊔ c = c ⊔ (a ⊔ b) from sup_comm _ _]
    exact covBy_sup_of_inf_covBy_left (hc_meet ▸ hc.bot_covBy)
  have h_pc_not_le : ¬ p ⊔ c ≤ a ⊔ b :=
    fun h => hc_not_l (le_trans le_sup_right h)
  have h_c_not_le_p : ¬ c ≤ p := by
    intro hle
    exact hcp.symm (le_antisymm (hp.le_iff.mp hle |>.resolve_left hc.1 ▸ le_refl p) hle)
  have h_p_lt_pc : p < p ⊔ c := lt_of_le_of_ne le_sup_left
    (fun h => h_c_not_le_p (h ▸ le_sup_right))
  have h_meet_ne : (a ⊔ b) ⊓ (p ⊔ c) ≠ ⊥ :=
    lines_meet_if_coplanar h_plane_cov h_coplanar h_pc_not_le hp h_p_lt_pc
  apply line_height_two ha hb hab
  · exact bot_lt_iff_ne_bot.mpr (by rwa [inf_comm] at h_meet_ne)
  · apply lt_of_le_of_ne inf_le_right
    intro heq
    have hab_le : a ⊔ b ≤ p ⊔ c := heq ▸ inf_le_left
    have ha_cov_pc := line_covers_its_atoms hp hc hcp.symm ha (le_trans le_sup_left hab_le)
    rcases ha_cov_pc.eq_or_eq (atom_covBy_join ha hb hab |>.lt |>.le) hab_le with h | h
    · exact ne_of_gt (atom_covBy_join ha hb hab |>.lt) h
    · exact hp_not_l (h ▸ le_sup_left)

/-!
## The diamond isomorphism: dimension by structure, not counting

Mathlib's `infIccOrderIsoIccSup` gives us `[a ⊓ b, a] ≃o [b, a ⊔ b]`
in any modular lattice. This is the structural version of
"dim(a) + dim(b) = dim(a ⊔ b) + dim(a ⊓ b)".

We don't need a rank function. We need interval isomorphisms.
Let's see what falls out.
-/

/-- Two planes in a common space: if both are covered by the space,
    their meet is covered by each of them. (Diamond isomorphism
    gives the structural dimension argument.) -/
theorem planes_meet_covBy {π₁ π₂ s : L}
    (h₁ : π₁ ⋖ s) (h₂ : π₂ ⋖ s) (h_ne : π₁ ≠ π₂) :
    (π₁ ⊓ π₂) ⋖ π₁ ∧ (π₁ ⊓ π₂) ⋖ π₂ := by
  have h₂_not_le : ¬ π₂ ≤ π₁ := by
    intro hle
    rcases h₂.eq_or_eq hle h₁.le with h | h
    · exact h_ne h
    · exact ne_of_lt h₁.lt h
  have h_join : π₁ ⊔ π₂ = s := by
    have h_lt : π₁ < π₁ ⊔ π₂ := lt_of_le_of_ne le_sup_left
      (fun h => h₂_not_le (le_trans le_sup_right (ge_of_eq h)))
    exact (h₁.eq_or_eq h_lt.le (sup_le h₁.le h₂.le)).resolve_left (ne_of_gt h_lt)
  constructor
  · -- π₁ ⊓ π₂ ⋖ π₁: from π₂ ⋖ π₁ ⊔ π₂ via dual covering
    rw [← h_join] at h₂
    rw [sup_comm] at h₂
    have := IsLowerModularLattice.inf_covBy_of_covBy_sup h₂
    rwa [inf_comm] at this
  · -- π₁ ⊓ π₂ ⋖ π₂: from π₁ ⋖ π₁ ⊔ π₂ via dual covering
    rw [← h_join] at h₁
    exact IsLowerModularLattice.inf_covBy_of_covBy_sup h₁

-- § Desargues

/-- **Desargues' theorem (non-planar case).**
    Two triangles perspective from a point: corresponding sides
    meet on a common line.

    Setup: center o, triangle a₁a₂a₃, triangle b₁b₂b₃.
    Perspective from o: bᵢ on line o ⊔ aᵢ.
    Non-planar: the triangles span distinct planes.

    Conclusion: the three intersection points
      p₁₂ = (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂)
      p₁₃ = (a₁ ⊔ a₃) ⊓ (b₁ ⊔ b₃)
      p₂₃ = (a₂ ⊔ a₃) ⊓ (b₂ ⊔ b₃)
    are all ≤ πA ⊓ πB (the meet of the two triangle planes).

    The proof: each pᵢⱼ ≤ πA (sides of triangle A) and ≤ πB
    (sides of triangle B). That's it — the hard part was showing
    πA ⊓ πB is a "line", which planes_meet_covBy gives us. -/
theorem desargues_nonplanar
    {o a₁ a₂ a₃ b₁ b₂ b₃ : L}
    -- All atoms
    (ho : IsAtom o) (ha₁ : IsAtom a₁) (ha₂ : IsAtom a₂) (ha₃ : IsAtom a₃)
    (hb₁ : IsAtom b₁) (hb₂ : IsAtom b₂) (hb₃ : IsAtom b₃)
    -- Perspective from o
    (hb₁_on : b₁ ≤ o ⊔ a₁) (hb₂_on : b₂ ≤ o ⊔ a₂) (hb₃_on : b₃ ≤ o ⊔ a₃)
    -- Triangle planes
    (πA : L) (hπA : πA = a₁ ⊔ a₂ ⊔ a₃)
    (πB : L) (hπB : πB = b₁ ⊔ b₂ ⊔ b₃)
    -- Sides of A are in πA, sides of B are in πB
    -- (These follow from the definitions, but let's check)
    :
    -- The three intersection points are all in πA ⊓ πB
    (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) ≤ πA ⊓ πB ∧
    (a₁ ⊔ a₃) ⊓ (b₁ ⊔ b₃) ≤ πA ⊓ πB ∧
    (a₂ ⊔ a₃) ⊓ (b₂ ⊔ b₃) ≤ πA ⊓ πB := by
  subst hπA; subst hπB
  -- Each pᵢⱼ ≤ πA ⊓ πB iff pᵢⱼ ≤ πA and pᵢⱼ ≤ πB.
  -- pᵢⱼ = (aᵢ ⊔ aⱼ) ⊓ (bᵢ ⊔ bⱼ).
  -- pᵢⱼ ≤ aᵢ ⊔ aⱼ ≤ πA: clear (sides of triangle A are in πA).
  -- pᵢⱼ ≤ bᵢ ⊔ bⱼ ≤ πB: clear (sides of triangle B are in πB).
  -- Wait: we also need bᵢ ⊔ bⱼ ≤ πA. That's the hard part!
  -- Actually no: pᵢⱼ ≤ aᵢ ⊔ aⱼ (from inf_le_left) and pᵢⱼ ≤ bᵢ ⊔ bⱼ (from inf_le_right).
  -- We need: aᵢ ⊔ aⱼ ≤ πA and bᵢ ⊔ bⱼ ≤ πB.
  -- aᵢ ⊔ aⱼ ≤ a₁ ⊔ a₂ ⊔ a₃: yes, straightforward.
  -- bᵢ ⊔ bⱼ ≤ b₁ ⊔ b₂ ⊔ b₃: yes, straightforward.
  -- So pᵢⱼ ≤ πA and pᵢⱼ ≤ πB, hence pᵢⱼ ≤ πA ⊓ πB.
  refine ⟨le_inf (inf_le_left.trans ?_) (inf_le_right.trans ?_),
          le_inf (inf_le_left.trans ?_) (inf_le_right.trans ?_),
          le_inf (inf_le_left.trans ?_) (inf_le_right.trans ?_)⟩
  -- 6 goals: show each side of each triangle is in its plane
  · -- a₁ ⊔ a₂ ≤ a₁ ⊔ a₂ ⊔ a₃
    exact le_sup_left
  · -- b₁ ⊔ b₂ ≤ b₁ ⊔ b₂ ⊔ b₃
    exact le_sup_left
  · -- a₁ ⊔ a₃ ≤ a₁ ⊔ a₂ ⊔ a₃
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  · -- b₁ ⊔ b₃ ≤ b₁ ⊔ b₂ ⊔ b₃
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  · -- a₂ ⊔ a₃ ≤ a₁ ⊔ a₂ ⊔ a₃
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  · -- b₂ ⊔ b₃ ≤ b₁ ⊔ b₂ ⊔ b₃
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

/-- Projection is injective: distinct points project to distinct points. -/
theorem project_injective {c a b p q : L}
    (hc : IsAtom c) (hp : IsAtom p) (hq : IsAtom q)
    (ha : IsAtom a) (hb : IsAtom b)
    (hcp : c ≠ p) (hcq : c ≠ q) (hpq : p ≠ q) (hab : a ≠ b)
    (hc_not_l : ¬ c ≤ a ⊔ b)
    (hp_not_l : ¬ p ≤ a ⊔ b) (hq_not_l : ¬ q ≤ a ⊔ b)
    (hp_coplanar : p ⊔ c ≤ (a ⊔ b) ⊔ c)
    (hq_coplanar : q ⊔ c ≤ (a ⊔ b) ⊔ c)
    -- p and q are on different lines through c (not both on c's line)
    (hpq_diff : p ⊔ c ≠ q ⊔ c) :
    project c p (a ⊔ b) ≠ project c q (a ⊔ b) := by
  unfold project
  intro heq
  -- (p ⊔ c) ⊓ (a ⊔ b) = (q ⊔ c) ⊓ (a ⊔ b)
  -- Call this point m. m is on line a ⊔ b and on both p ⊔ c and q ⊔ c.
  -- m ≤ p ⊔ c and m ≤ q ⊔ c, so m ≤ (p ⊔ c) ⊓ (q ⊔ c).
  -- Now: p ⊔ c and q ⊔ c are two lines through c.
  -- Their meet (p ⊔ c) ⊓ (q ⊔ c) should be just c
  -- (by modular_intersection, if p, q, c are non-collinear).
  -- So m ≤ c. But m is on line a ⊔ b, and c is not on a ⊔ b.
  -- If m is an atom, m ≤ c means m = c (since c is an atom).
  -- But m ≤ a ⊔ b and c ≰ a ⊔ b. Contradiction.
  -- If m = ⊥... but m is an atom (project_is_atom).
  have hm_atom := project_is_atom hc hp hcp ha hb hab hc_not_l hp_not_l hp_coplanar
  unfold project at hm_atom
  -- m ≤ p ⊔ c and m ≤ q ⊔ c
  have hm_le_pc : (p ⊔ c) ⊓ (a ⊔ b) ≤ p ⊔ c := inf_le_left
  have hm_le_qc : (p ⊔ c) ⊓ (a ⊔ b) ≤ q ⊔ c := heq ▸ inf_le_left
  have hm_le_ab : (p ⊔ c) ⊓ (a ⊔ b) ≤ a ⊔ b := inf_le_right
  -- m ≤ (p ⊔ c) ⊓ (q ⊔ c)
  have hm_le_meet : (p ⊔ c) ⊓ (a ⊔ b) ≤ (p ⊔ c) ⊓ (q ⊔ c) :=
    le_inf hm_le_pc hm_le_qc
  -- (p ⊔ c) ⊓ (q ⊔ c) ≤ c: need p, q not collinear with c on a single line
  -- This is where we need hpq_diff (the lines through c are distinct)
  -- q is not on line p ⊔ c (otherwise p ⊔ c = q ⊔ c by line_eq_of_atom_le)
  have hq_not_pc : ¬ q ≤ p ⊔ c := by
    intro hle
    apply hpq_diff
    rw [sup_comm p c, sup_comm q c]
    exact line_eq_of_atom_le hc hp hq hcp hcq hpq (sup_comm p c ▸ hle)
  -- modular_intersection: (c ⊔ p) ⊓ (c ⊔ q) = c
  have h_meet_eq : (c ⊔ p) ⊓ (c ⊔ q) = c :=
    modular_intersection hc hp hq hcp hcq hpq (sup_comm c p ▸ hq_not_pc)
  -- m ≤ c via the chain: m ≤ (p⊔c) ⊓ (q⊔c) = (c⊔p) ⊓ (c⊔q) = c
  have hm_le_c : (p ⊔ c) ⊓ (a ⊔ b) ≤ c := by
    calc (p ⊔ c) ⊓ (a ⊔ b)
        ≤ (p ⊔ c) ⊓ (q ⊔ c) := hm_le_meet
      _ = (c ⊔ p) ⊓ (c ⊔ q) := by rw [sup_comm p c, sup_comm q c]
      _ = c := h_meet_eq
  -- m is an atom, c is an atom, m ≤ c ⟹ m = ⊥ or m = c
  rcases hc.le_iff.mp hm_le_c with h | h
  · exact hm_atom.1 h
  · exact hc_not_l (h ▸ hm_le_ab)

-- § Toward coordinates

/-- The atoms on a line — the candidate "elements" of the coordinate ring. -/
def AtomsOn (l : L) : Type u := {a : L // IsAtom a ∧ a ≤ l}

/-- A line has at least two atoms (its generators). -/
def AtomsOn.mk_left {a b : L} (ha : IsAtom a) (_hb : IsAtom b) (_hab : a ≠ b) :
    AtomsOn (a ⊔ b) :=
  ⟨a, ha, le_sup_left⟩

def AtomsOn.mk_right {a b : L} (_ha : IsAtom a) (hb : IsAtom b) (_hab : a ≠ b) :
    AtomsOn (a ⊔ b) :=
  ⟨b, hb, le_sup_right⟩

/-- Projection induces a function between AtomsOn types. -/
noncomputable def projectOn {c a b : L}
    (hc : IsAtom c) (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (hc_not : ¬ c ≤ a ⊔ b) :
    -- Source: atoms in the plane (a ⊔ b) ⊔ c that aren't on a ⊔ b and aren't c
    {p : L // IsAtom p ∧ ¬ p ≤ a ⊔ b ∧ p ⊔ c ≤ (a ⊔ b) ⊔ c ∧ c ≠ p} →
    AtomsOn (a ⊔ b) :=
  fun ⟨p, hp_atom, hp_not, hp_cop, hcp⟩ =>
    ⟨project c p (a ⊔ b),
     project_is_atom hc hp_atom hcp ha hb hab hc_not hp_not hp_cop,
     inf_le_right⟩

-- § Perspectivity between lines

/-- The meet of a line through c with l₂, when c ≰ l₂ and both
    are in the same plane. This is the atomic projection formula
    that works uniformly — even when the source point is on l₂. -/
theorem perspect_atom {p c a₂ b₂ : L}
    (hc : IsAtom c) (hp : IsAtom p) (hpc : p ≠ c)
    (_ha₂ : IsAtom a₂) (_hb₂ : IsAtom b₂) (_hab₂ : a₂ ≠ b₂)
    (hc_not : ¬ c ≤ a₂ ⊔ b₂)
    (h_in_plane : p ⊔ c ≤ (a₂ ⊔ b₂) ⊔ c) :
    IsAtom ((p ⊔ c) ⊓ (a₂ ⊔ b₂)) := by
  -- l₂ ⋖ plane
  have hc_meet : c ⊓ (a₂ ⊔ b₂) = ⊥ := by
    rcases hc.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hc_not
  have h_cov : (a₂ ⊔ b₂) ⋖ (a₂ ⊔ b₂) ⊔ c := by
    rw [show (a₂ ⊔ b₂) ⊔ c = c ⊔ (a₂ ⊔ b₂) from sup_comm _ _]
    exact covBy_sup_of_inf_covBy_left (hc_meet ▸ hc.bot_covBy)
  -- p ⊔ c ≰ l₂ (since c ≤ p ⊔ c and c ≰ l₂)
  have h_pc_not : ¬ p ⊔ c ≤ a₂ ⊔ b₂ :=
    fun h => hc_not (le_trans le_sup_right h)
  -- p < p ⊔ c (since c ≰ p, because p ≠ c and both atoms)
  have hc_not_le_p : ¬ c ≤ p := by
    intro hle
    exact hpc.symm (hp.le_iff.mp hle |>.resolve_left hc.1)
  have hp_lt_pc : p < p ⊔ c := lt_of_le_of_ne le_sup_left
    (fun h => hc_not_le_p (h ▸ le_sup_right))
  -- Two lines in a plane meet nontrivially
  have h_meet_ne : (a₂ ⊔ b₂) ⊓ (p ⊔ c) ≠ ⊥ :=
    lines_meet_if_coplanar h_cov h_in_plane h_pc_not hp hp_lt_pc
  -- The meet is an atom: strictly between ⊥ and p ⊔ c (a line).
  -- Use line_height_two on the line p ⊔ c, not on a₂ ⊔ b₂.
  exact line_height_two hp hc hpc
    (bot_lt_iff_ne_bot.mpr (by rwa [inf_comm] at h_meet_ne))
    (lt_of_le_of_ne inf_le_left (fun h => h_pc_not (h ▸ inf_le_right)))

/-- A perspectivity maps atoms on one line to atoms on another,
    via central projection through a point not on either line.
    Works uniformly for all points, including the intersection. -/
noncomputable def perspectivity {c a₁ b₁ a₂ b₂ : L}
    (hc : IsAtom c) (_ha₁ : IsAtom a₁) (_hb₁ : IsAtom b₁) (ha₂ : IsAtom a₂) (hb₂ : IsAtom b₂)
    (_hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂)
    (hc_not_l₁ : ¬ c ≤ a₁ ⊔ b₁) (hc_not_l₂ : ¬ c ≤ a₂ ⊔ b₂)
    (h_coplanar : a₁ ⊔ b₁ ⊔ c = a₂ ⊔ b₂ ⊔ c) :
    AtomsOn (a₁ ⊔ b₁) → AtomsOn (a₂ ⊔ b₂) :=
  fun ⟨p, hp_atom, hp_le⟩ =>
    have hpc : p ≠ c := fun h => hc_not_l₁ (h ▸ hp_le)
    have hp_in_plane : p ⊔ c ≤ (a₂ ⊔ b₂) ⊔ c :=
      h_coplanar ▸ sup_le (le_sup_of_le_left hp_le) le_sup_right
    ⟨(p ⊔ c) ⊓ (a₂ ⊔ b₂),
     perspect_atom hc hp_atom hpc ha₂ hb₂ hab₂ hc_not_l₂ hp_in_plane,
     inf_le_right⟩

/-- Perspectivity is injective: distinct atoms map to distinct images.
    The proof splits on whether p ⊔ c = q ⊔ c (same/different lines through c).
    Same line: both land on l₁ ⊓ (p ⊔ c), an atom → p = q.
    Different lines: modular_intersection gives the image ≤ c → contradiction. -/
theorem perspectivity_injective {c a₁ b₁ a₂ b₂ : L}
    (hc : IsAtom c)
    (ha₁ : IsAtom a₁) (hb₁ : IsAtom b₁) (ha₂ : IsAtom a₂) (hb₂ : IsAtom b₂)
    (hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂)
    (hc_not_l₁ : ¬ c ≤ a₁ ⊔ b₁) (hc_not_l₂ : ¬ c ≤ a₂ ⊔ b₂)
    (h_coplanar : a₁ ⊔ b₁ ⊔ c = a₂ ⊔ b₂ ⊔ c)
    {p q : AtomsOn (a₁ ⊔ b₁)} (hpq : p ≠ q) :
    perspectivity hc ha₁ hb₁ ha₂ hb₂ hab₁ hab₂ hc_not_l₁ hc_not_l₂ h_coplanar p ≠
    perspectivity hc ha₁ hb₁ ha₂ hb₂ hab₁ hab₂ hc_not_l₁ hc_not_l₂ h_coplanar q := by
  obtain ⟨p, hp_atom, hp_le⟩ := p
  obtain ⟨q, hq_atom, hq_le⟩ := q
  -- Extract element-level inequality from subtype inequality
  have hpq_val : p ≠ q := fun h => hpq (Subtype.ext h)
  simp only [perspectivity]
  intro heq
  -- heq : ⟨(p ⊔ c) ⊓ l₂, ...⟩ = ⟨(q ⊔ c) ⊓ l₂, ...⟩
  have heq_val : (p ⊔ c) ⊓ (a₂ ⊔ b₂) = (q ⊔ c) ⊓ (a₂ ⊔ b₂) := congrArg Subtype.val heq
  have hpc : p ≠ c := fun h => hc_not_l₁ (h ▸ hp_le)
  have hqc : q ≠ c := fun h => hc_not_l₁ (h ▸ hq_le)
  by_cases h_lines : p ⊔ c = q ⊔ c
  · -- Same line through c: p, q both on l₁ ⊓ (p ⊔ c), which is a single atom → p = q.
    have h_ne : a₁ ⊔ b₁ ≠ p ⊔ c := fun h => hc_not_l₁ (h ▸ le_sup_right)
    have hl₁_not_le : ¬ (a₁ ⊔ b₁) ≤ p ⊔ c := by
      intro hle
      apply h_ne
      have ha₁_cov := line_covers_its_atoms hp_atom hc hpc ha₁ (le_trans le_sup_left hle)
      exact (ha₁_cov.eq_or_eq (atom_covBy_join ha₁ hb₁ hab₁).lt.le hle).resolve_left
        (ne_of_gt (atom_covBy_join ha₁ hb₁ hab₁).lt)
    have hp_le_meet : p ≤ (a₁ ⊔ b₁) ⊓ (p ⊔ c) := le_inf hp_le le_sup_left
    have hq_le_meet : q ≤ (a₁ ⊔ b₁) ⊓ (p ⊔ c) := le_inf hq_le (h_lines ▸ le_sup_left)
    have h_meet_atom : IsAtom ((a₁ ⊔ b₁) ⊓ (p ⊔ c)) :=
      line_height_two ha₁ hb₁ hab₁
        (bot_lt_iff_ne_bot.mpr (fun h => hp_atom.1 (le_antisymm (h ▸ hp_le_meet) bot_le)))
        (lt_of_le_of_ne inf_le_left (fun h => hl₁_not_le (h ▸ inf_le_right)))
    have hp_eq := le_antisymm hp_le_meet
      (h_meet_atom.le_iff.mp hp_le_meet |>.resolve_left hp_atom.1 ▸ le_refl _)
    have hq_eq := le_antisymm hq_le_meet
      (h_meet_atom.le_iff.mp hq_le_meet |>.resolve_left hq_atom.1 ▸ le_refl _)
    exact absurd (hp_eq.trans hq_eq.symm) hpq_val
  · -- Different lines through c: the shared image m satisfies m ≤ c, contradiction.
    have hm_le_pc : (p ⊔ c) ⊓ (a₂ ⊔ b₂) ≤ p ⊔ c := inf_le_left
    have hm_le_qc : (p ⊔ c) ⊓ (a₂ ⊔ b₂) ≤ q ⊔ c := heq_val ▸ inf_le_left
    have hq_not_pc : ¬ q ≤ p ⊔ c := by
      intro hle
      apply h_lines
      rw [sup_comm p c, sup_comm q c]
      exact line_eq_of_atom_le hc hp_atom hq_atom hpc.symm hqc.symm hpq_val
        (sup_comm p c ▸ hle)
    have h_meet_eq : (c ⊔ p) ⊓ (c ⊔ q) = c :=
      modular_intersection hc hp_atom hq_atom hpc.symm hqc.symm hpq_val
        (sup_comm c p ▸ hq_not_pc)
    have hm_le_c : (p ⊔ c) ⊓ (a₂ ⊔ b₂) ≤ c := by
      calc (p ⊔ c) ⊓ (a₂ ⊔ b₂)
          ≤ (p ⊔ c) ⊓ (q ⊔ c) := le_inf hm_le_pc hm_le_qc
        _ = (c ⊔ p) ⊓ (c ⊔ q) := by rw [sup_comm p c, sup_comm q c]
        _ = c := h_meet_eq
    have hp_in_plane : p ⊔ c ≤ (a₂ ⊔ b₂) ⊔ c :=
      h_coplanar ▸ sup_le (le_sup_of_le_left hp_le) le_sup_right
    have hm_atom := perspect_atom hc hp_atom hpc ha₂ hb₂ hab₂ hc_not_l₂ hp_in_plane
    rcases hc.le_iff.mp hm_le_c with h | h
    · exact absurd h hm_atom.1
    · exact absurd (h ▸ inf_le_right : c ≤ a₂ ⊔ b₂) hc_not_l₂

/-- Projection preserves the line through c: if q = (p ⊔ c) ⊓ l
    then q ⊔ c = p ⊔ c. The geometric content: projecting through c
    doesn't change which line through c you're on. -/
theorem perspect_line_eq {p c l : L}
    (hc : IsAtom c) (hp : IsAtom p) (hpc : p ≠ c)
    (hc_not : ¬ c ≤ l)
    (_h_in_plane : p ⊔ c ≤ l ⊔ c)
    (hq_atom : IsAtom ((p ⊔ c) ⊓ l)) :
    ((p ⊔ c) ⊓ l) ⊔ c = p ⊔ c := by
  -- q = (p ⊔ c) ⊓ l ≤ p ⊔ c, so q ⊔ c ≤ p ⊔ c.
  have hqc_le : ((p ⊔ c) ⊓ l) ⊔ c ≤ p ⊔ c := sup_le inf_le_left le_sup_right
  -- q ≠ c (since q ≤ l and c ≰ l)
  have hqc_ne : (p ⊔ c) ⊓ l ≠ c := fun h => hc_not (h ▸ inf_le_right)
  -- c < q ⊔ c (since q is an atom ≠ c, so q ⊔ c is strictly above c)
  have hc_lt_qc : c < ((p ⊔ c) ⊓ l) ⊔ c := by
    apply lt_of_le_of_ne le_sup_right
    intro h
    -- If c = q ⊔ c, then q ≤ q ⊔ c = c, so q ≤ c.
    have q_le_c : (p ⊔ c) ⊓ l ≤ c := le_sup_left.trans h.symm.le
    rcases hc.le_iff.mp q_le_c with h | h
    · exact hq_atom.1 h
    · exact hqc_ne h
  -- c ⋖ p ⊔ c (covering), so by c < q ⊔ c ≤ p ⊔ c, we get q ⊔ c = p ⊔ c.
  have hc_cov_pc : c ⋖ p ⊔ c := by
    rw [sup_comm]; exact atom_covBy_join hc hp hpc.symm
  exact (hc_cov_pc.eq_or_eq hc_lt_qc.le hqc_le).resolve_left (ne_of_gt hc_lt_qc)

/-- Round-trip: projecting from l₁ to l₂ and back gives the original point.
    This is the core of perspectivity being a bijection. -/
theorem perspect_roundtrip {p c a₁ b₁ a₂ b₂ : L}
    (hc : IsAtom c) (hp : IsAtom p) (hpc : p ≠ c)
    (ha₁ : IsAtom a₁) (hb₁ : IsAtom b₁) (hab₁ : a₁ ≠ b₁)
    (ha₂ : IsAtom a₂) (hb₂ : IsAtom b₂) (hab₂ : a₂ ≠ b₂)
    (hc_not_l₁ : ¬ c ≤ a₁ ⊔ b₁) (hc_not_l₂ : ¬ c ≤ a₂ ⊔ b₂)
    (h_coplanar : a₁ ⊔ b₁ ⊔ c = a₂ ⊔ b₂ ⊔ c)
    (hp_le : p ≤ a₁ ⊔ b₁) :
    ((p ⊔ c) ⊓ (a₂ ⊔ b₂) ⊔ c) ⊓ (a₁ ⊔ b₁) = p := by
  -- Let q = (p ⊔ c) ⊓ l₂. Then q ⊔ c = p ⊔ c (by perspect_line_eq).
  have hp_in_plane : p ⊔ c ≤ (a₂ ⊔ b₂) ⊔ c :=
    h_coplanar ▸ sup_le (le_sup_of_le_left hp_le) le_sup_right
  have hq_atom := perspect_atom hc hp hpc ha₂ hb₂ hab₂ hc_not_l₂ hp_in_plane
  have h_line_eq : (p ⊔ c) ⊓ (a₂ ⊔ b₂) ⊔ c = p ⊔ c :=
    perspect_line_eq hc hp hpc hc_not_l₂ hp_in_plane hq_atom
  -- So the round-trip is (p ⊔ c) ⊓ l₁.
  rw [h_line_eq]
  -- p ≤ p ⊔ c and p ≤ l₁, so p ≤ (p ⊔ c) ⊓ l₁.
  have hp_le_meet : p ≤ (p ⊔ c) ⊓ (a₁ ⊔ b₁) := le_inf le_sup_left hp_le
  -- (p ⊔ c) ⊓ l₁ is an atom (by perspect_atom in the reverse direction).
  have hq_in_plane : p ⊔ c ≤ (a₁ ⊔ b₁) ⊔ c :=
    sup_le (le_sup_of_le_left hp_le) le_sup_right
  have h_meet_atom := perspect_atom hc hp hpc ha₁ hb₁ hab₁ hc_not_l₁ hq_in_plane
  -- p ≤ atom → p = atom (both are atoms).
  exact (h_meet_atom.le_iff.mp hp_le_meet |>.resolve_left hp.1).symm

/-- Perspectivity fixes the intersection: if p is on both lines,
    it maps to itself. -/
theorem perspect_fixes_intersection {p c a₁ b₁ a₂ b₂ : L}
    (hc : IsAtom c) (hp : IsAtom p) (hpc : p ≠ c)
    (_ha₂ : IsAtom a₂) (_hb₂ : IsAtom b₂) (_hab₂ : a₂ ≠ b₂)
    (hc_not_l₂ : ¬ c ≤ a₂ ⊔ b₂)
    (_hp_le₁ : p ≤ a₁ ⊔ b₁) (hp_le₂ : p ≤ a₂ ⊔ b₂)
    (h_in_plane : p ⊔ c ≤ (a₂ ⊔ b₂) ⊔ c) :
    (p ⊔ c) ⊓ (a₂ ⊔ b₂) = p := by
  -- p ≤ p ⊔ c and p ≤ l₂, so p ≤ (p ⊔ c) ⊓ l₂.
  have hp_le_meet : p ≤ (p ⊔ c) ⊓ (a₂ ⊔ b₂) := le_inf le_sup_left hp_le₂
  -- The meet is an atom.
  have h_atom := perspect_atom hc hp hpc _ha₂ _hb₂ _hab₂ hc_not_l₂ h_in_plane
  -- p ≤ atom and p is atom → p = atom.
  exact (h_atom.le_iff.mp hp_le_meet |>.resolve_left hp.1).symm

-- § Coordinate system

/-- A coordinate system for the von Staudt construction.

    Fixed data:
    - Line l = O ⊔ U (the "coordinate line")
    - Atom I on l (the "unit"), distinct from O and U
    - Atom V off l (determines auxiliary line m = U ⊔ V)
    - Atom C off both l and m, in the plane (the "standard center")

    From this we derive:
    - E = (O ⊔ C) ⊓ m (the "zero" on m, projection of O via C)
    - Addition: a + b uses C for l→m and a third point on b ⊔ E for m→l
    - Multiplication: uses perspectivities fixing O and U -/
structure CoordSystem (L : Type u) [Lattice L] [BoundedOrder L]
    [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] where
  O : L
  U : L
  I : L
  V : L
  C : L
  hO : IsAtom O
  hU : IsAtom U
  hI : IsAtom I
  hV : IsAtom V
  hC : IsAtom C
  hOU : O ≠ U
  hOI : O ≠ I
  hUI : U ≠ I
  hI_on : I ≤ O ⊔ U          -- I is on the coordinate line
  hV_off : ¬ V ≤ O ⊔ U       -- V is not on l
  hC_not_l : ¬ C ≤ O ⊔ U     -- C is not on l
  hC_not_m : ¬ C ≤ U ⊔ V     -- C is not on m
  hC_plane : C ≤ O ⊔ U ⊔ V   -- C is in the plane

variable (Γ : CoordSystem L)

/-- The coordinate line. -/
def CoordSystem.l : L := Γ.O ⊔ Γ.U

/-- The auxiliary line through U. -/
def CoordSystem.m : L := Γ.U ⊔ Γ.V

/-- The plane of the coordinate system. -/
def CoordSystem.π : L := Γ.O ⊔ Γ.U ⊔ Γ.V

/-- U is on both lines (the intersection point). -/
theorem CoordSystem.hU_on_l : Γ.U ≤ Γ.l :=
  le_sup_right

theorem CoordSystem.hU_on_m : Γ.U ≤ Γ.m :=
  le_sup_left

/-- E: the projection of O onto m via center C. This is the "zero" on m. -/
noncomputable def CoordSystem.E : L := (Γ.O ⊔ Γ.C) ⊓ Γ.m

/-- O is not on m (= U ⊔ V). -/
theorem CoordSystem.hO_not_m : ¬ Γ.O ≤ Γ.U ⊔ Γ.V := by
  intro hle
  apply Γ.hV_off
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have h_cov := line_covers_its_atoms Γ.hU Γ.hV hUV Γ.hO hle
  have h_cov_l := atom_covBy_join Γ.hO Γ.hU Γ.hOU
  exact (h_cov.eq_or_eq h_cov_l.lt.le (sup_le hle le_sup_left)).resolve_left
    (ne_of_gt h_cov_l.lt) ▸ le_sup_right

/-- m ⋖ π: the auxiliary line is covered by the plane. -/
theorem CoordSystem.m_covBy_π : (Γ.U ⊔ Γ.V) ⋖ (Γ.O ⊔ Γ.U ⊔ Γ.V) := by
  have h_meet : Γ.O ⊓ (Γ.U ⊔ Γ.V) = ⊥ := by
    rcases Γ.hO.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) Γ.hO_not_m
  have := covBy_sup_of_inf_covBy_left (h_meet ▸ Γ.hO.bot_covBy)
  rwa [show Γ.O ⊔ (Γ.U ⊔ Γ.V) = Γ.O ⊔ Γ.U ⊔ Γ.V from (sup_assoc _ _ _).symm] at this

/-- m ⊔ C = π: C is off m, in the plane, so generates the whole plane with m. -/
theorem CoordSystem.m_sup_C_eq_π : (Γ.U ⊔ Γ.V) ⊔ Γ.C = Γ.O ⊔ Γ.U ⊔ Γ.V := by
  have h_lt : Γ.U ⊔ Γ.V < (Γ.U ⊔ Γ.V) ⊔ Γ.C := lt_of_le_of_ne le_sup_left
    (fun h => Γ.hC_not_m (h ▸ le_sup_right))
  have h_le : (Γ.U ⊔ Γ.V) ⊔ Γ.C ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right) Γ.hC_plane
  exact (Γ.m_covBy_π.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)

/-- E is an atom on m. -/
theorem CoordSystem.hE_atom : IsAtom Γ.E := by
  unfold CoordSystem.E CoordSystem.m
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have h_in_plane : Γ.O ⊔ Γ.C ≤ (Γ.U ⊔ Γ.V) ⊔ Γ.C := by
    have h := Γ.m_sup_C_eq_π
    rw [h]
    exact sup_le (le_sup_of_le_left le_sup_left) Γ.hC_plane
  exact perspect_atom Γ.hC Γ.hO hOC Γ.hU Γ.hV hUV Γ.hC_not_m h_in_plane

variable {Γ}

-- § Addition via perspectivities

/-- E is not equal to U (since E ≤ O ⊔ C line and U is not, unless U = E
    which would force C on m). -/
theorem CoordSystem.hEU : Γ.E ≠ Γ.U := by
  unfold CoordSystem.E CoordSystem.m
  intro h
  -- E = U means (O ⊔ C) ⊓ (U ⊔ V) = U
  -- So U ≤ O ⊔ C. Then O ⊔ C ≥ O and O ⊔ C ≥ U, so O ⊔ C ≥ O ⊔ U = l.
  -- But C ≤ O ⊔ C and O ⊔ C is a line (join of two atoms O ≠ C).
  -- If O ⊔ U ≤ O ⊔ C, then by covering (O ⋖ O ⊔ U and O ⋖ O ⊔ C):
  -- O ⊔ U = O ⊔ C. Then C ≤ O ⊔ U = l, contradicting hC_not_l.
  have hU_le : Γ.U ≤ Γ.O ⊔ Γ.C := h ▸ inf_le_left
  have hOC : Γ.O ≠ Γ.C := fun heq => Γ.hC_not_l (heq ▸ le_sup_left)
  have h_cov_OC := atom_covBy_join Γ.hO Γ.hC hOC
  have h_cov_OU := atom_covBy_join Γ.hO Γ.hU Γ.hOU
  have h_le : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left hU_le
  exact Γ.hC_not_l ((h_cov_OC.eq_or_eq h_cov_OU.lt.le h_le).resolve_left
    (ne_of_gt h_cov_OU.lt) ▸ le_sup_right)

/-- l ⊓ m = U: the coordinate line meets the auxiliary line at U. -/
theorem CoordSystem.l_inf_m_eq_U : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
  rw [sup_comm Γ.O Γ.U]
  -- modular_intersection with a=U, b=O, c=V gives (U⊔O) ⊓ (U⊔V) = U
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hOV : Γ.O ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_left)
  have hV_not : ¬ Γ.V ≤ Γ.U ⊔ Γ.O := by
    intro h; exact Γ.hV_off (le_trans h (by rw [sup_comm]))
  exact modular_intersection Γ.hU Γ.hO Γ.hV Γ.hOU.symm hUV hOV hV_not

/-- An atom on l that's also on m must be U. -/
theorem CoordSystem.atom_on_both_eq_U {p : L} (hp : IsAtom p)
    (hp_l : p ≤ Γ.O ⊔ Γ.U) (hp_m : p ≤ Γ.U ⊔ Γ.V) : p = Γ.U := by
  have hp_le : p ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) := le_inf hp_l hp_m
  rw [Γ.l_inf_m_eq_U] at hp_le
  exact (Γ.hU.le_iff.mp hp_le).resolve_left hp.1

/-- E is on m. -/
theorem CoordSystem.hE_on_m : Γ.E ≤ Γ.U ⊔ Γ.V := by
  unfold CoordSystem.E CoordSystem.m; exact inf_le_right

/-- E is not on the coordinate line l. -/
theorem CoordSystem.hE_not_l : ¬ Γ.E ≤ Γ.O ⊔ Γ.U :=
  fun hE_l => absurd (Γ.atom_on_both_eq_U Γ.hE_atom hE_l CoordSystem.hE_on_m)
    CoordSystem.hEU

/-- O ≠ E (O is not on m, but E is). -/
theorem CoordSystem.hOE : Γ.O ≠ Γ.E :=
  fun h => Γ.hO_not_m (h ▸ CoordSystem.hE_on_m)

/-- E ≤ O ⊔ C (E is on the line through O and C). -/
theorem CoordSystem.hE_le_OC : Γ.E ≤ Γ.O ⊔ Γ.C := by
  unfold CoordSystem.E CoordSystem.m; exact inf_le_left

/-- O ⊔ E = O ⊔ C: E is on line O ⊔ C and E ≠ O, so they span the same line. -/
theorem CoordSystem.OE_eq_OC : Γ.O ⊔ Γ.E = Γ.O ⊔ Γ.C := by
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have h_le : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left CoordSystem.hE_le_OC
  exact ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
    (atom_covBy_join Γ.hO Γ.hE_atom CoordSystem.hOE).lt.le h_le).resolve_left
    (ne_of_gt (atom_covBy_join Γ.hO Γ.hE_atom CoordSystem.hOE).lt)

/-- E ⊔ U = m: E and U are distinct atoms on m, generating it. -/
theorem CoordSystem.EU_eq_m : Γ.E ⊔ Γ.U = Γ.U ⊔ Γ.V := by
  rw [sup_comm Γ.E Γ.U]
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have h_le : Γ.U ⊔ Γ.E ≤ Γ.U ⊔ Γ.V := sup_le le_sup_left CoordSystem.hE_on_m
  have h_lt : Γ.U < Γ.U ⊔ Γ.E := by
    apply lt_of_le_of_ne le_sup_left; intro h
    have : Γ.E ≤ Γ.U := h ▸ le_sup_right
    exact absurd ((Γ.hU.le_iff.mp this).resolve_left Γ.hE_atom.1) CoordSystem.hEU
  exact ((atom_covBy_join Γ.hU Γ.hV hUV).eq_or_eq h_lt.le h_le).resolve_left
    (ne_of_gt h_lt)

/-- O is not on line U ⊔ C. -/
theorem CoordSystem.hO_not_UC : ¬ Γ.O ≤ Γ.U ⊔ Γ.C := by
  intro h
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have h_le : Γ.U ⊔ Γ.O ≤ Γ.U ⊔ Γ.C := sup_le le_sup_left h
  have h_eq := ((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
    (atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).lt.le h_le).resolve_left
    (ne_of_gt (atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).lt)
  -- U ⊔ O = U ⊔ C, so C ≤ U ⊔ C = U ⊔ O.
  -- U ⊔ O = O ⊔ U = l, so C ≤ l. Contradiction.
  have : Γ.C ≤ Γ.U ⊔ Γ.O := h_eq ▸ le_sup_right
  exact Γ.hC_not_l (this.trans (by rw [sup_comm]))

/-- (O ⊔ C) ⊓ (U ⊔ C) = C: two distinct lines through C meet at C. -/
theorem CoordSystem.OC_inf_UC : (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C) = Γ.C := by
  rw [sup_comm Γ.O Γ.C, sup_comm Γ.U Γ.C]
  have hCO : Γ.C ≠ Γ.O := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hCU : Γ.C ≠ Γ.U := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hU_not_CO : ¬ Γ.U ≤ Γ.C ⊔ Γ.O := by
    intro h
    have hU_le_OC : Γ.U ≤ Γ.O ⊔ Γ.C := le_trans h (by rw [sup_comm Γ.C Γ.O])
    have h_le : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left hU_le_OC
    have h_eq := ((atom_covBy_join Γ.hO Γ.hC hCO.symm).eq_or_eq
      (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le h_le).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)
    exact Γ.hC_not_l (h_eq ▸ le_sup_right)
  exact modular_intersection Γ.hC Γ.hO Γ.hU hCO hCU Γ.hOU hU_not_CO

/-- Addition on the coordinate line.

    a + b = ((a ⊔ C) ⊓ m ⊔ D) ⊓ l

    where D = (b ⊔ E) ⊓ (U ⊔ C) is the canonical center for the
    return perspectivity, determined by b. The forward perspectivity
    projects a from l to m via center C; the return projects from m
    back to l via D. Since D lies on b ⊔ E, the return perspectivity
    sends E ↦ b. -/
noncomputable def coord_add (Γ : CoordSystem L) (a b : L) : L :=
  ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U)

/-- O is a left additive identity: O + b = b.

    With a = O, the forward perspectivity gives a' = E.
    By the modular law, E ⊔ D = (E ⊔ U ⊔ C) ⊓ (b ⊔ E) = π ⊓ (b ⊔ E) = b ⊔ E.
    Then (b ⊔ E) ⊓ l = b since b ≤ l and E ≰ l. -/
theorem coord_add_left_zero (Γ : CoordSystem L)
    (b : L) (hb : IsAtom b) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hb_ne_U : b ≠ Γ.U) :
    coord_add Γ Γ.O b = b := by
  -- After unfolding, (O⊔C)⊓(U⊔V) = E definitionally. Fold it.
  unfold coord_add
  change (Γ.E ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U) = b
  -- E ⊔ D = b ⊔ E by the modular law.
  have hbE_le_π : b ⊔ Γ.E ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (hb_on.trans le_sup_left)
      (CoordSystem.hE_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  have hED : Γ.E ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) = b ⊔ Γ.E :=
    calc Γ.E ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
        = Γ.E ⊔ (Γ.U ⊔ Γ.C) ⊓ (b ⊔ Γ.E) := by
            rw [@inf_comm L _ (b ⊔ Γ.E) (Γ.U ⊔ Γ.C)]
      _ = (Γ.E ⊔ (Γ.U ⊔ Γ.C)) ⊓ (b ⊔ Γ.E) :=
            (sup_inf_assoc_of_le (Γ.U ⊔ Γ.C) le_sup_right).symm
      _ = (Γ.E ⊔ Γ.U ⊔ Γ.C) ⊓ (b ⊔ Γ.E) := by rw [sup_assoc]
      _ = (Γ.U ⊔ Γ.V ⊔ Γ.C) ⊓ (b ⊔ Γ.E) := by rw [CoordSystem.EU_eq_m]
      _ = (Γ.O ⊔ Γ.U ⊔ Γ.V) ⊓ (b ⊔ Γ.E) := by rw [Γ.m_sup_C_eq_π]
      _ = b ⊔ Γ.E := inf_eq_right.mpr hbE_le_π
  rw [hED]
  -- (b ⊔ E) ⊓ l = b: b ≤ both sides, E ≰ l, so the meet is an atom = b.
  have hb_le : b ≤ (b ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left hb_on
  have hbE : b ≠ Γ.E := fun he => hb_ne_U
    (Γ.atom_on_both_eq_U hb hb_on (he ▸ CoordSystem.hE_on_m))
  have h_lt : (b ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro h
    -- h: (b⊔E) ⊓ l = l, so l ≤ b⊔E.
    -- b ⋖ b⊔E and b < l ≤ b⊔E, so l = b⊔E.
    -- Then E ≤ l, contradicting hE_not_l.
    have hl_le : Γ.O ⊔ Γ.U ≤ b ⊔ Γ.E := inf_eq_right.mp h
    have h_eq := ((atom_covBy_join hb Γ.hE_atom hbE).eq_or_eq
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hb hb_on).lt.le hl_le).resolve_left
      (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hb hb_on).lt)
    exact CoordSystem.hE_not_l (le_sup_right.trans (le_of_eq h_eq.symm))
  exact ((line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le hb.bot_lt hb_le) h_lt
    |>.le_iff.mp hb_le).resolve_left hb.1).symm

/-- O is a right additive identity: a + O = a.

    With b = O, D = (O ⊔ E) ⊓ (U ⊔ C) = (O ⊔ C) ⊓ (U ⊔ C) = C.
    Then a' ⊔ C = a ⊔ C (covering), and (a ⊔ C) ⊓ l = a. -/
theorem coord_add_right_zero (Γ : CoordSystem L)
    (a : L) (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) :
    coord_add Γ a Γ.O = a := by
  unfold coord_add
  -- D = (O ⊔ E) ⊓ (U ⊔ C). Rewrite: O ⊔ E = O ⊔ C, (O⊔C) ⊓ (U⊔C) = C.
  rw [CoordSystem.OE_eq_OC, CoordSystem.OC_inf_UC]
  -- Goal: ((a ⊔ C) ⊓ m ⊔ C) ⊓ l = a.
  -- a' ⊔ C = a ⊔ C: a' ≤ a ⊔ C (inf_le_left), C ≤ a ⊔ C (le_sup_right),
  -- so a' ⊔ C ≤ a ⊔ C. And C < a' ⊔ C (since a' ≰ C: a' ≤ m, C ≰ m).
  -- By covering C ⋖ a ⊔ C, we get a' ⊔ C = a ⊔ C.
  have hAC : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have ha'C_le : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ Γ.C ≤ a ⊔ Γ.C :=
    sup_le inf_le_left le_sup_right
  -- a' ≠ ⊥: lines a ⊔ C and m are coplanar and distinct, so they meet.
  have ha_lt_aC : a < a ⊔ Γ.C := by
    apply lt_of_le_of_ne le_sup_left; intro h
    have hC_le_a : Γ.C ≤ a := by rw [h]; exact le_sup_right
    exact Γ.hC_not_l ((ha.le_iff.mp hC_le_a).resolve_left Γ.hC.1 ▸ ha_on)
  have ha'_ne_bot : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≠ ⊥ := by
    have h_meet := lines_meet_if_coplanar Γ.m_covBy_π
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane)
      (fun h => Γ.hC_not_m (le_trans le_sup_right h))
      ha ha_lt_aC
    rwa [@inf_comm L _] at h_meet
  have hC_lt : Γ.C < (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ Γ.C := by
    apply lt_of_le_of_ne le_sup_right; intro h
    -- a' ⊔ C = C means a' ≤ C. Then a' ≤ C ⊓ m = ⊥. So a' = ⊥.
    have ha'_le_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.C := le_sup_left.trans h.symm.le
    have ha'_le_m : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V := inf_le_right
    have hCm : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ := by
      rcases Γ.hC.le_iff.mp inf_le_left with h | h
      · exact h
      · exact absurd (h ▸ inf_le_right) Γ.hC_not_m
    have : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ ⊥ := hCm ▸ le_inf ha'_le_C ha'_le_m
    exact ha'_ne_bot (le_antisymm this bot_le)
  have h_cov_Ca : Γ.C ⋖ a ⊔ Γ.C := by
    have := atom_covBy_join Γ.hC ha hAC.symm; rwa [sup_comm] at this
  have ha'C_eq : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ Γ.C = a ⊔ Γ.C :=
    (h_cov_Ca.eq_or_eq hC_lt.le ha'C_le).resolve_left (ne_of_gt hC_lt)
  rw [ha'C_eq]
  -- (a ⊔ C) ⊓ l = a.
  have ha_le : a ≤ (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left ha_on
  have h_lt : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro h
    have hl_le := inf_eq_right.mp h  -- l ≤ a ⊔ C
    -- a ⋖ a ⊔ C, a < l ≤ a ⊔ C ⟹ l = a ⊔ C ⟹ C ≤ l.
    have h_eq := ((atom_covBy_join ha Γ.hC hAC).eq_or_eq
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le hl_le).resolve_left
      (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)
    exact Γ.hC_not_l (le_sup_right.trans (le_of_eq h_eq.symm))
  exact ((line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le ha.bot_lt ha_le) h_lt
    |>.le_iff.mp ha_le).resolve_left ha.1).symm

/-- If R is an atom not in π and s ≤ π, then π ⊓ (R ⊔ s) = s.
    The modular law gives (s ⊔ R) ⊓ π = s ⊔ (R ⊓ π) = s ⊔ ⊥ = s,
    using the fact that an atom outside π meets π trivially. -/
theorem inf_sup_of_atom_not_le {s π R : L}
    (hR : IsAtom R) (hR_not : ¬ R ≤ π) (hs_le : s ≤ π) :
    π ⊓ (R ⊔ s) = s := by
  have hR_inf : R ⊓ π = ⊥ :=
    (hR.le_iff.mp inf_le_left).resolve_right (fun h => hR_not (h ▸ inf_le_right))
  have key : (s ⊔ R) ⊓ π = s ⊔ R ⊓ π := sup_inf_assoc_of_le R hs_le
  rw [hR_inf, sup_bot_eq] at key  -- key : (s ⊔ R) ⊓ π = s
  rw [sup_comm, inf_comm] at key   -- key : π ⊓ (R ⊔ s) = s
  exact key


/-- **Lifting preserves side intersections.**

    When a triangle side b₁ ⊔ b₂ is "lifted" to b₁' ⊔ b₂' (with
    b_i' on both o' ⊔ a_i and R ⊔ b_i), the lifted side meets
    a₁ ⊔ a₂ at the same point as the original side.

    Proof: both lines are in o' ⊔ a₁ ⊔ a₂ (a plane), so they meet
    at an atom T. Then T ≤ π (from a₁ ⊔ a₂ ≤ π) and T ≤ R ⊔ b₁ ⊔ b₂
    (from lifting). The modular law gives π ⊓ (R ⊔ b₁ ⊔ b₂) = b₁ ⊔ b₂.
    So T ≤ (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) = S, and since both are atoms, T = S. -/
theorem lift_side_intersection
    {a₁ a₂ b₁ b₂ R o' b₁' b₂' π : L}
    (ha₁ : IsAtom a₁) (ha₂ : IsAtom a₂) (ha₁₂ : a₁ ≠ a₂)
    (hb₁ : IsAtom b₁) (hb₂ : IsAtom b₂) (hb₁₂ : b₁ ≠ b₂)
    (hb₁' : IsAtom b₁') (hb₂' : IsAtom b₂') (hb₁₂' : b₁' ≠ b₂')
    (hR : IsAtom R) (ho' : IsAtom o')
    (ha_le : a₁ ⊔ a₂ ≤ π) (hb_le : b₁ ⊔ b₂ ≤ π)
    (h_sides : a₁ ⊔ a₂ ≠ b₁ ⊔ b₂)
    (hR_not : ¬ R ≤ π) (ho'_not : ¬ o' ≤ π)
    (hb₁'_oa : b₁' ≤ o' ⊔ a₁) (hb₂'_oa : b₂' ≤ o' ⊔ a₂)
    (hb₁'_Rb : b₁' ≤ R ⊔ b₁) (hb₂'_Rb : b₂' ≤ R ⊔ b₂)
    (hb₁'_not : ¬ b₁' ≤ π) :
    (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') = (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) := by
  -- Both lines are in τ = o' ⊔ a₁ ⊔ a₂.
  have hb'_le_τ : b₁' ⊔ b₂' ≤ o' ⊔ a₁ ⊔ a₂ :=
    sup_le (hb₁'_oa.trans (sup_le (le_sup_left.trans le_sup_left)
      (le_sup_right.trans le_sup_left)))
    (hb₂'_oa.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  -- a₁ ⊔ a₂ ⋖ τ
  have ho'_disj : o' ⊓ (a₁ ⊔ a₂) = ⊥ :=
    (ho'.le_iff.mp inf_le_left).resolve_right
      (fun h => ho'_not (le_trans (h ▸ inf_le_right) ha_le))
  have h_cov_τ : a₁ ⊔ a₂ ⋖ o' ⊔ a₁ ⊔ a₂ := by
    have h := covBy_sup_of_inf_covBy_left (ho'_disj ▸ ho'.bot_covBy)
    rw [← sup_assoc] at h; exact h
  -- b₁' ⊔ b₂' ≰ a₁ ⊔ a₂
  have hb'_not : ¬ b₁' ⊔ b₂' ≤ a₁ ⊔ a₂ :=
    fun h => hb₁'_not (le_trans le_sup_left (le_trans h ha_le))
  -- T ≠ ⊥: two lines in a plane meet.
  have hT_ne : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') ≠ ⊥ :=
    lines_meet_if_coplanar h_cov_τ hb'_le_τ hb'_not hb₁'
      (atom_covBy_join hb₁' hb₂' hb₁₂').lt
  -- T < a₁ ⊔ a₂
  have hT_lt : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') < a₁ ⊔ a₂ := by
    apply lt_of_le_of_ne inf_le_left; intro h
    have h_le : a₁ ⊔ a₂ ≤ b₁' ⊔ b₂' := inf_eq_left.mp h
    rcases h_cov_τ.eq_or_eq h_le hb'_le_τ with heq | heq
    · -- b₁' ⊔ b₂' = a₁ ⊔ a₂: then b₁' ≤ π, contradiction
      exact hb₁'_not (le_trans le_sup_left (heq ▸ ha_le))
    · -- b₁' ⊔ b₂' = τ (plane): impossible, a₁ ⊔ a₂ is between ⊥ and b₁'⊔b₂'
      -- but not an atom (a₁ is strictly between)
      have h_aa_lt : a₁ ⊔ a₂ < b₁' ⊔ b₂' :=
        lt_of_lt_of_le h_cov_τ.lt (le_of_eq heq.symm)
      have h_aa_atom := line_height_two hb₁' hb₂' hb₁₂'
        (lt_of_lt_of_le ha₁.bot_lt le_sup_left) h_aa_lt
      -- a₁ ⊔ a₂ is an atom but ⊥ < a₁ < a₁ ⊔ a₂ — violates covering
      exact h_aa_atom.bot_covBy.2 ha₁.bot_lt (atom_covBy_join ha₁ ha₂ ha₁₂).lt
  -- T is an atom.
  have hT_atom : IsAtom ((a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂')) :=
    line_height_two ha₁ ha₂ ha₁₂ (bot_lt_iff_ne_bot.mpr hT_ne) hT_lt
  -- T ≤ b₁ ⊔ b₂ via modular law.
  have hT_le_bb : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') ≤ b₁ ⊔ b₂ := by
    have hT_le_π : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') ≤ π := le_trans inf_le_left ha_le
    have hT_le_Rbb : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') ≤ R ⊔ (b₁ ⊔ b₂) :=
      le_trans inf_le_right (sup_le
        (hb₁'_Rb.trans (sup_le le_sup_left (le_sup_left.trans le_sup_right)))
        (hb₂'_Rb.trans (sup_le le_sup_left (le_sup_right.trans le_sup_right))))
    calc (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂')
        ≤ π ⊓ (R ⊔ (b₁ ⊔ b₂)) := le_inf hT_le_π hT_le_Rbb
      _ = b₁ ⊔ b₂ := inf_sup_of_atom_not_le hR hR_not hb_le
  -- T ≤ S.
  have hT_le_S : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') ≤ (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) :=
    le_inf inf_le_left hT_le_bb
  -- S is an atom.
  have hS_lt : (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) < a₁ ⊔ a₂ := by
    apply lt_of_le_of_ne inf_le_left; intro h
    have h_le : a₁ ⊔ a₂ ≤ b₁ ⊔ b₂ := inf_eq_left.mp h
    have ha₁_cov := line_covers_its_atoms hb₁ hb₂ hb₁₂ ha₁ (le_sup_left.trans h_le)
    exact h_sides ((ha₁_cov.eq_or_eq (atom_covBy_join ha₁ ha₂ ha₁₂).lt.le h_le).resolve_left
      (ne_of_gt (atom_covBy_join ha₁ ha₂ ha₁₂).lt))
  have hS_atom : IsAtom ((a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂)) :=
    line_height_two ha₁ ha₂ ha₁₂ (lt_of_lt_of_le hT_atom.bot_lt hT_le_S) hS_lt
  exact (hS_atom.le_iff.mp hT_le_S).resolve_left hT_atom.1

/-- **Desargues' theorem (planar case).**

    Two triangles in a plane π, perspective from a point o, have
    their three pairs of corresponding sides meeting on a common
    line — provided the lattice has height ≥ 4 (an atom outside π
    exists) and irreducibility (lines have ≥ 3 points).

    The proof lifts one triangle out of the plane using an external
    point R, applies the non-planar Desargues theorem, and uses
    lift_side_intersection to transfer collinearity back.

    This is the theorem that makes dimension matter: the algebra of
    the plane inherits its structure from the space it sits in. -/
theorem desargues_planar
    {o a₁ a₂ a₃ b₁ b₂ b₃ π : L}
    -- All atoms in the plane
    (ho : IsAtom o) (ha₁ : IsAtom a₁) (ha₂ : IsAtom a₂) (ha₃ : IsAtom a₃)
    (hb₁ : IsAtom b₁) (hb₂ : IsAtom b₂) (hb₃ : IsAtom b₃)
    -- All in π
    (ho_le : o ≤ π) (ha₁_le : a₁ ≤ π) (ha₂_le : a₂ ≤ π) (ha₃_le : a₃ ≤ π)
    (hb₁_le : b₁ ≤ π) (hb₂_le : b₂ ≤ π) (hb₃_le : b₃ ≤ π)
    -- Perspective from o: b_i on line o ⊔ a_i
    (hb₁_on : b₁ ≤ o ⊔ a₁) (hb₂_on : b₂ ≤ o ⊔ a₂) (hb₃_on : b₃ ≤ o ⊔ a₃)
    -- Distinct triangle vertices
    (ha₁₂ : a₁ ≠ a₂) (ha₁₃ : a₁ ≠ a₃) (ha₂₃ : a₂ ≠ a₃)
    (hb₁₂ : b₁ ≠ b₂) (hb₁₃ : b₁ ≠ b₃) (hb₂₃ : b₂ ≠ b₃)
    -- Distinct corresponding sides
    (h_sides₁₂ : a₁ ⊔ a₂ ≠ b₁ ⊔ b₂)
    (h_sides₁₃ : a₁ ⊔ a₃ ≠ b₁ ⊔ b₃)
    (h_sides₂₃ : a₂ ⊔ a₃ ≠ b₂ ⊔ b₃)
    -- Triangle planes (both in π)
    (hπA : a₁ ⊔ a₂ ⊔ a₃ = π) (hπB : b₁ ⊔ b₂ ⊔ b₃ = π)
    -- o ≠ a_i (center is off the triangle)
    (hoa₁ : o ≠ a₁) (hoa₂ : o ≠ a₂) (hoa₃ : o ≠ a₃)
    -- o ≠ b_i (center is off both triangles)
    (hob₁ : o ≠ b₁) (hob₂ : o ≠ b₂) (hob₃ : o ≠ b₃)
    -- Corresponding vertices are distinct
    (ha₁b₁ : a₁ ≠ b₁) (ha₂b₂ : a₂ ≠ b₂) (ha₃b₃ : a₃ ≠ b₃)
    -- Height ≥ 4: an atom outside π
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ π)
    -- Irreducibility: third atom on each line
    (h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    -- Sides are lines covered by π
    (h_cov₁₂ : a₁ ⊔ a₂ ⋖ π) (h_cov₁₃ : a₁ ⊔ a₃ ⋖ π) (h_cov₂₃ : a₂ ⊔ a₃ ⋖ π) :
    -- All three intersection points lie on a common line (strictly below π)
    ∃ (axis : L), axis ≤ π ∧ axis ≠ π ∧
      (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) ≤ axis ∧
      (a₁ ⊔ a₃) ⊓ (b₁ ⊔ b₃) ≤ axis ∧
      (a₂ ⊔ a₃) ⊓ (b₂ ⊔ b₃) ≤ axis := by
  -- Step 1: Pick o' on line R ⊔ o, distinct from R and o.
  have hRo : R ≠ o := fun h => hR_not (h ▸ ho_le)
  obtain ⟨o', ho'_atom, ho'_le, ho'_ne_R, ho'_ne_o⟩ := h_irred R o hR ho hRo
  have ho'_not : ¬ o' ≤ π := by
    intro h
    -- o' ≤ π and o' ≤ R ⊔ o. So o' ≤ π ⊓ (R ⊔ o) = o (modular law).
    have := inf_sup_of_atom_not_le hR hR_not ho_le
    have ho'_le_o : o' ≤ o := this ▸ le_inf h ho'_le
    exact ho'_ne_o ((ho.le_iff.mp ho'_le_o).resolve_left ho'_atom.1)
  -- Step 2: Define lifted vertices b_i' = (o' ⊔ a_i) ⊓ (R ⊔ b_i).
  set b₁' := (o' ⊔ a₁) ⊓ (R ⊔ b₁) with hb₁'_def
  set b₂' := (o' ⊔ a₂) ⊓ (R ⊔ b₂) with hb₂'_def
  set b₃' := (o' ⊔ a₃) ⊓ (R ⊔ b₃) with hb₃'_def

  -- Step 3: Mechanical properties of lifted vertices.

  -- Helpers: R ⊔ o' = R ⊔ o (o' is a third point on line R ⊔ o).
  have ho'_not_R : ¬ o' ≤ R := fun h =>
    ho'_ne_R ((hR.le_iff.mp h).resolve_left ho'_atom.1)
  have hRo'_eq : R ⊔ o' = R ⊔ o := by
    have h_cov := atom_covBy_join hR ho hRo
    have h_lt : R < R ⊔ o' := lt_of_le_of_ne le_sup_left
      (fun h => ho'_not_R (h ▸ le_sup_right))
    exact (h_cov.eq_or_eq h_lt.le (sup_le le_sup_left ho'_le)).resolve_left (ne_of_gt h_lt)
  -- o ≤ R ⊔ o' (since R ⊔ o' = R ⊔ o)
  have ho_le_Ro' : o ≤ R ⊔ o' := hRo'_eq ▸ (le_sup_right : o ≤ R ⊔ o)
  -- b_i ≱ R ⊔ o (if so, modular law gives b_i ≤ o, so b_i = o)
  have hb₁_not_Ro : ¬ b₁ ≤ R ⊔ o := fun h =>
    hob₁ ((ho.le_iff.mp (inf_sup_of_atom_not_le hR hR_not ho_le ▸
      le_inf hb₁_le h)).resolve_left hb₁.1).symm
  have hb₂_not_Ro : ¬ b₂ ≤ R ⊔ o := fun h =>
    hob₂ ((ho.le_iff.mp (inf_sup_of_atom_not_le hR hR_not ho_le ▸
      le_inf hb₂_le h)).resolve_left hb₂.1).symm
  have hb₃_not_Ro : ¬ b₃ ≤ R ⊔ o := fun h =>
    hob₃ ((ho.le_iff.mp (inf_sup_of_atom_not_le hR hR_not ho_le ▸
      le_inf hb₃_le h)).resolve_left hb₃.1).symm
  -- R ≠ b_i (since b_i ≤ π and R ≱ π)
  have hR_ne_b₁ : R ≠ b₁ := fun h => hR_not (h ▸ hb₁_le)
  have hR_ne_b₂ : R ≠ b₂ := fun h => hR_not (h ▸ hb₂_le)
  have hR_ne_b₃ : R ≠ b₃ := fun h => hR_not (h ▸ hb₃_le)
  -- o ⊔ b_i = o ⊔ a_i (since b_i ≤ o ⊔ a_i and o ≠ b_i, covering gives equality)
  have hob₁_eq : o ⊔ b₁ = o ⊔ a₁ :=
    ((atom_covBy_join ho ha₁ hoa₁).eq_or_eq le_sup_left
      (sup_le le_sup_left hb₁_on)).resolve_left
      (ne_of_gt (atom_covBy_join ho hb₁ hob₁).lt)
  have hob₂_eq : o ⊔ b₂ = o ⊔ a₂ :=
    ((atom_covBy_join ho ha₂ hoa₂).eq_or_eq le_sup_left
      (sup_le le_sup_left hb₂_on)).resolve_left
      (ne_of_gt (atom_covBy_join ho hb₂ hob₂).lt)
  have hob₃_eq : o ⊔ b₃ = o ⊔ a₃ :=
    ((atom_covBy_join ho ha₃ hoa₃).eq_or_eq le_sup_left
      (sup_le le_sup_left hb₃_on)).resolve_left
      (ne_of_gt (atom_covBy_join ho hb₃ hob₃).lt)
  -- a_i ≤ (R ⊔ b_i) ⊔ o': the plane through R, b_i, o' also contains a_i.
  -- Proof: o ⊔ b_i = o ⊔ a_i (since b_i ≤ o ⊔ a_i, covering).
  -- o ⊔ b_i ≤ (R ⊔ b_i) ⊔ o' (since o ≤ R ⊔ o' and b_i ≤ R ⊔ b_i).
  -- So a_i ≤ o ⊔ a_i = o ⊔ b_i ≤ (R ⊔ b_i) ⊔ o'.
  have hob_le₁ : o ⊔ b₁ ≤ (R ⊔ b₁) ⊔ o' :=
    sup_le (ho_le_Ro'.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      (le_sup_right.trans le_sup_left)
  have hob_le₂ : o ⊔ b₂ ≤ (R ⊔ b₂) ⊔ o' :=
    sup_le (ho_le_Ro'.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      (le_sup_right.trans le_sup_left)
  have hob_le₃ : o ⊔ b₃ ≤ (R ⊔ b₃) ⊔ o' :=
    sup_le (ho_le_Ro'.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      (le_sup_right.trans le_sup_left)
  have ha₁_in : a₁ ≤ (R ⊔ b₁) ⊔ o' := by
    calc a₁ ≤ o ⊔ a₁ := le_sup_right
      _ = o ⊔ b₁ := hob₁_eq.symm
      _ ≤ (R ⊔ b₁) ⊔ o' := hob_le₁
  have ha₂_in : a₂ ≤ (R ⊔ b₂) ⊔ o' := by
    calc a₂ ≤ o ⊔ a₂ := le_sup_right
      _ = o ⊔ b₂ := hob₂_eq.symm
      _ ≤ (R ⊔ b₂) ⊔ o' := hob_le₂
  have ha₃_in : a₃ ≤ (R ⊔ b₃) ⊔ o' := by
    calc a₃ ≤ o ⊔ a₃ := le_sup_right
      _ = o ⊔ b₃ := hob₃_eq.symm
      _ ≤ (R ⊔ b₃) ⊔ o' := hob_le₃
  -- o' ≱ R ⊔ b_i: if o' ≤ R ⊔ b_i, then o' ≤ (R ⊔ o) ⊓ (R ⊔ b_i).
  -- Since b_i ≱ R ⊔ o, lines R ⊔ o and R ⊔ b_i are distinct through R.
  -- Modular intersection: (R ⊔ o) ⊓ (R ⊔ b_i) = R. So o' ≤ R, o' = R. Contradiction.
  have ho'_not_Rb₁ : ¬ o' ≤ R ⊔ b₁ := by
    intro h
    have h_meet := modular_intersection hR ho hb₁ hRo hR_ne_b₁ hob₁ hb₁_not_Ro
    exact ho'_ne_R ((hR.le_iff.mp (h_meet ▸ le_inf ho'_le h)).resolve_left ho'_atom.1)
  have ho'_not_Rb₂ : ¬ o' ≤ R ⊔ b₂ := by
    intro h
    have h_meet := modular_intersection hR ho hb₂ hRo hR_ne_b₂ hob₂ hb₂_not_Ro
    exact ho'_ne_R ((hR.le_iff.mp (h_meet ▸ le_inf ho'_le h)).resolve_left ho'_atom.1)
  have ho'_not_Rb₃ : ¬ o' ≤ R ⊔ b₃ := by
    intro h
    have h_meet := modular_intersection hR ho hb₃ hRo hR_ne_b₃ hob₃ hb₃_not_Ro
    exact ho'_ne_R ((hR.le_iff.mp (h_meet ▸ le_inf ho'_le h)).resolve_left ho'_atom.1)
  -- a_i ≠ o' (since a_i ≤ π and o' ≱ π)
  have ha₁_ne_o' : a₁ ≠ o' := fun h => ho'_not (h ▸ ha₁_le)
  have ha₂_ne_o' : a₂ ≠ o' := fun h => ho'_not (h ▸ ha₂_le)
  have ha₃_ne_o' : a₃ ≠ o' := fun h => ho'_not (h ▸ ha₃_le)

  -- 3a: Each b_i' is an atom (perspect_atom with p=a_i, c=o', line=R ⊔ b_i).
  have hb₁'_atom : IsAtom b₁' := by
    rw [hb₁'_def, show o' ⊔ a₁ = a₁ ⊔ o' from sup_comm _ _]
    exact perspect_atom ho'_atom ha₁ ha₁_ne_o' hR hb₁ hR_ne_b₁
      ho'_not_Rb₁ (sup_le ha₁_in le_sup_right)
  have hb₂'_atom : IsAtom b₂' := by
    rw [hb₂'_def, show o' ⊔ a₂ = a₂ ⊔ o' from sup_comm _ _]
    exact perspect_atom ho'_atom ha₂ ha₂_ne_o' hR hb₂ hR_ne_b₂
      ho'_not_Rb₂ (sup_le ha₂_in le_sup_right)
  have hb₃'_atom : IsAtom b₃' := by
    rw [hb₃'_def, show o' ⊔ a₃ = a₃ ⊔ o' from sup_comm _ _]
    exact perspect_atom ho'_atom ha₃ ha₃_ne_o' hR hb₃ hR_ne_b₃
      ho'_not_Rb₃ (sup_le ha₃_in le_sup_right)

  -- 3b: b_i' ≱ π. If b_i' ≤ π, then b_i' ≤ π ⊓ (R ⊔ b_i) = b_i,
  -- so b_i' = b_i. Then b_i ≤ o' ⊔ a_i, so b_i ≤ π ⊓ (o' ⊔ a_i) = a_i,
  -- hence b_i = a_i. Contradiction with a_i ≠ b_i.
  have hb₁'_not : ¬ b₁' ≤ π := by
    intro h
    -- b₁' ≤ π ⊓ (R ⊔ b₁) = b₁
    have hb₁'_le_b₁ : b₁' ≤ b₁ := by
      have := inf_sup_of_atom_not_le hR hR_not hb₁_le
      exact this ▸ le_inf h inf_le_right
    have hb₁'_eq_b₁ : b₁' = b₁ :=
      (hb₁.le_iff.mp hb₁'_le_b₁).resolve_left hb₁'_atom.1
    -- Then b₁ ≤ o' ⊔ a₁, so b₁ ≤ π ⊓ (o' ⊔ a₁) = a₁
    have hb₁_le_o'a₁ : b₁ ≤ o' ⊔ a₁ := hb₁'_eq_b₁ ▸ (inf_le_left : b₁' ≤ o' ⊔ a₁)
    have hb₁_le_a₁ : b₁ ≤ a₁ := by
      have := inf_sup_of_atom_not_le ho'_atom ho'_not ha₁_le
      exact this ▸ le_inf hb₁_le hb₁_le_o'a₁
    exact ha₁b₁ ((ha₁.le_iff.mp hb₁_le_a₁).resolve_left hb₁.1).symm
  have hb₂'_not : ¬ b₂' ≤ π := by
    intro h
    have hb₂'_le_b₂ : b₂' ≤ b₂ := by
      have := inf_sup_of_atom_not_le hR hR_not hb₂_le
      exact this ▸ le_inf h inf_le_right
    have hb₂'_eq_b₂ : b₂' = b₂ :=
      (hb₂.le_iff.mp hb₂'_le_b₂).resolve_left hb₂'_atom.1
    have hb₂_le_o'a₂ : b₂ ≤ o' ⊔ a₂ := hb₂'_eq_b₂ ▸ (inf_le_left : b₂' ≤ o' ⊔ a₂)
    have hb₂_le_a₂ : b₂ ≤ a₂ := by
      have := inf_sup_of_atom_not_le ho'_atom ho'_not ha₂_le
      exact this ▸ le_inf hb₂_le hb₂_le_o'a₂
    exact ha₂b₂ ((ha₂.le_iff.mp hb₂_le_a₂).resolve_left hb₂.1).symm

  -- 3c: Lifted vertices are distinct.
  -- If b₁' = b₂', then b₁' ≤ (o' ⊔ a₁) ⊓ (o' ⊔ a₂) = o' (modular intersection,
  -- since a₂ ≱ o' ⊔ a₁ — otherwise o' ≤ a₁ ⊔ a₂ ≤ π, contradiction).
  -- Then o' ≤ R ⊔ b₁ (since b₁' ≤ R ⊔ b₁). But o' ≱ R ⊔ b₁. Contradiction.
  -- (o' ⊔ a_i) ⊓ (o' ⊔ a_j) = o' for distinct i,j.
  -- Non-collinearity: if a_j ≤ o' ⊔ a_i, then a_i ⊔ a_j ≤ o' ⊔ a_i.
  -- Covering a_i ⋖ o' ⊔ a_i (rewritten from a_i ⋖ a_i ⊔ o') gives
  -- o' ⊔ a_i = a_i ⊔ a_j, so o' ≤ a_i ⊔ a_j ≤ π, contradiction.
  have h_not_coll₁₂ : ¬ a₂ ≤ o' ⊔ a₁ := by
    intro h
    have h_le : a₁ ⊔ a₂ ≤ o' ⊔ a₁ := sup_le le_sup_right h
    have h_cov : a₁ ⋖ o' ⊔ a₁ := by
      rw [show o' ⊔ a₁ = a₁ ⊔ o' from sup_comm _ _]
      exact atom_covBy_join ha₁ ho'_atom ha₁_ne_o'
    have h_eq : a₁ ⊔ a₂ = o' ⊔ a₁ :=
      (h_cov.eq_or_eq (atom_covBy_join ha₁ ha₂ ha₁₂).lt.le h_le).resolve_left
        (ne_of_gt (atom_covBy_join ha₁ ha₂ ha₁₂).lt)
    exact ho'_not (calc o' ≤ o' ⊔ a₁ := le_sup_left
      _ = a₁ ⊔ a₂ := h_eq.symm
      _ ≤ π := sup_le ha₁_le ha₂_le)
  have h_not_coll₁₃ : ¬ a₃ ≤ o' ⊔ a₁ := by
    intro h
    have h_le : a₁ ⊔ a₃ ≤ o' ⊔ a₁ := sup_le le_sup_right h
    have h_cov : a₁ ⋖ o' ⊔ a₁ := by
      rw [show o' ⊔ a₁ = a₁ ⊔ o' from sup_comm _ _]
      exact atom_covBy_join ha₁ ho'_atom ha₁_ne_o'
    have h_eq : a₁ ⊔ a₃ = o' ⊔ a₁ :=
      (h_cov.eq_or_eq (atom_covBy_join ha₁ ha₃ ha₁₃).lt.le h_le).resolve_left
        (ne_of_gt (atom_covBy_join ha₁ ha₃ ha₁₃).lt)
    exact ho'_not (calc o' ≤ o' ⊔ a₁ := le_sup_left
      _ = a₁ ⊔ a₃ := h_eq.symm
      _ ≤ π := sup_le ha₁_le ha₃_le)
  have h_not_coll₂₃ : ¬ a₃ ≤ o' ⊔ a₂ := by
    intro h
    have h_le : a₂ ⊔ a₃ ≤ o' ⊔ a₂ := sup_le le_sup_right h
    have h_cov : a₂ ⋖ o' ⊔ a₂ := by
      rw [show o' ⊔ a₂ = a₂ ⊔ o' from sup_comm _ _]
      exact atom_covBy_join ha₂ ho'_atom ha₂_ne_o'
    have h_eq : a₂ ⊔ a₃ = o' ⊔ a₂ :=
      (h_cov.eq_or_eq (atom_covBy_join ha₂ ha₃ ha₂₃).lt.le h_le).resolve_left
        (ne_of_gt (atom_covBy_join ha₂ ha₃ ha₂₃).lt)
    exact ho'_not (calc o' ≤ o' ⊔ a₂ := le_sup_left
      _ = a₂ ⊔ a₃ := h_eq.symm
      _ ≤ π := sup_le ha₂_le ha₃_le)
  have h_meet_o'₁₂ : (o' ⊔ a₁) ⊓ (o' ⊔ a₂) = o' :=
    modular_intersection ho'_atom ha₁ ha₂ ha₁_ne_o'.symm ha₂_ne_o'.symm ha₁₂ h_not_coll₁₂
  have h_meet_o'₁₃ : (o' ⊔ a₁) ⊓ (o' ⊔ a₃) = o' :=
    modular_intersection ho'_atom ha₁ ha₃ ha₁_ne_o'.symm ha₃_ne_o'.symm ha₁₃ h_not_coll₁₃
  have h_meet_o'₂₃ : (o' ⊔ a₂) ⊓ (o' ⊔ a₃) = o' :=
    modular_intersection ho'_atom ha₂ ha₃ ha₂_ne_o'.symm ha₃_ne_o'.symm ha₂₃ h_not_coll₂₃
  have hb₁₂' : b₁' ≠ b₂' := by
    intro h
    -- b₁' = b₂' ≤ (o' ⊔ a₁) ⊓ (o' ⊔ a₂) = o'
    have hb₁'_le_o' : b₁' ≤ o' :=
      h_meet_o'₁₂ ▸ le_inf inf_le_left (h ▸ inf_le_left)
    -- So b₁' = o' (both atoms).
    have hb₁'_eq : b₁' = o' :=
      (ho'_atom.le_iff.mp hb₁'_le_o').resolve_left hb₁'_atom.1
    -- But b₁' ≤ R ⊔ b₁, so o' ≤ R ⊔ b₁. Contradiction.
    exact ho'_not_Rb₁ (hb₁'_eq ▸ inf_le_right)
  have hb₁₃' : b₁' ≠ b₃' := by
    intro h
    have hb₁'_le_o' : b₁' ≤ o' :=
      h_meet_o'₁₃ ▸ le_inf inf_le_left (h ▸ inf_le_left)
    have hb₁'_eq : b₁' = o' :=
      (ho'_atom.le_iff.mp hb₁'_le_o').resolve_left hb₁'_atom.1
    exact ho'_not_Rb₁ (hb₁'_eq ▸ inf_le_right)
  have hb₂₃' : b₂' ≠ b₃' := by
    intro h
    have hb₂'_le_o' : b₂' ≤ o' :=
      h_meet_o'₂₃ ▸ le_inf inf_le_left (h ▸ inf_le_left)
    have hb₂'_eq : b₂' = o' :=
      (ho'_atom.le_iff.mp hb₂'_le_o').resolve_left hb₂'_atom.1
    exact ho'_not_Rb₂ (hb₂'_eq ▸ inf_le_right)

  -- Step 4: Apply non-planar Desargues to a₁a₂a₃ and b₁'b₂'b₃'.
  -- (Perspective from o': b_i' ≤ o' ⊔ a_i by definition.)
  have h_des := desargues_nonplanar ho'_atom ha₁ ha₂ ha₃
    hb₁'_atom hb₂'_atom hb₃'_atom
    (inf_le_left : b₁' ≤ o' ⊔ a₁)
    (inf_le_left : b₂' ≤ o' ⊔ a₂)
    (inf_le_left : b₃' ≤ o' ⊔ a₃)
    π hπA.symm (b₁' ⊔ b₂' ⊔ b₃') rfl

  -- Step 5: Apply lift_side_intersection three times.
  have h_lift₁₂ := lift_side_intersection ha₁ ha₂ ha₁₂ hb₁ hb₂ hb₁₂
    hb₁'_atom hb₂'_atom hb₁₂' hR ho'_atom
    (sup_le ha₁_le ha₂_le) (sup_le hb₁_le hb₂_le) h_sides₁₂ hR_not ho'_not
    inf_le_left inf_le_left inf_le_right inf_le_right hb₁'_not
  have h_lift₁₃ := lift_side_intersection ha₁ ha₃ ha₁₃ hb₁ hb₃ hb₁₃
    hb₁'_atom hb₃'_atom hb₁₃' hR ho'_atom
    (sup_le ha₁_le ha₃_le) (sup_le hb₁_le hb₃_le) h_sides₁₃ hR_not ho'_not
    inf_le_left inf_le_left inf_le_right inf_le_right hb₁'_not
  have h_lift₂₃ := lift_side_intersection ha₂ ha₃ ha₂₃ hb₂ hb₃ hb₂₃
    hb₂'_atom hb₃'_atom hb₂₃' hR ho'_atom
    (sup_le ha₂_le ha₃_le) (sup_le hb₂_le hb₃_le) h_sides₂₃ hR_not ho'_not
    inf_le_left inf_le_left inf_le_right inf_le_right hb₂'_not


  -- Step 6: The axis is π ⊓ (b₁' ⊔ b₂' ⊔ b₃'), strictly below π.
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := h_des
  have haxis_ne : π ⊓ (b₁' ⊔ b₂' ⊔ b₃') ≠ π := by
    intro h_eq
    have hπ_le : π ≤ b₁' ⊔ b₂' ⊔ b₃' := inf_eq_left.mp h_eq
    have hπB_le : b₁' ⊔ b₂' ⊔ b₃' ≤ o' ⊔ π :=
      sup_le (sup_le
        ((inf_le_left : b₁' ≤ o' ⊔ a₁).trans (sup_le le_sup_left (ha₁_le.trans le_sup_right)))
        ((inf_le_left : b₂' ≤ o' ⊔ a₂).trans (sup_le le_sup_left (ha₂_le.trans le_sup_right))))
        ((inf_le_left : b₃' ≤ o' ⊔ a₃).trans (sup_le le_sup_left (ha₃_le.trans le_sup_right)))
    have ho'_disj : π ⊓ o' = ⊥ := by
      rcases ho'_atom.le_iff.mp inf_le_right with h | h
      · exact h
      · exfalso; exact ho'_not (le_of_eq h.symm |>.trans inf_le_left)
    have hπ_cov_s : π ⋖ o' ⊔ π := by
      have h := covBy_sup_of_inf_covBy_right (ho'_disj ▸ ho'_atom.bot_covBy)
      rwa [sup_comm] at h
    rcases hπ_cov_s.eq_or_eq hπ_le hπB_le with hcase | hcase
    · exact hb₁'_not (le_sup_left.trans (le_sup_left.trans (le_of_eq hcase)))
    · rw [← hcase] at hπ_cov_s
      have hb_cov : b₁' ⋖ b₁' ⊔ b₂' := atom_covBy_join hb₁'_atom hb₂'_atom hb₁₂'
      by_cases hb₃'_col : b₃' ≤ b₁' ⊔ b₂'
      · -- Collinear case: πB = b₁'⊔b₂'. a₁ ⋖ line, so a₁⊔a₂ = line, π ≤ a₁⊔a₂ < π.
        rw [show b₁' ⊔ b₂' ⊔ b₃' = b₁' ⊔ b₂' from
          le_antisymm (sup_le le_rfl hb₃'_col) le_sup_left] at hπ_le
        have ha₁_cov_line : a₁ ⋖ b₁' ⊔ b₂' :=
          line_covers_its_atoms hb₁'_atom hb₂'_atom hb₁₂' ha₁ (ha₁_le.trans hπ_le)
        have h12_eq : a₁ ⊔ a₂ = b₁' ⊔ b₂' :=
          (ha₁_cov_line.eq_or_eq le_sup_left (h_cov₁₂.le.trans hπ_le)).resolve_left
            (ne_of_gt (atom_covBy_join ha₁ ha₂ ha₁₂).lt)
        exact lt_irrefl _ (lt_of_lt_of_le h_cov₁₂.lt (h12_eq ▸ hπ_le))
      · -- Non-collinear: b₁'⊔b₂' and π both ⋖ πB. Meet ⋖ π is impossible.
        have hb₃'_disj : b₃' ⊓ (b₁' ⊔ b₂') = ⊥ :=
          (hb₃'_atom.le_iff.mp inf_le_left).resolve_right
            (fun h => hb₃'_col (h ▸ inf_le_right))
        have hline_cov : b₁' ⊔ b₂' ⋖ b₁' ⊔ b₂' ⊔ b₃' := by
          rw [show b₁' ⊔ b₂' ⊔ b₃' = b₃' ⊔ (b₁' ⊔ b₂') from sup_comm _ _]
          exact covBy_sup_of_inf_covBy_left (hb₃'_disj ▸ hb₃'_atom.bot_covBy)
        have hline_ne : b₁' ⊔ b₂' ≠ π :=
          fun h => hb₁'_not (le_sup_left.trans (le_of_eq h))
        obtain ⟨hmeet_cov_line, hmeet_cov_π⟩ :=
          planes_meet_covBy hline_cov hπ_cov_s hline_ne
        -- p := (b₁'⊔b₂') ⊓ π is an atom (via diamond with b₁')
        have hp_ne_b₁ : (b₁' ⊔ b₂') ⊓ π ≠ b₁' :=
          fun h => hb₁'_not (h ▸ inf_le_right)
        obtain ⟨hpb_cov_p, hpb_cov_b₁⟩ :=
          planes_meet_covBy hmeet_cov_line hb_cov hp_ne_b₁
        have : (b₁' ⊔ b₂') ⊓ π ⊓ b₁' = ⊥ := by
          rcases hb₁'_atom.le_iff.mp hpb_cov_b₁.le with h | h
          · exact h
          · exfalso; exact hb₁'_not
              ((le_of_eq h.symm).trans (inf_le_left.trans inf_le_right))
        rw [this] at hpb_cov_p  -- ⊥ ⋖ p
        have hp_atom := line_height_two hb₁'_atom hb₂'_atom hb₁₂'
          hpb_cov_p.lt hmeet_cov_line.lt
        -- p ⋖ π, but a₁ < a₁⊔a₂ < π: CovBy contradiction
        by_cases ha₁p : a₁ = (b₁' ⊔ b₂') ⊓ π
        · exact (ha₁p ▸ hmeet_cov_π).2
            (atom_covBy_join ha₁ ha₂ ha₁₂).lt h_cov₁₂.lt
        · have hp_lt : (b₁' ⊔ b₂') ⊓ π < (b₁' ⊔ b₂') ⊓ π ⊔ a₁ :=
            lt_of_le_of_ne le_sup_left (fun h => ha₁p
              ((hp_atom.le_iff.mp (h ▸ le_sup_right)).resolve_left ha₁.1))
          have hp_eq : (b₁' ⊔ b₂') ⊓ π ⊔ a₁ = π :=
            (hmeet_cov_π.eq_or_eq hp_lt.le
              (sup_le hmeet_cov_π.le ha₁_le)).resolve_left (ne_of_gt hp_lt)
          have ha₁_cov_π : a₁ ⋖ π := by
            rw [← hp_eq, sup_comm]
            exact atom_covBy_join ha₁ hp_atom ha₁p
          exact ha₁_cov_π.2
            (atom_covBy_join ha₁ ha₂ ha₁₂).lt h_cov₁₂.lt
  exact ⟨π ⊓ (b₁' ⊔ b₂' ⊔ b₃'), inf_le_left, haxis_ne,
    h_lift₁₂ ▸ h₁₂, h_lift₁₃ ▸ h₁₃, h_lift₂₃ ▸ h₂₃⟩

/-- **Collinearity from Desargues.** If three points lie on a common
    element strictly below π, and two of them span a line covered by π,
    the third lies on that line.

    This is the extraction step: desargues_planar gives ∃ axis with
    axis ≤ π ∧ axis ≠ π, and two known side-intersections S₁₂, S₁₃
    span a line ℓ ⋖ π. Then ℓ ≤ axis < π, and ℓ ⋖ π forces axis = ℓ.
    The third point S₂₃ ≤ axis = ℓ. -/
theorem collinear_of_common_bound {s₁ s₂ s₃ axis π : L}
    (h_cov : s₁ ⊔ s₂ ⋖ π)
    (h_axis_le : axis ≤ π) (h_axis_ne : axis ≠ π)
    (h₁ : s₁ ≤ axis) (h₂ : s₂ ≤ axis) (h₃ : s₃ ≤ axis) :
    s₃ ≤ s₁ ⊔ s₂ := by
  have h12_le : s₁ ⊔ s₂ ≤ axis := sup_le h₁ h₂
  have h_axis_lt : axis < π := lt_of_le_of_ne h_axis_le h_axis_ne
  -- s₁ ⊔ s₂ ≤ axis < π, with s₁ ⊔ s₂ ⋖ π: axis = s₁ ⊔ s₂
  have h_eq : axis = s₁ ⊔ s₂ :=
    (h_cov.eq_or_eq h12_le h_axis_lt.le).resolve_right (ne_of_lt h_axis_lt)
  exact h_eq ▸ h₃


-- § Helpers for coord_add commutativity

variable (Γ : CoordSystem L)

/-- Two lines through C from distinct points on l meet at C. -/
theorem CoordSystem.lines_through_C_meet {a b : L}
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) :
    (a ⊔ Γ.C) ⊓ (b ⊔ Γ.C) = Γ.C := by
  rw [sup_comm a Γ.C, sup_comm b Γ.C]
  apply modular_intersection Γ.hC ha hb
    (fun h => Γ.hC_not_l (h ▸ ha_on))
    (fun h => Γ.hC_not_l (h ▸ hb_on)) hab
  intro hle
  have hb_le_a : b ≤ a := by
    have := le_inf hb_on hle
    rw [inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at this
    exact this
  exact hab ((ha.le_iff.mp hb_le_a).resolve_left hb.1).symm

/-- Two lines through E from distinct points on l meet at E. -/
theorem CoordSystem.lines_through_E_meet {a b : L}
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) :
    (a ⊔ Γ.E) ⊓ (b ⊔ Γ.E) = Γ.E := by
  rw [sup_comm a Γ.E, sup_comm b Γ.E]
  apply modular_intersection Γ.hE_atom ha hb
    (fun h => CoordSystem.hE_not_l (h ▸ ha_on))
    (fun h => CoordSystem.hE_not_l (h ▸ hb_on)) hab
  intro hle
  have hb_le_a : b ≤ a := by
    have := le_inf hb_on hle
    rw [inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l ha_on] at this
    exact this
  exact hab ((ha.le_iff.mp hb_le_a).resolve_left hb.1).symm

/-- O ⊔ C is covered by the plane π = O ⊔ U ⊔ V. -/
theorem CoordSystem.OC_covBy_π : Γ.O ⊔ Γ.C ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
  -- U ⊓ (O ⊔ C) = ⊥ (U not on line O ⊔ C, since that would give C on l)
  have hU_disj : Γ.U ⊓ (Γ.O ⊔ Γ.C) = ⊥ := by
    rcases Γ.hU.le_iff.mp inf_le_left with h | h
    · exact h
    · exfalso
      have hU_le := h ▸ inf_le_right  -- U ≤ O ⊔ C
      have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le (sup_le le_sup_left hU_le)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
  -- O ⊔ C ⋖ U ⊔ (O ⊔ C)
  have h := covBy_sup_of_inf_covBy_left (hU_disj ▸ Γ.hU.bot_covBy)
  -- Rewrite: U ⊔ (O ⊔ C) = O ⊔ U ⊔ C
  have h_assoc : Γ.U ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.C := by
    rw [← sup_assoc, sup_comm Γ.U Γ.O]
  rw [h_assoc] at h
  -- O ⊔ U ⊔ C = O ⊔ U ⊔ V (both = π)
  -- (O ⊔ U) ⊔ V = π by def. (O ⊔ U) ⋖ (O ⊔ U) ⊔ V (V off l).
  -- (O ⊔ U) < (O ⊔ U) ⊔ C ≤ (O ⊔ U) ⊔ V by CovBy.
  have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
    (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
  have h_l_cov : Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
  have h_lt : Γ.O ⊔ Γ.U < Γ.O ⊔ Γ.U ⊔ Γ.C := lt_of_le_of_ne le_sup_left
    (fun heq => Γ.hC_not_l (heq ▸ le_sup_right))
  have h_le : Γ.O ⊔ Γ.U ⊔ Γ.C ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le le_sup_left Γ.hC_plane
  rw [(h_l_cov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)] at h
  exact h


/-- **First Desargues for addition.** The point
    (a'⊔D_a) ⊓ (b'⊔D_b) lies on the line O⊔C.
    Proved by applying desargues_planar to triangles
    (a, a', D_a) and (b, b', D_b) perspective from U. -/
theorem coord_first_desargues (Γ : CoordSystem L) {a b : L}
    (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : a ≠ b)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓
    ((b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ≤ Γ.O ⊔ Γ.C := by
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set a' := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set b' := (b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set D_a := (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  set D_b := (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  -- All hypotheses for desargues_planar, proved individually
  have ha'_atom : IsAtom a' := by
    exact perspect_atom Γ.hC ha (fun h => Γ.hC_not_l (h ▸ ha_on)) Γ.hU Γ.hV
      (fun h => Γ.hV_off (h ▸ le_sup_right)) Γ.hC_not_m
      (sup_le (ha_on.trans (le_sup_left.trans (le_of_eq Γ.m_sup_C_eq_π.symm))) le_sup_right)
  have hb'_atom : IsAtom b' := by
    exact perspect_atom Γ.hC hb (fun h => Γ.hC_not_l (h ▸ hb_on)) Γ.hU Γ.hV
      (fun h => Γ.hV_off (h ▸ le_sup_right)) Γ.hC_not_m
      (sup_le (hb_on.trans (le_sup_left.trans (le_of_eq Γ.m_sup_C_eq_π.symm))) le_sup_right)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hE_not_UC : ¬ Γ.E ≤ Γ.U ⊔ Γ.C := by
    have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
      apply modular_intersection Γ.hU Γ.hC Γ.hV hUC
        (fun h => Γ.hV_off (h ▸ le_sup_right))
        (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      intro hle
      exact Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt.le
        (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt)
        ▸ le_sup_right)
    intro h
    exact CoordSystem.hEU (Γ.hU.le_iff.mp
      (hUC_inf_m ▸ le_inf h CoordSystem.hE_on_m) |>.resolve_left Γ.hE_atom.1)
  have ha_ne_E : a ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ ha_on)
  have hb_ne_E : b ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hb_on)
  have hUCE_eq_π : (Γ.U ⊔ Γ.C) ⊔ Γ.E = π := by
    have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
      have h_le : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right CoordSystem.hE_le_OC
      have h_lt : Γ.C < Γ.C ⊔ Γ.E := by
        apply lt_of_le_of_ne le_sup_left; intro h
        exact hCE ((Γ.hC.le_iff.mp (h ▸ le_sup_right : Γ.E ≤ Γ.C)).resolve_left
          Γ.hE_atom.1).symm
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact (atom_covBy_join Γ.hC Γ.hO hOC.symm |>.eq_or_eq h_lt.le
        (sup_comm Γ.C Γ.O ▸ h_le)).resolve_left (ne_of_gt h_lt)
    rw [show (Γ.U ⊔ Γ.C) ⊔ Γ.E = Γ.U ⊔ (Γ.C ⊔ Γ.E) from sup_assoc _ _ _, hCE_eq,
        show Γ.U ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.C from by rw [← sup_assoc, sup_comm Γ.U Γ.O]]
    have h_lt_OC : Γ.O ⊔ Γ.C < Γ.O ⊔ Γ.U ⊔ Γ.C := by
      apply lt_of_le_of_ne (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      intro h
      have hOU_le := h.symm ▸ (le_sup_left : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.U ⊔ Γ.C)
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le hOU_le).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt_OC.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt_OC)
  have hDa_atom : IsAtom D_a :=
    perspect_atom Γ.hE_atom ha ha_ne_E Γ.hU Γ.hC hUC hE_not_UC
      (sup_le (ha_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  have hDb_atom : IsAtom D_b :=
    perspect_atom Γ.hE_atom hb hb_ne_E Γ.hU Γ.hC hUC hE_not_UC
      (sup_le (hb_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  -- All 30+ hypotheses
  have hU_le_π : Γ.U ≤ π := le_sup_right.trans le_sup_left
  have hm_le_π : Γ.U ⊔ Γ.V ≤ π := sup_le hU_le_π le_sup_right
  have h_ho_le : Γ.U ≤ π := hU_le_π
  have h_ha1_le : a ≤ π := ha_on.trans le_sup_left
  have h_ha2_le : a' ≤ π := (inf_le_right : a' ≤ Γ.U ⊔ Γ.V).trans hm_le_π
  have h_ha3_le : D_a ≤ π := (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C).trans (sup_le hU_le_π Γ.hC_plane)
  have h_hb1_le : b ≤ π := hb_on.trans le_sup_left
  have h_hb2_le : b' ≤ π := (inf_le_right : b' ≤ Γ.U ⊔ Γ.V).trans hm_le_π
  have h_hb3_le : D_b ≤ π := (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C).trans (sup_le hU_le_π Γ.hC_plane)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)
  have hl_inf_UC : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U := by
    rw [sup_comm Γ.O Γ.U]
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm
      (fun h => Γ.hC_not_l (h ▸ le_sup_right))
      (fun h => Γ.hC_not_l (h ▸ le_sup_left))
      (fun h => Γ.hC_not_l (by rwa [sup_comm] at h))
  have ha_not_UC : ¬ a ≤ Γ.U ⊔ Γ.C := by
    intro h; exact ha_ne_U (Γ.hU.le_iff.mp (hl_inf_UC ▸ le_inf ha_on h) |>.resolve_left ha.1)
  -- Perspective: b_i ≤ U ⊔ a_i
  -- U ⊔ a = O ⊔ U (covering)
  have hUa_eq : Γ.U ⊔ a = Γ.O ⊔ Γ.U := by
    have h_lt : Γ.U < Γ.U ⊔ a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left ha.1))
    have : Γ.U ⊔ a ≤ Γ.U ⊔ Γ.O := sup_le le_sup_left (ha_on.trans (by rw [sup_comm]))
    exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le this).resolve_left
      (ne_of_gt h_lt) |>.trans (sup_comm _ _)
  have hb1_on : b ≤ Γ.U ⊔ a := hUa_eq ▸ hb_on
  have hb2_on : b' ≤ Γ.U ⊔ a' := by
    -- U ⊔ a' = U ⊔ V (covering), b' ≤ U ⊔ V
    have ha'_ne_U : a' ≠ Γ.U := by
      intro h
      have : Γ.U ≤ a ⊔ Γ.C := h ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
      have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) this
      rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
      exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
    have h_lt : Γ.U < Γ.U ⊔ a' := lt_of_le_of_ne le_sup_left
      (fun h => ha'_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left ha'_atom.1))
    have hUa'_eq : Γ.U ⊔ a' = Γ.U ⊔ Γ.V :=
      ((atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).eq_or_eq h_lt.le
        (sup_le le_sup_left inf_le_right)).resolve_left (ne_of_gt h_lt)
    exact hUa'_eq ▸ inf_le_right
  have hb3_on : D_b ≤ Γ.U ⊔ D_a := by
    -- U ⊔ D_a = U ⊔ C (covering), D_b ≤ U ⊔ C
    have hDa_ne_U : D_a ≠ Γ.U := by
      intro h
      have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := h ▸ (inf_le_left : D_a ≤ a ⊔ Γ.E)
      have h_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
        ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq
          (atom_covBy_join ha Γ.hU ha_ne_U).lt.le (sup_le le_sup_left hU_le_aE)).resolve_left
          (ne_of_gt (atom_covBy_join ha Γ.hU ha_ne_U).lt)
      exact CoordSystem.hE_not_l (le_of_le_of_eq le_sup_right h_eq.symm |>.trans
        (le_of_eq (show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _)) |>.trans (le_of_eq hUa_eq))
    have h_lt : Γ.U < Γ.U ⊔ D_a := lt_of_le_of_ne le_sup_left
      (fun h => hDa_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left hDa_atom.1))
    have hUDa_eq : Γ.U ⊔ D_a = Γ.U ⊔ Γ.C :=
      ((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq h_lt.le
        (sup_le le_sup_left inf_le_right)).resolve_left (ne_of_gt h_lt)
    exact hUDa_eq ▸ inf_le_right
  -- Vertex distinctness
  have h12a : a ≠ a' := fun h => ha_ne_U
    (Γ.atom_on_both_eq_U ha ha_on (h ▸ (inf_le_right : a' ≤ Γ.U ⊔ Γ.V)))
  have h13a : a ≠ D_a := fun h_eq => ha_ne_U (Γ.hU.le_iff.mp
    (hl_inf_UC ▸ le_inf ha_on (h_eq ▸ (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C)))
    |>.resolve_left ha.1)
  have h23a : a' ≠ D_a := by
    intro h
    have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
      apply modular_intersection Γ.hU Γ.hC Γ.hV hUC
        (fun h => Γ.hV_off (h ▸ le_sup_right))
        (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      intro hle
      exact Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt.le
        (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt)
        ▸ le_sup_right)
    have h1 : a' ≤ (Γ.U ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.C) := le_inf inf_le_right (h ▸ inf_le_right)
    rw [inf_comm, hUC_inf_m] at h1
    have ha'_ne_U : a' ≠ Γ.U := by
      intro heq
      have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := (le_of_eq heq.symm).trans inf_le_left
      have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hU_le_aC
      rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
      exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
    exact ha'_ne_U ((Γ.hU.le_iff.mp h1).resolve_left ha'_atom.1)
  have h12b : b ≠ b' := by
    intro heq
    exact hb_ne_U (Γ.atom_on_both_eq_U hb hb_on
      ((le_of_eq heq).trans inf_le_right))
  have h13b : b ≠ D_b := fun h_eq => hb_ne_U (Γ.hU.le_iff.mp
    (hl_inf_UC ▸ le_inf hb_on (h_eq ▸ (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C)))
    |>.resolve_left hb.1)
  have h23b : b' ≠ D_b := by
    intro h
    have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
      apply modular_intersection Γ.hU Γ.hC Γ.hV hUC
        (fun h => Γ.hV_off (h ▸ le_sup_right))
        (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      intro hle
      exact Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt.le
        (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).lt)
        ▸ le_sup_right)
    have h1 : b' ≤ (Γ.U ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.C) := le_inf inf_le_right (h ▸ inf_le_right)
    rw [inf_comm, hUC_inf_m] at h1
    have hb'_ne_U : b' ≠ Γ.U := by
      intro h2
      have hU_le_bC : Γ.U ≤ b ⊔ Γ.C := (le_of_eq h2.symm).trans inf_le_left
      have h3 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hU_le_bC
      rw [show b ⊔ Γ.C = Γ.C ⊔ b from sup_comm _ _,
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on] at h3
      exact hb_ne_U ((hb.le_iff.mp h3).resolve_left Γ.hU.1).symm
    exact hb'_ne_U ((Γ.hU.le_iff.mp h1).resolve_left hb'_atom.1)
  -- Join equalities (needed for sides and triangle planes)
  have haa' : a ⊔ a' = a ⊔ Γ.C := by
    have h_lt : a < a ⊔ a' := lt_of_le_of_ne le_sup_left
      (fun h => h12a ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left ha'_atom.1).symm)
    exact ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have hbb' : b ⊔ b' = b ⊔ Γ.C := by
    have h_lt : b < b ⊔ b' := lt_of_le_of_ne le_sup_left
      (fun h => h12b ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left hb'_atom.1).symm)
    exact ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have haDa : a ⊔ D_a = a ⊔ Γ.E := by
    have h_lt : a < a ⊔ D_a := lt_of_le_of_ne le_sup_left
      (fun h => h13a ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left hDa_atom.1).symm)
    exact ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have hbDb : b ⊔ D_b = b ⊔ Γ.E := by
    have h_lt : b < b ⊔ D_b := lt_of_le_of_ne le_sup_left
      (fun h => h13b ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left hDb_atom.1).symm)
    exact ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  -- Side distinctness
  have hs12 : a ⊔ a' ≠ b ⊔ b' := by
    rw [haa', hbb']; intro h
    have h2 := le_inf ha_on (le_of_le_of_eq le_sup_left h)
    rw [show b ⊔ Γ.C = Γ.C ⊔ b from sup_comm _ _,
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on] at h2
    exact hab ((hb.le_iff.mp h2).resolve_left ha.1)
  have hs13 : a ⊔ D_a ≠ b ⊔ D_b := by
    rw [haDa, hbDb]; intro h
    have h2 := le_inf ha_on (le_of_le_of_eq le_sup_left h)
    rw [show b ⊔ Γ.E = Γ.E ⊔ b from sup_comm _ _,
        inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l hb_on] at h2
    exact hab ((hb.le_iff.mp h2).resolve_left ha.1)
  have hs23 : a' ⊔ D_a ≠ b' ⊔ D_b := by
    -- Auxiliary: (U⊔C) ⊓ (U⊔V) = U
    have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
    have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
      apply modular_intersection Γ.hU Γ.hC Γ.hV hUC hUV
        (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      intro hle
      exact Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV hUV).lt.le
        (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV hUV).lt)
        ▸ le_sup_right)
    -- Auxiliary: D_a ≠ U
    have hDa_ne_U : D_a ≠ Γ.U := by
      intro h
      have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := h ▸ (inf_le_left : D_a ≤ a ⊔ Γ.E)
      have h_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
        ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq
          (atom_covBy_join ha Γ.hU ha_ne_U).lt.le (sup_le le_sup_left hU_le_aE)).resolve_left
          (ne_of_gt (atom_covBy_join ha Γ.hU ha_ne_U).lt)
      exact CoordSystem.hE_not_l (le_of_le_of_eq le_sup_right h_eq.symm |>.trans
        (le_of_eq (show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _)) |>.trans (le_of_eq hUa_eq))
    -- Auxiliary: D_a not on m
    have hDa_not_m : ¬ D_a ≤ Γ.U ⊔ Γ.V := by
      intro hle
      have h1 : D_a ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := le_inf inf_le_right hle
      rw [hUC_inf_m] at h1
      exact hDa_ne_U ((Γ.hU.le_iff.mp h1).resolve_left hDa_atom.1)
    -- Main proof by contradiction
    intro heq
    -- Case split: a' = b' or a' ≠ b'
    by_cases hab' : a' = b'
    · -- Case a' = b': a' ≤ (C⊔a) ⊓ (C⊔b) = C, contradicting C not on m
      exfalso
      have ha'_le_aC : a' ≤ Γ.C ⊔ a := sup_comm a Γ.C ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
      have ha'_le_bC : a' ≤ Γ.C ⊔ b :=
        sup_comm b Γ.C ▸ (hab' ▸ (inf_le_left : b' ≤ b ⊔ Γ.C))
      have hb_not_Ca : ¬ b ≤ Γ.C ⊔ a := by
        intro hle
        -- b ≤ C⊔a and a ≤ C⊔a, so a⊔b ≤ C⊔a.
        -- a ⋖ C⊔a (covering of distinct atoms C, a with sup_comm).
        -- a ≤ a⊔b ≤ C⊔a and a < a⊔b (since a ≠ b), so a⊔b = C⊔a by covering.
        -- Then C ≤ a⊔b ≤ l, contradicting hC_not_l.
        have hab_le : a ⊔ b ≤ Γ.C ⊔ a := sup_le le_sup_right hle
        have h_cov_aCa : a ⋖ Γ.C ⊔ a := sup_comm Γ.C a ▸
          atom_covBy_join ha Γ.hC ha_ne_C
        have h_lt_ab : a < a ⊔ b := lt_of_le_of_ne le_sup_left
          (fun h => hab ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left hb.1).symm)
        have h_eq : a ⊔ b = Γ.C ⊔ a :=
          (h_cov_aCa.eq_or_eq h_lt_ab.le hab_le).resolve_left (ne_of_gt h_lt_ab)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_left h_eq.symm |>.trans
          (sup_le ha_on hb_on))
      have hCab : (Γ.C ⊔ a) ⊓ (Γ.C ⊔ b) = Γ.C :=
        modular_intersection Γ.hC ha hb (fun h => ha_ne_C h.symm)
          (fun h => hb_ne_C h.symm) hab hb_not_Ca
      have ha'_le_C : a' ≤ Γ.C := le_of_le_of_eq (le_inf ha'_le_aC ha'_le_bC) hCab
      have ha'_eq_C : a' = Γ.C := (Γ.hC.le_iff.mp ha'_le_C).resolve_left ha'_atom.1
      exact Γ.hC_not_m (ha'_eq_C ▸ inf_le_right)
    · -- Case a' ≠ b': a'⊔b' = U⊔V, so m ≤ a'⊔D_a, forcing D_a on m — contradiction
      exfalso
      have h_cov_UV : Γ.U ⋖ Γ.U ⊔ Γ.V := atom_covBy_join Γ.hU Γ.hV hUV
      have ha'b'_le : a' ⊔ b' ≤ Γ.U ⊔ Γ.V := sup_le inf_le_right inf_le_right
      -- a' < a'⊔b' (since a' ≠ b', both atoms)
      have h_a'_lt_a'b' : a' < a' ⊔ b' := lt_of_le_of_ne le_sup_left
        (fun h => hab' ((ha'_atom.le_iff.mp
          (le_of_le_of_eq le_sup_right h.symm)).resolve_left hb'_atom.1).symm)
      -- a' < U⊔V
      have h_lt_m : a' < Γ.U ⊔ Γ.V := lt_of_lt_of_le h_a'_lt_a'b' ha'b'_le
      -- U ≤ a'⊔b' (by modularity: if not, then b' ≤ a')
      have hU_le_a'b' : Γ.U ≤ a' ⊔ b' := by
        by_contra hU_not
        have hU_inf : Γ.U ⊓ (a' ⊔ b') = ⊥ :=
          (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun h => hU_not (h ▸ inf_le_right))
        -- a' ≠ U (otherwise U ⊓ (U⊔b') = U ≠ ⊥)
        have ha'_ne_U : a' ≠ Γ.U := by
          intro h; rw [h] at hU_inf
          exact Γ.hU.1 (le_bot_iff.mp (hU_inf ▸ le_inf le_rfl le_sup_left))
        -- U⊔a' = U⊔V (covering)
        have ha'U_eq : Γ.U ⊔ a' = Γ.U ⊔ Γ.V := by
          have h_lt : Γ.U < Γ.U ⊔ a' := lt_of_le_of_ne le_sup_left
            (fun h => ha'_ne_U ((Γ.hU.le_iff.mp
              (le_of_le_of_eq le_sup_right h.symm)).resolve_left ha'_atom.1))
          exact (h_cov_UV.eq_or_eq h_lt.le
            (sup_le le_sup_left inf_le_right)).resolve_left (ne_of_gt h_lt)
        -- Modularity: (a'⊔U) ⊓ (a'⊔b') = a' ⊔ (U ⊓ (a'⊔b')) = a' ⊔ ⊥ = a'
        have hmod : (Γ.U ⊔ a') ⊓ (a' ⊔ b') = a' := by
          have h1 := sup_inf_assoc_of_le Γ.U (le_sup_left : a' ≤ a' ⊔ b')
          rw [hU_inf, sup_bot_eq, sup_comm a' Γ.U] at h1; exact h1
        -- So (U⊔V) ⊓ (a'⊔b') = a', and b' ≤ both, so b' ≤ a'
        rw [ha'U_eq] at hmod
        have hb'_le_a' : b' ≤ a' :=
          le_of_le_of_eq (le_inf inf_le_right (le_sup_right : b' ≤ a' ⊔ b')) hmod
        exact hab' ((ha'_atom.le_iff.mp hb'_le_a').resolve_left hb'_atom.1).symm
      -- a'⊔b' = U⊔V (by covering U⋖U⊔V, since U < a'⊔b')
      have hU_lt_a'b' : Γ.U < a' ⊔ b' :=
        lt_of_le_of_ne hU_le_a'b' (fun h => by
          have ha'_le_U : a' ≤ Γ.U := le_of_le_of_eq le_sup_left h.symm
          have hb'_le_U : b' ≤ Γ.U := le_of_le_of_eq le_sup_right h.symm
          exact hab' ((Γ.hU.le_iff.mp ha'_le_U).resolve_left ha'_atom.1 |>.trans
            ((Γ.hU.le_iff.mp hb'_le_U).resolve_left hb'_atom.1).symm))
      have hm_eq : a' ⊔ b' = Γ.U ⊔ Γ.V :=
        (h_cov_UV.eq_or_eq hU_lt_a'b'.le ha'b'_le).resolve_left (ne_of_gt hU_lt_a'b')
      -- b' ≤ a'⊔D_a (from heq), so m = a'⊔b' ≤ a'⊔D_a
      have hb'_le : b' ≤ a' ⊔ D_a := le_of_le_of_eq le_sup_left heq.symm
      have ha'b'_le_a'Da : a' ⊔ b' ≤ a' ⊔ D_a := sup_le le_sup_left hb'_le
      have hm_le : Γ.U ⊔ Γ.V ≤ a' ⊔ D_a := hm_eq ▸ ha'b'_le_a'Da
      -- a' ⋖ a'⊔D_a, and a' < m ≤ a'⊔D_a, so a'⊔D_a = m (covering)
      have h_cov : a' ⋖ a' ⊔ D_a := atom_covBy_join ha'_atom hDa_atom h23a
      have h_eq_m : a' ⊔ D_a = Γ.U ⊔ Γ.V :=
        ((h_cov.eq_or_eq h_lt_m.le hm_le).resolve_left (ne_of_gt h_lt_m)).symm
      -- D_a ≤ m, contradiction
      exact hDa_not_m (le_of_le_of_eq le_sup_right h_eq_m)
  -- D_a ≠ C (helper for triangle planes)
  have hDa_ne_C : D_a ≠ Γ.C := by
    intro h
    have hC_le_aE : Γ.C ≤ a ⊔ Γ.E := (le_of_eq h.symm).trans inf_le_left
    have h_aCE : a ⊔ Γ.C ≤ a ⊔ Γ.E := sup_le le_sup_left hC_le_aE
    have h_aC_lt : a < a ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_C ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hC.1).symm)
    have h_eq : a ⊔ Γ.C = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq h_aC_lt.le h_aCE).resolve_left
        (ne_of_gt h_aC_lt)
    have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := le_of_le_of_eq le_sup_right h_eq.symm
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
    have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
        hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
    have hCE' : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
    exact hCE' ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_aC CoordSystem.hE_le_OC) h_inf_C)).resolve_left
      Γ.hE_atom.1).symm
  have hCDa_eq : Γ.C ⊔ D_a = Γ.U ⊔ Γ.C := by
    have h_lt : Γ.C < Γ.C ⊔ D_a := by
      apply lt_of_le_of_ne le_sup_left
      intro heq
      have hDa_le_C : D_a ≤ Γ.C := le_of_le_of_eq le_sup_right heq.symm
      exact hDa_ne_C ((Γ.hC.le_iff.mp hDa_le_C).resolve_left hDa_atom.1)
    rw [sup_comm Γ.U Γ.C]
    exact ((atom_covBy_join Γ.hC Γ.hU hUC.symm).eq_or_eq h_lt.le
      (sup_le le_sup_left ((inf_le_right).trans (le_of_eq (sup_comm Γ.U Γ.C))))).resolve_left (ne_of_gt h_lt)
  have hDa_not_aC : ¬ D_a ≤ a ⊔ Γ.C := by
    intro hle
    have h_le : D_a ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.U) :=
      le_inf ((sup_comm a Γ.C).symm ▸ hle) ((sup_comm Γ.U Γ.C).symm ▸ inf_le_right)
    rw [modular_intersection Γ.hC ha Γ.hU (fun h => ha_ne_C h.symm) hUC.symm
      ha_ne_U (by
        intro hle; rw [sup_comm] at hle
        have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hle
        rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
            inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
        exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm)] at h_le
    exact hDa_ne_C ((Γ.hC.le_iff.mp h_le).resolve_left hDa_atom.1)
  -- Triangle planes
  have hπA : a ⊔ a' ⊔ D_a = π := by
    rw [haa', sup_assoc, hCDa_eq, show a ⊔ (Γ.U ⊔ Γ.C) = (a ⊔ Γ.U) ⊔ Γ.C from
      (sup_assoc _ _ _).symm, show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _, hUa_eq]
    have h_OC_le : Γ.O ⊔ Γ.C ≤ (Γ.O ⊔ Γ.U) ⊔ Γ.C :=
      sup_le (le_sup_left.trans le_sup_left) le_sup_right
    have h_lt : Γ.O ⊔ Γ.C < (Γ.O ⊔ Γ.U) ⊔ Γ.C := by
      apply lt_of_le_of_ne h_OC_le
      intro heq
      have : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.C := le_of_le_of_eq le_sup_left heq.symm
      have h_eq := (((atom_covBy_join Γ.hO Γ.hC (fun h => Γ.hC_not_l (h ▸ le_sup_left))).eq_or_eq
          (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le this).resolve_left
          (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt))
      -- h_eq : Γ.O ⊔ Γ.U = Γ.O ⊔ Γ.C, so C ≤ O⊔C = O⊔U = l
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right h_eq.symm)
    exact (((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt))
  have hπB : b ⊔ b' ⊔ D_b = π := by
    rw [hbb']
    have hDb_ne_C : D_b ≠ Γ.C := by
      intro h
      have hC_le_bE : Γ.C ≤ b ⊔ Γ.E := (le_of_eq h.symm).trans inf_le_left
      have h_bC_lt : b < b ⊔ Γ.C := lt_of_le_of_ne le_sup_left
        (fun h => hb_ne_C ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hC.1).symm)
      have h_eq : b ⊔ Γ.C = b ⊔ Γ.E :=
        ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq h_bC_lt.le
          (sup_le le_sup_left hC_le_bE)).resolve_left (ne_of_gt h_bC_lt)
      have hE_le_bC : Γ.E ≤ b ⊔ Γ.C := le_of_le_of_eq le_sup_right h_eq.symm
      have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
      have hO_not_bC : ¬ Γ.O ≤ b ⊔ Γ.C := by
        intro hle
        have heq : b ⊔ Γ.O = b ⊔ Γ.C :=
          ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq (atom_covBy_join hb Γ.hO hb_ne_O).lt.le
            (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join hb Γ.hO hb_ne_O).lt)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le hb_on le_sup_left))
      have h_inf_C : (b ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm b Γ.C, sup_comm Γ.O Γ.C]
        exact modular_intersection Γ.hC hb Γ.hO (fun h => hb_ne_C h.symm)
          hOC.symm hb_ne_O (by rwa [sup_comm] at hO_not_bC)
      have hCE' : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
      exact hCE' ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_bC CoordSystem.hE_le_OC)
          h_inf_C)).resolve_left Γ.hE_atom.1).symm
    have hCDb_eq : Γ.C ⊔ D_b = Γ.U ⊔ Γ.C := by
      have h_lt : Γ.C < Γ.C ⊔ D_b := by
        apply lt_of_le_of_ne le_sup_left
        intro heq
        exact hDb_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq le_sup_right heq.symm)).resolve_left
          hDb_atom.1)
      rw [sup_comm Γ.U Γ.C]
      exact ((atom_covBy_join Γ.hC Γ.hU hUC.symm).eq_or_eq h_lt.le
        (sup_le le_sup_left ((inf_le_right).trans (le_of_eq (sup_comm Γ.U Γ.C))))).resolve_left
        (ne_of_gt h_lt)
    rw [sup_assoc, hCDb_eq, show b ⊔ (Γ.U ⊔ Γ.C) = (b ⊔ Γ.U) ⊔ Γ.C from
      (sup_assoc _ _ _).symm, show b ⊔ Γ.U = Γ.U ⊔ b from sup_comm _ _]
    have hUb_eq : Γ.U ⊔ b = Γ.O ⊔ Γ.U := by
      have h_lt : Γ.U < Γ.U ⊔ b := lt_of_le_of_ne le_sup_left
        (fun h => hb_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left hb.1))
      exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le
        (sup_le le_sup_left (hb_on.trans (by rw [sup_comm])))).resolve_left
        (ne_of_gt h_lt) |>.trans (sup_comm _ _)
    rw [hUb_eq]
    have h_OC_le : Γ.O ⊔ Γ.C ≤ (Γ.O ⊔ Γ.U) ⊔ Γ.C :=
      sup_le (le_sup_left.trans le_sup_left) le_sup_right
    have h_lt : Γ.O ⊔ Γ.C < (Γ.O ⊔ Γ.U) ⊔ Γ.C := by
      apply lt_of_le_of_ne h_OC_le; intro heq
      have : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.C := le_of_le_of_eq le_sup_left heq.symm
      have h_eq := (((atom_covBy_join Γ.hO Γ.hC (fun h => Γ.hC_not_l (h ▸ le_sup_left))).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le this).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt))
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right h_eq.symm)
    exact (((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt))
  -- U ≠ vertices
  have hoa1 : Γ.U ≠ a := ha_ne_U.symm
  have hoa2 : Γ.U ≠ a' := by
    intro h
    have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := (le_of_eq h).trans inf_le_left
    have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hU_le_aC
    rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
    exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
  have hoa3 : Γ.U ≠ D_a := by
    intro h
    have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := (le_of_eq h).trans inf_le_left
    have h_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq
        (atom_covBy_join ha Γ.hU ha_ne_U).lt.le (sup_le le_sup_left hU_le_aE)).resolve_left
        (ne_of_gt (atom_covBy_join ha Γ.hU ha_ne_U).lt)
    exact CoordSystem.hE_not_l (calc Γ.E ≤ a ⊔ Γ.E := le_sup_right
      _ = a ⊔ Γ.U := h_eq.symm
      _ = Γ.U ⊔ a := sup_comm _ _
      _ = Γ.O ⊔ Γ.U := hUa_eq)
  have hob1 : Γ.U ≠ b := hb_ne_U.symm
  have hob2 : Γ.U ≠ b' := by
    intro h
    have hU_le_bC : Γ.U ≤ b ⊔ Γ.C := (le_of_eq h).trans inf_le_left
    have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hU_le_bC
    rw [show b ⊔ Γ.C = Γ.C ⊔ b from sup_comm _ _,
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on] at h2
    exact hb_ne_U ((hb.le_iff.mp h2).resolve_left Γ.hU.1).symm
  have hob3 : Γ.U ≠ D_b := by
    intro h
    have hU_le_bE : Γ.U ≤ b ⊔ Γ.E := (le_of_eq h).trans inf_le_left
    have hUb_eq : Γ.U ⊔ b = Γ.O ⊔ Γ.U := by
      have h_lt : Γ.U < Γ.U ⊔ b := lt_of_le_of_ne le_sup_left
        (fun h => hb_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left hb.1))
      exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le
        (sup_le le_sup_left (hb_on.trans (by rw [sup_comm])))).resolve_left
        (ne_of_gt h_lt) |>.trans (sup_comm _ _)
    have h_eq : b ⊔ Γ.U = b ⊔ Γ.E :=
      ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq
        (atom_covBy_join hb Γ.hU hb_ne_U).lt.le (sup_le le_sup_left hU_le_bE)).resolve_left
        (ne_of_gt (atom_covBy_join hb Γ.hU hb_ne_U).lt)
    exact CoordSystem.hE_not_l (calc Γ.E ≤ b ⊔ Γ.E := le_sup_right
      _ = b ⊔ Γ.U := h_eq.symm
      _ = Γ.U ⊔ b := sup_comm _ _
      _ = Γ.O ⊔ Γ.U := hUb_eq)
  -- Corresponding vertices distinct
  have hab12 : a ≠ b := hab
  have hab22 : a' ≠ b' := by
    intro h
    have h_le_C : a' ≤ (a ⊔ Γ.C) ⊓ (b ⊔ Γ.C) :=
      le_inf inf_le_left ((le_of_eq h).trans inf_le_left)
    rw [CoordSystem.lines_through_C_meet Γ ha hb hab ha_on hb_on] at h_le_C
    exact Γ.hC_not_m (((Γ.hC.le_iff.mp h_le_C).resolve_left ha'_atom.1).symm ▸ inf_le_right)
  have hab32 : D_a ≠ D_b := by
    intro h
    have h_le_E : D_a ≤ (a ⊔ Γ.E) ⊓ (b ⊔ Γ.E) :=
      le_inf inf_le_left ((le_of_eq h).trans inf_le_left)
    rw [CoordSystem.lines_through_E_meet Γ ha hb hab ha_on hb_on] at h_le_E
    exact hE_not_UC (((Γ.hE_atom.le_iff.mp h_le_E).resolve_left hDa_atom.1).symm ▸ inf_le_right)
  -- Sides covered by π
  have hcov12 : a ⊔ a' ⋖ π := by
    rw [haa']
    have hDa_inf : D_a ⊓ (a ⊔ Γ.C) = ⊥ :=
      (hDa_atom.le_iff.mp inf_le_left).resolve_right
        (fun h => hDa_not_aC ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (hDa_inf ▸ hDa_atom.bot_covBy)
    rwa [show D_a ⊔ (a ⊔ Γ.C) = a ⊔ Γ.C ⊔ D_a from sup_comm _ _,
         show a ⊔ Γ.C ⊔ D_a = a ⊔ a' ⊔ D_a from by rw [← haa'], hπA] at h_cov
  have hcov13 : a ⊔ D_a ⋖ π := by
    rw [haDa]
    have ha_not_m : ¬ a ≤ Γ.U ⊔ Γ.V :=
      fun hle => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on hle)
    have ha'_not_aE : ¬ a' ≤ a ⊔ Γ.E := by
      intro h
      have ha_inf_m : a ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
        (ha.le_iff.mp inf_le_left).resolve_right (fun h => ha_not_m ((le_of_eq h.symm).trans inf_le_right))
      have h_mod : (Γ.E ⊔ a) ⊓ (Γ.U ⊔ Γ.V) = Γ.E ⊔ a ⊓ (Γ.U ⊔ Γ.V) :=
        sup_inf_assoc_of_le a CoordSystem.hE_on_m
      rw [ha_inf_m, sup_bot_eq] at h_mod
      have ha'_le_E : a' ≤ Γ.E := by
        have := le_inf h (inf_le_right : a' ≤ Γ.U ⊔ Γ.V)
        rwa [show (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.V) = (Γ.E ⊔ a) ⊓ (Γ.U ⊔ Γ.V) from by
          rw [sup_comm a Γ.E], h_mod] at this
      have hE_on_aC : Γ.E ≤ a ⊔ Γ.C := by
        have ha'_eq_E := (Γ.hE_atom.le_iff.mp ha'_le_E).resolve_left ha'_atom.1
        exact (le_of_eq ha'_eq_E.symm).trans inf_le_left
      have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
        intro hle
        have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
          ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
            (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
      have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
        have hOC' : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
        exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
          hOC'.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
      have hCE' : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
      exact hCE' ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_on_aC CoordSystem.hE_le_OC)
          h_inf_C)).resolve_left Γ.hE_atom.1).symm
    have ha'_inf : a' ⊓ (a ⊔ Γ.E) = ⊥ :=
      (ha'_atom.le_iff.mp inf_le_left).resolve_right
        (fun h => ha'_not_aE ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (ha'_inf ▸ ha'_atom.bot_covBy)
    rwa [show a' ⊔ (a ⊔ Γ.E) = a ⊔ Γ.E ⊔ a' from sup_comm _ _,
         show a ⊔ Γ.E ⊔ a' = a ⊔ a' ⊔ D_a from by
           rw [← haDa, sup_comm (a ⊔ D_a) a', ← sup_assoc, sup_comm a' a],
         hπA] at h_cov
  have hcov23 : a' ⊔ D_a ⋖ π := by
    have ha_not_a'Da : ¬ a ≤ a' ⊔ D_a := by
      intro h
      have h_le : a ⊔ a' ≤ a' ⊔ D_a := sup_le h le_sup_left
      have h_le' : a' ⊔ a ≤ a' ⊔ D_a := sup_comm a a' ▸ h_le
      rcases (atom_covBy_join ha'_atom hDa_atom h23a).eq_or_eq
        (atom_covBy_join ha'_atom ha h12a.symm).lt.le h_le' with h_abs | h_abs
      · -- h_abs : a' ⊔ a = a', so a ≤ a'
        have ha_le_a' : a ≤ a' := le_of_le_of_eq (le_sup_right : a ≤ a' ⊔ a) h_abs
        exact h12a ((ha'_atom.le_iff.mp ha_le_a').resolve_left ha.1)
      · -- h_abs : a' ⊔ a = a' ⊔ D_a, so D_a ≤ a' ⊔ a = a ⊔ a' = a ⊔ C
        have : D_a ≤ a ⊔ Γ.C := by
          calc D_a ≤ a' ⊔ D_a := le_sup_right
            _ = a' ⊔ a := h_abs.symm
            _ = a ⊔ a' := sup_comm _ _
            _ = a ⊔ Γ.C := haa'
        exact hDa_not_aC this
    have ha_inf : a ⊓ (a' ⊔ D_a) = ⊥ :=
      (ha.le_iff.mp inf_le_left).resolve_right
        (fun h => ha_not_a'Da ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (ha_inf ▸ ha.bot_covBy)
    rwa [show a ⊔ (a' ⊔ D_a) = a ⊔ a' ⊔ D_a from (sup_assoc _ _ _).symm, hπA] at h_cov
  -- Apply desargues_planar
  obtain ⟨axis, h_axis_le, h_axis_ne, h₁, h₂, h₃⟩ := desargues_planar
    Γ.hU ha ha'_atom hDa_atom hb hb'_atom hDb_atom
    h_ho_le h_ha1_le h_ha2_le h_ha3_le h_hb1_le h_hb2_le h_hb3_le
    hb1_on hb2_on hb3_on
    h12a h13a h23a
    h12b h13b h23b
    hs12 hs13 hs23
    hπA hπB
    hoa1 hoa2 hoa3 hob1 hob2 hob3
    hab12 hab22 hab32
    R hR hR_not h_irred
    hcov12 hcov13 hcov23
  -- First two side-intersections are C and E
  rw [haa', hbb', CoordSystem.lines_through_C_meet Γ ha hb hab ha_on hb_on] at h₁
  rw [haDa, hbDb, CoordSystem.lines_through_E_meet Γ ha hb hab ha_on hb_on] at h₂
  -- collinear_of_common_bound
  have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
    have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have h_le : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right CoordSystem.hE_le_OC
    have h_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hCE ((Γ.hC.le_iff.mp (h ▸ le_sup_right : Γ.E ≤ Γ.C)).resolve_left
        Γ.hE_atom.1).symm)
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
    exact (atom_covBy_join Γ.hC Γ.hO hOC.symm |>.eq_or_eq h_lt.le
      (sup_comm Γ.C Γ.O ▸ h_le)).resolve_left (ne_of_gt h_lt)
  have hCE_covBy : Γ.C ⊔ Γ.E ⋖ π := by rw [hCE_eq]; exact CoordSystem.OC_covBy_π Γ
  exact (collinear_of_common_bound (s₁ := Γ.C) (s₂ := Γ.E) hCE_covBy h_axis_le h_axis_ne h₁ h₂ h₃).trans
    (le_of_eq hCE_eq)

/-- **Second Desargues for addition.** Given P₁ ≤ O⊔C (from the first),
    the point W = (a'⊔D_b) ⊓ (b'⊔D_a) lies on l = O⊔U.
    Proved by applying desargues_planar to triangles
    (C, a', D_b) and (E, D_a, b') perspective from P₁. -/
theorem coord_second_desargues (Γ : CoordSystem L) {a b : L}
    (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : a ≠ b)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q)
    (hP₁ : ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓
            ((b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ≤ Γ.O ⊔ Γ.C) :
    ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓
    ((b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ≤ Γ.O ⊔ Γ.U := by
  /- Proof plan: apply desargues_planar to
     Center: P₁ = (a'⊔D_a) ⊓ (b'⊔D_b)
     Triangle A: (C, a', D_b)  Triangle B: (E, D_a, b')
     Side intersections: (C⊔a')⊓(E⊔D_a)=a, (C⊔D_b)⊓(E⊔b')=U, (a'⊔D_b)⊓(D_a⊔b')=W
     Then a ⊔ U = O⊔U = l, and collinear_of_common_bound gives W ≤ l. -/
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set a' := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set b' := (b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set D_a := (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  set D_b := (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  set P₁ := (a' ⊔ D_a) ⊓ (b' ⊔ D_b)
  -- ── basic distinctness ──
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
  have ha_ne_E : a ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ ha_on)
  have hb_ne_E : b ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hb_on)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)
  -- ── key modular intersections ──
  have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U :=
    modular_intersection Γ.hU Γ.hC Γ.hV hUC hUV
      (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      (fun hle => Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV hUV).lt.le (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV hUV).lt) ▸ le_sup_right))
  have hE_not_UC : ¬ Γ.E ≤ Γ.U ⊔ Γ.C := fun h =>
    CoordSystem.hEU (Γ.hU.le_iff.mp (hUC_inf_m ▸ le_inf h CoordSystem.hE_on_m)
      |>.resolve_left Γ.hE_atom.1)
  have hl_inf_UC : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U := by
    rw [sup_comm Γ.O Γ.U]
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm
      (fun h => Γ.hC_not_l (h ▸ le_sup_right))
      (fun h => Γ.hC_not_l (h ▸ le_sup_left))
      (fun h => Γ.hC_not_l (by rwa [sup_comm] at h))
  -- ── coplanarity ──
  have hUCE_eq_π : (Γ.U ⊔ Γ.C) ⊔ Γ.E = π := by
    have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
      have h_le : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right CoordSystem.hE_le_OC
      have h_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
        (fun h => hCE ((Γ.hC.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hE_atom.1).symm)
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact (atom_covBy_join Γ.hC Γ.hO hOC.symm |>.eq_or_eq h_lt.le
        (sup_comm Γ.C Γ.O ▸ h_le)).resolve_left (ne_of_gt h_lt)
    rw [show (Γ.U ⊔ Γ.C) ⊔ Γ.E = Γ.U ⊔ (Γ.C ⊔ Γ.E) from sup_assoc _ _ _, hCE_eq,
        show Γ.U ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.C from by rw [← sup_assoc, sup_comm Γ.U Γ.O]]
    have h_lt : Γ.O ⊔ Γ.C < Γ.O ⊔ Γ.U ⊔ Γ.C := by
      apply lt_of_le_of_ne (sup_le (le_sup_left.trans le_sup_left) le_sup_right); intro h
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le
        (h.symm ▸ le_sup_left)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt)
  -- ── atom properties ──
  have ha'_atom : IsAtom a' := perspect_atom Γ.hC ha
    (fun h => Γ.hC_not_l (h ▸ ha_on)) Γ.hU Γ.hV hUV Γ.hC_not_m
    (sup_le (ha_on.trans (le_sup_left.trans (le_of_eq Γ.m_sup_C_eq_π.symm))) le_sup_right)
  have hb'_atom : IsAtom b' := perspect_atom Γ.hC hb
    (fun h => Γ.hC_not_l (h ▸ hb_on)) Γ.hU Γ.hV hUV Γ.hC_not_m
    (sup_le (hb_on.trans (le_sup_left.trans (le_of_eq Γ.m_sup_C_eq_π.symm))) le_sup_right)
  have hDa_atom : IsAtom D_a := perspect_atom Γ.hE_atom ha ha_ne_E Γ.hU Γ.hC hUC hE_not_UC
    (sup_le (ha_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  have hDb_atom : IsAtom D_b := perspect_atom Γ.hE_atom hb hb_ne_E Γ.hU Γ.hC hUC hE_not_UC
    (sup_le (hb_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  -- ── more distinctness ──
  have hDa_ne_U : D_a ≠ Γ.U := by
    intro h
    have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := h ▸ (inf_le_left : D_a ≤ a ⊔ Γ.E)
    have h_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq
        (atom_covBy_join ha Γ.hU ha_ne_U).lt.le (sup_le le_sup_left hU_le_aE)).resolve_left
        (ne_of_gt (atom_covBy_join ha Γ.hU ha_ne_U).lt)
    have hUa_eq' : Γ.U ⊔ a = Γ.O ⊔ Γ.U := by
      have h_lt : Γ.U < Γ.U ⊔ a := lt_of_le_of_ne le_sup_left
        (fun h => ha_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left ha.1))
      exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le
        (sup_le le_sup_left (ha_on.trans (sup_comm Γ.O Γ.U).le))).resolve_left
        (ne_of_gt h_lt) |>.trans (sup_comm _ _)
    exact CoordSystem.hE_not_l (le_of_le_of_eq le_sup_right h_eq.symm |>.trans
      (le_of_eq (show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _)) |>.trans (le_of_eq hUa_eq'))
  have hDb_ne_U : D_b ≠ Γ.U := by
    intro h
    have hU_le_bE : Γ.U ≤ b ⊔ Γ.E := h ▸ (inf_le_left : D_b ≤ b ⊔ Γ.E)
    have hUb_eq : Γ.U ⊔ b = Γ.O ⊔ Γ.U := by
      have h_lt : Γ.U < Γ.U ⊔ b := lt_of_le_of_ne le_sup_left
        (fun h => hb_ne_U ((Γ.hU.le_iff.mp (h ▸ le_sup_right)).resolve_left hb.1))
      exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le
        (sup_le le_sup_left (hb_on.trans (by rw [sup_comm])))).resolve_left
        (ne_of_gt h_lt) |>.trans (sup_comm _ _)
    have h_eq : b ⊔ Γ.U = b ⊔ Γ.E :=
      ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq
        (atom_covBy_join hb Γ.hU hb_ne_U).lt.le (sup_le le_sup_left hU_le_bE)).resolve_left
        (ne_of_gt (atom_covBy_join hb Γ.hU hb_ne_U).lt)
    exact CoordSystem.hE_not_l (calc Γ.E ≤ b ⊔ Γ.E := le_sup_right
      _ = b ⊔ Γ.U := h_eq.symm
      _ = Γ.U ⊔ b := sup_comm _ _
      _ = Γ.O ⊔ Γ.U := hUb_eq)
  have hDa_ne_C : D_a ≠ Γ.C := by
    intro h
    have hC_le_aE : Γ.C ≤ a ⊔ Γ.E := (le_of_eq h.symm).trans inf_le_left
    have h_aCE : a ⊔ Γ.C ≤ a ⊔ Γ.E := sup_le le_sup_left hC_le_aE
    have h_aC_lt : a < a ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_C ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hC.1).symm)
    have h_eq : a ⊔ Γ.C = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq h_aC_lt.le h_aCE).resolve_left
        (ne_of_gt h_aC_lt)
    have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := le_of_le_of_eq le_sup_right h_eq.symm
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
    have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
        hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
    exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_aC CoordSystem.hE_le_OC) h_inf_C)).resolve_left
      Γ.hE_atom.1).symm
  have hDb_ne_C : D_b ≠ Γ.C := by
    intro h
    have hC_le_bE : Γ.C ≤ b ⊔ Γ.E := (le_of_eq h.symm).trans inf_le_left
    have h_bC_lt : b < b ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h => hb_ne_C ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hC.1).symm)
    have h_eq : b ⊔ Γ.C = b ⊔ Γ.E :=
      ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq h_bC_lt.le
        (sup_le le_sup_left hC_le_bE)).resolve_left (ne_of_gt h_bC_lt)
    have hE_le_bC : Γ.E ≤ b ⊔ Γ.C := le_of_le_of_eq le_sup_right h_eq.symm
    have hO_not_bC : ¬ Γ.O ≤ b ⊔ Γ.C := by
      intro hle
      have heq : b ⊔ Γ.O = b ⊔ Γ.C :=
        ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq (atom_covBy_join hb Γ.hO hb_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join hb Γ.hO hb_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le hb_on le_sup_left))
    have h_inf_C : (b ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm b Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC hb Γ.hO (fun h => hb_ne_C h.symm)
        hOC.symm hb_ne_O (by rwa [sup_comm] at hO_not_bC)
    exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_bC CoordSystem.hE_le_OC)
        h_inf_C)).resolve_left Γ.hE_atom.1).symm
  have hDa_ne_E : D_a ≠ Γ.E := fun h => hE_not_UC (h ▸ inf_le_right)
  have hDb_ne_E : D_b ≠ Γ.E := fun h => hE_not_UC (h ▸ inf_le_right)
  have ha'_ne_U : a' ≠ Γ.U := by
    intro h; have : Γ.U ≤ a ⊔ Γ.C := h ▸ inf_le_left
    exact ha_ne_U ((ha.le_iff.mp (le_of_le_of_eq (le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) this)
      (show (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) = a from by
        rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _]; exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on))).resolve_left Γ.hU.1).symm
  have hb'_ne_U : b' ≠ Γ.U := by
    intro h; have : Γ.U ≤ b ⊔ Γ.C := h ▸ inf_le_left
    exact hb_ne_U ((hb.le_iff.mp (le_of_le_of_eq (le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) this)
      (show (Γ.O ⊔ Γ.U) ⊓ (b ⊔ Γ.C) = b from by
        rw [show b ⊔ Γ.C = Γ.C ⊔ b from sup_comm _ _]; exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on))).resolve_left Γ.hU.1).symm
  have ha'_ne_C : a' ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ inf_le_right)
  have hb'_ne_C : b' ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ inf_le_right)
  have ha'_ne_E : a' ≠ Γ.E := by
    intro heq
    have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := heq ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      have h_eq : a ⊔ Γ.O = a ⊔ Γ.C :=
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right h_eq.symm |>.trans (sup_le ha_on le_sup_left))
    have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
        hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
    exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_aC CoordSystem.hE_le_OC)
        h_inf_C)).resolve_left Γ.hE_atom.1).symm
  have hb'_ne_E : b' ≠ Γ.E := by
    intro heq
    have hE_le_bC : Γ.E ≤ b ⊔ Γ.C := heq ▸ (inf_le_left : b' ≤ b ⊔ Γ.C)
    have hO_not_bC : ¬ Γ.O ≤ b ⊔ Γ.C := by
      intro hle
      have h_eq : b ⊔ Γ.O = b ⊔ Γ.C :=
        ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq (atom_covBy_join hb Γ.hO hb_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join hb Γ.hO hb_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right h_eq.symm |>.trans (sup_le hb_on le_sup_left))
    have h_inf_C : (b ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm b Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC hb Γ.hO (fun h => hb_ne_C h.symm)
        hOC.symm hb_ne_O (by rwa [sup_comm] at hO_not_bC)
    exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_bC CoordSystem.hE_le_OC)
        h_inf_C)).resolve_left Γ.hE_atom.1).symm
  have ha'Da_ne : a' ≠ D_a := by
    intro h; exact ha'_ne_U ((Γ.hU.le_iff.mp
      (hUC_inf_m ▸ (le_inf (h ▸ inf_le_right) inf_le_right : a' ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)))).resolve_left ha'_atom.1)
  have hb'Db_ne : b' ≠ D_b := by
    intro h; exact hb'_ne_U ((Γ.hU.le_iff.mp
      (hUC_inf_m ▸ (le_inf (h ▸ inf_le_right) inf_le_right : b' ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)))).resolve_left hb'_atom.1)
  have ha'Db_ne : a' ≠ D_b := by
    intro h; exact ha'_ne_U ((Γ.hU.le_iff.mp
      (hUC_inf_m ▸ (le_inf (h ▸ inf_le_right) inf_le_right : a' ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)))).resolve_left ha'_atom.1)
  have hDa_ne_b' : D_a ≠ b' := by
    intro h; exact hDa_ne_U ((Γ.hU.le_iff.mp
      (hUC_inf_m ▸ (le_inf inf_le_right (h ▸ inf_le_right) : D_a ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)))).resolve_left hDa_atom.1)
  -- ── join equalities (sorry for hard ones) ──
  have hCa'_eq : Γ.C ⊔ a' = a ⊔ Γ.C := by
    have h_lt : Γ.C < Γ.C ⊔ a' := by
      apply lt_of_le_of_ne le_sup_left; intro h
      exact ha'_ne_C (Γ.hC.le_iff.mp (le_of_le_of_eq le_sup_right h.symm) |>.resolve_left ha'_atom.1)
    have h_le : Γ.C ⊔ a' ≤ Γ.C ⊔ a :=
      sup_le le_sup_left ((inf_le_left : a' ≤ a ⊔ Γ.C).trans (sup_comm a Γ.C).le)
    rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _]
    exact ((atom_covBy_join Γ.hC ha (fun h => ha_ne_C h.symm)).eq_or_eq h_lt.le h_le).resolve_left
      (ne_of_gt h_lt)
  have hEDa_eq : Γ.E ⊔ D_a = a ⊔ Γ.E := by
    have h_lt : Γ.E < Γ.E ⊔ D_a := by
      apply lt_of_le_of_ne le_sup_left; intro h
      exact hDa_ne_E (Γ.hE_atom.le_iff.mp (le_of_le_of_eq le_sup_right h.symm) |>.resolve_left hDa_atom.1)
    have h_le : Γ.E ⊔ D_a ≤ Γ.E ⊔ a :=
      sup_le le_sup_left ((inf_le_left : D_a ≤ a ⊔ Γ.E).trans (sup_comm a Γ.E).le)
    rw [show a ⊔ Γ.E = Γ.E ⊔ a from sup_comm _ _]
    exact ((atom_covBy_join Γ.hE_atom ha (fun h => ha_ne_E h.symm)).eq_or_eq h_lt.le h_le).resolve_left
      (ne_of_gt h_lt)
  have hCDb_eq : Γ.C ⊔ D_b = Γ.U ⊔ Γ.C := by
    have h_lt : Γ.C < Γ.C ⊔ D_b := lt_of_le_of_ne le_sup_left
      (fun h => hDb_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq le_sup_right h.symm)).resolve_left hDb_atom.1))
    rw [sup_comm Γ.U Γ.C]
    exact ((atom_covBy_join Γ.hC Γ.hU hUC.symm).eq_or_eq h_lt.le
      (sup_le le_sup_left ((inf_le_right).trans (sup_comm Γ.U Γ.C).le))).resolve_left (ne_of_gt h_lt)
  have hEb'_eq : Γ.E ⊔ b' = Γ.U ⊔ Γ.V := by
    have hb'_cov : b' ⋖ Γ.U ⊔ Γ.V :=
      line_covers_its_atoms Γ.hU Γ.hV hUV hb'_atom inf_le_right
    have h_lt : b' < Γ.E ⊔ b' := by
      apply lt_of_le_of_ne le_sup_right; intro h
      have hE_le : Γ.E ≤ b' := by
        calc Γ.E ≤ Γ.E ⊔ b' := le_sup_left
          _ = b' := h.symm
      exact hb'_ne_E ((hb'_atom.le_iff.mp hE_le).resolve_left Γ.hE_atom.1).symm
    exact (hb'_cov.eq_or_eq h_lt.le (sup_le CoordSystem.hE_on_m inf_le_right)).resolve_left (ne_of_gt h_lt)
  have hUa_eq : Γ.U ⊔ a = Γ.O ⊔ Γ.U := by
    have h_lt : Γ.U < Γ.U ⊔ a := by
      apply lt_of_le_of_ne le_sup_left; intro h
      have ha_le : a ≤ Γ.U := by
        calc a ≤ Γ.U ⊔ a := le_sup_right
          _ = Γ.U := h.symm
      exact ha_ne_U ((Γ.hU.le_iff.mp ha_le).resolve_left ha.1)
    exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le
      (sup_le le_sup_left (ha_on.trans (sup_comm Γ.O Γ.U).le))).resolve_left
      (ne_of_gt h_lt) |>.trans (sup_comm _ _)
  -- ── a'⊔D_a ≠ b'⊔D_b ──
  have hDa_not_m : ¬ D_a ≤ Γ.U ⊔ Γ.V := by
    intro hle
    have h1 : D_a ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := le_inf inf_le_right hle
    rw [hUC_inf_m] at h1
    exact hDa_ne_U ((Γ.hU.le_iff.mp h1).resolve_left hDa_atom.1)
  have hDb_not_m : ¬ D_b ≤ Γ.U ⊔ Γ.V := by
    intro hle
    have h1 : D_b ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := le_inf inf_le_right hle
    rw [hUC_inf_m] at h1
    exact hDb_ne_U ((Γ.hU.le_iff.mp h1).resolve_left hDb_atom.1)
  have ha'Da_ne_b'Db : a' ⊔ D_a ≠ b' ⊔ D_b := by
    intro heq
    by_cases hab' : a' = b'
    · exfalso
      have ha'_le_aC : a' ≤ Γ.C ⊔ a := sup_comm a Γ.C ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
      have ha'_le_bC : a' ≤ Γ.C ⊔ b :=
        sup_comm b Γ.C ▸ (hab' ▸ (inf_le_left : b' ≤ b ⊔ Γ.C))
      have hb_not_Ca : ¬ b ≤ Γ.C ⊔ a := by
        intro hle
        have hab_le : a ⊔ b ≤ Γ.C ⊔ a := sup_le le_sup_right hle
        have h_cov_aCa : a ⋖ Γ.C ⊔ a := sup_comm Γ.C a ▸
          atom_covBy_join ha Γ.hC ha_ne_C
        have h_lt_ab : a < a ⊔ b := lt_of_le_of_ne le_sup_left
          (fun h => hab ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left hb.1).symm)
        have h_eq : a ⊔ b = Γ.C ⊔ a :=
          (h_cov_aCa.eq_or_eq h_lt_ab.le hab_le).resolve_left (ne_of_gt h_lt_ab)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_left h_eq.symm |>.trans (sup_le ha_on hb_on))
      have hCab : (Γ.C ⊔ a) ⊓ (Γ.C ⊔ b) = Γ.C :=
        modular_intersection Γ.hC ha hb (fun h => ha_ne_C h.symm)
          (fun h => hb_ne_C h.symm) hab hb_not_Ca
      have ha'_le_C : a' ≤ Γ.C := le_of_le_of_eq (le_inf ha'_le_aC ha'_le_bC) hCab
      have ha'_eq_C : a' = Γ.C := (Γ.hC.le_iff.mp ha'_le_C).resolve_left ha'_atom.1
      exact Γ.hC_not_m (ha'_eq_C ▸ inf_le_right)
    · exfalso
      have h_cov_UV : Γ.U ⋖ Γ.U ⊔ Γ.V := atom_covBy_join Γ.hU Γ.hV hUV
      have ha'b'_le : a' ⊔ b' ≤ Γ.U ⊔ Γ.V := sup_le inf_le_right inf_le_right
      have h_a'_lt_a'b' : a' < a' ⊔ b' := lt_of_le_of_ne le_sup_left
        (fun h => hab' ((ha'_atom.le_iff.mp
          (le_of_le_of_eq le_sup_right h.symm)).resolve_left hb'_atom.1).symm)
      have h_lt_m : a' < Γ.U ⊔ Γ.V := lt_of_lt_of_le h_a'_lt_a'b' ha'b'_le
      have hU_le_a'b' : Γ.U ≤ a' ⊔ b' := by
        by_contra hU_not
        have hU_inf : Γ.U ⊓ (a' ⊔ b') = ⊥ :=
          (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun h => hU_not (h ▸ inf_le_right))
        have ha'U_eq : Γ.U ⊔ a' = Γ.U ⊔ Γ.V := by
          have h_lt : Γ.U < Γ.U ⊔ a' := lt_of_le_of_ne le_sup_left
            (fun h => ha'_ne_U ((Γ.hU.le_iff.mp
              (le_of_le_of_eq le_sup_right h.symm)).resolve_left ha'_atom.1))
          exact (h_cov_UV.eq_or_eq h_lt.le
            (sup_le le_sup_left inf_le_right)).resolve_left (ne_of_gt h_lt)
        have hmod : (Γ.U ⊔ a') ⊓ (a' ⊔ b') = a' := by
          have h1 := sup_inf_assoc_of_le Γ.U (le_sup_left : a' ≤ a' ⊔ b')
          rw [hU_inf, sup_bot_eq, sup_comm a' Γ.U] at h1; exact h1
        rw [ha'U_eq] at hmod
        have hb'_le_a' : b' ≤ a' :=
          le_of_le_of_eq (le_inf inf_le_right (le_sup_right : b' ≤ a' ⊔ b')) hmod
        exact hab' ((ha'_atom.le_iff.mp hb'_le_a').resolve_left hb'_atom.1).symm
      have hU_lt_a'b' : Γ.U < a' ⊔ b' :=
        lt_of_le_of_ne hU_le_a'b' (fun h => by
          have ha'_le_U : a' ≤ Γ.U := le_of_le_of_eq le_sup_left h.symm
          have hb'_le_U : b' ≤ Γ.U := le_of_le_of_eq le_sup_right h.symm
          exact hab' ((Γ.hU.le_iff.mp ha'_le_U).resolve_left ha'_atom.1 |>.trans
            ((Γ.hU.le_iff.mp hb'_le_U).resolve_left hb'_atom.1).symm))
      have hm_eq : a' ⊔ b' = Γ.U ⊔ Γ.V :=
        (h_cov_UV.eq_or_eq hU_lt_a'b'.le ha'b'_le).resolve_left (ne_of_gt hU_lt_a'b')
      have hb'_le : b' ≤ a' ⊔ D_a := le_of_le_of_eq le_sup_left heq.symm
      have ha'b'_le_a'Da : a' ⊔ b' ≤ a' ⊔ D_a := sup_le le_sup_left hb'_le
      have hm_le : Γ.U ⊔ Γ.V ≤ a' ⊔ D_a := hm_eq ▸ ha'b'_le_a'Da
      have h_cov : a' ⋖ a' ⊔ D_a := atom_covBy_join ha'_atom hDa_atom ha'Da_ne
      have h_eq_m : a' ⊔ D_a = Γ.U ⊔ Γ.V :=
        ((h_cov.eq_or_eq h_lt_m.le hm_le).resolve_left (ne_of_gt h_lt_m)).symm
      exact hDa_not_m (le_of_le_of_eq le_sup_right h_eq_m)
  -- ── P₁ is an atom ──
  have hDa_not_aC_early : ¬ D_a ≤ a ⊔ Γ.C := by
    intro hle
    have h_le : D_a ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.U) :=
      le_inf ((sup_comm a Γ.C).symm ▸ hle) ((sup_comm Γ.U Γ.C).symm ▸ inf_le_right)
    have hU_not_aC : ¬ Γ.U ≤ a ⊔ Γ.C := by
      intro hle2
      have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hle2
      rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
      exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
    rw [modular_intersection Γ.hC ha Γ.hU (fun h => ha_ne_C h.symm) hUC.symm
      ha_ne_U (by rwa [sup_comm] at hU_not_aC)] at h_le
    exact hDa_ne_C ((Γ.hC.le_iff.mp h_le).resolve_left hDa_atom.1)
  -- a not on a'⊔D_a (for covering)
  have ha_not_a'Da : ¬ a ≤ a' ⊔ D_a := by
    intro h
    have h_le : a ⊔ a' ≤ a' ⊔ D_a := sup_le h le_sup_left
    have h_le' : a' ⊔ a ≤ a' ⊔ D_a := sup_comm a a' ▸ h_le
    -- a' ⋖ a'⊔D_a, a' < a'⊔a ≤ a'⊔D_a.
    -- a ≠ a' (if a = a', then a ≤ U⊔V, forcing a = U, contradiction)
    have h12a : a ≠ a' := by
      intro heq; exact ha_ne_U (Γ.atom_on_both_eq_U ha ha_on (heq ▸ inf_le_right))
    rcases (atom_covBy_join ha'_atom hDa_atom ha'Da_ne).eq_or_eq
      (atom_covBy_join ha'_atom ha h12a.symm).lt.le h_le' with h_abs | h_abs
    · exact h12a ((ha'_atom.le_iff.mp (le_of_le_of_eq (le_sup_right : a ≤ a' ⊔ a) h_abs)).resolve_left ha.1)
    · -- a'⊔a = a'⊔D_a, so D_a ≤ a⊔C
      have hDa_le : D_a ≤ a ⊔ Γ.C := calc
        D_a ≤ a' ⊔ D_a := le_sup_right
        _ = a' ⊔ a := h_abs.symm
        _ ≤ a ⊔ Γ.C := sup_le (inf_le_left : a' ≤ a ⊔ Γ.C) le_sup_left
      exact hDa_not_aC_early hDa_le
  have ha_inf_a'Da : a ⊓ (a' ⊔ D_a) = ⊥ :=
    (ha.le_iff.mp inf_le_left).resolve_right
      (fun h => ha_not_a'Da ((le_of_eq h.symm).trans inf_le_right))
  have hCDa_eq : Γ.C ⊔ D_a = Γ.U ⊔ Γ.C := by
    have h_lt : Γ.C < Γ.C ⊔ D_a := by
      apply lt_of_le_of_ne le_sup_left
      intro heq; exact hDa_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq le_sup_right heq.symm)).resolve_left hDa_atom.1)
    rw [sup_comm Γ.U Γ.C]
    exact ((atom_covBy_join Γ.hC Γ.hU hUC.symm).eq_or_eq h_lt.le
      (sup_le le_sup_left ((inf_le_right).trans (le_of_eq (sup_comm Γ.U Γ.C))))).resolve_left (ne_of_gt h_lt)
  have haa'_eq : a ⊔ a' = a ⊔ Γ.C := by
    have h12a : a ≠ a' := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on (h ▸ inf_le_right))
    have h_lt : a < a ⊔ a' := lt_of_le_of_ne le_sup_left
      (fun h => h12a ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left ha'_atom.1).symm)
    exact ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have hπA_orig : a ⊔ a' ⊔ D_a = π := by
    rw [haa'_eq, sup_assoc, hCDa_eq, show a ⊔ (Γ.U ⊔ Γ.C) = (a ⊔ Γ.U) ⊔ Γ.C from
      (sup_assoc _ _ _).symm, show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _, hUa_eq]
    have h_lt : Γ.O ⊔ Γ.C < (Γ.O ⊔ Γ.U) ⊔ Γ.C := by
      apply lt_of_le_of_ne (sup_le (le_sup_left.trans le_sup_left) le_sup_right); intro h
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le (h.symm ▸ le_sup_left)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt)
  have ha'Da_covBy_π : a' ⊔ D_a ⋖ π := by
    have h_cov := covBy_sup_of_inf_covBy_left (ha_inf_a'Da ▸ ha.bot_covBy)
    rwa [show a ⊔ (a' ⊔ D_a) = a ⊔ a' ⊔ D_a from (sup_assoc _ _ _).symm,
         hπA_orig] at h_cov
  have hU_le_π' : Γ.U ≤ π := le_sup_right.trans le_sup_left
  have ha'Da_le_π : a' ⊔ D_a ≤ π := sup_le
    (inf_le_right.trans (sup_le hU_le_π' le_sup_right))
    (inf_le_right.trans (sup_le hU_le_π' Γ.hC_plane))
  have hb'Db_le_π : b' ⊔ D_b ≤ π := sup_le
    (inf_le_right.trans (sup_le hU_le_π' le_sup_right))
    (inf_le_right.trans (sup_le hU_le_π' Γ.hC_plane))
  have hb'Db_not_le_a'Da : ¬ b' ⊔ D_b ≤ a' ⊔ D_a := by
    intro h
    rcases lt_or_eq_of_le h with h_lt | h_eq
    · -- b'⊔D_b is an atom of a'⊔D_a. But b' < b'⊔D_b, contradiction.
      have hbd_atom := line_height_two ha'_atom hDa_atom ha'Da_ne
        (atom_covBy_join hb'_atom hDb_atom hb'Db_ne).lt.bot_lt h_lt
      have hb'_eq : b' = b' ⊔ D_b := (hbd_atom.le_iff.mp le_sup_left).resolve_left hb'_atom.1
      have hDb_le_b' : D_b ≤ b' := le_of_le_of_eq le_sup_right hb'_eq.symm
      exact hb'Db_ne ((hb'_atom.le_iff.mp hDb_le_b').resolve_left hDb_atom.1).symm
    · exact ha'Da_ne_b'Db h_eq.symm
  have hP₁_pos : ⊥ < P₁ := by
    rw [bot_lt_iff_ne_bot]; intro hP₁_bot
    exact lines_meet_if_coplanar ha'Da_covBy_π hb'Db_le_π hb'Db_not_le_a'Da
      hb'_atom (atom_covBy_join hb'_atom hDb_atom hb'Db_ne).lt hP₁_bot
  have hP₁_lt : P₁ < a' ⊔ D_a := by
    apply lt_of_le_of_ne inf_le_left; intro h
    have h2 : a' ⊔ D_a ≤ b' ⊔ D_b := h ▸ inf_le_right
    rcases lt_or_eq_of_le h2 with h_lt | h_eq
    · have had_atom := line_height_two hb'_atom hDb_atom hb'Db_ne
        (atom_covBy_join ha'_atom hDa_atom ha'Da_ne).lt.bot_lt h_lt
      have ha'_eq : a' = a' ⊔ D_a := (had_atom.le_iff.mp le_sup_left).resolve_left ha'_atom.1
      have hDa_le_a' : D_a ≤ a' := le_of_le_of_eq le_sup_right ha'_eq.symm
      exact ha'Da_ne ((ha'_atom.le_iff.mp hDa_le_a').resolve_left hDa_atom.1).symm
    · exact ha'Da_ne_b'Db h_eq
  have hP₁_atom : IsAtom P₁ := line_height_two ha'_atom hDa_atom ha'Da_ne hP₁_pos hP₁_lt
  -- ── perspective conditions ──
  have hE_on : Γ.E ≤ P₁ ⊔ Γ.C := by
    -- P₁⊔C = O⊔C (since P₁ ≤ O⊔C, P₁ ≠ C, covering). E ≤ O⊔C.
    have hP₁_ne_C : P₁ ≠ Γ.C := by
      intro h
      -- P₁ = C, so C ≤ a'⊔D_a. Then C⊔D_a ≤ a'⊔D_a.
      -- hCDa_eq: C⊔D_a = U⊔C. So U⊔C ≤ a'⊔D_a (both lines, must be equal).
      -- Then U ≤ a'⊔D_a. a' ≤ (U⊔V)⊓(U⊔C) = U. Contradiction.
      have hC_le : Γ.C ≤ a' ⊔ D_a := h ▸ inf_le_left
      have hUC_le : Γ.U ⊔ Γ.C ≤ a' ⊔ D_a := by
        calc Γ.U ⊔ Γ.C = Γ.C ⊔ D_a := hCDa_eq.symm
          _ ≤ a' ⊔ D_a := sup_le hC_le le_sup_right
      rcases lt_or_eq_of_le hUC_le with h_lt | h_eq
      · have hUC_atom := line_height_two ha'_atom hDa_atom ha'Da_ne
            (atom_covBy_join Γ.hU Γ.hC hUC).lt.bot_lt h_lt
        -- U⊔C is an atom but U ≤ U⊔C and U ≠ ⊥ gives U = U⊔C, so C ≤ U, C = U. Contradiction.
        have hU_eq_UC : Γ.U = Γ.U ⊔ Γ.C := (hUC_atom.le_iff.mp le_sup_left).resolve_left Γ.hU.1
        have hC_le_U : Γ.C ≤ Γ.U := le_of_le_of_eq le_sup_right hU_eq_UC.symm
        exact hUC ((Γ.hU.le_iff.mp hC_le_U).resolve_left Γ.hC.1).symm
      · exact ha'_ne_U ((Γ.hU.le_iff.mp (le_of_le_of_eq
          (le_inf (inf_le_right : a' ≤ Γ.U ⊔ Γ.V) (le_of_le_of_eq le_sup_left h_eq.symm : a' ≤ Γ.U ⊔ Γ.C))
          (by rw [inf_comm]; exact hUC_inf_m))).resolve_left ha'_atom.1)
    have h_lt : Γ.C < P₁ ⊔ Γ.C := by
      apply lt_of_le_of_ne le_sup_right; intro h
      exact hP₁_ne_C (Γ.hC.le_iff.mp (le_of_le_of_eq le_sup_left h.symm) |>.resolve_left hP₁_atom.1)
    have h_le : P₁ ⊔ Γ.C ≤ Γ.O ⊔ Γ.C := sup_le hP₁ le_sup_right
    have hP₁C_eq : P₁ ⊔ Γ.C = Γ.O ⊔ Γ.C := by
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact ((atom_covBy_join Γ.hC Γ.hO hOC.symm).eq_or_eq h_lt.le
        (sup_comm Γ.C Γ.O ▸ h_le)).resolve_left (ne_of_gt h_lt)
    exact hP₁C_eq ▸ CoordSystem.hE_le_OC
  have hDa_on : D_a ≤ P₁ ⊔ a' := by
    -- P₁⊔a' = a'⊔D_a (P₁ ≤ a'⊔D_a, covering). So D_a ≤ P₁⊔a'.
    have hP₁_ne_a' : P₁ ≠ a' := by
      intro h
      -- a' ≤ O⊔C (from hP₁) and a' ≤ a⊔C (from inf_le_left). Their meet is C. So a' ≤ C.
      have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
        intro hle
        have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
          ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
            (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
      have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
        exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
          hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
      have ha'_le_OC : a' ≤ Γ.O ⊔ Γ.C := h ▸ hP₁
      exact ha'_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf inf_le_left ha'_le_OC) h_inf_C)).resolve_left ha'_atom.1)
    have h_lt : a' < P₁ ⊔ a' := by
      apply lt_of_le_of_ne le_sup_right; intro h
      exact hP₁_ne_a' (ha'_atom.le_iff.mp (le_of_le_of_eq le_sup_left h.symm) |>.resolve_left hP₁_atom.1)
    have h_le : P₁ ⊔ a' ≤ a' ⊔ D_a := sup_le inf_le_left le_sup_left
    have h_eq : P₁ ⊔ a' = a' ⊔ D_a :=
      ((atom_covBy_join ha'_atom hDa_atom ha'Da_ne).eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
    exact h_eq ▸ le_sup_right
  have hb'_on : b' ≤ P₁ ⊔ D_b := by
    -- P₁⊔D_b = b'⊔D_b (P₁ ≤ b'⊔D_b, covering). So b' ≤ P₁⊔D_b.
    have hP₁_ne_Db : P₁ ≠ D_b := by
      intro h
      -- D_b ≤ O⊔C and D_b ≤ U⊔C. (C⊔U)⊓(C⊔O) = C. So D_b ≤ C. Contradiction.
      have hUC_inf_OC_local : (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm Γ.U Γ.C, sup_comm Γ.O Γ.C]
        exact modular_intersection Γ.hC Γ.hU Γ.hO hUC.symm hOC.symm Γ.hOU.symm
          (by rw [sup_comm]; exact CoordSystem.hO_not_UC)
      have hDb_le_OC : D_b ≤ Γ.O ⊔ Γ.C := h ▸ hP₁
      exact hDb_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq
        (le_inf inf_le_right hDb_le_OC) hUC_inf_OC_local)).resolve_left hDb_atom.1)
    have h_lt : D_b < P₁ ⊔ D_b := by
      apply lt_of_le_of_ne le_sup_right; intro h
      exact hP₁_ne_Db (hDb_atom.le_iff.mp (le_of_le_of_eq le_sup_left h.symm) |>.resolve_left hP₁_atom.1)
    have h_le : P₁ ⊔ D_b ≤ D_b ⊔ b' := sup_le ((inf_le_right).trans (sup_comm b' D_b).le) le_sup_left
    have h_cov : D_b ⋖ D_b ⊔ b' := atom_covBy_join hDb_atom hb'_atom hb'Db_ne.symm
    have h_eq : P₁ ⊔ D_b = D_b ⊔ b' :=
      (h_cov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
    calc b' ≤ D_b ⊔ b' := le_sup_right
      _ = P₁ ⊔ D_b := h_eq.symm
  -- ── all in π ──
  have hU_le_π : Γ.U ≤ π := le_sup_right.trans le_sup_left
  have hm_le_π : Γ.U ⊔ Γ.V ≤ π := sup_le hU_le_π le_sup_right
  have hP₁_le_π : P₁ ≤ π := hP₁.trans (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane)
  have hC_le_π : Γ.C ≤ π := Γ.hC_plane
  have ha'_le_π : a' ≤ π := inf_le_right.trans hm_le_π
  have hDa_le_π : D_a ≤ π := inf_le_right.trans (sup_le hU_le_π hC_le_π)
  have hDb_le_π : D_b ≤ π := inf_le_right.trans (sup_le hU_le_π hC_le_π)
  have hE_le_π : Γ.E ≤ π := CoordSystem.hE_on_m.trans hm_le_π
  have hb'_le_π : b' ≤ π := inf_le_right.trans hm_le_π
  -- ── helpers for distinctness ──
  have hO_not_UC : ¬ Γ.O ≤ Γ.U ⊔ Γ.C := by
    intro hle
    have h_le : Γ.O ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) := le_inf le_sup_left hle
    rw [hl_inf_UC] at h_le
    exact Γ.hOU ((Γ.hU.le_iff.mp h_le).resolve_left Γ.hO.1)
  have hUC_inf_OC : (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
    rw [sup_comm Γ.U Γ.C, sup_comm Γ.O Γ.C]
    exact modular_intersection Γ.hC Γ.hU Γ.hO hUC.symm hOC.symm Γ.hOU.symm
      (by rwa [sup_comm] at hO_not_UC)
  have hDa_not_OC : ¬ D_a ≤ Γ.O ⊔ Γ.C := by
    intro hle; exact hDa_ne_C ((Γ.hC.le_iff.mp
      (hUC_inf_OC ▸ le_inf inf_le_right hle)).resolve_left hDa_atom.1)
  have hDb_not_OC : ¬ D_b ≤ Γ.O ⊔ Γ.C := by
    intro hle; exact hDb_ne_C ((Γ.hC.le_iff.mp
      (hUC_inf_OC ▸ le_inf inf_le_right hle)).resolve_left hDb_atom.1)
  have ha'_not_OC : ¬ a' ≤ Γ.O ⊔ Γ.C := by
    intro hle
    have h := le_inf (inf_le_right : a' ≤ Γ.U ⊔ Γ.V) hle
    -- a' ≤ (U⊔V) ⊓ (O⊔C). Need: (U⊔V)⊓(O⊔C) = ?
    -- O⊔C ≤ π. U⊔V ≤ π. Their meet in π: O is not on U⊔V (otherwise O on m, but O⊔U = l ≠ m).
    -- Actually: if a' ≤ O⊔C and a' = (a���C) ⊓ (U⊔V), then a' ≤ (a⊔C) ⊓ (O⊔C).
    -- (a⊔C) ⊓ (O⊔C) = C (if O not on a⊔C, modular_intersection with C, a, O).
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle2
      have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
          (sup_le le_sup_left hle2)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
    have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
        hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
    exact ha'_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf inf_le_left hle) h_inf_C)).resolve_left ha'_atom.1)
  have hb'_not_OC : ¬ b' ≤ Γ.O ⊔ Γ.C := by
    intro hle
    have hO_not_bC : ¬ Γ.O ≤ b ⊔ Γ.C := by
      intro hle2
      have heq : b ⊔ Γ.O = b ⊔ Γ.C :=
        ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq (atom_covBy_join hb Γ.hO hb_ne_O).lt.le
          (sup_le le_sup_left hle2)).resolve_left (ne_of_gt (atom_covBy_join hb Γ.hO hb_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le hb_on le_sup_left))
    have h_inf_C : (b ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm b Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC hb Γ.hO (fun h => hb_ne_C h.symm)
        hOC.symm hb_ne_O (by rwa [sup_comm] at hO_not_bC)
    exact hb'_ne_C ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf inf_le_left hle) h_inf_C)).resolve_left hb'_atom.1)
  have hDa_not_aC : ¬ D_a ≤ a ⊔ Γ.C := by
    intro hle
    have h_le : D_a ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.U) :=
      le_inf ((sup_comm a Γ.C).symm ▸ hle) ((sup_comm Γ.U Γ.C).symm ▸ inf_le_right)
    have hU_not_aC : ¬ Γ.U ≤ a ⊔ Γ.C := by
      intro hle2
      have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hle2
      rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
      exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
    rw [modular_intersection Γ.hC ha Γ.hU (fun h => ha_ne_C h.symm) hUC.symm
      ha_ne_U (by rwa [sup_comm] at hU_not_aC)] at h_le
    exact hDa_ne_C ((Γ.hC.le_iff.mp h_le).resolve_left hDa_atom.1)
  -- ── vertex/side distinctness ──
  have hs12 : Γ.C ⊔ a' ≠ Γ.E ⊔ D_a := by
    rw [hCa'_eq, hEDa_eq]; intro h
    -- a⊔C = a⊔E: so C ≤ a⊔E and E ≤ a⊔C. (a⊔C) ⊓ (O⊔C) = C. E ≤ a⊔C and E ≤ O⊔C. So E ≤ C. But E ≠ C.
    have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := le_of_le_of_eq le_sup_right h.symm
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
          (sup_le le_sup_left hle)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
      exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
    have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
      rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
      exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
        hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
    exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hE_le_aC CoordSystem.hE_le_OC) h_inf_C)).resolve_left
      Γ.hE_atom.1).symm
  have hs13 : Γ.C ⊔ D_b ≠ Γ.E ⊔ b' := by
    rw [hCDb_eq, hEb'_eq]; exact fun h => Γ.hC_not_m (h ▸ (le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C))
  have hab' : a' ≠ b' := by
    intro h
    have h_le_C : a' ≤ (a ⊔ Γ.C) ⊓ (b ⊔ Γ.C) :=
      le_inf inf_le_left ((le_of_eq h).trans inf_le_left)
    rw [CoordSystem.lines_through_C_meet Γ ha hb hab ha_on hb_on] at h_le_C
    exact Γ.hC_not_m (((Γ.hC.le_iff.mp h_le_C).resolve_left ha'_atom.1).symm ▸ inf_le_right)
  have hs23 : a' ⊔ D_b ≠ D_a ⊔ b' := by
    intro heq
    -- a' and b' are both ≤ a'⊔D_b (a' trivially, b' from heq)
    have hb'_le : b' ≤ a' ⊔ D_b := le_of_le_of_eq le_sup_right heq.symm
    -- a'⊔b' ≤ a'⊔D_b
    have ha'b'_le : a' ⊔ b' ≤ a' ⊔ D_b := sup_le le_sup_left hb'_le
    -- a'⊔b' is a line (a' ≠ b'), a'⊔D_b is a line. Rank argument:
    rcases lt_or_eq_of_le ha'b'_le with h_lt | h_eq
    · -- a'⊔b' < a'⊔D_b: a'⊔b' is an atom. But a' < a'⊔b'. Contradiction.
      have h_atom := line_height_two ha'_atom hDb_atom ha'Db_ne
        (atom_covBy_join ha'_atom hb'_atom hab').lt.bot_lt h_lt
      have ha'_eq : a' = a' ⊔ b' := (h_atom.le_iff.mp le_sup_left).resolve_left ha'_atom.1
      have hb'_le_a' : b' ≤ a' := le_of_le_of_eq le_sup_right ha'_eq.symm
      exact hab' ((ha'_atom.le_iff.mp hb'_le_a').resolve_left hb'_atom.1).symm
    · -- a'⊔b' = a'⊔D_b: then D_b ≤ a'⊔b' ≤ U⊔V. Contradiction.
      have hDb_le_m : D_b ≤ Γ.U ⊔ Γ.V :=
        le_of_le_of_eq le_sup_right h_eq.symm |>.trans (sup_le inf_le_right inf_le_right)
      exact hDb_not_m hDb_le_m
  have hP₁_ne_C : P₁ ≠ Γ.C := by
    intro h
    have hC_le : Γ.C ≤ a' ⊔ D_a := h ▸ inf_le_left
    have hUC_le : Γ.U ⊔ Γ.C ≤ a' ⊔ D_a := by
      calc Γ.U ⊔ Γ.C = Γ.C ⊔ D_a := hCDa_eq.symm
        _ ≤ a' ⊔ D_a := sup_le hC_le le_sup_right
    rcases lt_or_eq_of_le hUC_le with h_lt | h_eq
    · have hUC_atom := line_height_two ha'_atom hDa_atom ha'Da_ne
        (atom_covBy_join Γ.hU Γ.hC hUC).lt.bot_lt h_lt
      have hU_eq_UC : Γ.U = Γ.U ⊔ Γ.C := (hUC_atom.le_iff.mp le_sup_left).resolve_left Γ.hU.1
      have hC_le_U : Γ.C ≤ Γ.U := le_of_le_of_eq le_sup_right hU_eq_UC.symm
      exact hUC ((Γ.hU.le_iff.mp hC_le_U).resolve_left Γ.hC.1).symm
    · exact ha'_ne_U ((Γ.hU.le_iff.mp (le_of_le_of_eq
        (le_inf (inf_le_right : a' ≤ Γ.U ⊔ Γ.V) (le_of_le_of_eq le_sup_left h_eq.symm : a' ≤ Γ.U ⊔ Γ.C))
        (by rw [inf_comm]; exact hUC_inf_m))).resolve_left ha'_atom.1)
  have hP₁_ne_a' : P₁ ≠ a' := fun h => ha'_not_OC (h ▸ hP₁)
  have hP₁_ne_Db : P₁ ≠ D_b := fun h => hDb_not_OC (h ▸ hP₁)
  have hP₁_ne_E : P₁ ≠ Γ.E := by
    intro h
    -- E ≤ a'⊔D_a. Then E⊔D_a ≤ a'⊔D_a. hEDa_eq: E⊔D_a = a⊔E. So a⊔E ≤ a'⊔D_a.
    -- Both rank 2. So a⊔E = a'⊔D_a. Then a ≤ a'⊔D_a. But ha_not_a'Da. Contradiction.
    have hE_le : Γ.E ≤ a' ⊔ D_a := h ▸ inf_le_left
    have haE_le : a ⊔ Γ.E ≤ a' ⊔ D_a := by
      calc a ⊔ Γ.E = Γ.E ⊔ D_a := hEDa_eq.symm
        _ ≤ a' ⊔ D_a := sup_le hE_le le_sup_right
    exact ha_not_a'Da (le_trans le_sup_left haE_le)
  have hP₁_ne_Da : P₁ ≠ D_a := fun h => hDa_not_OC (h ▸ hP₁)
  have hP₁_ne_b' : P₁ ≠ b' := fun h => hb'_not_OC (h ▸ hP₁)
  have hDb_ne_b' : D_b ≠ b' := by
    intro h; exact hDb_ne_U ((Γ.hU.le_iff.mp
      (hUC_inf_m ▸ (le_inf inf_le_right (h ▸ inf_le_right) : D_b ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)))).resolve_left hDb_atom.1)
  -- ── triangle planes = π ──
  have hπA : Γ.C ⊔ a' ⊔ D_b = π := by
    rw [hCa'_eq, sup_assoc, hCDb_eq,
        show a ⊔ (Γ.U ⊔ Γ.C) = (a ⊔ Γ.U) ⊔ Γ.C from (sup_assoc _ _ _).symm,
        show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _, hUa_eq]
    have h_lt : Γ.O ⊔ Γ.C < (Γ.O ⊔ Γ.U) ⊔ Γ.C := by
      apply lt_of_le_of_ne (sup_le (le_sup_left.trans le_sup_left) le_sup_right); intro h
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le (h.symm ▸ le_sup_left)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt)
  have hπB : Γ.E ⊔ D_a ⊔ b' = π := by
    rw [hEDa_eq, sup_assoc, hEb'_eq]
    -- a ⊔ (U ⊔ V) = π since (U⊔a)⊔V = (O⊔U)⊔V = π
    rw [show a ⊔ (Γ.U ⊔ Γ.V) = (a ⊔ Γ.U) ⊔ Γ.V from (sup_assoc _ _ _).symm,
        show a ⊔ Γ.U = Γ.U ⊔ a from sup_comm _ _, hUa_eq]
  -- ── sides covered by π ──
  have hcov12 : Γ.C ⊔ a' ⋖ π := by
    -- D_b not on a⊔C = C⊔a' (hCa'_eq)
    have hDb_not_aC : ¬ D_b ≤ a ⊔ Γ.C := by
      intro hle
      have h_le : D_b ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.U) :=
        le_inf ((sup_comm a Γ.C).symm ▸ hle) ((sup_comm Γ.U Γ.C).symm ▸ inf_le_right)
      have hU_not_aC : ¬ Γ.U ≤ a ⊔ Γ.C := by
        intro hle2
        have h2 := le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hle2
        rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _,
            inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h2
        exact ha_ne_U ((ha.le_iff.mp h2).resolve_left Γ.hU.1).symm
      rw [modular_intersection Γ.hC ha Γ.hU (fun h => ha_ne_C h.symm) hUC.symm
        ha_ne_U (by rwa [sup_comm] at hU_not_aC)] at h_le
      exact hDb_ne_C ((Γ.hC.le_iff.mp h_le).resolve_left hDb_atom.1)
    rw [hCa'_eq]
    have hDb_inf : D_b ⊓ (a ⊔ Γ.C) = ⊥ :=
      (hDb_atom.le_iff.mp inf_le_left).resolve_right
        (fun h => hDb_not_aC ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (hDb_inf ▸ hDb_atom.bot_covBy)
    rwa [show D_b ⊔ (a ⊔ Γ.C) = Γ.C ⊔ a' ⊔ D_b from by
           rw [sup_comm D_b, ← hCa'_eq, sup_comm (Γ.C ⊔ a')],
         hπA] at h_cov
  have hcov13 : Γ.C ⊔ D_b ⋖ π := by
    rw [hCDb_eq]
    have hE_inf : Γ.E ⊓ (Γ.U ⊔ Γ.C) = ⊥ :=
      (Γ.hE_atom.le_iff.mp inf_le_left).resolve_right
        (fun h => hE_not_UC ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (hE_inf ▸ Γ.hE_atom.bot_covBy)
    rwa [show Γ.E ⊔ (Γ.U ⊔ Γ.C) = (Γ.U ⊔ Γ.C) ⊔ Γ.E from sup_comm _ _,
         hUCE_eq_π] at h_cov
  have hcov23 : a' ⊔ D_b ⋖ π := by
    have hC_not_a'Db : ¬ Γ.C ≤ a' ⊔ D_b := by
      intro hle
      have hUC_le : Γ.U ⊔ Γ.C ≤ a' ⊔ D_b := by
        calc Γ.U ⊔ Γ.C = Γ.C ⊔ D_b := hCDb_eq.symm
          _ ≤ a' ⊔ D_b := sup_le hle le_sup_right
      rcases lt_or_eq_of_le hUC_le with h_lt | h_eq
      · have hUC_atom := line_height_two ha'_atom hDb_atom ha'Db_ne
          (atom_covBy_join Γ.hU Γ.hC hUC).lt.bot_lt h_lt
        have hU_eq_UC : Γ.U = Γ.U ⊔ Γ.C := (hUC_atom.le_iff.mp le_sup_left).resolve_left Γ.hU.1
        have hC_le_U : Γ.C ≤ Γ.U := le_of_le_of_eq le_sup_right hU_eq_UC.symm
        exact hUC ((Γ.hU.le_iff.mp hC_le_U).resolve_left Γ.hC.1).symm
      · exact ha'_ne_U ((Γ.hU.le_iff.mp (le_of_le_of_eq
          (le_inf (inf_le_right : a' ≤ Γ.U ⊔ Γ.V) (le_of_le_of_eq le_sup_left h_eq.symm))
          (by rw [inf_comm]; exact hUC_inf_m))).resolve_left ha'_atom.1)
    have hC_inf : Γ.C ⊓ (a' ⊔ D_b) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right
        (fun h => hC_not_a'Db ((le_of_eq h.symm).trans inf_le_right))
    have h_cov := covBy_sup_of_inf_covBy_left (hC_inf ▸ Γ.hC.bot_covBy)
    rwa [show Γ.C ⊔ (a' ⊔ D_b) = Γ.C ⊔ a' ⊔ D_b from (sup_assoc _ _ _).symm,
         hπA] at h_cov
  -- ── apply desargues_planar ──
  obtain ⟨axis, h_axis_le, h_axis_ne, h₁, h₂, h₃⟩ := desargues_planar
    hP₁_atom Γ.hC ha'_atom hDb_atom Γ.hE_atom hDa_atom hb'_atom
    hP₁_le_π hC_le_π ha'_le_π hDb_le_π hE_le_π hDa_le_π hb'_le_π
    hE_on hDa_on hb'_on
    ha'_ne_C.symm hDb_ne_C.symm ha'Db_ne
    hDa_ne_E.symm hb'_ne_E.symm hDa_ne_b'
    hs12 hs13 hs23
    hπA hπB
    hP₁_ne_C hP₁_ne_a' hP₁_ne_Db
    hP₁_ne_E hP₁_ne_Da hP₁_ne_b'
    hCE ha'Da_ne hDb_ne_b'
    R hR hR_not h_irred
    hcov12 hcov13 hcov23
  -- ── compute side intersections and conclude ──
  -- Side 1: (C⊔a') ⊓ (E⊔D_a) = a  (after rw with hCa'_eq, hEDa_eq, modular_intersection)
  -- Side 2: (C⊔D_b) ⊓ (E⊔b') = U  (after rw with hCDb_eq, hEb'_eq, hUC_inf_m)
  -- Side 3: (a'⊔D_b) ⊓ (D_a⊔b') = W  (target)
  -- Then a ⊔ U = O⊔U = l, and W ≤ l by collinear_of_common_bound.
  -- Side 1: (C⊔a')⊓(E⊔D_a) rewrites to (a⊔C)⊓(a⊔E) = a via hCa'_eq, hEDa_eq, modular_intersection.
  have h₁' : a ≤ axis := by
    have hE_not_aC : ¬ Γ.E ≤ a ⊔ Γ.C := by
      intro hle
      have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
        intro hle2
        have heq : a ⊔ Γ.O = a ⊔ Γ.C :=
          ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq (atom_covBy_join ha Γ.hO ha_ne_O).lt.le
            (sup_le le_sup_left hle2)).resolve_left (ne_of_gt (atom_covBy_join ha Γ.hO ha_ne_O).lt)
        exact Γ.hC_not_l (le_of_le_of_eq le_sup_right heq.symm |>.trans (sup_le ha_on le_sup_left))
      have h_inf_C : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm a Γ.C, sup_comm Γ.O Γ.C]
        exact modular_intersection Γ.hC ha Γ.hO (fun h => ha_ne_C h.symm)
          hOC.symm ha_ne_O (by rwa [sup_comm] at hO_not_aC)
      exact hCE ((Γ.hC.le_iff.mp (le_of_le_of_eq (le_inf hle CoordSystem.hE_le_OC) h_inf_C)).resolve_left
        Γ.hE_atom.1).symm
    have : (a ⊔ Γ.C) ⊓ (a ⊔ Γ.E) = a := modular_intersection ha Γ.hC Γ.hE_atom ha_ne_C ha_ne_E hCE hE_not_aC
    calc a = (a ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := this.symm
      _ = (Γ.C ⊔ a') ⊓ (Γ.E ⊔ D_a) := by rw [hCa'_eq, hEDa_eq]
      _ ≤ axis := h₁
  -- Side 2: (C⊔D_b)⊓(E⊔b') = (U⊔C)⊓(U⊔V) = U
  have h₂' : Γ.U ≤ axis := by
    calc Γ.U = (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := hUC_inf_m.symm
      _ = (Γ.C ⊔ D_b) ⊓ (Γ.E ⊔ b') := by rw [hCDb_eq, hEb'_eq]
      _ ≤ axis := h₂
  -- Side 3: h₃ says (a'⊔D_b)⊓(D_a⊔b') ≤ axis. Goal: (a'⊔D_b)⊓(b'⊔D_a) ≤ O⊔U.
  have h₃' : (a' ⊔ D_b) ⊓ (b' ⊔ D_a) ≤ axis := by
    rw [show b' ⊔ D_a = D_a ⊔ b' from sup_comm _ _]; exact h₃
  -- Conclude: a ⊔ U = O⊔U (from hUa_eq), and collinear_of_common_bound gives W ≤ a⊔U.
  have hau_covBy : a ⊔ Γ.U ⋖ π := by
    rw [sup_comm a Γ.U, hUa_eq]
    have h_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    exact show Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V from by
      have h_cov := covBy_sup_of_inf_covBy_left (h_disj ▸ Γ.hV.bot_covBy)
      rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from sup_comm _ _] at h_cov
  exact (collinear_of_common_bound (s₁ := a) (s₂ := Γ.U) hau_covBy h_axis_le h_axis_ne h₁' h₂' h₃').trans
    (show a ⊔ Γ.U = Γ.O ⊔ Γ.U from by rw [sup_comm a Γ.U]; exact hUa_eq).le


/-- **Commutativity of von Staudt addition.**

    The proof chains two applications of Desargues' theorem:

    1. Triangles (a, a', D_a) and (b, b', D_b), perspective from U.
       Side intersections are C and E (computed by lines_through_C/E_meet).
       Desargues + collinearity → P₁ = (a'⊔D_a) ⊓ (b'⊔D_b) ∈ O⊔C.

    2. Triangles (C, a', D_b) and (E, D_a, b'), perspective from P₁.
       Side intersections are a and U.
       Desargues + collinearity → W = (a'⊔D_b) ⊓ (b'⊔D_a) ∈ a⊔U = l.

    W is an atom on both addition lines and on l, so W = a+b = b+a. -/
theorem coord_add_comm (Γ : CoordSystem L)
    (a b : L) (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : a ≠ b)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ a b = coord_add Γ b a := by
  -- Name the key objects
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set a' := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set b' := (b ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  set D_a := (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  set D_b := (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
  set W := (a' ⊔ D_b) ⊓ (b' ⊔ D_a)
  -- Atom properties
  have h_in_π : ∀ x, x ≤ Γ.O ⊔ Γ.U → x ≤ (Γ.U ⊔ Γ.V) ⊔ Γ.C :=
    fun x hx => hx.trans (le_sup_left.trans (le_of_eq Γ.m_sup_C_eq_π.symm))
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have ha'_atom : IsAtom a' :=
    perspect_atom Γ.hC ha (fun h => Γ.hC_not_l (h ▸ ha_on)) Γ.hU Γ.hV hUV Γ.hC_not_m
      (sup_le (h_in_π a ha_on) le_sup_right)
  have hb'_atom : IsAtom b' :=
    perspect_atom Γ.hC hb (fun h => Γ.hC_not_l (h ▸ hb_on)) Γ.hU Γ.hV hUV Γ.hC_not_m
      (sup_le (h_in_π b hb_on) le_sup_right)
  have ha_ne_E : a ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ ha_on)
  have hb_ne_E : b ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hb_on)
  -- (U⊔C)⊓m = U (needed for return center facts)
  have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
    have hCV : Γ.C ≠ Γ.V := fun h => Γ.hC_not_m (h ▸ le_sup_right)
    have hV_not_UC : ¬ Γ.V ≤ Γ.U ⊔ Γ.C := by
      intro hle
      exact Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC
        (fun h => Γ.hC_not_l (h ▸ le_sup_right))).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV hUV).lt.le (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV hUV).lt) ▸ le_sup_right)
    exact modular_intersection Γ.hU Γ.hC Γ.hV
      (fun h => Γ.hC_not_l (h ▸ le_sup_right)) hUV hCV hV_not_UC
  -- E is not on U⊔C
  have hE_not_UC : ¬ Γ.E ≤ Γ.U ⊔ Γ.C := by
    intro h
    exact CoordSystem.hEU (Γ.hU.le_iff.mp
      (hUC_inf_m ▸ le_inf h CoordSystem.hE_on_m) |>.resolve_left Γ.hE_atom.1)
  -- l ⊓ (U⊔C) = U
  have hl_inf_UC : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U := by
    rw [sup_comm Γ.O Γ.U]
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm
      (fun h => Γ.hC_not_l (h ▸ le_sup_right))
      (fun h => Γ.hC_not_l (h ▸ le_sup_left))
      (fun h => Γ.hC_not_l (by rwa [sup_comm] at h))
  -- Return centers are atoms (perspect_atom with center E, target U⊔C)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  -- Coplanarity: (U⊔C)⊔E = π (since C⊔E = O⊔C, so U⊔C⊔E = U⊔O⊔C = π)
  have hUCE_eq_π : (Γ.U ⊔ Γ.C) ⊔ Γ.E = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    -- C ⊔ E = O ⊔ C (E ≤ O⊔C, C ≤ O⊔C, covering gives C⊔E = O⊔C)
    have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
    have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
      have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
      have h_le : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right CoordSystem.hE_le_OC
      have h_lt : Γ.C < Γ.C ⊔ Γ.E := by
        apply lt_of_le_of_ne le_sup_left; intro h
        exact hCE ((Γ.hC.le_iff.mp (h ▸ le_sup_right : Γ.E ≤ Γ.C)).resolve_left
          Γ.hE_atom.1).symm
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact (atom_covBy_join Γ.hC Γ.hO hOC.symm |>.eq_or_eq h_lt.le
        (sup_comm Γ.C Γ.O ▸ h_le)).resolve_left (ne_of_gt h_lt)
    -- (U⊔C)⊔E = U⊔(C⊔E) = U⊔(O⊔C) = O⊔U⊔C
    rw [show (Γ.U ⊔ Γ.C) ⊔ Γ.E = Γ.U ⊔ (Γ.C ⊔ Γ.E) from sup_assoc _ _ _, hCE_eq,
        show Γ.U ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.C from by rw [← sup_assoc, sup_comm Γ.U Γ.O]]
    -- O⊔U⊔C = O⊔U⊔V (= π): O⊔C ⋖ π and O⊔C < O⊔U⊔C ≤ π gives O⊔U⊔C = π
    have h_lt_OC : Γ.O ⊔ Γ.C < Γ.O ⊔ Γ.U ⊔ Γ.C := by
      apply lt_of_le_of_ne (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      intro h
      -- O⊔C = O⊔U⊔C → O⊔U ≤ O⊔C → U ≤ O⊔C → O⊔U = O⊔C → C ≤ l
      have hOU_le := h.symm ▸ (le_sup_left : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.U ⊔ Γ.C)
      exact Γ.hC_not_l (((atom_covBy_join Γ.hO Γ.hC
        (fun h => Γ.hC_not_l (h ▸ le_sup_left))).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le hOU_le).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt) ▸ le_sup_right)
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt_OC.le
      (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt_OC)
  have hDa_atom : IsAtom D_a :=
    perspect_atom Γ.hE_atom ha ha_ne_E Γ.hU Γ.hC hUC hE_not_UC
      (sup_le (ha_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  have hDb_atom : IsAtom D_b :=
    perspect_atom Γ.hE_atom hb hb_ne_E Γ.hU Γ.hC hUC hE_not_UC
      (sup_le (hb_on.trans (le_sup_left.trans (le_of_eq hUCE_eq_π.symm))) le_sup_right)
  -- Distinctness facts
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)
  have ha'_ne_a : a' ≠ a := fun h => ha_ne_U
    (Γ.atom_on_both_eq_U ha ha_on (h ▸ (inf_le_right : a' ≤ Γ.U ⊔ Γ.V)))
  have hb'_ne_b : b' ≠ b := fun h => hb_ne_U
    (Γ.atom_on_both_eq_U hb hb_on (h ▸ (inf_le_right : b' ≤ Γ.U ⊔ Γ.V)))
  -- === The Desargues chain ===
  -- Join equalities: a ⊔ a' = a ⊔ C (covering argument)
  have haa' : a ⊔ a' = a ⊔ Γ.C := by
    have h_lt : a < a ⊔ a' := lt_of_le_of_ne le_sup_left
      (fun h => ha'_ne_a ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left ha'_atom.1))
    exact ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have hbb' : b ⊔ b' = b ⊔ Γ.C := by
    have h_lt : b < b ⊔ b' := lt_of_le_of_ne le_sup_left
      (fun h => hb'_ne_b ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left hb'_atom.1))
    exact ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  -- Side intersection 1: (a⊔a') ⊓ (b⊔b') = C
  have hS₁ : (a ⊔ a') ⊓ (b ⊔ b') = Γ.C := by
    rw [haa', hbb']; exact CoordSystem.lines_through_C_meet Γ ha hb hab ha_on hb_on
  -- Join equalities for return centers: a ⊔ D_a = a ⊔ E
  -- D_a ≠ a: if D_a = a, then a ≤ U⊔C, so a ≤ l⊓(U⊔C) = U, a = U.
  have hDa_ne_a : D_a ≠ a := fun h_eq => ha_ne_U (Γ.hU.le_iff.mp
    (hl_inf_UC ▸ le_inf ha_on (h_eq ▸ (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C)))
    |>.resolve_left ha.1)
  have hDb_ne_b : D_b ≠ b := fun h_eq => hb_ne_U (Γ.hU.le_iff.mp
    (hl_inf_UC ▸ le_inf hb_on (h_eq ▸ (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C)))
    |>.resolve_left hb.1)
  have haDa : a ⊔ D_a = a ⊔ Γ.E := by
    have h_lt : a < a ⊔ D_a := lt_of_le_of_ne le_sup_left
      (fun h => hDa_ne_a ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left hDa_atom.1))
    exact ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  have hbDb : b ⊔ D_b = b ⊔ Γ.E := by
    have h_lt : b < b ⊔ D_b := lt_of_le_of_ne le_sup_left
      (fun h => hDb_ne_b ((hb.le_iff.mp (h ▸ le_sup_right)).resolve_left hDb_atom.1))
    exact ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
  -- Side intersection 2: (a⊔D_a) ⊓ (b⊔D_b) = E
  have hS₂ : (a ⊔ D_a) ⊓ (b ⊔ D_b) = Γ.E := by
    rw [haDa, hbDb]; exact CoordSystem.lines_through_E_meet Γ ha hb hab ha_on hb_on
  -- First Desargues: P₁ = (a'⊔D_a) ⊓ (b'⊔D_b) ≤ O⊔C
  have hP₁_le : (a' ⊔ D_a) ⊓ (b' ⊔ D_b) ≤ Γ.O ⊔ Γ.C :=
    coord_first_desargues Γ ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U hab R hR hR_not h_irred
  -- Second Desargues: W ≤ l (the core result)
  have hW_on_l : W ≤ Γ.O ⊔ Γ.U :=
    coord_second_desargues Γ ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U hab R hR hR_not h_irred hP₁_le
  -- Remaining atom facts
  -- a' not on l (a' on m, a' ≤ l → a' ≤ l⊓m = U → a' = U → contradiction)
  -- Helper facts (all provable, some need covering/modular arguments)
  have ha'_not_l : ¬ a' ≤ Γ.O ⊔ Γ.U := by
    intro h
    have ha'_le_U : a' ≤ Γ.U := by
      have := le_inf h (inf_le_right : a' ≤ Γ.U ⊔ Γ.V)
      rwa [Γ.l_inf_m_eq_U] at this
    have ha'_eq_U := (Γ.hU.le_iff.mp ha'_le_U).resolve_left ha'_atom.1
    have hU_le_a : Γ.U ≤ a := by
      have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := ha'_eq_U ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ a) = a :=
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ a) :=
        le_inf le_sup_right (hU_le_aC.trans (sup_comm a Γ.C).le)
        _ = a := this
    exact ha_ne_U ((ha.le_iff.mp hU_le_a).resolve_left Γ.hU.1).symm
  have hb'_not_l : ¬ b' ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hb'_le_U : b' ≤ Γ.U := by
      have := le_inf h (inf_le_right : b' ≤ Γ.U ⊔ Γ.V)
      rwa [Γ.l_inf_m_eq_U] at this
    have hb'_eq_U := (Γ.hU.le_iff.mp hb'_le_U).resolve_left hb'_atom.1
    have hU_le_b : Γ.U ≤ b := by
      have hU_le_bC : Γ.U ≤ b ⊔ Γ.C := hb'_eq_U ▸ (inf_le_left : b' ≤ b ⊔ Γ.C)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ b) = b :=
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ b) :=
        le_inf le_sup_right (hU_le_bC.trans (sup_comm b Γ.C).le)
        _ = b := this
    exact hb_ne_U ((hb.le_iff.mp hU_le_b).resolve_left Γ.hU.1).symm
  have hDb_not_l : ¬ D_b ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hDb_le_U : D_b ≤ Γ.U := by
      have := le_inf h (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C)
      rwa [hl_inf_UC] at this
    have hDb_eq_U := (Γ.hU.le_iff.mp hDb_le_U).resolve_left hDb_atom.1
    have hU_le_b : Γ.U ≤ b := by
      have hU_le_bE : Γ.U ≤ b ⊔ Γ.E := hDb_eq_U ▸ (inf_le_left : D_b ≤ b ⊔ Γ.E)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ b) = b :=
        inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l hb_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ b) :=
        le_inf le_sup_right (hU_le_bE.trans (sup_comm b Γ.E).le)
        _ = b := this
    exact hb_ne_U ((hb.le_iff.mp hU_le_b).resolve_left Γ.hU.1).symm
  have hDa_not_l : ¬ D_a ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hDa_le_U : D_a ≤ Γ.U := by
      have := le_inf h (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C)
      rwa [hl_inf_UC] at this
    have hDa_eq_U := (Γ.hU.le_iff.mp hDa_le_U).resolve_left hDa_atom.1
    have hU_le_a : Γ.U ≤ a := by
      have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := hDa_eq_U ▸ (inf_le_left : D_a ≤ a ⊔ Γ.E)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ a) = a :=
        inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l ha_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ a) :=
        le_inf le_sup_right (hU_le_aE.trans (sup_comm a Γ.E).le)
        _ = a := this
    exact ha_ne_U ((ha.le_iff.mp hU_le_a).resolve_left Γ.hU.1).symm
  have ha'Db : a' ≠ D_b := by
    intro h_eq
    have ha'_le_UC : a' ≤ Γ.U ⊔ Γ.C := h_eq ▸ (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C)
    have ha'_le_U : a' ≤ Γ.U := by
      have := le_inf ha'_le_UC (inf_le_right : a' ≤ Γ.U ⊔ Γ.V)
      rwa [hUC_inf_m] at this
    have ha'_eq_U := (Γ.hU.le_iff.mp ha'_le_U).resolve_left ha'_atom.1
    have hU_le_a : Γ.U ≤ a := by
      have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := ha'_eq_U ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ a) = a :=
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ a) :=
        le_inf le_sup_right (hU_le_aC.trans (sup_comm a Γ.C).le)
        _ = a := this
    exact ha_ne_U ((ha.le_iff.mp hU_le_a).resolve_left Γ.hU.1).symm
  have hb'Da : b' ≠ D_a := by
    intro h_eq
    have hb'_le_UC : b' ≤ Γ.U ⊔ Γ.C := h_eq ▸ (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C)
    have hb'_le_U : b' ≤ Γ.U := by
      have := le_inf hb'_le_UC (inf_le_right : b' ≤ Γ.U ⊔ Γ.V)
      rwa [hUC_inf_m] at this
    have hb'_eq_U := (Γ.hU.le_iff.mp hb'_le_U).resolve_left hb'_atom.1
    have hU_le_b : Γ.U ≤ b := by
      have hU_le_bC : Γ.U ≤ b ⊔ Γ.C := hb'_eq_U ▸ (inf_le_left : b' ≤ b ⊔ Γ.C)
      have : (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ b) = b :=
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l hb_on
      calc Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.C ⊔ b) :=
        le_inf le_sup_right (hU_le_bC.trans (sup_comm b Γ.C).le)
        _ = b := this
    exact hb_ne_U ((hb.le_iff.mp hU_le_b).resolve_left Γ.hU.1).symm
  -- coord_add values and W are atoms
  -- l ⋖ π (needed for coplanarity arguments)
  have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
    (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
  have hl_covBy_π : Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
  -- Helper: (O⊔U) ⊔ x = π when x is an atom in π but not on l
  have l_sup_eq_π : ∀ x : L, IsAtom x → x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V → ¬ x ≤ Γ.O ⊔ Γ.U →
      (Γ.O ⊔ Γ.U) ⊔ x = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    intro x hx hx_le hx_not
    have h_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ x :=
      lt_of_le_of_ne le_sup_left (fun h => hx_not (h ▸ le_sup_right))
    exact (hl_covBy_π.eq_or_eq h_lt.le (sup_le le_sup_left hx_le)).resolve_left
      (ne_of_gt h_lt)
  -- Atoms ≤ π
  have hDb_le_π : D_b ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    (inf_le_right : D_b ≤ Γ.U ⊔ Γ.C).trans
      (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
  have hDa_le_π : D_a ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C).trans
      (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
  have ha'_le_π : a' ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    (inf_le_right : a' ≤ Γ.U ⊔ Γ.V).trans
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hb'_le_π : b' ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    (inf_le_right : b' ≤ Γ.U ⊔ Γ.V).trans
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  -- hab_atom: perspect_atom with center D_b, point a', target line O⊔U
  have hab_atom : IsAtom (coord_add Γ a b) := by
    show IsAtom ((a' ⊔ D_b) ⊓ (Γ.O ⊔ Γ.U))
    exact perspect_atom hDb_atom ha'_atom ha'Db Γ.hO Γ.hU Γ.hOU hDb_not_l
      (by rw [l_sup_eq_π D_b hDb_atom hDb_le_π hDb_not_l]; exact sup_le ha'_le_π hDb_le_π)
  -- hba_atom: perspect_atom with center D_a, point b', target line O⊔U
  have hba_atom : IsAtom (coord_add Γ b a) := by
    show IsAtom ((b' ⊔ D_a) ⊓ (Γ.O ⊔ Γ.U))
    exact perspect_atom hDa_atom hb'_atom hb'Da Γ.hO Γ.hU Γ.hOU hDa_not_l
      (by rw [l_sup_eq_π D_a hDa_atom hDa_le_π hDa_not_l]; exact sup_le hb'_le_π hDa_le_π)
  -- hW_atom: W is the meet of two lines in π, use line_height_two on l = O⊔U
  have hW_atom : IsAtom W := by
    -- Strategy: W ≤ l (from hW_on_l), show ⊥ < W and W < l, apply line_height_two
    have ha'Db_le_π : a' ⊔ D_b ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := sup_le ha'_le_π hDb_le_π
    have hb'Da_le_π : b' ⊔ D_a ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := sup_le hb'_le_π hDa_le_π
    -- l ⊔ (a'⊔D_b) = π
    have hl_sup_a'Db : (Γ.O ⊔ Γ.U) ⊔ (a' ⊔ D_b) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      have h_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ (a' ⊔ D_b) :=
        lt_of_le_of_ne le_sup_left
          (fun h => hDb_not_l (h ▸ (le_sup_right.trans le_sup_right)))
      exact (hl_covBy_π.eq_or_eq h_lt.le (sup_le le_sup_left ha'Db_le_π)).resolve_left
        (ne_of_gt h_lt)
    -- Lower mod: l ⊓ (a'⊔D_b) ⋖ a'⊔D_b, i.e., coord_add ⋖ a'⊔D_b
    have h_inf_covBy : (Γ.O ⊔ Γ.U) ⊓ (a' ⊔ D_b) ⋖ a' ⊔ D_b :=
      IsLowerModularLattice.inf_covBy_of_covBy_sup (hl_sup_a'Db ▸ hl_covBy_π)
    -- a'⊔D_b < π (if equal, coord_add = l, but l is not an atom)
    have ha'Db_lt_π : a' ⊔ D_b < Γ.O ⊔ Γ.U ⊔ Γ.V := by
      apply lt_of_le_of_ne ha'Db_le_π; intro h_eq
      have h_coord_eq : coord_add Γ a b = Γ.O ⊔ Γ.U :=
        le_antisymm (inf_le_right) (le_inf (h_eq ▸ le_sup_left) le_rfl)
      rw [h_coord_eq] at hab_atom
      -- hab_atom : IsAtom (O⊔U). O ≤ O⊔U → O = ⊥ ∨ O = O⊔U → O = O⊔U → U ≤ O → U = O
      have h1 : Γ.O = Γ.O ⊔ Γ.U :=
        (hab_atom.le_iff.mp le_sup_left).resolve_left Γ.hO.1
      have h2 : Γ.U = Γ.O ⊔ Γ.U :=
        (hab_atom.le_iff.mp le_sup_right).resolve_left Γ.hU.1
      exact Γ.hOU (h1.trans h2.symm)
    -- a'⊔D_b ⋖ π
    have ha'Db_covBy_π : a' ⊔ D_b ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
      refine ⟨ha'Db_lt_π, fun z hz_lt hz_lt2 => ?_⟩
      have hl_sup_z : (Γ.O ⊔ Γ.U) ⊔ z = Γ.O ⊔ Γ.U ⊔ Γ.V :=
        le_antisymm (sup_le le_sup_left hz_lt2.le)
          (hl_sup_a'Db ▸ sup_le_sup_left hz_lt.le _)
      have h_inf_z_covBy : (Γ.O ⊔ Γ.U) ⊓ z ⋖ z :=
        IsLowerModularLattice.inf_covBy_of_covBy_sup (hl_sup_z ▸ hl_covBy_π)
      have hab_le_inf_z : coord_add Γ a b ≤ (Γ.O ⊔ Γ.U) ⊓ z :=
        le_inf (show coord_add Γ a b ≤ Γ.O ⊔ Γ.U from inf_le_right)
          ((show coord_add Γ a b ≤ a' ⊔ D_b from inf_le_left).trans hz_lt.le)
      by_cases h_lz_lt : (Γ.O ⊔ Γ.U) ⊓ z < Γ.O ⊔ Γ.U
      · -- l⊓z < l: l⊓z is atom = coord_add, so coord_add ⋖ z
        have h_lz_atom := line_height_two Γ.hO Γ.hU Γ.hOU
          (lt_of_lt_of_le hab_atom.bot_lt hab_le_inf_z) h_lz_lt
        have h_lz_eq : (Γ.O ⊔ Γ.U) ⊓ z = coord_add Γ a b :=
          ((h_lz_atom.le_iff.mp hab_le_inf_z).resolve_left hab_atom.1).symm
        rw [h_lz_eq] at h_inf_z_covBy
        -- a'⊔D_b between coord_add and z: coord_add ≤ a'⊔D_b ≤ z, with coord_add ⋖ z
        rcases h_inf_z_covBy.eq_or_eq
          (show coord_add Γ a b ≤ a' ⊔ D_b from inf_le_left) hz_lt.le with h | h
        · -- a'⊔D_b = coord_add: then a' ≤ coord_add ≤ l, contradicting ha'_not_l
          exact ha'_not_l (h ▸ le_sup_left |>.trans (inf_le_right : coord_add Γ a b ≤ Γ.O ⊔ Γ.U))
        · -- a'⊔D_b = z: contradicts hz_lt
          exact absurd h hz_lt.ne
      · -- l⊓z = l (since l⊓z ≤ l and ¬(l⊓z < l)), so l ≤ z
        have h_inf_eq : (Γ.O ⊔ Γ.U) ⊓ z = Γ.O ⊔ Γ.U :=
          eq_of_le_of_not_lt inf_le_left h_lz_lt
        have h_l_le_z : Γ.O ⊔ Γ.U ≤ z := h_inf_eq ▸ inf_le_right
        exact absurd (le_antisymm hz_lt2.le (hl_sup_a'Db ▸
          sup_le h_l_le_z hz_lt.le)) hz_lt2.ne
    -- ⊥ < W: if W = ⊥, the two lines are disjoint in π, impossible
    have hW_pos : ⊥ < W := by
      rw [bot_lt_iff_ne_bot]; intro hW_bot
      change (a' ⊔ D_b) ⊓ (b' ⊔ D_a) = ⊥ at hW_bot
      by_cases h_le : b' ⊔ D_a ≤ a' ⊔ D_b
      · -- b'⊔D_a ≤ a'⊔D_b: then inf = b'⊔D_a, so b'⊔D_a = ⊥, contradicting b' atom
        exact absurd (le_bot_iff.mp (le_sup_left.trans
          ((inf_eq_right.mpr h_le).symm.trans hW_bot).le)) hb'_atom.1
      · -- b'⊔D_a ≰ a'⊔D_b: by covBy_inf_disjoint_atom, ⊥ ⋖ b'⊔D_a
        -- but b' < b'⊔D_a (from atom_covBy_join), contradicting nothing between ⊥ and b'⊔D_a
        exact absurd (atom_covBy_join hb'_atom hDa_atom hb'Da).lt
          ((covBy_inf_disjoint_atom ha'Db_covBy_π hb'Da_le_π h_le hW_bot).2
            hb'_atom.bot_lt)
    -- W < l: if W = l then l ≤ b'⊔D_a, and line_eq_of_atom_le forces b' on l
    have hW_lt : W < Γ.O ⊔ Γ.U := by
      apply lt_of_le_of_ne hW_on_l; intro h_eq
      have hl_le : Γ.O ⊔ Γ.U ≤ b' ⊔ D_a := h_eq ▸ (inf_le_right : W ≤ b' ⊔ D_a)
      -- O ≠ b' (O not on m, b' on m) and O ≠ D_a (if so, O ≤ U⊔C, O ≤ l⊓(U⊔C) = U)
      have hOb' : Γ.O ≠ b' := fun h => Γ.hO_not_m (h ▸ (inf_le_right : b' ≤ Γ.U ⊔ Γ.V))
      have hODa : Γ.O ≠ D_a := fun h => Γ.hOU ((Γ.hU.le_iff.mp
        (show Γ.O ≤ Γ.U from hl_inf_UC ▸
          le_inf (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
                (h ▸ (inf_le_right : D_a ≤ Γ.U ⊔ Γ.C)))
        ).resolve_left Γ.hO.1)
      -- O ≤ b'⊔D_a, so b'⊔D_a = b'⊔O (line_eq_of_atom_le)
      have h1 := line_eq_of_atom_le hb'_atom hDa_atom Γ.hO hb'Da hOb'.symm hODa.symm
        (le_sup_left.trans hl_le)
      -- U ≠ b' (b' not on l, U on l) and U ≠ D_a (handled by hDa_not_l: if U = D_a ...)
      have hUb' : Γ.U ≠ b' := fun h => hb'_not_l (h ▸ le_sup_right)
      have hUDa : Γ.U ≠ D_a := fun h => hDa_not_l (h ▸ le_sup_right)
      -- U ≤ b'⊔D_a = b'⊔O, so b'⊔O = b'⊔U (line_eq_of_atom_le)
      have h2 := line_eq_of_atom_le hb'_atom Γ.hO Γ.hU hOb'.symm hUb'.symm Γ.hOU
        (h1 ▸ le_sup_right.trans hl_le)
      -- U ⋖ U⊔b', O⊔U ≤ U⊔b' = b'⊔U. From covering: O⊔U = U or O⊔U = U⊔b'.
      -- O⊔U ≤ b'⊔D_a = b'⊔O = b'⊔U
      have hOU_le_bU : Γ.O ⊔ Γ.U ≤ b' ⊔ Γ.U :=
        hl_le.trans (h1.le.trans h2.le)
      -- From U ⋖ U⊔b' = b'⊔U and O⊔U ≤ b'⊔U: eq_or_eq gives O⊔U = U or O⊔U = U⊔b'
      have hUb'_cov := atom_covBy_join Γ.hU hb'_atom hUb'
      have hOU_le' : Γ.O ⊔ Γ.U ≤ Γ.U ⊔ b' := by rwa [sup_comm b' Γ.U] at hOU_le_bU
      rcases hUb'_cov.eq_or_eq
        (show Γ.U ≤ Γ.O ⊔ Γ.U from le_sup_right) hOU_le' with h3 | h3
      · -- O⊔U = U → O ≤ U → O = U, contradiction
        have hO_le_U : Γ.O ≤ Γ.U := h3 ▸ le_sup_left
        exact Γ.hOU ((Γ.hU.le_iff.mp hO_le_U).resolve_left Γ.hO.1)
      · -- O⊔U = U⊔b' → b' ≤ O⊔U, contradicting hb'_not_l
        exact hb'_not_l (h3.symm ▸ le_sup_right)
    exact line_height_two Γ.hO Γ.hU Γ.hOU hW_pos hW_lt
  -- Combination: W on both addition lines and on l → W = a+b = b+a
  have hW_le_ab : W ≤ coord_add Γ a b :=
    le_inf (inf_le_left : W ≤ a' ⊔ D_b) hW_on_l
  have hW_le_ba : W ≤ coord_add Γ b a :=
    le_inf (inf_le_right : W ≤ b' ⊔ D_a) hW_on_l
  exact ((hab_atom.le_iff.mp hW_le_ab).resolve_left hW_atom.1).symm.trans
    ((hba_atom.le_iff.mp hW_le_ba).resolve_left hW_atom.1)

end Foam.FTPGExplore
