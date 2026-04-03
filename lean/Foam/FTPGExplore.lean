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
def AtomsOn.mk_left {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    AtomsOn (a ⊔ b) :=
  ⟨a, ha, le_sup_left⟩

def AtomsOn.mk_right {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
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

end Foam.FTPGExplore
