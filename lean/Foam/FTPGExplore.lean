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

end Foam.FTPGExplore
