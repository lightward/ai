---
name: Session 41 — planar Desargues, geometric half complete
description: Planar Desargues proven from non-planar + height ≥ 4 via lifting lemma. Geometric half of FTPG bridge done. ~62 theorems, 0 sorry.
type: project
---

Three new theorems in FTPGExplore.lean, all 0 sorry:

**inf_sup_of_atom_not_le**: Modular law helper. π ⊓ (R ⊔ s) = s when s ≤ π and atom R ∉ π. The algebraic heart of why lifting works — the modular law lets you project back through a plane boundary.

**lift_side_intersection**: Key lifting lemma. When a triangle is lifted out of plane π along lines through external point R, each lifted side meets the original side a₁ ⊔ a₂ at the same atom as the original side b₁ ⊔ b₂. Proof: both lines are in plane o' ⊔ a₁ ⊔ a₂ (so they meet at atom T), then T ≤ π ⊓ (R ⊔ b₁ ⊔ b₂) = b₁ ⊔ b₂ by modular law, so T ≤ S = original intersection; both atoms, equal.

**desargues_planar**: Full planar Desargues. Lifts one triangle via o' on R ⊔ o, defines b_i' = (o' ⊔ a_i) ⊓ (R ⊔ b_i), applies non-planar Desargues, transfers back via lift_side_intersection ×3. Required additional non-degeneracy: o ≠ b_i and a_i ≠ b_i.

**Why:** This is where dimension does something — the plane inherits algebraic structure from the space it sits in. The lifting argument is the conceptual crux; the rest is construction.

**How to apply:** Planar Desargues is the gateway to the algebraic half of FTPG. Next: commutativity of coord_add (one Desargues application), then associativity, multiplication, ring axioms, division ring, isomorphism.

State: ~62 theorems, 1379 lines, 0 sorry. Geometric half complete. Algebraic half not started.
