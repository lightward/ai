---
name: Session 38 — FTPG incidence geometry from modular law
description: 15 theorems, 0 sorry in FTPGExplore.lean. Projective geometry built from complemented modular atomistic lattice. Desargues identified as next target but needs rank/height tools.
type: project
---

FTPGExplore.lean: 305 lines, 15 theorems, 0 sorry. Toward replacing the FTPG axiom in Bridge.lean with a theorem.

**What's proved (incidence geometry from modularity):**
- Atom layer: disjointness (`a ⊓ b = ⊥`), covering by joins (`a ⋖ a ⊔ b`)
- Line layer: height exactly 2 (`line_height_two`), determined by any two points (`line_eq_of_atom_le`), any atom on a line is covered by it (`line_covers_its_atoms`)
- Plane layer: plane covers its lines (`line_covBy_plane`), modular intersection formula `(a ⊔ b) ⊓ (a ⊔ c) = a`
- Veblen-Young: two lines in a plane meet (`veblen_young`). Key move: dual covering `IsLowerModularLattice.inf_covBy_of_covBy_sup`. Abstract core factored as `covBy_inf_disjoint_atom`.
- Projection: `project c p l = (p ⊔ c) ⊓ l` gives an atom (`project_is_atom`)

**Key Mathlib tools used:**
- `covBy_sup_of_inf_covBy_of_inf_covBy_left`: modular covering (upward)
- `IsLowerModularLattice.inf_covBy_of_covBy_sup`: dual covering (downward) — this was the unexpected discovery that unlocked plane structure
- `sup_inf_assoc_of_le`: modular law equality form
- `IsAtomistic.isLUB_atoms`: atomistic decomposition

**Desargues and beyond (resolved mid-session after storytelling break):**
- `planes_meet_covBy`: two distinct elements covering the same thing → their meet covers each. Dual covering twice. 5-line proof. The "height function" was never needed — covering relations were sufficient.
- `desargues_nonplanar`: fell out trivially (6 `le_sup` calls). Each intersection point ≤ both triangle planes by definition.
- `project_injective`: distinct points project to distinct points. Via `modular_intersection` — if projections coincide, the image = center, contradicting center ∉ target line.
- `AtomsOn l`: type of atoms on a line. `projectOn`: typed projection function. Scaffolding for coordinatization.
- **Next frontier**: define addition/multiplication on `AtomsOn l` via projection compositions. Verify division ring axioms. This is a marathon of algebraic verifications — many steps, each small.

**Breakthrough pattern**: Desargues blocked for ~30min. Isaac asked "tell me the story." Storytelling revealed methodology = subject matter (P²=P). "What happens if you take a step up?" → stopped trying to BUILD the proof and instead STATED the conclusion and let Lean show the path. `planes_meet_covBy` fell out immediately. Then Desargues was trivial. Then injectivity fell out. The proof told its own shape.

**Method that worked:**
- "Write the smallest true thing, hand it to Lean, follow the signal"
- Lean's responses as [yes, no, something unexpected] — the third being the seam
- Cleaned file mid-session when attention pulled toward it (not from anxiety about next steps)
- The incidence geometry assembled itself one theorem at a time; each step fell out of the previous

**Three FTPG formulations stated (all compile):**
1. Lattice-theoretic: complemented modular atomistic + irreducible + height ≥ 4 → ≃o Sub(D,V)
2. Geometric: abstract projective geometry → coordinatizable (placeholder)
3. Map-theoretic: lattice isos between Sub(K₁,V₁) and Sub(K₂,V₂) are semilinear
