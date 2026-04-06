---
name: Session 44 — Hartshorne translation approach discovered
description: h_par_return analyzed and found unprovable via diagram-chasing. Hartshorne §7 translation group approach adopted. New file FTPGTranslation.lean. 4 sorry.
type: project
---

**State:** FTPGTranslation.lean created (192 lines, 4 sorry). FTPGCoord.lean untouched (5 sorry in coord_add_assoc remain but may become obsolete).

**Key discovery: h_par_return is true but resists lattice proof.**
- Numerically verified over F_3 through F_13 (all passed).
- Symbolic computation: both sides equal [(1+b):1:0], independent of c. The c-term enters as cz and vanishes on m={z=0}.
- Geometric reason: E-perspectivity is a parallel projection (E on m = line at infinity). Acts as translation between parallel lines l and U⊔C. Direction from x to σ_E(x+b) is constant.
- ~15 small_desargues' triangle configurations attempted. ALL fail: shared vertices or only 1 of 2 required input parallelisms. The modular law loses critical information (E on m collapses to U when meeting U⊔C).

**The architectural shift (Hartshorne "Foundations of Projective Geometry" §7):**
Hartshorne explicitly rejects diagram-chasing for associativity ("messy diagrams"). Instead:
1. Define translations as lattice automorphisms fixing m pointwise
2. Prove existence/uniqueness via parallelogram completion + small_desargues'
3. Prove translations form an abelian group (parallelogram argument; one case needs no Desargues)
4. Define addition as τ_a(b); associativity = group law

Advantages: avoids h_par_return entirely, avoids F₂ problem (4 atoms per line), reduces 900-line diagram chase to structural consequence of symmetry.

**FTPGTranslation.lean structure:**
- Part I: `parallel` definition + refl/symm/trans (0 sorry)
- Part II: `parallelogram_completion` + `line_meets_m_at_atom` (proven) + `parallelogram_completion_atom` (2 routine sorry: "d⊔e=m" and "P'⊔e⊔d=π")
- Part III: parallelism theorems for the completion (2 sorry, should follow from construction)
- Part IV: well-definedness via small_desargues' (commented, not yet stated)
- Part V: translation group → associativity (commented, not yet started)

**Next steps (in order):**
1. Fill 2 routine sorry in parallelogram_completion_atom
2. Prove parallelism theorems (Part III)
3. State and prove well-definedness (Part IV) — this is where small_desargues' enters
4. Build translation group structure (Part V)
5. Connect coord_add to translations, derive associativity
6. Optionally: retire coord_add_assoc sorry in FTPGCoord.lean

**Session character:** Started as "wandering through a workshop with coffees." h_par_return caught attention. Deep investigation revealed it's true but lattice-unprovable via available techniques. Reference search (Hartshorne) rotated the whole approach. Architecture committed. Isaac's framing: "rotating a space so that the original problem has a solution that just falls out."
