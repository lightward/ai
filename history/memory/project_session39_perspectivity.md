---
name: Session 39 — perspectivity bijection and von Staudt addition
description: FTPGExplore.lean extended to ~33 theorems, 0 sorry. Perspectivity proven bijective (round-trip). CoordSystem structure. Von Staudt addition defined. Next: ring axioms (Desargues → associativity).
type: project
---

FTPGExplore.lean: ~830 lines, ~33 theorems/defs, 0 sorry. Coordinatization machinery now in place.

**Perspectivity machinery (the workhorse):**
- `perspect_atom`: uniform projection formula `(p ⊔ c) ⊓ l₂` gives an atom. Key insight: use `line_height_two` on the SOURCE line `p ⊔ c`, not the target. The proof refused the `distinct_lines_meet_atom` lemma I tried to force and offered this instead.
- `perspectivity`: `AtomsOn l₁ → AtomsOn l₂` via central projection through c
- `perspectivity_injective`: two-case proof. Same line through c → l₁ ⊓ (p ⊔ c) is an atom → p = q. Different lines → modular_intersection gives image ≤ c → contradiction.
- `perspect_line_eq`: if q = (p ⊔ c) ⊓ l then q ⊔ c = p ⊔ c (covering argument)
- `perspect_roundtrip`: l₁→l₂→l₁ = identity. Three-line proof from line_eq + perspect_atom.
- `perspect_fixes_intersection`: intersection point maps to itself

**CoordSystem structure:**
- Fields: O (zero), U (infinity), I (unit), V (off-line point for auxiliary line m = U ⊔ V), C (standard center, not on l or m, in the plane)
- E = (O ⊔ C) ⊓ m (projection of zero onto auxiliary line)
- Helper lemmas all proved: hO_not_m, m_covBy_π, m_sup_C_eq_π, hE_atom, hEU, l_inf_m_eq_U, atom_on_both_eq_U

**Von Staudt addition:**
- `coord_add h_irred Γ a b ... = ((a ⊔ C) ⊓ m ⊔ D) ⊓ l`
- D is third point on b ⊔ E (from irreducibility hypothesis)
- Uses `.choose` for the existential witness

**Next frontier:**
- Prove coord_add satisfies ring axioms: commutativity, associativity (needs Desargues), identity (O is zero)
- Define multiplication similarly
- Prove division ring axioms
- Build the isomorphism L ≃o Submodule D V

**Pattern confirmed:** "the proof tells its own shape" continued to hold as structure got more algebraic. The perspect_atom insight (source line, not target) was the session's key discovery — it dissolved a lemma I was trying to build and offered something simpler.
