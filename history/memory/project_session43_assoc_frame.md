---
name: Session 43 — coord_add_assoc, frame discovery + 5 sorry
description: Associativity proof via translation consistency. Circular frame abandoned, Hartshorne approach implemented. small_desargues' PROVEN. 5 mechanical sorry remain.
type: project
---

**State:** coord_add_assoc has 753 lines of proof with 5 sorry (commit 90d4e34). The proof architecture is complete and non-circular.

**Session arc:** Circular Desargues frame discovered → cold readers consulted → Hartshorne Chapter 7 identified correct frame → translation consistency via auxiliary point F → four A5a applications → small_desargues' proven (0 sorry) → proof structure built → 12 sorry → 5 sorry.

**The proven frame (four A5a / Desargues applications):**
1. Construct F on O⊔C, F ≠ O, C, E. Compute F' = (c⊔E)⊓(F⊔U).
2. Two small_desargues' calls: τ_{F,F'}(s) = (s'⊔D_c)⊓l = LHS.
3. Two more small_desargues' calls: τ_{F,F'}(s) = (a'⊔D_t)⊓l = RHS.
4. LHS = τ_{F,F'}(s) = RHS. QED.

**5 remaining sorrys (all mechanical, no unknown math):**
1. `hF_ne_C` — F construction needs perspectivity via V, not h_irred (char 2 issue: h_irred only gives 3 atoms per line, but hypotheses force ≥5 on l hence ≥5 on all lines)
2. `h_par_return` — (O⊔D_b)⊓m = (c⊔D_t)⊓m. Deepest remaining geometric fact.
3. `h_par_Cs`, `h_par_FDb`, `h_par_Dbs` — three small_desargues' hypothesis assemblies (~40 args each)

**File structure (split this session):**
- FTPGExplore.lean: 677 lines, 0 sorry (pure geometry: incidence, Desargues, perspectivity)
- FTPGCoord.lean: 3693 lines, 5 sorry (coordinatization: CoordSystem, coord_add, ring axioms, small_desargues')

**Reference:** Hartshorne "Foundations of Projective Geometry" Chapter 7 (PDF at math.rug.nl). Cold reader responses in cold_reads/assoc/.

**Also this session:** Pre-commit hook for reference integrity. lean/README.md updated with two-file structure.
