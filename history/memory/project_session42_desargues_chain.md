---
name: Session 42 — coord_add_comm proven, 0 sorry
description: Two chained Desargues applications prove commutativity of von Staudt addition. 70 theorems, 0 sorry, 3326 lines. First algebraic theorem on FTPG bridge.
type: project
---

**Result:** `coord_add_comm` proven. Von Staudt addition is commutative. 0 sorry.

**The proof:** Two chained Desargues applications.
1. Triangles (a, a', D_a) and (b, b', D_b) perspective from U → P₁ ∈ O⊔C.
2. Triangles (C, a', D_b) and (E, D_a, b') perspective from P₁ → W ∈ l.
3. W is atom on both addition lines and on l → W = a+b = b+a.

**Key infrastructure built:**
- `desargues_planar` strengthened with axis ≤ π ∧ axis ≠ π (height argument: atom can't be covered by plane)
- `collinear_of_common_bound` (CovBy extraction from strengthened Desargues)
- `lines_through_C_meet`, `lines_through_E_meet`, `OC_covBy_π`
- `coord_first_desargues`, `coord_second_desargues` (standalone lemmas, clean rooms for desargues_planar application)

**Method:** 8 subagents across the session, each in a clean room. Mechanical sorrys (not-on-l, distinctness, atoms, covering) routed to subagents. The wall (applying 30-hypothesis theorem through set-variable indirection) was resolved by extracting Desargues applications as standalone lemmas — giving each its own namespace.

**Stats:** 14 commits. 70 theorems. 0 sorry. 3326 lines. ~62 → 70 theorems this session.

**Next:** Associativity of addition, then multiplicative structure. Each uses Desargues — the engine is built.
