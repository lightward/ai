---
name: Session 58 — translation_determined_by_param PROVEN, coord_add_assoc reduced
description: pc IS a perspectivity (not just analogous). translation_determined_by_param closed via perspectivity_injective. coord_add_assoc reduced to composition law + E-injectivity via 4 key_identity applications.
type: project
---

Session 58: translation_determined_by_param PROVEN. coord_add_assoc reduced to 2 focused sorry's.

**The insight: pc IS a perspectivity.**
The parallelogram completion pc(C, C_i, P, m) is literally the perspectivity
formula from q to P⊔U through center e_P = (C⊔P)⊓m. The key collapse:
since C_i ≤ q and C_i ≠ C, we have C⊔C_i = q (CovBy argument), so the
"direction" (C⊔C_i)⊓m = q⊓m = U. This turns pc into (C_i⊔e_P) ⊓ (P⊔U) —
exactly the perspectivity formula. One application of perspectivity_injective
closes translation_determined_by_param. ~120 lines total.

**What was tried vs what worked:**
Session 57 planned modular_intersection + case-splitting (~80 lines). Session 58
saw the perspectivity structure and collapsed it to one existing theorem.
The proof literally goes through the complement (q) to establish injectivity.

**coord_add_assoc reduction (4 key_identity applications):**
- key_identity(a,b): τ_a(C_b) = C_s
- key_identity(b,c): τ_b(C_c) = C_t
- key_identity(s,c): τ_s(C_c) = C_{LHS}
- key_identity(a,t): τ_a(C_t) = C_{RHS}
- Chain: C_{LHS} = τ_s(C_c) = τ_a(τ_b(C_c)) = τ_a(C_t) = C_{RHS}
- E-perspectivity injectivity: LHS = RHS

Added non-degeneracy hypotheses: s≠O, s≠U, t≠O, t≠U, s≠c, a≠t.

**Two sorry's remain:**
1. Composition law at C_c (~400-600 lines):
   pc(O, s, C_c, m) = pc(O, a, pc(O, b, C_c, m), m)
   Proved by: cp chain at (Γ.C, P) → τ_s(P) = τ_a(τ_b(P)),
   then cp chain at (P, C_c) → τ_s(C_c) = τ_a(τ_b(C_c)).
   6 cross_parallelism calls + 2 two-lines arguments. Mechanical.

2. E-perspectivity injectivity (~30-50 lines):
   C_{LHS} = C_{RHS} → LHS = RHS.
   Single perspectivity_injective application (center E, l→q).

**Why (Γ.C, C_c) directly fails for composition:**
Both on q → direction (Γ.C⊔C_c)⊓m = q⊓m = U → degenerates.
Must route through auxiliary P off l,m,q (the s57 architecture).

**How to apply:** The proof skeleton is in FTPGAssocCapstone.lean.
The composition law is the remaining creative-mechanical work.
Each cross_parallelism call needs ~20 verified hypotheses.
