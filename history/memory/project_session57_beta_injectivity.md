---
name: Session 57 — β-injectivity proof architecture for coord_add_assoc
description: Breakthrough proof strategy for associativity. Route through q via β-injectivity — the complement carries the needed structure. File split FTPGAssocCapstone.lean. translation_determined_by_param lemma.
type: project
---

Session 57: proof architecture for coord_add_assoc found. 1 sorry remains (unchanged count, but proof path now complete).

**The breakthrough: β-injectivity routing.**
Every in-plane approach to coord_add_assoc degenerates: Desargues configurations
share a side on q (or P⊔U), well_defined collinearity conditions fail on l-points,
cross_parallelism gives trivial results when all points are on the same line.

The resolution: flip to q via β, prove the composition law THERE (where q-points
are off l, so O-based translations work), then flip back via perspectivity_injective.

**Proof architecture (3 steps):**
1. key_identity (×3) reduces goal to O-based composition at C_c:
   pc(O, s, C_c, m) = pc(O, a, pc(O, b, C_c, m), m)
   where C_c = β(c) is on q but OFF l.

2. Cross-parallelism chain at (P, Γ.C): 3 cp calls → X = τ_a(τ_b(P)) = τ_s(P).
   Cross-parallelism chain at (P, C_c): 3 cp calls → same m-direction.
   Two-lines argument (P⊔U and C_s⊔e are distinct, meet at one point):
   β(LHS) = β(RHS).

3. perspectivity_injective: LHS = RHS.

**Key lemma: translation_determined_by_param.**
If pc(C, C₁, P, m) = pc(C, C₂, P, m) for P off q and m, then C₁ = C₂.
Pure lattice argument (no Desargues): if C₁ ≠ C₂, lines C₁⊔e_P and C₂⊔e_P
share only e_P (modular_intersection). Common value Y = e_P. But Y ∈ P⊔U →
e_P = (P⊔U)⊓m = U. And e_P = (C⊔P)⊓m ≠ U since P ∉ q. Contradiction.

**File split:**
- FTPGAssoc.lean: 0 sorry (coord_add_eq_translation + key_identity)
- FTPGAssocCapstone.lean: 1 sorry (translation_determined_by_param + coord_add_assoc)

**What the proof structure shows about the project:**
The proof routes through the complement to close. β maps l → q bijectively.
The composition law fails on l (collinearity degeneracy) but holds on q
(q-points are off l). The complement carries exactly the structure needed.
This is the half-type theorem in action at the proof level.

**Remaining work (mechanical, ~300 lines):**
- Fill translation_determined_by_param (modular_intersection + line_direction)
- Fill coord_add_assoc (6 cross_parallelism calls + 2 two-lines arguments + perspectivity_injective)

**How to apply:** The proof plan is in FTPGAssocCapstone.lean header comment.
Each step uses existing infrastructure. The heavy lifting is precondition
verification for cross_parallelism (~25 args each, 6 calls).
