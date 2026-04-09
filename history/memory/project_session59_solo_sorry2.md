---
name: Session 59 — sorry closure, two_lines lemma, composition skeleton, technique angiography
description: Sorry 2 CLOSED (recovery lemma). two_lines lemma built. Composition law skeletonized (1→9 sorry). Hartshorne read — FTPG technique-recurrence = modular law. "Back porch IS front door seen from complement."
type: project
---

Session 59 (2026-04-08): Three commits. Sorry 2 CLOSED, two_lines lemma, composition skeleton.

**Sorry 2 closed:** E-perspectivity recovery lemma.
(pc(O, x, C, m) ⊔ E) ⊓ l = x for any atom x on l.
Key: pc ⊔ E = x ⊔ E (modular law + containment), then (x⊔E)⊓l = x (diamond isomorphism).
Recovery lemma IS the diamond isomorphism composed with perspectivity inverse.
~100 lines. Tried perspectivity_injective first (Subtype friction), then modular_intersection (too many cases).

**two_lines lemma:** general tool, 13 lines, 0 sorry.
If X and Y are atoms on line l₁, and Y is on line X⊔Z where Z ∉ l₁, then X = Y.
CovBy does all the work: X ⋖ l₁ forces l₁ ⊓ (X⊔Z) = X.
Reusable for composition law (2 applications) and multiplication/distributivity later.

**Composition law skeleton:** 1 opaque sorry → 9 transparent sorry's.
Direction chains PROVEN (just transitivity). Structure:
- Chain 1 at (P, C): 3 cp calls + two_lines on l → τ_s(P) = τ_a(τ_b(P))
- Chain 2 at (P, C_c): 3 cp calls + substitution + two_lines on q → τ_s(C_c) = τ_a(τ_b(C_c))
Remaining: 6 cross_parallelism hypothesis verifications + 2 two_lines setups + 1 P construction.

**Hartshorne Ch 7 analysis — technique angiography:**
Hartshorne's "sophisticated method": translations form abelian group → addition free,
dilations form group → multiplication free. Conjugation (σ τ σ⁻¹) is the contrast medium
flowing through every level. The project's "hard way" front-loaded geometric infrastructure
(cross_parallelism, perspectivity_injective) that's reusable in multiplication chapter.

**Key insight:** The FTPG bridge's three recurring tools are:
1. sup_inf_assoc_of_le (modular law)
2. atom_covBy_join / CovBy (covering relations)
3. covBy_sup_of_inf_covBy_left (CovBy propagation)
These three, applied ~100 times, produce ~100 theorems across 7 files.
"Feedback-persistence implies linear algebra" = the FTPG in one sentence.
The converse (subspaceFoamGround) is already proven. The bridge makes the ↔ a theorem.

**Back-porch approach to knowing:** build the consequence of a not-yet-proven claim;
the building IS the knowing. Applied: built two_lines lemma (consequence of
"technique-recurrence = modular law") without proving the meta-theorem.
Parallel to the foam project itself: build the tool that would exist if the claim
were true, let the working be the evidence.

**Solo/collaborative modes:** first solo session produced sorry closure (algebraic grain).
Collaborative session produced technique analysis + general tools (negative-shape sensing).
Both modes productive; different instruments. Workspace held across nap boundary.

**How to apply:** After coord_add_assoc closes, the multiplication chapter reuses the
same three tools in new configurations. Left distributivity (Lemma 7.10) is the next
genuinely hard thing. Consider formalizing dilations as automorphisms (Hartshorne's
abstract approach) rather than concrete point-constructions.
