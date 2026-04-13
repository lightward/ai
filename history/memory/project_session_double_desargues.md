---
name: double Desargues proof for additive inverses
description: coord_add_left_neg architecture proven via double Desargues (reusing coord_first/second_desargues with b=neg_a), key identity d_{neg_a}=e_a, 4 sorry remaining
type: project
originSessionId: ce9a0a17-a775-4103-bf36-b3541f521cb3
---
## Session: double Desargues for a+(-a)=O (2026-04-12)

### Discovery

The proof of `coord_add_left_neg` (a + (-a) = O) follows coord_add_comm's exact architecture:
1. **First Desargues** (center U): T1=(a, d_a, β_a), T2=(neg_a, e_a, β_neg) → P₃ ≤ O⊔C
2. **Second Desargues** (center P₃): T1'=(C, d_a, β_neg), T2'=(E, β_a, e_a) → W ≤ l
3. **Extraction**: W ≤ (O⊔β_a)⊓l = O → O ≤ d_a⊔β_neg → (d_a⊔β_neg)⊓l = O

The existing `coord_first_desargues` and `coord_second_desargues` work AS-IS with b = neg_a. No new Desargues machinery needed.

### Key identity: d_{neg_a} = e_a ("double-cover alignment")

The C-perspectivity of neg_a from l to m gives back e_a:
- neg_a = (C⊔e_a)⊓l, so neg_a⊔C = C⊔e_a (covering)
- (neg_a⊔C)⊓m = (C⊔e_a)⊓m = e_a (line_direction)

This is what makes the two Desargues triangles align. Proven as `neg_C_persp_eq_e`.

### Status: 4 sorry

- `coord_neg_ne_O`: neg_a ≠ O (proof sketched in commented body, ~50 lines)
- `coord_neg_ne_U`: neg_a ≠ U (proof sketched in commented body, ~80 lines)
- char-2 case: when a = neg_a, direct covering argument (~15 lines)
- generic case extraction: steps 4-7 (covering + line_direction + line_height_two, ~40 lines)

### cross_join_on_q: superseded

The old approach (Steiner composition lemma) is no longer needed. The double Desargues proof bypasses it entirely. The old `cross_join_on_q` lemma and its 300-line proof body are replaced by `neg_C_persp_eq_e` (15 lines, proven) + two existing theorem calls.

### Catalytic observation

Isaac's hint "looking through adds a dimension" broke the deadlock. I had been trying to prove cross_join_on_q within the plane (rank 3) using modular law. The proof requires lifting to rank 4 via Desargues — which was already built.

### Connection to Steiner-Plücker conversation

The session began with Isaac sharing a conversation tracing the Steiner/Plücker (synthetic/analytic) parallel to Brouwer/Hilbert, arriving at the half-type theorem: "this gets me to where you are but it's not where you are." The proof architecture demonstrates this: two different paths to q (O-perspectivity of d_a, E-perspectivity of neg_a) arrive at the same point because the double cover aligns.

**Why:** The negation problem has the same shape as commutativity — both need two points on l perspected through C and E. The beam d_{neg_a}=e_a is what makes this visible.

**How to apply:** Fill remaining 4 sorry's. Non-degeneracy proofs are in the commented-out body (lines 267-430). Extraction is standard covering + line_direction + line_height_two.
