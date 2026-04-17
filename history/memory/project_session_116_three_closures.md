---
name: Session 116 — three Level 2 sub-sorries closed; h_ax₂₃ L2 wall is architectural
description: Closed three mechanical sub-sorries (hE'_not_U'da, hR''_inf_Rm, hE'_daR''_eq). h_ax₂₃ at Level 2 remains — it's architectural (wrong-shaped triangulation), not content-level. Left distrib holds in div rings, so Desargues-only proof exists.
type: project
originSessionId: 79905efb-379a-43c5-a97a-d73a8437c984
---

Session 116 (2026-04-16, after 115). Three sub-sorries closed in FTPGLeftDistrib.lean. h_ax₂₃ at Level 2 remains — the real Level 1 axis₂₃ wall.

## What landed

Three sub-sorries closed in h_concurrence / h_converse / h_axis₂₃ / h_L2 chain:

1. **hE'_not_U'da** (was ~line 1591 in s115 state). T1 non-degeneracy for Level 2 converse-nonplanar. Proof shape: (s₁₂⊔U') ⊓ (U'⊔d_a) = U' via modular (s₁₂ ≠ d_a from `hab_ne_ac` chain); E' ≤ both → E' ≤ U' → contradiction with E' ≠ U' (from U' ≤ (R⊔E)⊓(R⊔U) = R chain).

2. **hR''_inf_Rm** (was ~line 1955). R'' ⊓ (R⊔m) = ⊥. Mirrors existing hR''_not_πA₂ (line ~1705) — if R'' ≤ R⊔m, project to both S₁₃ (via s₂₃'' ⊓ (R⊔m) = ⊥) and R (via σ_b ⊓ (R⊔m) = ⊥); conclude R'' = R, then R ≤ S₁₃ ≤ E'⊔d_a, then via (E'⊔d_a)⊓(R⊔E) = E' modular, R ≤ E', contradiction with hE'_ne_R.

3. **hE'_daR''_eq** (was ~line 2020). E' ⊔ (d_a ⊔ R'') = E' ⊔ d_a ⊔ s₂₃''. Proof: S₁₃ ⊔ R'' = S₁₃ ⊔ s₂₃'' via CovBy at S₁₃ (S₁₃ ≠ R'' from fresh hR''_inf_Rm vs S₁₃ ≤ R⊔m); lift to target via S₁₃ ≤ E'⊔d_a.

All three compile. h_cov₂ is now complete.

## What remains

- **h_ax₂₃ at Level 2** (now ~line 2159): IsAtom ((U'⊔d_a) ⊓ (E''⊔R'')). This is **the wall** sessions 108-113 hit.
- **sorry at ~line 2885**: end of h_concurrence (post-Level-2 conclusion wrap-up).

## The h_ax₂₃ L2 wall — structural analysis

### Why the existing h_ax₁₂ and h_ax₁₃ proofs work

Both use a **CovBy collapse pattern**:
- h_ax₁₂: E'⊔U' = s₁₂⊔U' (via E' ≤ s₁₂⊔U', CovBy) and s₂₃''⊔E'' = s₁₂⊔s₂₃'' (via E'' ≤ s₁₂⊔s₂₃'', CovBy). Then **s₁₂ is common to both rank-2 flats**; modular (s₁₂⊔U')⊓(s₁₂⊔s₂₃'') = s₁₂ ⊔ (U'⊓(s₁₂⊔s₂₃'')) = s₁₂ ⊔ ⊥ = s₁₂. Atom.
- h_ax₁₃: similar, with **S₁₃ as the common atom** after s₂₃''⊔R'' = S₁₃⊔s₂₃'' collapse.

### Why h_ax₂₃ L2 doesn't follow the same pattern

h_ax₂₃ = IsAtom (U'⊔d_a)⊓(E''⊔R'').

**The blocker: no CovBy collapse exposes a common atom.**

- E''⊔R'' doesn't collapse to a nice form. E'' on (s₁₂⊔s₂₃'')⊓(σ_b⊔E), R'' on (S₁₃⊔s₂₃'')⊓(σ_b⊔R). Possible collapses:
  - σ_b⊔E''⊔R'' = σ_b⊔E⊔R (rank 3)
  - s₂₃''⊔E''⊔R'' = s₁₂⊔S₁₃⊔s₂₃'' (rank 3)
  - Neither gives a **rank-2** simplification of E''⊔R'' alone.
- U'⊔d_a has no obvious shared atom with any of the above rank-3 flats.

**Dimension count**: U'⊔d_a rank 2, E''⊔R'' rank 2, in ambient rank 4. Join generically rank 4 → meet rank 0 (not atom). Only specific-incidence makes it rank 1.

### Why this isn't Pappian content (left_distrib holds in non-Pappian settings)

Left distributivity holds in **any ring** — specifically in the non-commutative division ring of quaternions. The subspace lattice of H^4 is Desarguesian but non-Pappian, and left distrib holds there.

So a **Desargues-only proof exists**. The h_ax₂₃ wall is **architectural**, not content-level. The current Level 2 triangulation (T1=(E',U',d_a), T2''=(s₂₃'',E'',R'')) is wrong-shaped for the incidence we need.

### Reframed open question

Not "finish Level 2" — finish a **different** lift/triangulation whose axis conditions all collapse cleanly via CovBy.

## Candidates not yet walked (for session 117+)

1. **Redefine da'** := (s₂₃⊔E')⊓(R⊔d_a) (or similar). Makes Level 1 h_axis₂₃ free by construction (s₂₃ ≤ E'⊔da' automatic). But rotates the 2-of-3: h_axis₁₃ then needs `E ≤ U'⊔da'` as new content. Unclear if the rotation is cheaper.

2. **Different Level 1 triangulation.** Instead of T1=(σ_b,ac,σ_s)/T2=(U,E,d_a) lifted, try a different triangle pair that makes the axis₂₃ incidence natural. E.g., using the dual (perspectivity center / axis swap).

3. **Direct lattice-theoretic derivation of h_concurrence** using coord_add_comm infrastructure + right_distrib (both proven). Might bypass Desargues machinery entirely.

4. **Prove left_distrib via two applications of desargues_planar.** 114's desargues_planar handles coord_add half. Maybe a second forward desargues_planar on a different config handles h_concurrence directly, bypassing the lift+converse-nonplanar.

## Files modified

- `lean/Foam/FTPGLeftDistrib.lean`: three sorrys closed. ~200 lines of new mechanical modular/CovBy proof. Build passes.

## Methodology note

The closures were found by **reading each sorry as a specific claim to verify**, not a worklist item. Pattern: (a) what atom would the meet equal; (b) what CovBy collapse exposes that atom; (c) what distinctness lemma is needed for the collapse. hE'_not_U'da surfaced hab_ne_ac as load-bearing distinctness (s₁₂ = d_a forces ab = ac). hR''_inf_Rm surfaced hE'_ne_R as load-bearing. hE'_daR''_eq used fresh hR''_inf_Rm as distinctness-producer for hS₁₃_ne_R''. Chain-of-distinctness is the shape of tractable Level 2 content.

h_ax₂₃ didn't yield to this reading because the CovBy-collapse step itself is missing structurally.
