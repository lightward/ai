---
name: Session 48 — cross-parallelism proven
description: cross_parallelism PROVEN (0 sorry). key_identity and coord_add_assoc structured (25 sorry in bookkeeping). Proof architecture: circularity → orthogonal individual property → composition.
type: project
---

## Session 48 results

**cross_parallelism** (Part IV-B): FULLY PROVEN, 0 sorry. ~250 lines.
- Statement: a single translation preserves the direction of any line between two points it acts on.
- Proof: one application of small_desargues' with center d = direction atom on m. Plus a degenerate case split (P⊔Q = P'⊔Q' → conclusion trivially true).
- This is the "individual-level property, orthogonal to the circle" that Isaac identified.

**key_identity**: τ_a(C_b) = C_{a+b}. STRUCTURED, ~10 sorry remaining.
- Proof chain: τ_a(C_b) ≤ q (lattice computation) → cross-parallelism gives ((a+b)⊔τ_a(C_b))⊓m = E → τ_a(C_b) ≤ q ⊓ ((a+b)⊔E) = C_{a+b} → both atoms → equal.
- Hard sorry: the cross-parallelism call (needs G off l, m, q + well-definedness rebases).
- All other sorry are atom proofs, on-l proofs, distinctness.

**coord_add_assoc**: 1 sorry. Follows same pattern as key_identity with one more cross-parallelism call.
- Architecture: parallelism from Part III + key_identity + cross-parallelism → atom containment → done.

## Key discoveries

1. **Circularity as launchpad** (Isaac's insight): associativity ↔ translation composition is a circle. The proof goes ORTHOGONAL to the circle — proving that each individual translation preserves structure (cross-parallelism), then deriving composition from individual properties.

2. **The 3-ingredient proof** of coord_add_assoc:
   - Part III parallelism: (C_b ⊔ (b+c)) ⊓ m = e_c (free from existing infrastructure)
   - Key Identity via cross-parallelism: τ_a(C_b) = C_{a+b}
   - Cross-parallelism composition: ((a+(b+c)) ⊔ C_{a+b}) ⊓ m = e_c → containment → done

3. **General-position point G**: needed because base pair (O,a) degenerates for b∈l, and (C,C_a) degenerates for C_b∈q. G off l, m, q exists when plane has ≥5 atoms/line (forced by hypotheses). Construction via h_irred on a⊔C with by_cases on m-membership.

## Sorry inventory (25 total)

- 2 well-definedness rebases (the "hard" bookkeeping — each ~20 hypothesis checks)
- ~15 non-degeneracy for cross_parallelism call (atoms distinct, not on lines, etc.)
- ~5 atom/on-l proofs (s is atom, s on l, etc.)
- 1 G-on-m case (fallback to h_irred on b⊔C)
- 1 coord_add_assoc (follows key_identity pattern)
