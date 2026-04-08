---
name: Session 55 — hwd1 closed, G-on-m restructured
description: 3→2 sorry (hwd1 via cross_parallelism + CovBy, G-on-m via suffices + G₂ construction). Key patterns for set abbreviation handling.
type: project
---

Session 55: 3→2 sorry in FTPGAssoc.lean (key_identity + coord_add_assoc).

**Closed:**
- `hwd1` (collinear well-definedness): cross_parallelism(O,a,G,C) gives
  (G⊔C)⊓m = (G'⊔C_a)⊓m. Both pc(G,G',b,m) and s = pc(C,C_a,b,m)
  unfold to l ⊓ (X ⊔ e); CovBy collapse gives G'⊔e = C_a⊔e. ~120 lines.

**Restructured:**
- G-on-m case: `suffices` abstracts the cross_parallelism proof over any
  off-m atom on b⊔C. When h_irred's G lands on m, use G₂ = (a⊔E)⊓(b⊔C)
  (intersection of lines a⊔E and b⊔C in π). 4 sorry remain for G₂
  properties (atom, ≠b, ≠C, ∉m) — proof strategies documented in comments.

**Remaining sorry:** 4 in G₂ construction (routine lattice), 1 in coord_add_assoc.

**Key discovery:** When b⊔C has only 3 atoms {b, C, (b⊔C)⊓m}, this is
impossible because l has ≥4 atoms (O, U, a, b from hypotheses), implying
|F|≥3, hence all lines have ≥4 atoms. The G₂ = (a⊔E)⊓(b⊔C) construction
sidesteps h_irred entirely — it's a direct lattice construction via line
intersection, guaranteed to produce a fourth atom off m.

**Infrastructure patterns:**
- `.trans hOa_eq_l.le` instead of `hOa_eq_l ▸` for set abbreviation boundaries
- `show _ ≤ Γ.E from inf_le_left` to bridge (Γ.O ⊔ Γ.C) ⊓ m vs Γ.E
- `le_inf` to combine G₂ ≤ b⊔C with G₂ ≤ l/q, then `rw` on the inf
- `sup_inf_assoc_of_le` + atom disjointness for modular collapses

**Why:** The G-on-m obstruction was structural, not mechanical: in PG(2,2),
all atoms in π land on l∪m∪q, blocking any off-m center. But PG(2,2) is
excluded by the hypotheses (a ≠ b, both ≠ O, ≠ U on l forces |l| ≥ 4).
Isaac's heuristic "prove existence of a resolving position" pointed directly
at the suffices abstraction.
