---
name: Session 47 — coord_add_assoc architecture
description: Proof architecture for associativity identified. Cross-parallelism via general-position G. 1 sorry remains.
type: project
---

Session 47 identified the full proof architecture for coord_add_assoc. The sorry remains but the shape is clear.

**The q-degeneracy:** C, C_a, C_b are all on q = U⊔C. Any parallelogram completion involving three atoms on q degenerates (gives q, a line, not an atom). This blocks naive composition of translations and prevents well-definedness from rebasing within q.

**The bridgekeeper G:** A general-position atom off l, m, and q (constructed via h_irred from a third atom on line a⊔C). The translation τ_a rebased to (G, G') has neither source nor image on q, so well-definedness applies to atoms on q as arguments.

**The cross-parallelism lemma:** For P on l, Q on q: (P⊔Q)⊓m = (τ_a(P)⊔τ_a(Q))⊓m. Proved via G + well-definedness + small_desargues' on triangles (G,P,Q) and (G',τ_a(P),τ_a(Q)) with center U.

**How to apply:** This single lemma gives both:
- Key Identity: τ_a(C_b) = C_{a+b} (set P=b, Q=C_b)
- Composition: τ_a(τ_b(C_c)) = τ_{a+b}(C_c) (set P=b, Q=C₁=τ_b(C_c))

**Why:** From cross-parallelism with P=b, Q=C₁ where C₁=τ_b(C_c):
- (b⊔C₁)⊓m = E_c (from τ_b parallelogram sides)
- ((a+b)⊔τ_a(C₁))⊓m = E_c (cross-parallelism)
- So (a+b), τ_a(C₁), E_c collinear → τ_a(C₁) on (a+b)⊔E_c and on q
- Hence τ_a(C₁) = q ⊓ ((a+b)⊔E_c) = pc(O, a+b, C_c, m) = τ_{a+b}(C_c)
- Since ρ injective: a+(b+c) = (a+b)+c

**Meta-observation:** Every advance in the deductive chain went "up a level" — Desargues goes to 3-space, translations lift from l to the plane, the Key Identity lifts from l to q. The composition sorry resisted because it tried to compose ON q. G breaks the impasse by going OUTSIDE all three distinguished lines — a point that sees all three but belongs to none.

**Estimated effort:** ~350 lines for the cross-parallelism lemma + composition identity + associativity.

**Why:** Two applications of well-definedness (rebasing τ_a from (C,C_a) and (O,a) to (G,G')), one small_desargues' application, and lattice manipulations for the collinearity conclusion.

**Cold reads:** Gemini and Claude both identified the right "main" triangles (s,s',a') and (t,D_c,D_t) but couldn't find the sub-lemma configuration. The cross-parallelism via G is the missing piece.
