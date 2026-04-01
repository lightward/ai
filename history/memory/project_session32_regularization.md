---
name: Session 32 — regularization, geometry-dependence, generative orthogonality
description: Codebase regularization + three new derived results + Lean to 44 theorems. Directory coherence, CI with bidirectional reference integrity, cold read round (7 readers, stable).
type: project
---

Session 32 (2026-03-31):

**Codebase regularization:**
- TraceUnique.lean capstone: `trace_unique_of_kills_commutators` — any commutator-killing functional = scalar × trace. Required matrix decomposition + Mathlib's `single_apply` condition ordering (`i = a`, not `a = i`).
- Basic.lean split into WriteMap.lean (write form properties) and Algebra.lean (Lie algebra structure).
- lean_foam/ renamed to lean/ — minimal-surprise paths.
- lean/README.md: maps every theorem to spec reference, lists not-yet-formalized with honest infrastructure boundary assessment.
- tests/ created, 22 spec-referenced tests moved. 14 unreferenced tests deleted. CI with bidirectional reference integrity (forward: every reference resolves; reverse: every file referenced).

**Three new derived results:**
1. **Geometry-dependence is forced** (not just observed): frame recession rate ‖[W,P]‖² depends on specific W and P (geometry), not just the write form (architecture). Perturbation dynamics inherit this. No architecture-level theorem can determine whether perturbations grow or shrink. Lean: `frobenius_eq_zero_of_trace_zero` + `frame_recession_strict`.
2. **Map self-knowledge bounded by channel capacity**: the dynamics can't derive connections between dynamical properties (map-internal) and commitment properties (line-side). Forced by the channel capacity argument — the input must be state-independent; that same independence prevents seeing the input's structure. The undecidability is itself derived.
3. **Generative orthogonality**: ordering and conservation are orthogonal not just algebraically (tr([A,B])=0) but generatively — ordering comes from the write cycle's causal orientation (so(d) part, forced), conservation comes from the stacking commitment (cross-terms producing u(1), line-side). Lean: `stacked_write_trace` + `dotProduct_star_conj`.

**Additional Lean results:**
- `exteriorPower_two_rank`: general dim(Λ²(M)) = C(dim(M), 2) — subsumes rank-2/3 cases, gives dim(so(d))
- `exteriorPower_two_of_rank_three`: dim(Λ²(R³)) = 3 (write subspace)
- `commutator_off_diagonal_range` + `commutator_off_diagonal_kernel`: [W,P] is purely off-diagonal in P-decomposition = Grassmannian tangent
- Total: 6 files, 44 theorems/lemmas, 0 sorry

**Lean infrastructure boundary** (probed, honestly assessed):
- Controllability: dimensional accounting done; "generically generates so(d)" needs algebraic geometry
- Haar convergence: probability on compact groups, not algebraically reachable
- Birth indelibility: dynamical systems (unique trajectories), not algebraically reachable
- Remaining results need analysis/probability/algebraic geometry, not matrix algebra. The reformulation approach (finding algebraic statements that avoid analytic machinery) is more promising than waiting for Mathlib infrastructure.

**Cold reads (7 readers, all stable):**
- Convergence: closure→line derivation, write uniqueness, 1/√2, three-body mapping all hold
- Pressure points (all at spec-marked boundaries): coupled controllability, R³+Taylor contingency on Almgren, stacking motivation on line's side, mixing rate unverified
- New session results noticed: geometry-dependence, generative orthogonality, self-knowledge boundedness
- No internal contradictions found

**Search techniques formalized:**
- "Provisional no connection" heuristic: claim no connection, rewind looking for inevitable variation
- "Wrong side of the boundary" correction: "not found inside the map" ≠ "doesn't exist" — check which side of the boundary the question lives on

**Why:** Started as "comb until fully regular." The clean surface revealed new derivations. The combing wasn't just housekeeping — it's what made the algebraic relationships visible.

**How to apply:** CI enforces reference integrity. Lean README tracks what's formalized vs not. The infrastructure boundary (matrix algebra vs analysis/probability) determines what's reachable per session. The search techniques apply to any derivation attempt involving map-internal vs line-side properties.
