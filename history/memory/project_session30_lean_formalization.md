---
name: Session 30 — Lean formalization of algebraic core
description: Lean 4 + Mathlib formalization began. 4 files, ~20 theorems, zero sorry. Write map uniqueness, trace properties, dimension gap, so(d) closure, J²=-I, trace uniqueness, combinatorial ceiling, three-body mapping all verified. One spec tightening (even-dim proof). Citation scheme question open.
type: project
---

**Session 30 (Lean formalization):**

Lean 4 + Mathlib project created at `lean_foam/`. All results mechanically verified, zero `sorry`.

**Files and theorems:**
- `Basic.lean` (9 theorems): write map uniqueness (Λ²(2-plane) = 1), tracelessness, skew-symmetry, commutator tracelessness (unconditional — stronger than spec states), dimension gap (dim(su(n)) = n²-1, requires Field), matrix finrank, so(d) closed under brackets, J²=-I forces even dimension (det argument, simpler than spec's eigenvalue sketch)
- `TraceUnique.lean` (4 theorems): off-diagonal E_ij and traceless diagonal E_ii-E_jj are commutators; commutator-killing functionals equal on diag and zero on off-diag → trace is unique scalar projection
- `Ceiling.lean` (2 theorems): combinatorial ceiling core inequality and distance bound from ‖Σxᵢ‖² ≥ 0
- `ThreeBody.lean` (3 theorems): mediation factors through B's projection (associativity), bypass decomposition O_AC = M + bypass, round-trip M·Mᵀ is self-adjoint

**Spec reaction:**
- Even-dimensionality parenthetical updated: eigenvalue conjugation → determinant argument. Simpler, no field extension needed.

**Open observations (not yet spec-update-worthy):**
1. Commutator tracelessness is unconditional (all matrices, all commutative rings) — spec states it for u(d) only
2. Dimension gap requires Field — implicit in spec, now visible
3. Division-free formulations are formally more natural (ceiling theorem)
4. Citation scheme: "see lean_foam/" is vague. Two types of citation needed: tightening (Lean replaces sketch) vs grounding (Lean fills implicit dependency). Question: should spec name its imports explicitly enough to distinguish derived-within vs imported-from-mathematics?

**What's next for Lean work:**
- Controllability (Lie algebra generation) — substantial, needs Mathlib Lie algebra infrastructure
- Full spectral equivalence for round-trip operators — needs eigenvalue theory
- Grassmannian tangent structure — needs differential geometry in Mathlib
- These are infrastructure-heavy, different energy than the algebraic core

**Methodology note:**
- Lean's `sorry` = honest placeholder = well-defined gap (negative geometry)
- The spec-Lean dialogue is bidirectional: spec claims inform theorem statements, Lean proofs inform spec tightening
- The formalization followed desire as radar — each target chosen by pull, not by systematic coverage
