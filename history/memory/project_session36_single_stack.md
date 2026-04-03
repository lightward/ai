---
name: Session 36 — single Lean stack
description: Foam/ unified from Deductive/ + LeanFoam/. 13 files, 1 axiom (FTPG), 0 sorry. Capstone closed, O(d) gap filled, Bridge axiom stated.
type: project
---

## Session 36: single Lean stack — Foam/

**Major restructuring:** Two Lean directories (Deductive/ + LeanFoam/) unified into one: Foam/. 13 files, 1 axiom (FTPG), 0 sorry.

### New theorems this session

**Ground.lean rewritten as capstone:**
- `subspaceFoamGround`: Sub(K, V) satisfies FoamGround (complemented, modular, bounded) — all Mathlib instances
- `symmetric_quadratic_zero_imp_zero`: polarization for matrices (symmetric + vanishing quadratic form → zero). Proved via Mathlib's `toBilin'Aux` bilinear form.
- `orthogonality_forced`: vᵀMv = 1 for all unit v → M = I. Scales to all vectors, applies polarization to M - I. **This closes the O(d) gap** — the group is forced, not chosen.

**Bridge.lean (new file):**
- `ftpg` (axiom): the fundamental theorem of projective geometry — complemented modular lattice → subspace lattice. The ONE axiom in the formalization.
- `dimension_unique` (theorem): lattice isomorphism preserves dimension. Uses `Module.length_eq_finrank` from Mathlib. The axiom can only be satisfied in one way.

**Migrated from LeanFoam/:**
- Confinement.lean: write confinement to Λ²(P)
- TraceUnique.lean: trace is the unique commutator-killing functional
- Dynamics.lean: frame recession (8 theorems)

### What was dropped
LeanFoam/ removed entirely. Lateral results released to git history:
- Ceiling (Cauchy-Schwarz on N unitaries)
- Three-body mediation/bypass (matrix associativity)
- Dimensional accounting (dim gl(n) = n²)
- J²=-I forces even dim
- so(d) closure under brackets
- Old Ground axiom (feedback_persistence — did zero deductive work)
- Old Lattice.lean (superseded by capstone)
- Old Modularity.lean (rank additivity proof — lateral)

### Key insight: forced vs inherited
Results from the foam fall into two categories:
1. **Forced by P²=P**: the deductive chain (eigenvalues through O(d))
2. **Inherited from the medium**: facts about linear algebra that apply once P²=P selects the setting

Both follow from ground (closure → lattice → FTPG → linear algebra → P²=P). The distinction is Lean-structural: forced results use P²=P as hypothesis; inherited results use Mathlib directly.

P²=P is the intersection point — everything forced descends from it, everything inherited is available at it.

### The full chain
```
axiom(FTPG) → L ≅ Sub(D,V) → D=ℝ → P²=P → chain → FoamGround ✓
```
One axiom. One story. The capstone closes the loop.

### Directory renamed
Deductive/ → Foam/. "Deductive" described the method; "Foam" describes the thing. Lakefile, CI, README all updated. `lake build` succeeds (2319 jobs).

### Commit
`0f996c0` — pushed to main.

### Next
Filter the spec through what the Lean work revealed. The spec may simplify.
