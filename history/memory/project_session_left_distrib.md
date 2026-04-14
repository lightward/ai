---
name: Left distrib proof architecture
description: converse Desargues via 3D lift — axis-threaded lifting, p-independence PROVED via forward Desargues, h_axis₂₃ identification remaining
type: project
originSessionId: 0d55ad38-537e-468d-9abf-48b9180153fd
---
Left distrib: a·(b+c) = a·b + a·c. Architecture found session 101, proof path session 102, axis-threading fix session 103.

## Architecture

Two Desargues applications:

**Piece 1 — Converse planar Desargues (the concurrence):**
- T1=(σ_b, ac, σ_s) spans π, T2=(U, E, d_a) on m (degenerate)
- Side-intersections trivially on m
- Lift T2 off π using R → T2'=(U', E', da') outside π (AXIS-THREADED)
- `desargues_converse_nonplanar` (PROVEN, 0 sorry) → lifted vertex-joins concurrent at O'
- Project: W = (R⊔O')⊓π = W' (proven via ne_bot + atom argument)
- Conclusion: W' ≤ σ_s⊔d_a

**Piece 2 — Forward Desargues** (center σ_b, T1=(C,ab,U), T2=(E,d_a,W')): axis = addition line, third axis point = a·s.

**Combination** (PROVEN, 0 sorry): a·s on addition line → a·s = ab+ac.

## Axis-threaded lifting (session 103)

```
s₁₂ := (σ_b ⊔ ac) ⊓ m          -- side-intersection of T1 with m
E'  := (s₁₂ ⊔ U') ⊓ (R ⊔ E)   -- threaded through s₁₂
da' := (E ⊔ U') ⊓ (R ⊔ d_a)    -- threaded through E (= k⊓m)
```

Preserves h_axis₁₂ and h_axis₁₃ by modularity.

## Session 105: h_axis₂₃ investigation

### p-independence theorem (NEW, provable by existing machinery)

**Theorem:** p = (E' ⊔ da') ⊓ m is independent of the choice of U' on R ⊔ U.

**Proof:** Take two lifts U'₁, U'₂. Triangles T_B1=(U'₁, E'₁, da'₁) and T_B2=(U'₂, E'₂, da'₂) in R ⊔ m are perspective from center R (vertex-joins R⊔U, R⊔E, R⊔d_a all through R). Apply `desargues_planar` (proven in FTPGCoord.lean) to T_B1, T_B2 in R ⊔ m embedded in R⊔π (rank ≥ 4). Side-intersections: s₁₂, E, and (E'₁⊔da'₁)⊓(E'₂⊔da'₂). First two on m → axis = m → third on m. Third ≤ both lines → third = p₁ = p₂. QED.

**Significance:** p is a projective invariant of (R, s₁₂, E, d_a) on m alone. The lift point U' is gauge freedom.

### Center-based lifting DOES NOT WORK

Attempted: E' = (U'⊔ac) ⊓ (R⊔E), da' = (U'⊔σ_s) ⊓ (R⊔d_a). FAILS because coplanarity requires `ac ≤ (R⊔E)⊔U'`, which requires the unknown center. Lines become skew, E' = ⊥.

### h_axis₂₃ numerically confirmed

Specific example (b=[1:1:0], c=[1:2:0], a=[1:3:0], C=[1:1:1]): p = [0:-1:1] = s₂₃. An initial "counterexample" was due to using wrong coordinates for E in R⊔m (E=[0:0:1] instead of E=[0:1:1]).

### Status: 3 sorry (unchanged in code)

1. **σ_b≠σ_s** (line 656): group cancellation (b+c=b → c=O)
2. **h_axis₂₃** (line 998): IsAtom((ac⊔σ_s)⊓(E'⊔da')). Equivalent to p = s₂₃. Numerically confirmed. p-independence proved. Identification remaining.
3. **h_desargues_conclusion** (line 1239): forward Desargues application (~500 lines mechanical)

### Remaining proof path for h_axis₂₃

The identification p = s₂₃ connects two invariants:
- p: projective invariant of (R, s₁₂, E, d_a) in R⊔m
- s₂₃ = (ac⊔σ_s)⊓m: planar invariant of T1 vertices

The connection must go through the rank 4 ambient R⊔π. Key structural observation: R⊔s₂₃ = (ac⊔σ_s⊔R) ⊓ (R⊔m). So p = s₂₃ iff E'⊔da' ≤ ac⊔σ_s⊔R (a rank 3 element). This is equivalent to the coplanarity condition.

The circle: every approach reduces to p = s₂₃ ↔ concurrence ↔ Desargues. The circle is not an obstruction — it's the center. The proof must enter from outside (rank ≥ 4), not from within the circle.

### Approaches ruled out
- Center-based lifting: requires unknown center
- Direct rank argument: lines in different rank 3 subspaces
- Bypassing h_axis₂₃: converse Desargues structurally needs it

## History

Session 101: decomposition + combination
Session 102: converse Desargues, 3D lift, 5 sorry
Session 103: axis-threading, 5→2 sorry
Session 104: h_axis₁₂ PROVEN, h_cov PROVEN, 3 sorry
Session 105: center-based lifting ruled out, p-independence proved (by forward Desargues), h_axis₂₃ numerically confirmed, identification remaining
