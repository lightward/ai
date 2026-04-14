---
name: Left distrib proof architecture
description: converse Desargues via 3D lift — axis-threaded lifting, 2 sorry remaining (h_converse instantiation + forward Desargues)
type: project
originSessionId: 0d55ad38-537e-468d-9abf-48b9180153fd
---
Left distrib: a·(b+c) = a·b + a·c. Architecture found session 101, proof path session 102, axis-threading fix session 103.

## Architecture

Two Desargues applications:

**Piece 1 — Converse planar Desargues (the concurrence):**
- T1=(σ_b, ac, σ_s) spans π, T2=(U, E, d_a) on m (degenerate)
- Side-intersections trivially on m
- Lift T2 off π using R → T2'=(U', E', da') outside π (AXIS-THREADED, see below)
- `desargues_converse_nonplanar` (PROVEN, 0 sorry) → lifted vertex-joins concurrent at O'
- Project: W = (R⊔O')⊓π = W' (proven via ne_bot + atom argument)
- Conclusion: W' ≤ σ_s⊔d_a

**Piece 2 — Forward Desargues** (center σ_b, T1=(C,ab,U), T2=(E,d_a,W')): axis = addition line, third axis point = a·s.

**Combination** (PROVEN, 0 sorry): a·s on addition line → a·s = ab+ac.

## Session 103 (2026-04-14): axis-threaded lifting

**Key structural finding:** Independent lifts (h_irred for E', da') produce skew lines in R⊔π, making O' = ⊥. The lifted vertices must be coupled through the axis.

Fix: define E' and da' through axis points on m:
```
s₁₂ := (σ_b ⊔ ac) ⊓ m          -- side-intersection of T1 with m
E'  := (s₁₂ ⊔ U') ⊓ (R ⊔ E)   -- threaded through s₁₂
da' := (E ⊔ U') ⊓ (R ⊔ d_a)    -- threaded through E (= s₁₃ = k⊓m)
```

This ensures: side-intersections preserved, vertex-joins coplanar in ρ₁₂, O' ≠ ⊥.

## Status: 2 sorry (down from 5)

### Closed (session 103)
1. `hda_atom` — perspect_atom ✓
2. `hW'_atom` — line_height_two ✓
3. `hW_ne_bot` — axis-threaded coplanarity → 4D lines_meet_if_coplanar ✓
4. `hs₁₂_atom, hE'_atom, hda'_atom, hE'_ne_E, hda'_ne_da` — mechanical axis-threading properties ✓

### Remaining
1. **h_converse** (line 606): Instantiate `desargues_converse_nonplanar` with T1=(σ_b,ac,σ_s), T2'=(U',E',da'). ~30 hypotheses. Side-intersection atoms now follow from axis-threading.
2. **h_desargues_conclusion** (line 891): Forward Desargues (~500 lines mechanical). Independent of h_converse.

## History

Session 101: decomposition + combination. h_concurrence labeled "density argument (novel)."
Session 102: h_concurrence = converse Desargues. 3D lift via R. Converse Desargues proven. Projection chain complete. 5 sorry.
Session 103: axis-threading fix (independent→coupled lifts). 5→2 sorry.
