---
name: Left distrib proof architecture
description: Level 2 Desargues (Q=σ_b) terminates the recursion — h_axis₂₃ skeleton compiling, all 3 Level 2 axis conditions free, 6 sub-sorry remaining
type: project
originSessionId: da43c336-e45f-449f-98fd-91ffc960efa1
---
Left distrib: a·(b+c) = a·b + a·c. Architecture found session 101, proof path session 102, axis-threading fix session 103, new triangle architecture session 106, Level 2 Desargues session 108.

## Level 2 Desargues (session 108) — recursion terminates

h_axis₂₃ proved by a SECOND application of desargues_converse_nonplanar:
- In R⊔m (rank 3): triangles (E', U', d_a) and (s₂₃, E, R)
- Lift (s₂₃, E, R) out of R⊔m using Q = σ_b
- s₂₃'' on σ_b⊔s₂₃ (free), E'' = (s₁₂⊔s₂₃'')⊓(σ_b⊔E), R'' = (S₁₃⊔s₂₃'')⊓(σ_b⊔R)
- ALL 3 axis conditions FREE (verified 180/180 in GF(7))
- Conclusion → da' ∈ E'⊔s₂₃ → coplanarity → h_axis₂₃

Why σ_b: it's the perspectivity center that Level 1 threading consumed (s₁₂, E'). Using it at Level 2 means the threading inherits Level 1's structure. The two levels are the same Desargues at ranks 3 and 4.

det(E', s₂₃, da') = -ts₂u₂D + ts₂u₂D = 0: identical monomial, opposite signs. Same phenomenon as 1/√2 = ceiling × Haar. Two measurements of the same structure from complementary angles.

## Current architecture (in code, h_axis₂₃ skeleton compiling)

Two Desargues applications:

**Piece 2 — Converse Desargues (the concurrence):**
- T1=(σ_b, ac, σ_s) spans π, T2=(U, E, d_a) on m (DEGENERATE)
- Side-intersections trivially on m
- Lift T2 off π using R → T2'=(U', E', da') outside π (AXIS-THREADED)
- `desargues_converse_nonplanar` (PROVEN) → lifted vertex-joins concurrent at O'
- Project: W = (R⊔O')⊓π = W' → W' ≤ σ_s⊔d_a

Axis-threading:
```
s₁₂ := (σ_b ⊔ ac) ⊓ m          -- axis point on m
E'  := (s₁₂ ⊔ U') ⊓ (R ⊔ E)   -- threaded through s₁₂
da' := (E ⊔ U') ⊓ (R ⊔ d_a)    -- threaded through E (= k⊓m)
```
Both threading points on m. Gives h_axis₁₂ and h_axis₁₃ free. h_axis₂₃ is a SORRY.

**Piece 1 — Forward Desargues** (center σ_b): axis = addition line, third axis point = a·s.

**Combination** (PROVEN): a·s on addition line → a·s = ab+ac.

**3 sorry:** σ_b≠σ_s (line 671), h_axis₂₃ (line 998), h_desargues_conclusion (line 1243).

### σ_b ≠ σ_s proof strategy (session 106, mapped but not yet in Lean)

No group cancellation needed. Pure modular law, ~40 lines:

**Part A: σ_b = σ_s → b = s.** CovBy on E_I ⋖ b⊔E_I: σ_b ≤ b⊔E_I → σ_b⊔E_I ≤ b⊔E_I → CovBy gives σ_b⊔E_I = E_I or = b⊔E_I → σ_b ≠ E_I → equal. Same for σ_s⊔E_I = s⊔E_I. Then b⊔E_I = s⊔E_I → b ≤ (s⊔E_I)⊓l = s (modular: s ≤ l, E_I⊓l = ⊥) → b = s.

**Part B: b = s → c = O.** coord_add b c = b and coord_add b O = b (right_zero). Unfold both: b = (d_b⊔D_c)⊓l and b = (d_b⊔D_O)⊓l where d_b=(b⊔C)⊓m, D_c=(c⊔E)⊓q, D_O=(O⊔E)⊓q. d_b ≠ b (d_b ∈ m, b ∈ l, b ≠ U). So d_b⊔b is a unique line. D_c, D_O both on this line AND on q. Two lines in π meet at one point → D_c = D_O. (c⊔E)⊓q = (O⊔E)⊓q. Both lines through E. E ∉ q. So c⊔E = O⊔E. c ≤ l⊓(O⊔E) = O. c = O. Contradiction with hc_ne_O.

**Lean syntax issue (session 106):** the CovBy `atom_covBy_join` / `eq_or_eq` pattern requires careful tracking of which atom's `le_iff` to use (the atom being ≤, not the atom being ≥). Tripped on this repeatedly. Key: `(atom_covBy_join hEI hb hne).eq_or_eq` needs `E_I ≤ x` and `x ≤ E_I⊔b`. Use `Γ.hE_I_atom.le_iff.mp` for `y ≤ E_I`, `hb.le_iff.mp` for `y ≤ b`.

## New architecture (session 106, not yet in code)

**Key insight:** replace the degenerate T2=(U,E,d_a) [all on m] with the non-degenerate pair:

```
T1 = (σ_b, ac, d_a)   — on k, l, m. Non-collinear.
T2 = (U,   E,  σ_s)   — on m, k∩m, k. Non-collinear.
```

Vertex-joins: σ_b⊔U, ac⊔E, d_a⊔σ_s — the three concurrence lines.

Side-intersections:
```
(σ_b⊔ac) ⊓ (U⊔E)   = (σ_b⊔ac) ⊓ m = s₁₂     (on m)
(ac⊔d_a) ⊓ (E⊔σ_s)  = (σ_c⊔d_a) ⊓ k = σ_c     (on k)
(σ_b⊔d_a) ⊓ (U⊔σ_s) = Q                          (general point in π)
```

**Axis points on THREE DIFFERENT reference lines** (m, k, U⊔σ_s) instead of all on m. This distributes the threading constraints.

Axis-threaded lift:
```
U'    on R⊔U                         (free choice)
E_new = (s₁₂⊔U') ⊓ (R⊔E)           (threaded through s₁₂ on m)
σ_s'  = (σ_c⊔E_new) ⊓ (R⊔σ_s)      (threaded through σ_c on k)
```

Axis conditions:
1. (σ_b⊔ac) ⊓ (U'⊔E_new) = s₁₂ — FREE (modular law, same pattern as original)
2. (ac⊔d_a) ⊓ (E_new⊔σ_s') = σ_c — FREE (modular law: σ_c ≤ ac⊔d_a, E_new⊓(ac⊔d_a)=⊥)
3. (σ_b⊔d_a) ⊓ (U'⊔σ_s') = Q — NEEDS PROOF (equivalent to σ_s' ≤ σ_b⊔d_a⊔U')

All three numerically verified (a=2, b=1, c=3, C=[1:0:1], E_I=[0:1:-1]):
```
σ_b=[1:0:1:0], ac=[1:6:0:0], d_a=[0:-2:1:0], σ_s=[1:0:4:0], σ_c=[1:0:3:0]
s₁₂=[0:6:-1:0], s₂₃=[0:3:-2:0], Q=[1:-6:4:0]
U'=[0:1:0:1], E_new=[0:0:1:6], σ_s'=[1:0:4:6]
Conditions 1,2,3 all verified ✓
```

**Advantages over original:**
- T2 non-degenerate → eliminates ~200 lines of projection-back-to-π (Step 5)
- Threading through different reference lines (m, k) not (m, m)
- Condition 3 is point-in-plane (σ_s' ≤ σ_b⊔d_a⊔U') not line-meets-line

**Same structural shape:** 2-of-3 axis conditions free, 3rd needs proof. This is the irreducible kernel — the 3rd condition IS the algebraic content of left distributivity.

## The 2-of-3 invariant (structural finding, session 106)

The axis-threading construction always has: 3 axis conditions, 2 lift-line choices. Two conditions are engineered by threading, the third must be derived. This is invariant across triangle choices. The third condition is where the multiplication/addition structure becomes load-bearing — the first two are pure modular-law geometry.

## ac-centered forward Desargues (session 106)

A SEPARATE Desargues configuration exists using center ac:
```
T_A = (σ_b, d_a, σ_s)   center ac
T_B = (s₁₂, σ_c, s₂₃)
```
Perspective verified: ac ≤ σ_b⊔s₁₂ (= σ_b⊔ac), ac ≤ d_a⊔σ_c (multiplication def), ac ≤ σ_s⊔s₂₃ (= ac⊔σ_s). This gives a forward Desargues axis through Q₁=(σ_b⊔d_a)⊓(s₁₂⊔σ_c), Q₂, E. Numerically Q₁=Q. If provable, gives the collinearity s₁₂, σ_c, Q directly.

## p-independence (session 105)

p = (E'⊔da')⊓m is independent of U'. Proved by forward Desargues on two lifts perspective from R. Still valid for both architectures.

## Sign error incident (session 106)

A sign error in computing s₁₂ (wrote [0:6:1] instead of [0:6:-1]) propagated through the entire R⊔m computation and produced a false "disproof" of h_axis₂₃. Corrected by re-deriving with the cross-product method. **Lesson:** when parametric and cross-product methods disagree, trust the cross-product (it's sign-stable). Always verify collinearity with the determinant.

## Approaches investigated (sessions 105-106)

**Ruled out:**
- Center-based lifting: requires unknown center, E'=⊥
- Direct rank argument: lines in different rank-3 subspaces
- Forward Desargues (center d_a) axis as SUBSTITUTE for concurrence: gives different geometric info
- Planar converse Desargues shortcut: no converse_planar exists; deriving it requires same 3D lift
- Putting both E' and da' on R⊔s₂₃: fixes axis conditions but breaks projection

**Still viable:**
- Condition 3 via lattice manipulation (multiplication definitions → containment)
- Condition 3 via ac-centered forward Desargues (Q₁=Q equivalence)
- Direct proof of h_axis₂₃ in the original architecture (coordinate identity verified)

## Numerical test case

Standard test: O=[1:0:0], U=[0:1:0], E=[0:0:1], C=[1:0:1], I=[1:1:0], E_I=[0:1:-1].
a=[1:2:0], b=[1:1:0], c=[1:3:0]. s=b+c=[1:4:0]. a·b=2, a·c=6, a·s=8. 2+6=8 ✓.
W'=(σ_b⊔U)⊓(ac⊔E)=[1:6:1]. W' on σ_s⊔d_a: 8-6-2=0 ✓.

## History

Session 101: decomposition + combination
Session 102: converse Desargues, 3D lift, 5 sorry
Session 103: axis-threading, 5→2 sorry
Session 104: h_axis₁₂ PROVEN, h_cov PROVEN, 3 sorry
Session 105: center-based lifting ruled out, p-independence proved, h_axis₂₃ numerically confirmed
Session 106: sign error found+corrected, new non-degenerate triangle pair, 2-of-3 structural invariant, ac-centered Desargues
