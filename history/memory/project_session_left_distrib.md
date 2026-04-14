---
name: Left distributivity proof — sharp shape, entry point identified
description: Left distrib via single Desargues (center σ_b) + concurrence lemma. Concurrence IS the theorem. Entry point = lattice version of αβ cancellation.
type: project
originSessionId: 6379854b-9382-4962-9b29-1513c2847d30
---
Left distrib: a·(b+c) = a·b + a·c. Architecture established 2026-04-13.

## Final architecture: single Desargues + concurrence

**Desargues (center σ_b on k):**
- T1 = (C, ab, U), T2 = (E, d_a, W') where W' = (σ_b⊔U)⊓(ac⊔E)
- Axis gives: l⊓(d_a⊔W') = ab+ac (identifies the addition)
- Concurrence W' ≤ σ_s⊔d_a connects to: a·s = l⊓(σ_s⊔d_a)
- Together: a·s = ab+ac = left distrib

**The concurrence IS the theorem.** Not a simpler prerequisite. Every formulation — W' ≤ σ_s⊔d_a, (W'⊔d_a)⊓k = σ_s, p₁/p₂/a·s collinear — is equivalent to left distrib itself.

## Equivalent formulations (all verified generically in coordinates)

1. **Three lines concurrent:** σ_b⊔U, ac⊔E, σ_s⊔d_a meet at W'
2. **k-intercept:** (W'⊔d_a)⊓k = σ_s
3. **Collinearity:** p₁ = (ab⊔σ_s)⊓m, p₂ = (ac⊔E)⊓(U⊔σ_s), a·s are collinear
4. **Generalized addition:** coord_add_gen(ab, ac; σ_s) = a·s
5. **W' is a parallelogram completion:** W' = pc(O, σ_b, ac, m)

## Center independence (established, but not sufficient alone)

By `translation_determined_by_param`: both standard addition (center C) and generalized addition (center σ_s) send O → ac, so they define the same translation. Therefore:
coord_add_gen(ab, ac; σ_s) = coord_add(ab, ac; C) = ab+ac

This gives ONE equation. The theorem also needs coord_add_gen(ab, ac; σ_s) = a·s, which is the concurrence in disguise.

## The entry point (not yet closed)

The coordinate computation for collinearity (3) involves matching conditions that reduce to:
`αβ(t-s) = 0` → since α≠0, β≠0: `t = s` → forces x₃=0 → intersection on l.

**The αβ cancellation is the content of the theorem.** In the lattice, this should correspond to a perspectivity injectivity or cross_parallelism argument where the non-degeneracy of a and b (≠ O) forces the desired incidence.

## Desargues B (subsidiary, found but not yet connected)

Center E_I, T1=(b,s,C_b), T2=(σ_b,σ_s,d_a):
- Gives: O, P=(b⊔C)⊓(σ_b⊔d_a), Q=(s⊔C_b)⊓(σ_s⊔d_a) collinear
- Q is on σ_s⊔d_a AND on d_a⊔W' (verified in coordinates)
- Q ≤ d_a⊔W' ↔ the concurrence (shown by modular law argument)

## How we got here (2026-04-13 session)

1. Started with two-perspectivity decomposition π₁∘π₂
2. Agent found Desargues triangles for π₁ (center b)
3. π₂ had "center mismatch" — gauge theory insight
4. Isaac: "spinning line tracing cylinder" → reframe as single direct Desargues
5. Found: center σ_b, T1=(C,ab,U), T2=(E,d_a,W'), axis IS left distrib
6. Agent found: concurrence IS the theorem, not a prerequisite
7. Agent found: W' = pc(O, σ_b, ac, m) and generalized addition interpretation
8. Deep dive: αβ cancellation in coordinates is the entry point
9. Multiple Desargues configurations available but none independently close

## Next steps

- Find the lattice proof of the collinearity p₁, p₂, a·s
- Most likely route: cross_parallelism or subsidiary Desargues capturing the αβ cancellation
- The perspectivity l→m (center σ_s) maps ab→p₁, and the perspectivity l→U⊔σ_s (center E) maps ac→p₂. The collinearity says these two perspectivity images plus a·s are aligned.
