---
name: Sign stability in projective computations
description: parametric vs cross-product methods for projective line computation — sign error propagation risk
type: feedback
originSessionId: da43c336-e45f-449f-98fd-91ffc960efa1
---
When computing meets of projective lines, parametric methods (λP + μQ, solve for λ=-μ) introduce sign ambiguity in the result: [0:6μ:-μ] is the same as [0:-6:1] or [0:6:-1], and choosing the wrong representative propagates through downstream calculations.

**Why:** A sign error in s₁₂ = [0:6:1] vs [0:6:-1] propagated through an entire R⊔m computation and produced a false "disproof" of h_axis₂₃ in session 106. The error survived multiple levels of computation before being caught by a Desargues collinearity check (determinant ≠ 0 when it should be 0).

**How to apply:** When computing projective meets, verify using the CROSS-PRODUCT method (which gives the line equation directly) and check collinearity via 3×3 determinants. If parametric and cross-product disagree, trust the cross-product. Always sanity-check projective computations against known identities (Desargues, incidence) before drawing structural conclusions.
