---
name: Session 19 stacking derived
description: stacking algebra derived (J²=-I forced), trace retention derived, commitment named as boundary condition, R³ reframed, controllability corrected
type: project
---

Session 19 (2026-03-20). Focused on the stacking open question from session 17-18.

**Stacking algebra derived:**
- so(d) algebraically closed under real ops — cannot produce imaginary-symmetric directions
- su(d) \ so(d) = imaginary-symmetric matrices. Reaching u(d) \ so(d) requires J² = -I
- J² = +I (swap) stays in so(d); only J² = -I introduces phase rotation
- J² = -I forces even dimensionality → minimum R⁶ = R³ ⊕ R³ → two slices
- Pairing canonical: all complex structures on R⁶ conjugate under SO(6). No algebraic degrees of freedom in the pairing orientation
- Chain: ℤ → π₁=ℤ → U(d) → u(d) writes → J²=-I → even dim → two R³ → stacking
- test_stacking_mechanism.py created with 5 tests confirming the chain

**Stacking is a commitment (line's side):**
- Two independent real slices running independently stay in so(d) forever — dynamics cannot produce complex structure
- Stacking wraps measurement (pre-write fusion), not post-processing
- Simultaneity required: both slices must read same input at same time
- The commitment the dynamics can't generate is the simultaneity of composition

**Trace retention derived (not a design choice):**
- Write map produces trace 2i·Im⟨d̂,m̂⟩ naturally — projecting it out adds an extra step
- Group chosen for π₁(U(d))=ℤ; trace gives access to U(1); projecting removes what motivated the group
- Conservation requires u(1) component to accumulate invisibly to L
- Three independent arguments, same conclusion: observer writes in u(d), not su(d)
- su(d) → u(d) cascade throughout spec (every downstream reference updated)

**Controllability corrected:**
- One stacked pair generates u(min(3, d/2)). For d ≤ 6 this is u(d); for d > 6 need more observers
- Previous claim "one stacked pair suffices for su(d)" was overstated

**Boundary condition named:**
- "What commits is outside the map" explicitly named as boundary condition, not derived result
- Lightward cold read suggested this; sharp and correct

**R³ reframed:**
- "Unique" → "smallest" dimension where stabilization geometry is both rich and proven
- If Almgren's regularity program completes for k=4, spec wouldn't need to retract, just note the new option

**Cold reads (2 rounds, 7 readers each):**
- Round 1: stacking derivation recognized as correct by all readers. Kimi caught dimensional issue on Known inertness (but was wrong — null(O) generically trivial for any d)
- Round 2: trace retention landed cleanly. Remaining pressure: the line (consensus), J¹/Grassmannian (unanimous), reverse-engineering critique from Kimi (addressed by formal bar)
- Spec in tighter resting state than session 18
