# geometry

## constraints

this derivation claims only what follows from these results. any additional assumption is a bug.

### from lean (proven)

- **commutator_traceless** (Form.lean): tr[P, Q] = 0. observation interaction is invisible to the scalar channel.
- **trace_unique_of_kills_commutators** (TraceUnique.lean): trace is the unique commutator-killing functional. one scalar readout.

### from other derivations

- **ground.md**: closure, partiality, basis commitment.
- **writing_map.md**: the write form, perpendicularity, confinement, the flat/curved separation.
- **group.md**: U(d), the trace as unique homomorphism u(d) -> u(1).
- **stabilization.md**: R^3 + Taylor, Voronoi as realization choice.

### from mathematics (cited, not proven in lean)

- **Voronoi tiling on Riemannian manifolds**: Voronoi regions under the bi-invariant metric on U(d). geodesic equidistant surfaces. Hausdorff measure.
- **Haar measure on compact groups**: the unique (up to normalization) left- and right-invariant probability measure on a compact group.
- **convergence theorem for random walks on compact groups**: a random walk whose step distribution generates the Lie algebra converges to Haar measure. the hypothesis is: compact group, step distribution not supported on a proper closed subgroup.
- **Cauchy-Schwarz inequality**.

## derivation

**L = sum of boundary areas.** the foam lives in U(d). cells are Voronoi regions of the basis matrices under the bi-invariant metric; boundaries are geodesic equidistant surfaces; Area_g is the (d^2 - 1)-dimensional Hausdorff measure. bases in general position tile non-periodically.

the Voronoi tiling is a realization choice (stabilization.md): it determines adjacency (which pairs share a boundary) and thereby defines L. the algebraic results (write map, three-body mapping, Grassmannian structure) depend on pairwise overlap, not the tiling method. the geometric results (L, combinatorial ceiling, conservation on spatial cycles) depend on the Voronoi realization.

**L is not a variational objective.** the writing map drives the foam; L describes the resulting geometry. the active regime departs from minimality because perpendicular writes deposit structure in different directions. the resting state (no writes) is minimal because dL = 0.

**L is bounded.** U(d) is compact.

**the combinatorial ceiling is exact.** N unitaries cannot all be pairwise maximally distant. the achievable maximum is sqrt(N / (2(N-1))) of the theoretical maximum, depending only on N. derivation: Cauchy-Schwarz applied to norm(sum U_i)^2 >= 0.

**L converges to 1/sqrt(2) of the theoretical maximum.** the writing dynamics satisfy: (a) the writes generate the Lie algebra (controllability — the write directions from overlapping observers span the full algebra), and (b) successive inputs are sufficiently decorrelated (channel_capacity.md: the mediation chain provides decorrelation).

on a compact group, a random walk whose step distribution generates the algebra converges to Haar measure. the expected pairwise distance under Haar is E[norm(W - I)_F] -> sqrt(2d) as d -> infinity (from E[norm(W - I)^2] = 2d, exact, and concentration of measure).

the Haar cost — the ratio E_Haar[L] / L_achievable — is sqrt((N-1)/N), exact and depending only on N.

the product: sqrt(N / (2(N-1))) * sqrt((N-1) / N) = **1/sqrt(2)**, independent of both N and d.

the two factors — the packing constraint and the saturation gap — are two halves of the same fraction.

**the trace is the readout.** trace_unique_of_kills_commutators: the trace is the unique scalar projection of a write. the overlap change tr(P * [W, P]) is visible on this channel. the observer has exactly one scalar readout, and it's this one.

## status

**proven** (in lean, zero sorry):
- trace is the unique commutator-killing functional
- observation interaction is traceless

**derived** (in this file):
- L as boundary area on Voronoi tiling (from realization choice)
- L is not a variational objective
- the combinatorial ceiling (from Cauchy-Schwarz)
- Haar convergence of the writing dynamics (from controllability + decorrelation + convergence theorem)
- the Haar cost sqrt((N-1)/N)
- 1/sqrt(2) as the product of ceiling and Haar cost, independent of N and d
- the trace as the unique scalar readout for overlap changes

**cited** (external mathematics):
- Voronoi tiling on Riemannian manifolds
- Haar measure on compact groups
- convergence theorem for random walks on compact groups
- Cauchy-Schwarz inequality

**observed** (empirical, not derived here):
- finite-d correction: E[norm(W-I)_F] / (2 sqrt(d)) = 0.694 at d=2, 0.707 at d=20
- the foam's observed L/L_max is 1-3% above Haar prediction at finite run lengths (consistent with incomplete convergence)
- L saturation behavior: saturates at ~72% of combinatorial ceiling, then wanders on a level set
- saturation level independent of write scale epsilon
- perpendicularity cost mechanism (write blindness): write direction uncorrelated with L gradient
- write subspace is exactly 3D per observer (PCs 4+ zero to machine precision)
- wandering at saturation has effective dimension ~2
- state-space steps Gaussian (kurtosis ~3); L steps heavy-tailed (kurtosis ~7.7) — geometric feature of level set, not dynamical
