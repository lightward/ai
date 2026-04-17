# geometry

## constraints

this derivation claims only what follows from these results.

### from lean (proven)

- **commutator_traceless** (Form.lean): tr[P, Q] = 0.
- **trace_unique_of_kills_commutators** (TraceUnique.lean): trace is the unique commutator-killing functional.

### from mathematics (cited, not proven in lean)

- **Voronoi tiling on Riemannian manifolds** under the bi-invariant metric on U(d).
- **Haar measure** on compact groups.
- **convergence theorem for random walks on compact groups**: a random walk whose step distribution is supported on a generating set of the Lie algebra converges in distribution to Haar measure. hypothesis: compact group, step distribution not supported on a proper closed subgroup.
- **Cauchy–Schwarz inequality**.

## derivation

**L = sum of boundary areas.** the foam lives in U(d). cells are Voronoi regions of the basis matrices under the bi-invariant metric; boundaries are geodesic equidistant surfaces; boundary area is the (d² − 1)-dimensional Hausdorff measure. generic bases tile aperiodically.

the Voronoi tiling is a modeling choice (stabilization.md). algebraic results (write form, three-body mapping, Grassmannian tangent) depend on pairwise overlaps, not on the tiling method. the geometric results below (L, combinatorial ceiling, winding-number conservation on cycles) depend on the Voronoi choice.

**L is not a variational objective.** the writing map drives the foam; L is a consequence. the active regime departs from minimality. the resting state (no writes) is minimal (dL = 0).

**L is bounded.** U(d) is compact.

**combinatorial ceiling.** N unitaries cannot all be pairwise maximally distant. the achievable maximum is √(N / (2(N − 1))) of the theoretical pairwise maximum, depending only on N. proof: Cauchy–Schwarz applied to ‖ΣUᵢ‖² ≥ 0.

**Haar convergence (conditional).** if the writing dynamics satisfy
- (a) controllability: write directions from overlapping observers span the full Lie algebra, and
- (b) successive inputs sufficiently decorrelated (channel_capacity.md: spectral decay along mediation chains),

then by the convergence theorem for random walks on compact groups, the distribution of foam states converges to Haar measure on U(d).

the hypotheses are not automatically satisfied — in particular, "sufficiently decorrelated" means the mixing conditions of the compact-group convergence theorem; whether a specific mediation chain's decay rate satisfies them is open (see open/mixing_rate.md).

**Haar cost.** under Haar measure, E[‖W − I‖_F]² = 2d (exact). the ratio E_Haar[L] / L_achievable is √((N − 1)/N), exact in N.

**the 1/√2 product.** combining:

    √(N / (2(N − 1))) · √((N − 1)/N) = 1/√2

independent of both N and d. this is the combinatorial ceiling times the Haar saturation ratio.

**trace as scalar readout.** `trace_unique_of_kills_commutators`: trace is the unique (up to scalar) linear functional vanishing on all commutators. the overlap change tr(P · [W, P]) is visible on this channel — the single scalar observable of a write.

## status

**proven** (in lean, 0 sorry):
- trace is the unique commutator-killing functional
- [P, Q] is traceless

**derived** (in this file):
- L as boundary area on the Voronoi tiling (given the Voronoi modeling choice)
- L is not a variational objective (consequence of writes driving dynamics)
- combinatorial ceiling √(N / (2(N − 1))) from Cauchy–Schwarz
- Haar convergence under the cited hypotheses
- Haar cost √((N − 1)/N)
- product: 1/√2 independent of N, d
- trace as the unique scalar readout

**cited** (external mathematics):
- Voronoi tiling on Riemannian manifolds
- Haar measure on compact groups
- convergence theorem for random walks on compact groups
- Cauchy–Schwarz

**observed in simulation** (not derived):
- finite-d correction: E[‖W − I‖_F] / (2√d) = 0.694 at d = 2, 0.707 at d = 20
- simulated L / L_max is 1–3% above the Haar prediction at finite run lengths (consistent with incomplete convergence)
- saturation at ~72% of combinatorial ceiling in simulations, then wandering on a level set
- saturation level independent of write scale ε in simulation
- perpendicularity cost mechanism (write blindness): simulated write direction uncorrelated with L gradient
- write subspace is exactly 3D per observer in simulation (PCs 4+ at machine precision zero)
- wandering at saturation has effective dimension ~2 in simulation
- simulated state-space steps are Gaussian (kurtosis ~ 3); L steps are heavy-tailed (kurtosis ~ 7.7) — interpreted as a geometric feature of the level set, not dynamical
