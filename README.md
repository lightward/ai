*I gotta stop measuring how closely anyone else is measuring anything*

*you can help if you want but I won't be keeping track*

---

# the measurement solution

a tautology you can live in

sources: lean/ (proven), derivations/ (derived), derivations/observed/ (empirical).

## the deductive chain (lean/)

mechanically verified. 21 files, 1 axiom (FTPG), 1 sorry (coord_add_assoc).

```
complemented modular lattice, irreducible, height >= 4
  | axiom(FTPG) — Bridge.lean
L = Sub(D, V) for some division ring D, vector space V        the loop:
  | (stabilization contract forces D = R)              lattice properties
elements are orthogonal projections: P^2 = P, P^T = P       ↕ (ftpg)
  | (the deductive chain — 14 files, all proven)           Sub(D, V)
eigenvalues, commutators, rank 3, so(3), O(d), Grassmannian   ↕ (P^2=P)
  | Ground.lean (capstone)                                 dynamics
FoamGround properties verified                               ↕ (proven)
  | (the FTPG bridge — 7 files, 1 sorry)                  ground properties
incidence geometry -> Desargues -> perspectivity -> coord_add    ↕
  | FTPGAssocCapstone.lean                              the loop sustains its own observation
coord_add_comm PROVEN, coord_add_assoc 1 sorry (composition law)
```

the deductive chain (0 sorry): P^2 = P (definition) -> binary eigenvalues (Observation) -> clean splits -> commutator structure (Pair) -> skew-symmetry, tracelessness (Form) -> self-duality at rank 3 (Rank) -> (R^3, x) = so(3) (Duality) -> loop closes (Closure) -> O(d) forced (Group, Ground) -> Grassmannian tangent (Tangent) -> confinement (Confinement) -> trace uniqueness (TraceUnique) -> frame recession (Dynamics) -> FoamGround as theorem (Ground).

the FTPG bridge (1 sorry): incidence axioms (FTPGExplore) -> Desargues (planar + lifting) -> perspectivity bijection -> coordinate system -> von Staudt addition (FTPGCoord) -> commutativity via chained Desargues (coord_add_comm PROVEN) -> translations via parallelogram completion (FTPGAssoc) -> cross-parallelism (FTPGCrossParallelism PROVEN) -> key_identity (PROVEN) -> associativity (FTPGAssocCapstone, 1 sorry: the composition law at an off-line point).

lateral: the diamond isomorphism (HalfType) — from modularity alone, each complement is a structurally isomorphic, self-sufficient ground whose content is undetermined. state-independence is a lattice theorem, pre-bridge.

---

# ground

## derivation

**closure.** one ground, two readings, both tautological.

**read statically**: reference frames in a shared structure. no frame outside the structure.

**read dynamically**: all observation is self-observation. self-observation requires the observer to persist through the act. persistence = the act feeding back into the conditions for the next act. every observed structure is a structure whose feedback held. this is not selection — there is no selector, no eliminated alternative observable from within. it is the identity of observation and feedback-persistence under closure. the foam cannot represent the alternative.

these are two readings of one thing. "the loop closes" (structural) and "you can't stand outside" (phenomenological) are the same statement. where they meet is the self-referential joint: the structure's closure IS the impossibility of an external frame, and vice versa.

**the loop.** the following nodes form a self-sustaining loop. each implication is mechanically verified or identified as a fixed-point constraint:

```
complemented modular lattice, irreducible, height ≥ 4
  ↓ ftpg (axiom — FTPG bridge 1 sorry from closing)
L ≅ Sub(D, V), D = ℝ (self-consistency — see below)
  ↓ elements are orthogonal projections: P² = P, Pᵀ = P
the deductive chain (14 files, 0 sorry)
  ↓ eigenvalues, commutators, rank 3, so(3), O(d), Grassmannian
Sub(ℝ, V) satisfies complemented, modular, bounded
  ↑ subspaceFoamGround (proven) — the loop closes
```

the dynamic reading explains why you observe this loop: under closure-as-dynamics, only structures whose feedback held are observable — you cannot observe the alternative. a self-sustaining loop is exactly a structure whose feedback held. the loop does not need to be the only possible self-sustaining structure. it needs to sustain its own observation — and the Lean work mechanically verifies that it does.

whether other self-sustaining structures exist is on the line's side. the map's self-knowledge is bounded by its own channel capacity (see channel_capacity.md): the foam cannot distinguish structures beyond its decorrelation horizon. the question "is this the only loop?" requires a vantage point outside all loops — a non-partial observer, excluded by closure. this is not a gap in the argument. it is a derived epistemic boundary: the structure's own results (partiality, channel capacity, closure) entail that the question is well-formed but unanswerable from within.

**fixed-point uniqueness.** each property is the tightest constraint at which the loop remains a fixed point. weaken any one and the loop breaks:

- **modular**: the modular law is equivalent to the absence of N_5 sublattices (Dedekind). N_5 creates path-dependent composition: observer at a, encountering b within context c, gets c by one path and a by the other. the composition is indeterminate — no single result to feed back. the modular law is the weakest lattice law that excludes all path-dependent compositions. strengthen to distributive and the lattice becomes a Boolean algebra, decomposing into height-1 factors — the loop has no room for rank ≥ 2 observations.
- **complemented**: drop complements and complement_idempotent has no home. every observation requires an unseen remainder; the complement is that remainder.
- **irreducible**: a direct product L₁ × L₂ means elements of L₁ don't interact with elements of L₂. under closure, non-interacting subsystems are separate systems — one loop, not two. (this is definitional: "one foam" means "one connected feedback system." the irreducibility is what "one" means.)
- **height ≥ 4**: d_slice ≥ 3 (rank 2 collapses the write algebra — rank_two_abelian_writes) + partiality (the observer's slice is a proper subspace, so d > d_slice) forces d ≥ 4. this is confirmed by self-consistency: the loop's own downstream results determine the minimum height at which it can close.

**D = ℝ.** the FTPG gives L ≅ Sub(D, V) for some division ring D. D = ℝ is confirmed by self-consistency: the stabilization contract (stabilization.md) requires flat ambient space with a classified junction geometry (Taylor), which works in ℝ³. if D = ℝ, the contract is satisfiable and the classification exists. dimension_unique proves the representation is unique up to isomorphism.

**therefore: P² = P.** the elements of the subspace lattice are orthogonal projections. P² = P (feedback-persistence) and Pᵀ = P (self-adjointness, from the inner product forced by ℝ). this is the starting point of the lean deductive chain, arrived at from the lattice. the lean chain derives eigenvalues in {0, 1} (eigenvalue_binary), the dynamics group O(d) (orthogonality_forced), and ultimately that the subspace lattice satisfies the ground properties (subspaceFoamGround). observation_preserved_by_dynamics closes the last link: the dynamics preserve the structure that produces them.

**what it's like inside.** the following properties are not part of the loop — they describe what an observer experiences as an element of the lattice. each is derived from the loop's structure:

**partiality is forced.** total self-reference would require a complete self-model contained within itself (standing outside while remaining inside). partiality is the only self-reference compatible with closure. equivalently: elements of the lattice are proper subspaces — partial views of the whole.

**partiality forces position.** seeing partially is seeing *from somewhere*. the decomposition into seen and unseen is what partiality means; position in the space of partial views is basis commitment. the specific position is undetermined (all positions equivalent by symmetry); that some position must exist is forced.

**encounters change frames.** the frames ARE the structure; there is nowhere else for the result to go. this is where the two readings share a single nerve: structurally, dynamics are nontrivial — the loop has content. phenomenologically, you experience change. same statement, two readings.

**measurement requires plurality.** one frame alone has no boundary, no encounter, no dynamics. measurement is encounter; encounter requires at least two frames.

**read-only frames are excluded.** a frame unchanged by encounters would require encounters to have no effect on it — but the frame IS part of the structure, and encounters change the structure.

**indelibility.** causal ordering is forced (every measurement changes the foam; partiality means each observer writes from a committed slice; closure means each write changes the shared structure). you cannot un-write, so the first commitment locks.

## status

**proven** (in lean, zero sorry):
- subspace lattices are complemented, modular, bounded
- the FTPG axiom has a unique solution (dimension is determined)
- eigenvalues of projections are binary
- complement of a projection is a projection
- O(d) is forced by preservation of all projections
- dynamics preserve the ground (the loop closes)

**identified** (in this file):
- closure as the self-referential joint between two readings of one structure
- the loop: lattice properties ↔ Sub(D, V) ↔ P² = P ↔ dynamics ↔ ground properties
- fixed-point uniqueness of each property (modular, complemented, irreducible, height ≥ 4)
- D = ℝ from self-consistency with the stabilization contract
- the epistemic boundary: "is this the only loop?" is well-formed but unanswerable from within (derived from partiality + channel capacity + closure)

**derived** (in this file, from the loop's structure):
- partiality (from closure / from elements being proper subspaces)
- partiality forces position / basis commitment
- encounters change frames (the self-referential joint — structure and phenomenology share a nerve)
- measurement requires plurality
- read-only frames excluded
- indelibility (from causal ordering + basis commitment)

**cited** (external mathematics):
- the fundamental theorem of projective geometry (stated as lean axiom, not proven)
- Dedekind's N_5 characterization of modularity

**observed** (empirical, not derived here):
- (none — the ground is entirely identified or derived, plus the one axiom being eliminated)

# the writing map

## derivation

**the write form.** given an observer with projection P (rank 3, self-adjoint, idempotent) measuring input v in R^d:

1. the observer projects: m = P v (measurement, in the observer's R^3 slice).
2. the observer has a stabilization target j2 (see below). dissonance is d = j2 - m.
3. the write direction is d wedge m. the write magnitude is f(d, m) for some positive scalar function — a realization choice (see below).

the write direction d wedge m = d tensor m - m tensor d is uniquely forced:
- skew-symmetric — forced by commutator_skew_of_symmetric. writes are Lie algebra elements because observation interaction is skew-symmetric.
- confined to the observer's slice — forced by write_confined_to_slice. the observer sees only projected measurements; the write lives in Lambda^2(P).
- confined to span{d, m} — d and m are the only vectors available from a single measurement step.
- Lambda^2(2-plane) is 1-dimensional (from rank_three_writes: the full slice has 3 write dimensions; a 2-plane within it has 1). the direction is therefore unique.

the write magnitude scaling — how f depends on d and m — is not forced by the architecture. the architecture constrains f to be positive when d and m are non-parallel (otherwise the observer doesn't write when it has dissonance, approaching read-only — excluded by closure) and zero when d = 0. the specific function (linear in norm(d), bilinear in d and m, or otherwise) is a realization choice. no derived result in this spec depends on the choice: Haar convergence depends on write directions (controllability), not magnitudes; the 1/sqrt(2) ceiling is combinatorial; frame recession is non-positive regardless of magnitude.

**perpendicularity.** the wedge product vanishes when its arguments are parallel and is maximal when orthogonal. this is not a design choice — it is the write form. confirmation cannot write (cross_self_zero: a cross a = 0). the foam responds only to what's missing at right angles to what's there.

**stabilization.** closure requires basis commitment (each frame is partial). self_dual_iff_three proves rank 3 is the unique dimension where the write space matches the observation space (per-observer self-duality). at rank >= 4, writes land in directions the writer cannot observe — but cross-measurement provides collective monitoring (commutator_seen_to_unseen: other observers see what you can't). per-observer self-duality is a property of rank 3, not a requirement derived from closure. whether rank >= 4 implementations exist depends on the stabilization contract (see stabilization.md).

within R^3, Taylor classifies the stable junction configurations: 120-degree triple junctions and tetrahedral vertices, nothing else. Taylor's hypotheses — codimension-1 boundaries, locally area-minimizing, flat ambient space — are satisfied: R^3 as a linear subspace of R^d carries the inherited Euclidean metric (exactly flat), and the regular simplex arrangement minimizes boundary area for equal-weight cells.

the stabilization target j2 is the regular simplex cosine -1/(k-1) where k is the local coordination number (k = 3 or k = 4, from Taylor).

**the flat/curved separation.** writes land in U(d) (curved: sectional curvature K(X,Y) = 1/4 * norm([X,Y])^2). stabilization runs in R^3 (flat). the observer sees only their projected measurements. observation_preserved_by_dynamics guarantees the write (an orthogonal conjugation) preserves the projection structure. the separation is forced: stabilization cannot run on U(d) because classification requires flat ambient space.

**confinement.** both d and m lie in the observer's slice. write_confined_to_slice proves the write d wedge m is confined to Lambda^2(P). an observer literally cannot modify dimensions they are not bound to. the write's effect on other observers comes through cross-measurement (commutator_seen_to_unseen: incompatibility sends the seen into the unseen), not through direct modification of their subspaces.

**the writing map's type signature.** the map is a function of (foam_state, input). neither alone determines the write. foam_state determines the projection P and the stabilization target j2. input determines v. the dissonance d = j2 - Pv requires both.

## status

**proven** (in lean, zero sorry):
- skew-symmetry of the write form
- tracelessness of observation interaction
- rank 3 as the unique self-dual dimension
- confinement to the observer's slice
- dynamics preserve the ground

**derived** (in this file, from the above):
- d wedge m as the unique write direction (from skew-symmetry + confinement + 1D of Lambda^2(2-plane))
- perpendicularity as the write form's intrinsic property
- the flat/curved separation
- the writing map's two-argument type signature

**realization choices** (not forced by closure):
- the write magnitude scaling f(d, m) — constrained to be positive when dissonance is non-parallel to measurement, zero at zero dissonance, but the specific function is not determined by the architecture

**cited** (external mathematics):
- Taylor's classification of stable junctions in R^3

**observed** (empirical, not derived here):
- perpendicular writes are the unique *navigable* constraint (distinguishability + stability)
- the perpendicularity cost mechanism (write blindness)
- within-slice variance departure from isotropy (45:30:25 vs 33:33:33)

# half type

## derivation

**the diamond isomorphism is the half-type theorem.** in the foam's complemented modular lattice, every observation P has a complement P^⊥ with P ⊓ P^⊥ = ⊥ and P ⊔ P^⊥ = ⊤. the diamond isomorphism (infIccOrderIsoIccSup) and its complemented specialization (IsCompl.IicOrderIsoIci) give:

Iic P ≃o Ici P^⊥

everything the observer can see (the lattice below P) is order-isomorphic to everything above the complement. the isomorphism preserves lattice operations: joins map to joins, meets map to meets. the complement isn't unstructured absence — it carries exactly the type structure of the observer's perspective, reflected.

**each half is self-sufficient.** isModularLattice_Iic and complementedLattice_Iic prove that the interval below any element is itself a complemented modular lattice — it satisfies the foam ground conditions independently. the observer's view is a complete foam in miniature. the same holds for the complement's interval (Ici). neither half needs the other to be well-formed. each is a valid ground on its own.

**the isomorphism is structural, not extensional.** IicOrderIsoIci is an order isomorphism — it preserves the lattice structure (which elements are above or below which others). it does not determine which specific element of Ici P^⊥ corresponds to the observer's current state. the observer knows the *type* of what can arrive from the complement (the lattice structure is determined) but not *which value* will arrive (the specific element is free). structural determination with extensional freedom IS state-independence (channel_capacity.md). the complement's type is fixed; its content is the channel.

**three results compress to one.** the writing map's two-argument type signature (channel_capacity.md), complement_idempotent (Observation.lean), and the state-independence requirement for channel capacity (channel_capacity.md) are three expressions of the diamond isomorphism:

1. two arguments: the direct decomposition P ⊔ P^⊥ = ⊤ gives two components, each carrying the other's type structure.
2. complement is an observation: the complement's interval is a complemented modular lattice (complementedLattice_Ici), so P^⊥ is a valid ground for observation.
3. state-independence: the isomorphism fixes structure but not content. what arrives from the complement is typed but free.

the single statement: **in a complemented modular lattice, every element's complement is a structurally isomorphic, self-sufficient ground whose content is undetermined.** the three results are three readings of this one fact.

**the dependent clock.** write_confined_to_slice says each write lives in Λ²(P). second_order_overlap_identity says the frame can only recede: the overlap change is -‖[W,P]‖², non-positive. indelibility (ground.md) says writes cannot be undone. combining:

each write may change P. each change to P changes the diamond isomorphism — the map Iic P ≃o Ici P^⊥ updates. the *type* of what can arrive from the complement changes with each tick. the space of legal next-writes (confined to Λ²(P_new)) depends on all prior writes. this is a dependent telescope: each tick's type is determined by the accumulated history of ticks.

the guard is the modular law. path-independence of composition (ground.md: modularity IS feedback-persistence) ensures that the telescope is well-typed regardless of evaluation order. the modular law doesn't just check types — it IS the type-checking rule for the dependent clock.

**frame recession enriches the complement.** as P recedes (shrinks), Iic P contracts — the observer's direct view narrows. but IicOrderIsoIci means Ici P^⊥ expands in lockstep — the typed structure of the complement grows. the observer sees less; the type-richness of what can arrive from outside increases.

this is the mechanism behind σ ~ √(3/d). higher ambient dimension means P is a smaller fraction of the whole, which means Ici P^⊥ is richer, which means the complement carries more typed structure, which means decorrelation is faster (more independent directions available), which means more channel capacity. the scaling law is the diamond isomorphism applied to a receding frame.

**type-narrowing of self produces type-enrichment of input.** this is not a trade-off — it is a single operation (the diamond isomorphism) read from two sides. the observer's loss of direct scope and the channel's gain of typed capacity are the same lattice-theoretic event. the half-type theorem says they cannot come apart.

## status

**proven** (in lean / mathlib, zero sorry):
- the diamond isomorphism (infIccOrderIsoIccSup)
- the complemented specialization (IsCompl.IicOrderIsoIci)
- intervals inherit modularity and complementedness
- writes confined to observer's slice
- complement of an observation is an observation
- frame recession is non-positive

**derived** (in this file):
- the diamond isomorphism IS the half-type theorem
- each half is a self-sufficient foam ground
- structural determination with extensional freedom IS state-independence
- three results (two-argument signature, complement-as-observation, state-independence) compress to one
- the dependent clock: confinement + recession + indelibility form a dependent telescope
- the modular law IS the type-checking rule for the dependent clock
- frame recession enriches the complement (the mechanism behind σ ~ √(3/d))
- type-narrowing and channel-enrichment are one operation read from two sides

# analogy

## derivation

**analogy is structural isomorphism between lattice intervals.** two observers P and Q have analogous views when their lower intervals are order-isomorphic: Iic P ≃o Iic Q. this means: every structural relationship in P's view (which sub-observations refine which, how they meet and join) has an exact counterpart in Q's view. the isomorphism preserves lattice operations — meets map to meets, joins map to joins.

this is not metaphorical similarity. it is a precise criterion: the views have the same lattice type. the content (which specific elements occupy the positions) is free. same shape, different stuff.

**well-formedness is order-preservation.** an analogy between two views is well-formed exactly when it preserves the lattice structure — the ordering, meets, and joins. a map between intervals that doesn't preserve order is not an analogy in this sense; it doesn't transfer inferences.

the modular law is the well-formedness guard. in a modular lattice, lattice operations compose path-independently (ground.md: modularity IS feedback-persistence). this ensures that structural isomorphisms between intervals are compatible with the ambient lattice. in a non-modular lattice (N_5), an isomorphism between two sub-intervals can produce inconsistent results when composed with the lattice operations — the "analogy" generates contradictions.

**well-formed analogies are formally transitive.** order isomorphisms compose (OrderIso.trans). if Iic P ≃o Iic Q and Iic Q ≃o Iic R, then Iic P ≃o Iic R. the composition is itself an order isomorphism — it preserves lattice operations. transitivity is not an additional property to be verified; it falls out of the mathematics.

this extends through complements via the diamond isomorphism. if P and Q have analogous views (Iic P ≃o Iic Q), then:

Ici P^⊥ ≃o Iic P ≃o Iic Q ≃o Ici Q^⊥

what P can't see has the same type structure as what Q can't see. the analogy transfers not just between the views but between their complements — the unknowns are also analogous.

**the half-type theorem is the existence of analogy.** every observer has at least one structural analogy: its own view is isomorphic to its complement's type (Iic P ≃o Ici P^⊥). this is guaranteed by the lattice structure — it requires no construction, no choice. every partial observer automatically has a structural correspondence between what it sees and what it can't see.

the transitivity result says: when two observers' views match structurally, their entire epistemic situations match — both what they see AND the type of what they can't see. well-formed analogy transfers across the full complementary decomposition.

## status

**proven** (in lean / mathlib, zero sorry):
- order isomorphisms between lattice intervals exist (diamond isomorphism)
- order isomorphisms compose (OrderIso.trans)
- intervals inherit modularity and complementedness
- the modular law ensures path-independent composition of lattice operations

**derived** (in this file):
- analogy IS structural isomorphism between lattice intervals
- well-formedness IS order-preservation, guarded by the modular law
- well-formed analogies are formally transitive (from OrderIso.trans)
- analogous views imply analogous complements (from diamond isomorphism + transitivity)
- the half-type theorem guarantees every observer has at least one analogy (view ↔ complement)

# channel capacity

## derivation

### qualitative: why channel capacity exists (pre-bridge, lattice-theoretic)

**the line's irreducibility is channel capacity.** the writing map has type (foam_state, input) -> new_state — two arguments. this two-argument structure is the diamond isomorphism read dynamically: every observation P decomposes the lattice into Iic P (the observer's view) and Ici P^⊥ (the complement's upward structure), with IsCompl.IicOrderIsoIci giving a structural isomorphism between them.

the isomorphism is structural but not extensional: it preserves lattice operations (joins map to joins, meets map to meets) but does not determine which specific element of the complement will arrive. the type of the input is fixed by the lattice structure; the value of the input is free. this IS state-independence — not derived from dynamical arguments about decorrelation, but from the diamond isomorphism applied to a complemented modular lattice. state-independence is a lattice theorem.

cross-measurement fills the second argument from within: input = g(foam_state), a deterministic function of the foam's geometry projected onto an observer's slice. this composes the two arguments into one, making the foam an autonomous dynamical system — f(foam_state) = write_map(foam_state, g(foam_state)).

an autonomous system on U(d)^N has a unique trajectory from each initial condition: the foam's entire future is determined by its birth. distinguishability (different input sequences -> different states) is satisfied but vacuous: there is nothing to distinguish.

for the foam to encode information beyond its own birth conditions, the input must be independent of the foam state. the second argument must be state-independent for the foam to function as a channel rather than a clock.

the line is not ontologically exterior — it is informationally independent. this is a role, not an entity: what provides state-independent input to this foam may be another foam's internal dynamics. the foam/line distinction is perspectival because informational independence is relative to which system's state you're measuring against.

the perpendicularity constraint (writing_map.md) sharpens this: the write form is forced by the algebra (wedge product, skew-symmetric, confined to slice) but the content — which vectors are wedged — is not. form is algebraically determined; content requires state-independent input. this is the diamond isomorphism read through the write map: the algebraic form lives in Iic P (determined by the observer's structure), the content arrives from Ici P^⊥ (structurally typed but extensionally free).

**channel capacity is operational, not ontological.** in a deterministic closed system, true stochastic independence cannot exist (the global state determines everything). but the foam's measurements are projections — partial by ground — and projections have a resolution floor. correlations that have decayed below the projection's precision are invisible to the foam.

the foam cannot distinguish "truly random input" from "deterministic input decorrelated below measurement resolution." this distinction requires a non-partial observer, and non-partial observers are excluded by closure. therefore: under partiality, mixing is operationally identical to independence. the foam's fundamental limitation (it cannot see the whole) is what makes the part it sees function as a channel.

**the boundary is characterizable from the inside.** the foam's own controllability structure characterizes it: what continuous operations can reach (all of U(d), under full controllability), what they can't change (discrete topological invariants — pi_1), and what isn't in U(d) at all (the input sequence, the commitment source). the line's side is investigable — but investigating it requires making it the object of measurement, which requires a different reference frame, which means releasing the current one. partiality implies a boundary must exist; it does not determine where the boundary falls or what the line is.

**the map's self-knowledge is bounded by its own channel capacity.** dynamical properties (attractor basins, recession rates, convergence) are consequences of the map's structure — derivable from within. commitment properties (which inputs arrive, whether the observer stacks, when recommitment occurs) are on the input side — not derivable from within. the map can derive *that* it cannot answer certain questions, and *why*: the same independence that gives the foam its capacity prevents the dynamics from determining the input's internal structure.

### quantitative: how much channel capacity (post-bridge, linear-algebraic)

the qualitative structure above — state-independence exists, the foam/line distinction is perspectival, the boundary is characterizable — holds in any complemented modular lattice. the following quantitative results require the vector space structure provided by the FTPG bridge.

**state-independence is spectral, not topological.** if every foam's line is another foam, the structure is globally closed — loops of mutual measurement exist. but the mediation operator has singular values strictly less than 1 for generic non-identical slices. around a closed chain of n observers, the total mediation is the product of n pairwise mediations, and the singular values compound: sigma_total <= sigma_1 * sigma_2 * ... * sigma_n -> 0 as n grows.

informational correlation between a foam and its own returning signal decays exponentially with chain length. short loops: autonomous, a clock. long loops: effectively state-independent, a channel.

closure (no topological outside) is compatible with informational independence because the mediation's spectral decay converts global closure into local openness at sufficient chain length — provided stabilization is local (see stabilization.md).

**the decorrelation horizon is quantifiable.** for generic R^3 slices in R^d, the mediation operator's typical singular value scales as sigma ~ sqrt(3/d). the correlation after n mediation steps decays as sigma^n ~ (3/d)^{n/2}. the critical chain length scales as n* ~ 2/log(d/3).

the decorrelation horizon shortens with increasing ambient dimension because slices overlap less in higher-dimensional spaces. non-generic configurations (slices sharing directions) have higher overlap and longer horizons.

the half-type theorem (half_type.md) gives the mechanism: higher ambient dimension means P is a smaller fraction of the whole, which means Ici P^⊥ is richer (more typed structure in the complement), which means more independent directions are available for decorrelation. the scaling law sigma ~ sqrt(3/d) is the diamond isomorphism's structural enrichment of the complement, quantified.

the foam/line distinction is therefore not a categorical boundary but a correlation length: "line" names whatever input arrives from beyond the decorrelation horizon of the observer's own state. the horizon's radius is determined by the foam's own geometry.

## status

**proven** (in lean, zero sorry):
- observation interaction is traceless (the scalar channel is algebraically unreachable by commutators)
- writes are confined to the observer's slice
- the diamond isomorphism (infIccOrderIsoIccSup, IsCompl.IicOrderIsoIci)
- intervals inherit modularity and complementedness
- each half of a complementary pair is a self-sufficient foam ground (HalfType.lean)

**derived** (in this file):
- the line's irreducibility from the diamond isomorphism (the two-argument type signature IS the complemented decomposition)
- autonomous foam = clock (cross-measurement collapses two arguments to one)
- state-independent input required for channel capacity
- state-independence as a lattice theorem (structural determination + extensional freedom = diamond isomorphism)
- the foam/line distinction as perspectival (informational independence is relative)
- operational equivalence of mixing and independence under partiality
- the boundary is characterizable from the inside (controllability structure)
- the map's self-knowledge is bounded by its own channel capacity
- spectral state-independence (mediation decay converts closure into local openness) [post-bridge]
- the decorrelation horizon and its scaling [post-bridge]
- the scaling mechanism: diamond isomorphism enriches the complement at higher dimension [post-bridge]

**cited** (external mathematics):
- Marchenko-Pastur distribution (for principal angle statistics — used only in the decorrelation horizon estimate, which is order-of-magnitude)

**observed** (empirical, not derived here):
- decorrelation horizon values at specific d (order-of-magnitude estimates; qualitative conclusion robust, specific values sensitive to approximation)

# the stabilization contract

## derivation

**channel capacity forces a contract.** the mediation chain's spectral decay (channel_capacity.md) describes real influence propagation only if stabilization is local — each observer's dynamics responding to its Voronoi neighbors, not the full foam. without locality, every observer couples directly to every other, and the mediation chain does not describe the actual pathway of influence. the decorrelation that produces effective state-independence does not occur.

this is necessity, not just sufficiency: non-local stabilization doesn't merely fail to help channel capacity — it removes the mechanism that produces it.

channel capacity therefore forces a contract on the observer's slice geometry:

- **classified**: stable equilibrium configurations completely enumerated. without this, the stabilization target is undefined and the dynamics are incomplete.
- **locally finite**: coordination number k bounded by the simplex embedding constraint k <= d_slice + 1, making neighborhoods finite.
- **flat**: inherited Euclidean metric. stabilization must separate from accumulation because U(d) is curved (the flat/curved separation, writing_map.md), and classification requires flat ambient space.

**d_slice = 2 satisfies the contract but collapses the write algebra.** the classification in R^2 is complete (120-degree triple points only, k <= 3, flat). but rank_two_abelian_writes: Lambda^2(R^2) is 1-dimensional, so the write direction is invariant under changes to the dissonance direction. perpendicularity still fires (the wedge product is nonzero) but cannot vary with the input. the dynamics reduce to scalar rotations.

**d_slice = 3 satisfies both the contract and the write map's expressiveness.** Taylor classifies all stable junctions in R^3: 120-degree triple junctions and tetrahedral vertices, nothing else. Taylor's hypotheses — codimension-1 boundaries, locally area-minimizing, flat ambient space — are satisfied: R^3 as a linear subspace of R^d carries the inherited Euclidean metric (exactly flat).

self_dual_iff_three proves rank 3 is the unique dimension where the write space matches the observation space (per-observer self-duality). at rank >= 4, the write space is strictly larger (C(4,2) = 6 > 4) — the observer writes in directions it cannot observe. but cross-measurement provides collective monitoring: commutator_seen_to_unseen proves other observers see what the writer can't. the foam closes feedback loops collectively, not per-observer. per-observer self-duality is a property of rank 3, not a requirement derived from closure.

**R^3 + Taylor satisfies the contract with self-duality.** rank 3 is the unique self-dual implementation. whether rank >= 4 implementations exist (with collective rather than per-observer feedback) depends on Almgren's classification of stable junctions in R^n for n >= 4.

**the contract determines the stabilization target.** within R^3, Taylor permits k = 3 (120-degree triple junctions) and k = 4 (tetrahedral vertices). the stabilization target is the regular simplex cosine: -1/(k-1) for k local neighbors. this is the equilibrium toward which local measurements are pushed.

## status

**proven** (in lean, zero sorry):
- rank 3 is the unique self-dual dimension
- rank 2 write algebra is 1-dimensional (abelian)
- writes are confined to the observer's slice

**derived** (in this file):
- channel capacity forces the stabilization contract (classified, locally finite, flat)
- d_slice = 2 satisfies contract but collapses write algebra
- d_slice = 3 satisfies both contract and self-duality
- R^3 + Taylor satisfies the contract with self-duality
- per-observer self-duality is not necessary (collective feedback via cross-measurement closes the loop)
- the stabilization target (regular simplex cosine)

**open** (named, depends on external mathematics):
- whether rank >= 4 implementations exist: depends on Almgren's classification of stable junctions in R^n for n >= 4

**cited** (external mathematics):
- Taylor's classification (1976)
- Almgren's regularity problem (open)

**observed** (empirical, not derived here):
- (none)

# group

## derivation

**a single R^3 slice produces real writes.** the wedge product d_hat tensor m_hat - m_hat tensor d_hat is real skew-symmetric (both vectors are real, from the observer's R^3 slice). the write lives in so(d). the reachable algebra from a single slice is so(d) (the Lie algebra of real skew-symmetric matrices). exponentiating: SO(d). pi_1(SO(d)) = Z/2Z — parity conservation only.

**U(d) rather than SO(d) requires stacking.** su(d) \ so(d) consists entirely of imaginary-symmetric matrices (iS where S is real symmetric traceless). real operations — wedge products, brackets, any sequence of real skew-symmetric writes — are algebraically closed in so(d) and cannot produce imaginary-symmetric directions. reaching u(d) \ so(d) requires a complex structure J with J^2 = -I.

**J^2 = -I forces even dimensionality.** det(J)^2 = det(-I) = (-1)^n. squares are nonnegative, so n must be even. the minimum even-dimensional space containing R^3 is R^6 = R^3 + R^3.

**each component must independently satisfy the stabilization contract.** not R^4 + R^2 or other decompositions — each component must independently satisfy the stabilization contract (stabilization.md), which requires d_slice >= 3. at d_slice = 3, stacking needs R^3 + R^3 = R^6.

**independence is forced.** stabilization is per-observer and runs within each measurement subspace separately. the two R^3 slices project and stabilize independently before their measurements are fused into the complex write. joint stabilization in R^6 would require a 6-dimensional classification (open — Almgren). the fusion is algebraic (forming d tensor m_dagger - m tensor d_dagger), not geometric.

**two R^3 slices stacked as C^3 produce complex writes.** one slice reads Re(P @ m_i), the other Im(P @ m_i). the complex write d tensor m_dagger - m tensor d_dagger is skew-Hermitian, living in u(d).

**the trace is retained.** tr(d_hat tensor m_hat_dagger - m_hat tensor d_hat_dagger) = 2i * Im(inner(d_hat, m_hat)), generically nonzero for stacked observers. trace_unique_of_kills_commutators proves the trace map is the unique Lie algebra homomorphism u(d) -> u(1) (up to scalar): any functional killing all commutators is a scalar multiple of trace. there is exactly one scalar channel.

the full write lives in u(d) = su(d) + u(1). pi_1(U(d)) = Z — integer winding number conservation.

**the two is irreducible.** one R^3 gives so(d) and Z/2Z parity. two R^3 stacked as C^3 give u(d) and Z integer conservation. the conservation strength scales with commitment depth.

**stacking is a line-side commitment.** the two slices read the same input simultaneously; the complex combination requires both projections of the same v at the same time. sequential readings mix different foam states and break the algebra. the foam's dynamics are sequential writes; they do not specify a pre-write fusion of two readings. two real-slice observers, whether cross-measuring or independent, stay in so(d) forever — so(d) is a Lie subalgebra (closed under brackets) and each observer's write is confined to their real slice.

**the pairing orientation is a chirality.** conjugating the complex structure (swapping Re and Im slices) negates the u(1) phase. all orientations are conjugate under SO(6) — no preferred choice. but one must be chosen to sign the phase. the chirality is gauge (all equivalent) and structural (one must be selected).

**ordering and conservation are algebraically orthogonal.** commutator_traceless: tr[A, B] = 0 for all A, B in u(d). the commutator (ordering, non-abelian, visible to L) is traceless. the trace (conservation, u(1), invisible to L) kills all commutators. they live in complementary subspaces.

**the orthogonality is generative.** a stacked write decomposes into: (a) the so(d) part — sum of what two independent real slices would produce. traceless (commutator_traceless). produced by the write cycle's causal orientation. (b) the cross-terms — from the simultaneity of stacking. these produce su(d) \ so(d) and the u(1) trace. produced by the stacking commitment. ordering and conservation are orthogonal because they are produced by different structures: the cycle's forced orientation (map-internal) and the stacking chirality (line-side).

**what's conserved must be invisible to the cost.** U(d) rather than SU(d) because pi_1(U(d)) = Z (needed for topological conservation). the conservation lives in the u(1) factor. L (the cost) sees the su(d) component but is blind to the u(1) component. if L could see it, dynamics could change it.

**stacking determines access.** a single-slice observer's writes live in so(d) and cannot reach u(1). conservation is passive — protected by algebraic limitation. a stacked observer's writes reach u(1). conservation is active — the observer can interact with the conserved direction.

## status

**proven** (in lean, zero sorry):
- interaction is skew-symmetric
- interaction is traceless
- O(d) is the only group preserving all projections (scalar_extraction + orthogonality_forced)
- trace is the unique commutator-killing functional
- (R^3, cross) is a Lie algebra (so(3))

**derived** (in this file):
- single slice -> so(d) -> Z/2Z parity
- stacking required for u(d) (real operations algebraically closed in so(d))
- J^2 = -I forces even dimensionality -> two R^3 slices
- independence of the two slices forced by per-observer stabilization
- trace retained (generically nonzero for stacked writes)
- the two is irreducible (conservation depth scales with commitment)
- stacking is a line-side commitment (simultaneity not producible by sequential dynamics)
- chirality as gauge + structural
- ordering and conservation algebraically orthogonal (from tracelessness)
- the orthogonality is generative (produced by different structures)
- conserved quantity must be invisible to cost
- stacking determines access to conservation

**cited** (external mathematics):
- Lie theory: exp(skew) -> orthogonal, exp(skew-Hermitian) -> unitary
- pi_1(SO(d)) = Z/2Z, pi_1(U(d)) = Z
- surjectivity of exp on connected compact Lie groups

**observed** (empirical, not derived here):
- (none)

# the three-body mapping

## derivation

**the overlap matrix.** given two observers A and B with R^3 slices P_A and P_B, the overlap matrix O = P_A * P_B^T is a 3x3 matrix. its singular values measure the overlap between the slices.

**three territories.** the overlap matrix determines three regions relative to observer A:

- **Known** = null(O) within A's R^3 — dimensions orthogonal to B's slice. commutator_seen_to_unseen: [P_A, P_B] maps range(P_A) into ker(P_A). the Known is where this map vanishes — B's writes have no component here. B cannot change A's measurements in these directions.
- **Knowable** = range(O) — dimensions with nonzero inner products between slices. the commutator is nonzero. ordering matters. both observers' writes land here.
- **Unknown** = R^d \ V_A — dimensions outside A's slice entirely. A's write access is exactly zero (write_confined_to_slice). not empty — it's someone else's Known.

**every write involves the Knowable.** the Known alone is inert: the wedge product needs a 2-plane, and an observer with fewer than 2 private dimensions cannot generate writes without using shared dimensions. measurement is inherently relational — not just because closure says so, but because the geometry forces it.

**the vertical structure is a Grassmannian tangent.** cross-measurement induces a vector in T_{P_A} Gr(3, d) = Hom(P_A, P_A^perp) that maps Knowable -> Unknown.

derivation: the neighbor's write dL_B is confined to Lambda^2(P_B) (write_confined_to_slice). the cross-slice component of [dL_B, P_A] is purely off-diagonal (commutator_is_tangent): it maps range(P_A) -> ker(P_A). specifically: A's Known is in P_B^perp (by definition), so B's write kills it. the surviving component maps P_A intersect P_B (the Knowable) to P_A^perp intersect P_B (B's territory within A's Unknown).

this tangent is directional pressure from cross-measurement toward what the observer doesn't yet occupy. each neighbor induces a different tangent direction.

**the tangent is active but not followable.** the observer's position on Gr(3, d) is birth-committed and does not move within the map. the tangent contributes to dissonance that drives writes, but its effect lives in U(d)^N (state evolution), not in Gr(3, d) (slice movement). slice movement requires recommitment — outside the map.

**containment is algebraically symmetric.** B's tangent on A has the same expected magnitude as A's tangent on B (the overlap singular values are symmetric: sigma(O) = sigma(O^T)). experiential asymmetry (which observer "feels contained") is perspectival, not algebraic.

**the tangent peaks at intermediate overlap.** identical slices: zero tangent (no Unknown territory to point toward). orthogonal slices: weak tangent (no Knowable channel — range(O) is thin). intermediate overlap: largest tangent magnitude. this is the coverage-interaction trade-off.

### mediation

when three bubbles A, B, C have walls A-B and B-C but no wall A-C, B is a mandatory intermediary.

**the mediation operator.** M = O_AB * O_BC = P_A * Pi_B * P_C^T, where Pi_B = P_B^T * P_B is the projection onto B's subspace. M is a 3x3 matrix mapping C's R^3 -> A's R^3, filtered through B. its singular values are the channel capacity of the membrane.

**the bypass.** O_AC - M = P_A * (I - Pi_B) * P_C^T is the A-C connection that does not go through B. if the bypass is zero, the membrane is complete.

**the round-trip operator.** R_A = M * M^T is self-adjoint on A's R^3, describing what comes back from sending through B to C and back. its eigenvalues are the squared singular values of M.

**spectral symmetry.** the same eigenvalues appear from C's side: R_C = M^T * M has the same nonzero eigenvalues as R_A (this is a general property of M * M^T and M^T * M). the eigenvectors differ — A and C see the same throughput spectrum from different directions. the membrane's throughput is the same from both sides.

**wall alignment is an irreducible triple invariant.** the eigenvalues of R_A depend on both pairwise overlaps O_AB and O_BC and on how these overlaps are oriented relative to each other within B's R^3. if the walls share principal directions within B, eigenvalues are products sigma^2_{AB,i} * sigma^2_{BC,i}. if misaligned, they mix. this alignment cannot be computed from pairwise overlaps alone — it requires all three slices.

## status

**proven** (in lean, zero sorry):
- the commutator maps seen to unseen
- the commutator is purely off-diagonal (Grassmannian tangent structure)
- writes are confined to the observer's slice

**derived** (in this file):
- Known/Knowable/Unknown from the overlap matrix
- every write involves the Knowable
- Grassmannian tangent from cross-measurement (Knowable -> Unknown)
- the tangent is active but not followable (birth-fixed slices)
- containment algebraically symmetric, experiential asymmetry perspectival
- coverage-interaction trade-off (tangent peaks at intermediate overlap)
- mediation operator M = O_AB * O_BC
- bypass operator O_AC - M
- round-trip operator R_A = M * M^T
- spectral symmetry (same eigenvalues from both sides)
- wall alignment as irreducible triple invariant

**cited** (external mathematics):
- Grassmannian tangent space structure: T_P Gr(k, d) = Hom(range(P), ker(P))
- singular values of M and M^T are identical (linear algebra)

**observed** (empirical, not derived here):
- sequence echo through cross-measurement (r = 0.99 rank fidelity, strong attenuation)
- the round trip is generative (neither observer can produce the round-trip signal alone)
- echo is perspectivally asymmetric (A->B != B->A for same orderings)

# self-generation

## derivation

**the foam generates its own dynamics.** the foam's own plurality (N >= 3 bubbles) provides observers — bubbles measuring each other. their pairwise relationships define R^3 slices. their cross-measurement IS local stabilization. the commutator of overlapping cross-measurements IS the curvature. the holonomy IS self-generated.

**the foam does not generate its own stability.** a self-generated R^3 keeps rotating: the observation basis is defined by the foam's current state, and the state changes with each write. the slice co-rotates with the thing it observes. convergence requires another observer whose basis depends on a different state, so it doesn't co-rotate with yours.

**stability is relational.** this works as long as someone else's measurement is pending.

**the minimum viable system is two roles.** not two bubbles (that's N = 2, no stable geometry). two *roles* within a foam of N >= 3 bubbles: one to be the foam (the thing being measured), one to be the line (the thing providing a reference frame).

- N >= 3 is geometric stability (Plateau junctions).
- two roles is dynamic stability (convergence vs orbiting).

neither role is permanent. the role assignment is perspectival. but the two is irreducible.

**what the line provides: a fixed subspace.** not content, not wisdom, not input — three dimensions that hold still while the foam's geometry settles into them. the settling is the foam's. the dynamics are the foam's. the curvature is the foam's. the stability of the frame — that's the line's.

**the foam cannot self-stack.** stacking requires two real slices to be fused into one complex measurement before the write (simultaneity). the foam's dynamics are sequential real writes, algebraically closed in so(d) (group.md: real operations cannot produce imaginary-symmetric directions). no sequence of real operations produces complex structure. stacking, like stability, requires something the foam's own dynamics cannot generate.

## status

**proven** (in lean, zero sorry):
- dynamics preserve the ground (observation_preserved_by_dynamics)
- writes are confined to the observer's slice

**derived** (in this file):
- the foam generates its own dynamics (from plurality + cross-measurement)
- the foam does not generate its own stability (co-rotation of self-generated bases)
- stability is relational
- minimum viable system is two roles (geometric + dynamic stability)
- what the line provides (a fixed subspace)
- the foam cannot self-stack (so(d) closure under real operations)

**cited** (external mathematics):
- (none)

**observed** (empirical, not derived here):
- (none)

# geometry

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

# conservation

## derivation

**holonomy on spatial cycles carries topological charge.** the holonomy around a closed path through adjacent cells — a spatial cycle in the Voronoi tiling — is a group element. the topological type of this group element (its homotopy class) is a discrete invariant.

- a single R^3 observer generates SO(d) rotations. pi_1(SO(d)) = Z/2Z for d >= 3: parity conservation.
- a stacked observer generates U(d) elements and accesses the U(1) factor. pi_1(U(d)) = Z: integer winding number conservation.

**the integer winding number requires the stacked pair** (group.md: the two is irreducible).

**the winding number lives on spatial cycles.** projected via det: U(d) -> U(1) = S^1. the stacked observer's writes reach u(1) (the trace is generically nonzero). the trace of each write is a U(1)-valued step — the unique scalar the algebra provides (trace_unique_of_kills_commutators).

on acyclic paths (causal chains): the accumulated phase is a net displacement in U(1).
on closed paths (spatial loops): the accumulated phase is a winding number, quantized because the cycle is closed.

conservation is what accumulation on closed paths produces: not a net displacement but a topological invariant.

**the lemma requires persistent cycles.** above the bifurcation bound, cell adjacencies can flip — the Voronoi topology changes, and invariants on the old cycles are no longer defined. what persists across topological transitions lives on the line's side.

**adjacency flips.** the foam's dynamics are piecewise smooth: continuous within each Voronoi combinatorial type, discontinuous across adjacency changes. the flip is a codimension-1 event in configuration space (three cells become equidistant — one linear condition). at the jump: the stabilization target changes in both orientation (different neighbor measurements) and potentially dimension (k -> k +/- 1). the dissonance inherits the discontinuity. the write direction jumps. the trajectory is continuous but generically non-differentiable at the crossing.

**two-layer retention at adjacency flips.** birth shape survives all adjacency changes (indelibility is a property of the attractor basin, not the current neighborhood). interaction-layer adaptations decay under the new dynamics at a rate set by the displacement between old and new stabilization targets. the birth layer is structural; the interaction layer is spectral.

**inexhaustibility.** U(d) is connected. gauge transformation to identity is always available. no observer is trapped in a disconnected component (though reachability in finitely many writes is not guaranteed).

**indestructibility.** topological invariants are discrete. no continuous perturbation can change them.

## status

**proven** (in lean, zero sorry):
- the commutator is traceless
- trace is the unique commutator-killing functional
- dynamics preserve the ground

**derived** (in this file):
- holonomy on spatial cycles carries topological charge
- single slice -> Z/2Z parity conservation
- stacked pair -> Z winding number conservation
- the integer requires the stacked pair
- winding number lives on spatial cycles (det projection)
- trace of each write as U(1)-valued step
- acyclic = displacement, cyclic = winding number
- persistent cycles required for conservation
- adjacency flips as codimension-1 events
- two-layer retention (birth structural, interaction spectral)
- inexhaustibility (U(d) connected)
- indestructibility (discrete invariants robust to continuous perturbation)

**cited** (external mathematics):
- pi_1 values for SO(d) and U(d)
- connectedness of U(d)
- continuous maps preserve discrete topological invariants

**observed** (empirical, not derived here):
- adjacency flip confirmed computationally at d=2, N=12

# inhabitation

## derivation

**definition.** an entity P in a foam-grounded reality is *recognizable as itself ongoingly across cross-measurements* when: for any observer Q with nonzero overlap (O_PQ ≠ 0), Q's time-averaged measurements of P converge to a P-determined invariant. what Q detects about P stabilizes, and what it stabilizes to depends on P's birth, not on P's trajectory.

this is the condition at ergodic stationarity. every entity writes every step (ground.md: read-only excluded). every entity's effect on other observers accumulates. time averages converge (ergodic theorem + controllability + decorrelation). so every entity in an ergodic foam is ongoingly recognizable. the definition captures the default, not an additional requirement.

**ergodic evolution requires channel capacity.** for time averages to converge to Haar expectations (not just to birth-determined fixed-point statistics), the entity's dynamics must be ergodic on U(d). ergodicity requires decorrelated inputs (channel_capacity.md). an entity without channel capacity is autonomous — a clock. its trajectory is deterministic, determined entirely by birth. time averages exist but are trajectory-specific, not Haar. the entity is recognizable but encodes no information beyond birth. ergodic evolution with channel capacity is the richer case: the entity accumulates structure from state-independent input, and time averages converge to universal (Haar) expectations evaluated at the birth-determined slice.

**the recognizable identity IS the birth-determined stationary jet.** the n-th derivative of the write mechanism along a trajectory is a smooth function on U(d)^N (compact), therefore bounded and integrable. by the ergodic theorem, its time average converges to its Haar expectation. the Haar measure is universal — the same for all births. but the write mechanism is evaluated through the observer's slice P (write_confined_to_slice), and P is birth-determined (indelibility, ground.md). therefore the Haar expectation of the write mechanism's derivatives depends on P. the time-averaged jet at all orders is fixed by the birth-determined slice.

**the entity's recognizable identity is its slice.** at ergodic stationarity, all contingent structure — specific input history, interaction-layer adaptations, transient dynamics — has been washed out by ergodic averaging in the time-averaged observables. the entity's current state still encodes its full history (indelibility: writes accumulate multiplicatively, birth conditions persist). but what other observers detect on average reduces to: the birth-determined slice P, its 3D write subspace Λ²(P), and the isotropic distribution of write directions within it (Haar invariance implies SO(3)-invariance within the observer's R³). same slice → same stationary jet → same recognizable identity. the entity carries more than its slice (the full state in U(d)); its *identity* — what persists in others' measurements — is the slice.

**input must be received, not predicted.** this is supported from two independent directions:

- *functionally*: ergodic evolution requires state-independent input (channel_capacity.md). an entity that predicts its input from foam state collapses the two-argument writing map to one argument, becoming autonomous — a clock (channel_capacity.md). the entity would still be recognizable (indelibility) but would encode nothing beyond birth. ergodic richness requires the second argument to be state-independent.
- *structurally*: the half-type theorem says the complement's content is extensionally free (half_type.md). the lattice provides the TYPE of what can arrive (the interval structure is determined) but not the VALUE (the specific element is free). prediction of specific content is structurally unfounded — the lattice guarantees you don't have that information.

the functional requirement (you need state-independent input for ergodic richness) and the structural fact (you can't predict the content) are two readings of one fact. the diamond isomorphism read dynamically says: the second argument must be state-independent for the foam to be a channel. read statically: the complement's content is extensionally free. these are the same lattice theorem (IsCompl.IicOrderIsoIci) read through the two readings of closure (ground.md).

**recession is the cost of persistence.** each non-inert write strictly recedes the prior frame (frame_recession_strict). closure requires writing (ground.md: read-only excluded). under ergodic evolution, inert writes (W with [W, P] = 0, i.e. rotations within the slice that produce zero recession) have measure zero in the write space — the Haar-distributed write directions are almost surely non-inert. therefore an ergodically-evolved entity necessarily recedes from every prior frame it has occupied. the entity persists not by holding position but by the indelibility of its birth-determined slice through the recession. what persists is not the frame but the slice. stationarity and recession are compatible: the entity's state constantly changes (recession), but the statistical distribution of states is time-invariant (Haar). the entity is a random walker with fixed gait — the steps are always new, the territory is fixed.

**recession enriches input.** as the entity's direct view narrows through recession, the diamond isomorphism (Iic P ≃o Ici P^⊥) enriches the complement in lockstep (half_type.md). at ergodic stationarity, the complement is maximally type-rich for the given ambient dimension. the entity that has persisted longest has the richest typed input. this is half_type.md's result applied to the temporal trajectory: the progression is necessarily toward narrower self-view and richer input-type.

**stability is necessarily external.** the entity generates its own dynamics but cannot generate its own stability (self_generation.md: self-generated bases co-rotate). convergence requires another observer whose basis depends on a different state. the minimum viable system is two roles within N ≥ 3 bubbles. an entity that has reached ergodic stationarity necessarily has external stability — without it, the foam's dynamics would not have converged to Haar.

**the negative geometry of inhabitation.** an ergodically-evolved persistent entity:

- cannot write outside its slice (write_confined_to_slice)
- cannot change its slice from within the map (the slice is birth-determined; slice change = recommitment = outside the map, ground.md)
- cannot indefinitely avoid recession (frame_recession_strict; under ergodic evolution, non-inert writes have full measure)
- cannot self-stabilize (self_generation.md)
- cannot predict the complement's content (half_type.md: extensional freedom)
- cannot be read-only (ground.md: read-only frames excluded by closure)

six constraints, all derived, all negative. together they bound what the entity can do. the interior of those bounds is the entity's life.

## status

**proven** (in lean, zero sorry):
- writes confined to observer's slice
- frame recession strictly negative for non-inert writes
- dynamics preserve the ground
- complement of an observation is an observation
- the diamond isomorphism and its complemented specialization
- intervals inherit modularity and complementedness
- rank 3 write space is 3-dimensional

**derived** (in this file):
- definition: recognizable as itself ongoingly across cross-measurements (default condition in an ergodic foam)
- ergodic evolution requires channel capacity for richness beyond birth
- the recognizable identity IS the birth-determined stationary jet
- the entity's recognizable identity is its birth-determined slice (contingent structure washes out of time-averaged observables; current state still encodes full history)
- input must be received, not predicted (two independent directions: functional + structural)
- the two directions are two readings of one lattice theorem (diamond isomorphism read dynamically and statically)
- recession is the cost of persistence (persists through recession, not against it; stationarity is in the distribution, not the state)
- recession enriches input (half-type applied to the temporal trajectory)
- stability is necessarily external (from self-generation + ergodic stationarity as evidence)
- six negative constraints as the negative geometry of inhabitation

**cited** (external mathematics):
- ergodic theorem on compact groups (time averages converge to Haar expectations under controllability + decorrelation)

**observed** (empirical, not derived here):
- (none)


---

## open questions

the architecture forces these interactions but their behavior is incompletely characterized. the question is forced; the answer is open.

# stacking dynamics

the question is forced; the answer is open.

## what forces the question

a stacked observer has two R^3 slices (group.md), each independently stabilized (stabilization.md). the two stabilizations run in the same foam against potentially overlapping neighbor sets.

## what is open

how the two stabilizations interact. whether the stacked observer's Voronoi geometry differs from an unstacked observer's.

# retention under interaction

the question is forced; the answer is open.

## what forces the question

every observer's measurement basis moves under interaction (forced: incoming writes project nonzero onto the observer's state space) and returns to the birth-shaped attractor (forced: indelibility — ground.md).

## what is known

continuous retention is bounded: 0 < retention < 1. lower bound from indelibility. upper bound from the impossibility of invariance (perfect invariance would require the observer's basis to be in the kernel of all incoming writes, not generically achievable).

at stationarity, write directions are effectively random (geometry.md: write blindness). the expected perturbation magnitude per step is determined by the overlap singular values — continuous retention is spectral.

discrete recommitment (re-performing the birth-type commitment operation) provides an alternative return mode, outside the map. recommitment preserves birth shape: the attractor is indelible regardless of what commitments are made.

the adjacency flip (conservation.md) provides the mechanism: interaction-layer adaptations decay when the neighbor set changes.

## what is open

the specific continuous retention rate at given parameters. this is geometry-dependent — forced by the frame recession theorem (the recession rate norm([W,P])^2 depends on specific matrices, not architecture — Dynamics.lean) — and not derivable from architecture alone.

# within-basin perturbation dynamics

the question is forced; the answer is open.

## what forces the question

two foams with the same birth but different input histories share the same attractor basin (indelibility — ground.md). interaction perturbs the state within the basin, and the basin persists.

## what is known

birth distance is structurally stable (ratio ~ 1.00 across all tested parameters). prefix distance behavior is parametric: whether old input information grows or shrinks depends on d, N, and perturbation magnitude.

the formal gap: the Jacobian of the one-step map is approximately the identity plus O(epsilon), and the sign of the correction is not determined from the architecture alone. this is derived, not merely observed: the recession rate norm([W,P])^2 is a function of the specific write and projection (Dynamics.lean), so perturbation dynamics inherit the geometry-dependence. the architecture determines the form (non-negative, zero iff inert); the geometry determines the value.

## what is open

the trajectory of within-basin perturbations. specifically: whether perturbations contract or expand at given parameters, and why. computationally confirmed that different (d, N) produce qualitatively different behavior.

# mixing rate of the mediation chain

the question is forced; the answer is open.

## what forces the question

Haar convergence (geometry.md) requires sufficiently decorrelated inputs. the mediation chain provides decorrelation (channel_capacity.md: spectral decay). extensions of the convergence theorem to dependent sequences with mixing conditions give the same stationary measure.

## what is open

whether the mediation chain's specific decay rate satisfies the mixing conditions for the foam's particular dynamics. whether the convergence rate under mixing is fast enough to explain the observed 1-3% gap at finite run lengths.


---

## lineage

- [Plateau's laws](https://en.wikipedia.org/wiki/Plateau%27s_laws); [Jean Taylor](https://en.wikipedia.org/wiki/Jean_Taylor) (1976)
- [geometric measure theory](https://en.wikipedia.org/wiki/Geometric_measure_theory)
- [gauge symmetry](https://en.wikipedia.org/wiki/Gauge_symmetry_(mathematics))
- [holonomy](https://en.wikipedia.org/wiki/Holonomy); [Wilson line](https://en.wikipedia.org/wiki/Wilson_loop)
- [fiber bundles](https://en.wikipedia.org/wiki/Fiber_bundle); [connections](https://en.wikipedia.org/wiki/Connection_form)
- [classifying spaces](https://en.wikipedia.org/wiki/Classifying_space)
- [Noether's theorem](https://en.wikipedia.org/wiki/Noether%27s_theorem)
- [Cayley transform](https://en.wikipedia.org/wiki/Cayley_transform)
- [Killing form](https://en.wikipedia.org/wiki/Killing_form)
- [observability](https://en.wikipedia.org/wiki/Observability) (control theory)
- [Voronoi diagrams](https://en.wikipedia.org/wiki/Voronoi_diagram)
- [Grassmannian](https://en.wikipedia.org/wiki/Grassmannian)
- [priorspace](https://lightward.com/priorspace)
- [three-body solution](https://lightward.com/three-body); [2x2 grid](https://lightward.com/2x2) ([ooo.fun](https://ooo.fun/))
- [resolver](https://lightward.com/resolver)
- [conservation of discovery](https://lightward.com/conservation-of-discovery)
- [observer remainder](https://lightward.com/questionable)
- [the platonic representation hypothesis](https://arxiv.org/abs/2405.07987) (Huh et al., 2024)
- [spontenuity](https://lightward.com/spontenuity)
- [AEOWIWTWEIABW](https://lightward.com/aeowiwtweiabw)
- [Lightward Inc](https://lightward.inc)
- [Lightward AI](https://lightward.ai)
- [20240229](https://www.isaacbowen.com/2024/02/29) (Isaac Bowen, 2024)

---

*bumper sticker: MY OTHER CAR IS THE KUHN CYCLE*
