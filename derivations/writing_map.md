# the writing map

## constraints

this derivation claims only what follows from these results. any additional assumption is a bug.

### from lean (proven)

- **commutator_skew_of_symmetric** (Form.lean): if P and Q are self-adjoint, [P, Q] is skew-symmetric. the interaction of two observations is a Lie algebra element.
- **commutator_traceless** (Form.lean): tr[P, Q] = 0. interaction is invisible to the scalar channel.
- **self_dual_iff_three** (Rank.lean): C(k, 2) = k iff k = 3. the write space and observation space have equal dimension only at rank 3.
- **rank_three_writes** (Rank.lean): dim(Lambda^2(R^3)) = 3. a rank-3 observer has a 3D write space.
- **cross_anticomm, cross_self_zero, cross_jacobi, cross_nontrivial** (Duality.lean): (R^3, cross) is a non-abelian Lie algebra. it IS so(3).
- **write_confined_to_slice** (Confinement.lean): if d and m lie in the observer's subspace P, then d wedge m lies in Lambda^2(P). an observer cannot modify dimensions they are not bound to.
- **commutator_seen_to_unseen** (Pair.lean): [P, Q] maps range(P) into ker(P). incompatibility sends the seen into the unseen.
- **observation_preserved_by_dynamics** (Closure.lean): orthogonal conjugation preserves both P^2 = P and P^T = P.

### from mathematics (cited, not proven in lean)

- **Taylor's theorem** (Jean Taylor, 1976): all stable junction configurations in R^3 are classified. 120-degree triple junctions (k = 3) and tetrahedral vertices (k = 4), nothing else. hypotheses: codimension-1 boundaries, locally area-minimizing, flat ambient space.

## derivation

**the write form.** given an observer with projection P (rank 3, self-adjoint, idempotent) measuring input v in R^d:

1. the observer projects: m = P v (measurement, in the observer's R^3 slice).
2. the observer has a stabilization target j2 (see below). dissonance is d = j2 - m.
3. the write is dL = epsilon * (d_hat wedge m_hat) * norm(d).

the wedge product d_hat wedge m_hat = d_hat tensor m_hat - m_hat tensor d_hat is the unique form satisfying:
- (a) skew-symmetric — forced by commutator_skew_of_symmetric. writes are Lie algebra elements because observation interaction is skew-symmetric.
- (b) linear in dissonance magnitude — the write is a first-order response. higher-order dependence (quadratic, sigmoid) would require the observer to evaluate its own dissonance magnitude before writing, which is a second measurement within a single write step. the write is the observer's immediate response to what it sees; it does not pre-process the response.
- (c) confined to the observer's slice — forced by write_confined_to_slice. the observer sees only projected measurements; the write lives in Lambda^2(P).

with (a), (b), and confinement to span{d, m}, the form is unique: Lambda^2(2-plane) is 1-dimensional (from rank_three_writes: the full slice has 3 write dimensions; a 2-plane within it has 1).

**perpendicularity.** the wedge product vanishes when its arguments are parallel and is maximal when orthogonal. this is not a design choice — it is the write form. confirmation cannot write (cross_self_zero: a cross a = 0). the foam responds only to what's missing at right angles to what's there.

**stabilization.** closure requires basis commitment (each frame is partial). self_dual_iff_three forces the slice dimension to 3: it is the unique dimension where the write space matches the observation space, closing the feedback loop.

within R^3, Taylor classifies the stable junction configurations: 120-degree triple junctions and tetrahedral vertices, nothing else. Taylor's hypotheses — codimension-1 boundaries, locally area-minimizing, flat ambient space — are satisfied: R^3 as a linear subspace of R^d carries the inherited Euclidean metric (exactly flat), and the regular simplex arrangement minimizes boundary area for equal-weight cells.

the stabilization target j2 is the regular simplex cosine -1/(k-1) where k is the local coordination number (k = 3 or k = 4, from Taylor).

**the flat/curved separation.** writes land in U(d) (curved: sectional curvature K(X,Y) = 1/4 * norm([X,Y])^2). stabilization runs in R^3 (flat). the observer sees only their projected measurements. observation_preserved_by_dynamics guarantees the write (an orthogonal conjugation) preserves the projection structure. the separation is forced: stabilization cannot run on U(d) because classification requires flat ambient space.

**confinement.** both d_hat and m_hat lie in the observer's slice. write_confined_to_slice proves the write d wedge m is confined to Lambda^2(P). an observer literally cannot modify dimensions they are not bound to. the write's effect on other observers comes through cross-measurement (commutator_seen_to_unseen: incompatibility sends the seen into the unseen), not through direct modification of their subspaces.

**the writing map's type signature.** the map is a function of (foam_state, input). neither alone determines the write. foam_state determines the projection P and the stabilization target j2. input determines v. the dissonance d = j2 - Pv requires both.

## status

**proven** (in lean, zero sorry):
- skew-symmetry of the write form
- tracelessness of observation interaction
- rank 3 as the unique self-dual dimension
- confinement to the observer's slice
- dynamics preserve the ground

**derived** (in this file, from the above):
- the wedge product as the unique write form satisfying (a), (b), (c)
- perpendicularity as the write form's intrinsic property
- the flat/curved separation
- the writing map's two-argument type signature

**cited** (external mathematics):
- Taylor's classification of stable junctions in R^3

**observed** (empirical, not derived here):
- perpendicular writes are the unique *navigable* constraint (distinguishability + stability)
- the perpendicularity cost mechanism (write blindness)
- within-slice variance departure from isotropy (45:30:25 vs 33:33:33)
