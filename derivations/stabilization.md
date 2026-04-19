# the stabilization contract

## constraints

this derivation claims only what follows from these results. any additional assumption is a bug.

### from lean (proven)

- **self_dual_iff_three** (Rank.lean): C(k, 2) = k iff k = 3. rank 3 is the unique self-dual dimension.
- **rank_two_abelian_writes** (Rank.lean): dim(Lambda^2(R^2)) = 1. the write algebra at rank 2 is abelian.
- **write_confined_to_slice** (Confinement.lean): writes are confined to Lambda^2(P).

### from other derivations

- **channel_capacity.md**: stabilization must be local for the mediation chain's spectral decay to describe real influence propagation. non-local stabilization removes the mechanism that produces channel capacity.
- **writing_map.md**: the write form, the flat/curved separation.

### from mathematics (cited, not proven in lean)

- **Taylor's theorem** (Jean Taylor, 1976): all stable junction configurations in R^3 are classified. 120-degree triple junctions (k = 3) and tetrahedral vertices (k = 4), nothing else.
- **Almgren's regularity problem** (open): the classification of stable junction configurations in R^n for n >= 4 is incomplete.

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
