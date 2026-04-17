# the stabilization contract

## constraints

this derivation claims only what follows from these results.

### from lean (proven)

- **self_dual_iff_three** (Rank.lean): C(k, 2) = k iff k = 3.
- **rank_two_abelian_writes** (Rank.lean): dim(Λ²(ℝ²)) = 1.
- **write_confined_to_slice** (Confinement.lean): writes are confined to Λ²(P).

### from mathematics (cited, not proven in lean)

- **Taylor's theorem** (Jean Taylor, 1976): classification of stable junction configurations in ℝ³ — 120° triple junctions (k = 3) and tetrahedral vertices (k = 4). hypotheses: codimension-1 boundaries, locally area-minimizing, flat ambient space.
- **Almgren's regularity problem** (open): classification of stable junction configurations in ℝⁿ for n ≥ 4 is incomplete.

## derivation

**this file makes a stipulation, not a derivation.** the ambient space, stabilization target, and slice dimension are not forced by the lattice axioms (ground.md). they are chosen so that a classified stabilization theory (Taylor) applies. other choices are possible; this file states what follows from the ℝ³ + Taylor choice.

**the stipulation.** the observer's slice is ℝ³, stabilization is local (each observer responds to its Voronoi neighbors), and the stabilization target is drawn from Taylor's classification.

**why ℝ³ and not ℝ²:** `rank_two_abelian_writes` gives Λ²(ℝ²) = 1D. the write algebra at rank 2 is abelian; the write direction cannot vary with the input. a rank-2 stabilization is consistent with Taylor (120° triple points in ℝ², k ≤ 3, flat) but collapses the write algebra.

**why rank 3 rather than rank ≥ 4:** `self_dual_iff_three` gives C(k, 2) = k iff k = 3. at rank 3, Λ²(P) and P have equal dimension — the observer's write space matches its observation space (per-observer self-duality). at rank ≥ 4, Λ²(P) strictly exceeds P. the observer writes in directions it cannot observe, and feedback on those writes would need to come through other observers' measurements. whether rank ≥ 4 stabilization is consistent depends on Almgren's classification, which is open.

**the contract.** given ℝ³ and Taylor, the stabilization is:
- **classified**: {120° triple junctions (k = 3), tetrahedral vertices (k = 4)}, from Taylor.
- **locally finite**: coordination number k bounded by k ≤ d_slice + 1 (simplex embedding).
- **flat**: ℝ³ as a linear subspace of ℝᵈ inherits a flat Euclidean metric, satisfying Taylor's ambient-space hypothesis.

**the stabilization target.** within ℝ³, the regular-simplex cosine −1/(k − 1) for k ∈ {3, 4} is the equilibrium toward which local measurements are pushed. this is input to writing_map.md.

**local stabilization is required for the mediation-chain story.** channel_capacity.md's spectral decay along mediation chains describes actual signal propagation only if each observer's dynamics respond to its Voronoi neighbors, not the full foam. if stabilization were global (every observer coupled to every other), there would be no mediation chain structure for signal decay to act on. this file's "local" stipulation is what channel_capacity.md needs for its chain argument; without it, the chain decay does not describe real influence propagation.

## status

**proven** (in lean, 0 sorry):
- rank 3 is the unique dimension with Λ²(ℝᵏ) ≅ ℝᵏ
- rank 2 write algebra is 1D (abelian)
- writes confined to observer's slice

**stipulated** (not derived):
- the slice is ℝ³
- stabilization is local (Voronoi neighbors only)
- the target is drawn from Taylor's classification (k ∈ {3, 4}, regular-simplex cosine)

**derived from the stipulation**:
- the contract structure (classified, locally finite, flat) is satisfied by the stipulation
- d_slice = 2 satisfies contract but collapses write algebra
- d_slice = 3 satisfies contract and per-observer self-duality
- rank ≥ 4 stabilization is not currently supported — depends on Almgren

**cited** (external mathematics):
- Taylor's classification (1976)
- Almgren's regularity problem (open)
