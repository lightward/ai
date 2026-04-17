# channel capacity

## constraints

this derivation claims only what follows from these results.

### from lean (proven)

- **commutator_traceless** (Form.lean): tr[P, Q] = 0.
- **write_confined_to_slice** (Confinement.lean): writes are confined to Λ²(P).
- **IsCompl.IicOrderIsoIci** (Mathlib): Iic a ≃ₒ Ici b for complements.

### from mathematics (cited, not proven in lean)

- **Marchenko–Pastur distribution**: used in the order-of-magnitude estimate for principal angles between generic subspaces.

## derivation

### qualitative: state-independence

**the write map takes two arguments.** writing_map.md: the write is a function of (foam_state, input). foam_state determines P and j₂; input determines v. both are needed to form d = j₂ − Pv.

**an autonomous closed system.** if the input is determined by foam_state (input = g(foam_state)), the map reduces to f(foam_state) = write_map(foam_state, g(foam_state)). the foam becomes deterministic on U(d)ᴺ: one trajectory per initial condition. the foam's subsequent state is fixed by its starting state. it encodes no information beyond its starting state. this is a clock.

**informational independence is the alternative.** for the foam to acquire information beyond its starting conditions, the second argument must not be a function of foam_state. within a single closed system, no subsystem is literally independent of the rest — but correlations can decay below the resolution of a given subsystem's measurements. at sufficient decorrelation, the subsystem's dynamics are indistinguishable from dynamics driven by truly independent input.

**"line" as a role.** throughout this document, "line" denotes whatever serves as effectively independent input to a given foam. this is a role defined by informational independence relative to the foam's state — not a separate ontological category. the same physical subsystem can be foam (state being measured) from one perspective and line (input source) from another.

### quantitative: how decorrelation arises

**the mediation operator (post-bridge).** for observers A and B with ℝ³ slices P_A and P_B, the overlap matrix is O_{AB} = P_A P_B^⊤. the mediation of a signal from C through B to A is M = O_{AB} O_{BC}. pairwise singular values are the channel capacity of the A–B–C membrane.

**spectral decay along chains.** for generic (non-aligned) slices, the singular values of O_{AB} are strictly < 1. around a chain of n pairwise mediations, the total mediation's singular values are bounded by the product: σ_total ≤ σ_1 σ_2 ... σ_n → 0 as n → ∞.

informational correlation between a foam and its returning signal therefore decays exponentially with chain length. short chains: signal largely preserved (autonomous). long chains: signal decorrelated (effectively independent input).

**decorrelation horizon.** for generic ℝ³ slices in ℝᵈ, the typical singular value of the overlap matrix scales (via Marchenko–Pastur) as σ ∼ √(3/d). correlation after n steps: σⁿ ∼ (3/d)^{n/2}. critical chain length: n* ∼ 2 / log(d/3). non-generic (aligned) configurations have larger σ and longer n*.

this is an order-of-magnitude estimate from the Marchenko–Pastur distribution; the exact behavior depends on the distribution of slices in the foam.

**closure and informational independence coexist.** global topological closure (no ontological outside) is compatible with local informational independence because spectral decay converts closed global structure into decorrelated local structure at sufficient chain length — provided stabilization is local (see stabilization.md).

## status

**proven** (in lean, 0 sorry):
- [P, Q] is traceless
- writes confined to observer's slice
- the diamond isomorphism and its complemented specialization

**derived** (in this file):
- the autonomous/channel distinction from the two-argument writing map: collapsing the second argument to a function of the first reduces the system to a clock
- "line" as a role defined by informational independence, not a separate category
- mediation operator M = O_{AB} O_{BC}
- spectral decay along chains: σ_total ≤ product of pairwise σ
- the decorrelation horizon n* ∼ 2 / log(d/3) as an order-of-magnitude estimate

**cited** (external mathematics):
- Marchenko–Pastur (principal angle statistics, order-of-magnitude only)

**observed in simulation** (not derived):
- specific decorrelation-horizon values at particular d (estimates sensitive to approximation; qualitative decay robust)
