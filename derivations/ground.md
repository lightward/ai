# ground

## constraints

this derivation claims only what follows from these results.

### from lean (proven)

- **subspaceFoamGround** (Ground.lean): the subspace lattice of a vector space over a division ring is complemented, modular, and bounded.
- **ftpg** (Bridge.lean): axiom (being eliminated). a complemented modular lattice of sufficient structure is isomorphic to the subspace lattice of a vector space over a division ring.
- **dimension_unique** (Bridge.lean): if two finite-dimensional vector spaces over the same division ring have order-isomorphic submodule lattices, they have the same dimension.
- **eigenvalue_binary** (Observation.lean): P² = P implies eigenvalues in {0, 1}.
- **complement_idempotent** (Observation.lean): P² = P implies (I − P)² = I − P.
- **rank_two_abelian_writes** (Rank.lean): rank 2 → 1D write space.
- **orthogonality_forced** (Ground.lean): if M is symmetric and vᵀMv = 1 for all unit v, then M = I.
- **observation_preserved_by_dynamics** (Closure.lean): orthogonal conjugation preserves both P² = P and Pᵀ = P.

### from mathematics (cited, not proven in lean)

- **Dedekind's characterization**: a lattice is modular iff it contains no sublattice isomorphic to N₅.

## derivation

**the loop.** the following implications form a circular chain. each arrow is either mechanically verified, cited from standard mathematics, or explicitly stipulated:

```
complemented modular lattice, irreducible, height ≥ 4
  ↓ ftpg (axiom — bridge in progress, 0 sorry so far)
L ≅ Sub(D, V) for some division ring D
  ↓ stipulation: D = ℝ (see below)
elements are orthogonal projections: P² = P, Pᵀ = P
  ↓ deductive chain in lean (14 files, 0 sorry)
  ↓ eigenvalues binary, O(d) forced, dynamics preserve the ground
Sub(ℝ, V) is complemented, modular, bounded
  ↑ subspaceFoamGround (proven) — closes the circle
```

the chain is a circle only if the D = ℝ step is granted. in the current state, that step is a modeling stipulation, not a theorem (see below).

**fixed-point uniqueness.** each of the four lattice properties — complemented, modular, irreducible, height ≥ 4 — is the tightest constraint at which the chain remains a fixed point. weaken any one and the chain breaks:

- **modular**: Dedekind's theorem says modular = no N₅. in N₅, the composition a ∧ (b ∨ c) can differ from (a ∧ b) ∨ c, i.e. lattice operations are path-dependent. strengthening modular to distributive makes the lattice Boolean, which decomposes into height-1 factors — too narrow for rank ≥ 2 projections.
- **complemented**: without complements, `complement_idempotent` has no home — there is no I − P to witness.
- **irreducible**: if L ≅ L₁ × L₂, the factors are independent systems, not one lattice.
- **height ≥ 4**: rank 2 collapses the write algebra (`rank_two_abelian_writes`); the observer's slice being a proper subspace (rank ≥ 3, strict) forces ambient dimension d ≥ 4.

the height ≥ 4 bound is partially downstream: it uses rank_two_abelian_writes, which holds over ℝ. in spirit, the lower bound is imposed by what the chain needs to carry, not by the lattice axioms in isolation.

**stipulation: D = ℝ.** FTPG returns L ≅ Sub(D, V) for some division ring D. the value of D is not determined by the lattice. this document, and the lean chain downstream of the bridge, stipulate D = ℝ. the choice is motivated by the downstream target: real orthogonal projections, inner products, Lie algebras over ℝ. formalizing a derivation of D = ℝ from internal constraints (if one exists) would require additional structure not currently identified. `dimension_unique` shows the representation is unique up to isomorphism once D is fixed; it does not fix D.

**therefore (conditional on D = ℝ): P² = P.** the elements of Sub(ℝ, V) under the inner product are orthogonal projections. from P² = P and Pᵀ = P, the lean chain derives eigenvalues in {0, 1} (`eigenvalue_binary`), forces the dynamics group to O(d) (`orthogonality_forced`), and closes the circle via `subspaceFoamGround`: the subspace lattice satisfies the original lattice axioms.

## status

**proven** (in lean, 0 sorry):
- subspace lattices are complemented, modular, bounded
- under FTPG, dimension is determined
- eigenvalues of projections are binary
- complement of a projection is a projection
- O(d) is forced by preservation of all projections
- dynamics preserve the ground (orthogonal conjugation preserves P² = P and Pᵀ = P)

**identified** (in this file, as arguments from the proven results):
- the circular loop: lattice axioms ↔ Sub(D, V) ↔ P² = P ↔ O(d)-dynamics ↔ lattice axioms
- fixed-point uniqueness argument for each of: modular, complemented, irreducible, height ≥ 4

**stipulated** (not derived):
- D = ℝ. motivated by downstream targets; not forced by the lattice alone.

**cited** (external mathematics):
- FTPG (stated as lean axiom, not yet proven)
- Dedekind's N₅ characterization of modularity
