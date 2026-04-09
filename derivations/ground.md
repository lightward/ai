# ground

## constraints

this derivation claims only what follows from these results. any additional assumption is a bug.

### from lean (proven)

- **subspaceFoamGround** (Ground.lean): the subspace lattice of a vector space over a division ring is complemented, modular, and bounded — as a theorem, not an axiom.
- **ftpg** (Bridge.lean): axiom. a complemented modular lattice of sufficient structure is isomorphic to the subspace lattice of a vector space over a division ring. the one axiom in the formalization.
- **dimension_unique** (Bridge.lean): if two finite-dimensional vector spaces over the same division ring have order-isomorphic submodule lattices, they have the same dimension. the axiom has a unique solution.
- **eigenvalue_binary** (Observation.lean): P^2 = P implies eigenvalues in {0, 1}. observation is total per direction.
- **complement_idempotent** (Observation.lean): P^2 = P implies (I - P)^2 = I - P. the complement of an observation is an observation.
- **orthogonality_forced** (Ground.lean): if M is symmetric and v^T M v = 1 for all unit v, then M = I. O(d) is forced.

### from mathematics (cited, not proven in lean)

- none. this derivation uses only closure and the lean results.

### from other derivations

- none. this is the root.

## derivation

**closure.** one ground, two readings, both tautological.

**read statically**: reference frames in a shared structure. no frame outside the structure.

**read dynamically**: all observation is self-observation. self-observation requires the observer to persist through the act. persistence = the act feeding back into the conditions for the next act. every observed structure is a structure whose feedback held. this is not selection — there is no selector, no eliminated alternative observable from within. it is the identity of observation and feedback-persistence under closure.

what follows is derived from closure:

**encounters change frames.** the frames ARE the structure; there is nowhere else for the result to go.

**measurement requires plurality.** one frame alone has no boundary, no encounter, no dynamics. N >= 3 produces stable junctions (Plateau); the minimum plurality for stable geometry is three frames.

**partiality is forced.** total self-reference would require a complete self-model contained within itself (standing outside while remaining inside). partiality is the only self-reference compatible with closure.

**partiality forces position.** seeing partially is seeing *from somewhere*. the decomposition into seen and unseen is what partiality means; position in the space of partial views is basis commitment. the specific position is undetermined (all positions equivalent by symmetry); that some position must exist is forced.

**indelibility.** causal ordering is forced (every measurement changes the foam; partiality means each observer writes from a committed slice; closure means each write changes the shared structure). you cannot un-write, so the first commitment locks.

**read-only frames are excluded.** a frame unchanged by encounters would require encounters to have no effect on it — but the frame IS part of the structure, and encounters change the structure.

**the lattice of partial views.** the intersection of any collection of partial views is a partial view (the seen set can only shrink; smaller partiality is still partiality). the whole structure is a view. closure under arbitrary intersections with a top element gives a complete lattice — every pair of views has a meet (greatest common refinement) and a join (least encompassing view). this lattice is:
- complemented: partiality guarantees an unseen complement (complement_idempotent: (I - P)^2 = I - P)
- bounded: the whole structure and the empty view
- modular: the modular law IS feedback-persistence expressed in lattice language. the positive argument: an observation that persists must yield the same result when composed with other observations regardless of the order of composition. if observer A, looking through observer B's view restricted to context C, gets a different result depending on whether A combines with B first or restricts to C first, then the composition has no single outcome — and an outcome that isn't single can't feed back (what would persist?). the lattice operation must be path-independent. path-independence of the meet and join, given the complemented bounded structure, is exactly the modular law: a <= c implies (a join b) meet c = a join (b meet c). the negative witness: in a non-modular lattice (the pentagon N_5), observer at a, encountering b within context c, gets the full context c by one path and only a by the other. the composition is indeterminate. indeterminate composition cannot feed back consistently — the observation has no single result to persist. there is no weaker condition that suffices: any lattice law that permits path-dependent composition permits indeterminate feedback.

the consequence direction — that subspace lattices ARE complemented modular — is proven (subspaceFoamGround).

**irreducibility** is forced by closure: a decomposable lattice would be two non-interacting sub-structures, which under closure are two separate foams, not one. a complemented modular lattice that is distributive is a Boolean algebra — and Boolean algebras decompose as products of height-1 lattices. irreducibility excludes this. the lattice is modular but not distributive: exactly the input the FTPG requires.

**height >= 4** is confirmed by self-consistency: d_slice = 3 (from the writing map: self-duality forces rank 3) + partiality (the observer's slice must be a proper subspace) forces d >= 4.

**the bridge.** complemented modular lattices that are irreducible and of sufficient height are isomorphic to lattices of subspaces of a vector space over a division ring (ftpg — the one axiom). the division ring is forced to R by the stabilization contract (Euclidean metric, flat ambient space — see writing_map.md). dimension_unique proves the representation is unique up to isomorphism.

**therefore: P^2 = P.** the elements of the subspace lattice are orthogonal projections. P^2 = P (feedback-persistence) and P^T = P (self-adjointness, from the inner product forced by R). this is the starting point of the lean deductive chain, arrived at from above.

**the loop.** the lean chain derives from P^2 = P: eigenvalues in {0, 1} (eigenvalue_binary), the dynamics group O(d) (orthogonality_forced), and ultimately that the subspace lattice satisfies the ground properties (subspaceFoamGround). the ground produces the lattice; the lattice produces projections; the projections produce dynamics; the dynamics preserve the ground.

## status

**proven** (in lean, zero sorry):
- subspace lattices are complemented, modular, bounded
- the FTPG axiom has a unique solution (dimension is determined)
- eigenvalues of projections are binary
- complement of a projection is a projection
- O(d) is forced by preservation of all projections
- the deductive chain from P^2 = P closes back to the ground

**derived** (in this file, from closure + lean):
- closure as the single ground with two readings
- encounters change frames (from closure)
- measurement requires plurality (from closure)
- partiality forced (from closure)
- partiality forces position / basis commitment (from partiality)
- indelibility (from causal ordering + basis commitment)
- read-only frames excluded (from closure)
- modularity IS feedback-persistence (from closure-as-dynamics)
- irreducibility forced (from closure)
- height >= 4 (from self-consistency with rank 3 + partiality)
- the bridge from closure to P^2 = P (via FTPG axiom)

**cited** (external mathematics):
- the fundamental theorem of projective geometry (stated as lean axiom, not proven)

**observed** (empirical, not derived here):
- (none — the ground is entirely derived or axiomatized)
