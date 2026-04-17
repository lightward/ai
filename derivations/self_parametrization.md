# self-parametrization

## constraints

this derivation claims only what follows from these results.

### from lean (proven)

- **two_persp** (FTPGCoord.lean): the shared two-perspectivity composition pattern. `two_persp Γ r₁ s₁ r₂ s₂ = (r₁ ⊓ s₁ ⊔ r₂ ⊓ s₂) ⊓ l`.
- **coord_add_eq_two_persp** (FTPGCoord.lean): `coord_add` factors through `two_persp` by `rfl`. bridge: m.
- **coord_mul_eq_two_persp** (FTPGMul.lean): `coord_mul` factors through `two_persp` by `rfl`. bridge: O ⊔ C.
- **coord_add_left_zero, coord_add_right_zero** (FTPGCoord.lean): O is the additive identity.
- **coord_mul_left_one, coord_mul_right_one** (FTPGMul.lean): I is the multiplicative identity.
- **CoordSystem** (FTPGCoord.lean): the data (O, U, I, V, C) with C off l and m, in the plane.
- **IsCompl.IicOrderIsoIci** (Mathlib): the diamond isomorphism. perspectivities between lines in the projective plane instantiate order isomorphisms between atom-intervals.
- **OrderIso.trans** (Mathlib): order isomorphisms compose.

### from mathematics (cited, not proven in lean)

- **FTPG (classical)**: the coordinate ring is determined up to isomorphism by the lattice. different choices of (O, U, I, C) yield isomorphic rings.

## derivation

**the two_persp functor.** both `coord_add` and `coord_mul` factor through the same composition of two perspectivities. the pattern: form two points p₁ = r₁ ⊓ s₁ and p₂ = r₂ ⊓ s₂ from pairs of lines, join them, project onto l. different choices of the four line arguments yield different binary operations on l.

perspectivities between lines are order isomorphisms between atom-intervals (this is the content of the diamond isomorphism specialized to the projective plane). composition of two perspectivities is an `OrderIso.trans`. `two_persp` is therefore a projectivity — a composition of two order isomorphisms — and the coordinate operations are specific instantiations of it.

**bridge parameters.** the choice of bridge line and "zero" point determines which operation `two_persp` becomes. with l the coordinate line and m a distinct line through U (the point at infinity on l), three non-degenerate pairings of points from {O, U, I} ⊂ l generate three operations:

| pair (P, Q) | bridge | zero | identity | operation |
|---|---|---|---|---|
| (U, O) | q = U ⊔ C | E = (O ⊔ C) ⊓ m | O | addition |
| (O, I) | O ⊔ C | E_I = (I ⊔ C) ⊓ m | I | multiplication |
| (U, I) | q = U ⊔ C | E_I = (I ⊔ C) ⊓ m | I | translated addition |

pairings with Q = U collapse (zero becomes U, the point at infinity — operation is trivial).

**parameter space.** P and Q need not be distinguished points. any (P, Q) with P ≠ Q and Q ≠ U gives a valid `two_persp` operation. the parameter space is {(P, Q) ∈ l × l : P ≠ Q, Q ≠ U}. atoms on l serve both as operands and as parameters.

**the external input C.** C is the one element not drawn from l. it lies in the plane, off l and m. changing C changes the coordinate system; by FTPG, different choices of C yield isomorphic coordinate rings.

**concrete identities proven in lean.** both coordinate operations factor through `two_persp` by `rfl`:

    coord_add a b = two_persp Γ (a ⊔ C) m (b ⊔ E) q
    coord_mul a b = two_persp Γ (O ⊔ C) (b ⊔ E_I) (a ⊔ C) m

the bridge line is the only structural difference between addition and multiplication in this formulation.

## status

**proven** (in lean, 0 sorry):
- `two_persp` factorization of `coord_add` and `coord_mul` (both by `rfl`)
- additive identity: O + b = b, a + O = a
- multiplicative identity: I · a = a, a · I = a
- zero annihilation: O · b = O, a · O = O

**derived** (in this file):
- the parameter space for `two_persp` operations as {(P, Q) ∈ l × l : P ≠ Q, Q ≠ U}
- three non-degenerate pairings of {O, U, I} correspond to addition, multiplication, translated addition
- changing C (cited from FTPG) yields an isomorphic coordinate ring

**open**:
- formalize the (U, I) translated-addition operation in lean
- verify the translated-addition conjecture: op_{U,I}(a, b) = a + b − 1 in coordinates
- characterize which (P, Q) pairs yield group operations
