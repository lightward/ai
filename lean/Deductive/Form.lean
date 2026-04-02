/-
# Form — Self-Adjointness and the Skew-Symmetric Commutator

Up to now: P² = P over any field, no inner product.
Three theorems from one observation, four from two.

Now we introduce self-adjointness: Pᵀ = P. The observation
"looks the same from both sides." This requires a notion of
transpose (inner product / bilinear form).

What new structure does this force? We work with matrices
(where transpose is concrete) to keep it grounded.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul

namespace Deductive

open Matrix

variable {n : Type*} [Fintype n]

/-!
## The commutator of self-adjoint matrices is skew-symmetric

If P and Q are symmetric (Pᵀ = P, Qᵀ = Q), then
[P, Q]ᵀ = (PQ - QP)ᵀ = QP - PQ = -[P, Q].

The incompatibility of two self-consistent observations is
skew-symmetric. It has the form of a Lie algebra element.

This is where the write map's skew-symmetry comes from — not
from a design choice about U(d), but from the structure of
two observations interacting. The group choice is forced by
the ground.
-/

/-- The commutator of symmetric matrices is skew-symmetric.
    Two self-adjoint observations interact antisymmetrically.

    This is the algebraic origin of the write map's form:
    observation × observation → Lie algebra element. -/
theorem commutator_skew_of_symmetric
    {R : Type*} [CommRing R]
    (P Q : Matrix n n R)
    (hP : Pᵀ = P) (hQ : Qᵀ = Q) :
    (P * Q - Q * P)ᵀ = -(P * Q - Q * P) := by
  rw [transpose_sub, transpose_mul, transpose_mul, hP, hQ]
  simp [neg_sub]

/-!
## The commutator of self-adjoint idempotents is traceless

tr(PQ - QP) = tr(PQ) - tr(QP) = 0 by cyclicity of trace.

This is actually true for ANY two matrices (proven in
LeanFoam/Algebra.lean). But in this context it means:
the interaction of two observations produces something
invisible to the scalar readout.

Combined with skew-symmetry: the interaction lives in su(d),
not u(d). The conserved direction is ALGEBRAICALLY UNREACHABLE
by observation-observation interaction.
-/

/-- The commutator of any two matrices is traceless.
    (Restated here in the deductive context: observation
    interaction is invisible to the scalar channel.) -/
theorem commutator_traceless
    {R : Type*} [CommRing R]
    (P Q : Matrix n n R) :
    trace (P * Q - Q * P) = 0 := by
  rw [trace_sub, trace_mul_comm]
  exact sub_self _

/-!
## Self-adjoint idempotent = orthogonal projection

When Pᵀ = P and P² = P, the matrix IS an orthogonal projection.
These two conditions together are what "observation" means in the
inner product setting:
- P² = P: feedback-persistence (observing the observed = the observed)
- Pᵀ = P: self-consistency (the observation looks the same from both sides)

The range and kernel are orthogonal complements. The "unseen" is
not just disjoint from the "seen" — it's PERPENDICULAR.
-/

-- Signpost: seen_unseen_orthogonal
-- For self-adjoint idempotent P: if Pv = v and Pw = 0, then v · w = 0.
-- The seen and unseen are perpendicular. Formulation TBD (inner product
-- on matrix-vector spaces needs care in Lean).

/-!
## What's emerged

Introducing self-adjointness (Pᵀ = P) alongside idempotency (P² = P):

1. The commutator [P,Q] is skew-symmetric (commutator_skew_of_symmetric)
2. The commutator is traceless (commutator_traceless)
3. Seen and unseen are perpendicular (signposted, not yet formalized)

Result 1 is where the write map lives. Not because we chose U(d)
and derived skew-symmetry — but because two self-adjoint observations
interacting PRODUCES skew-symmetry. The Lie algebra structure is
forced by the ground.

Result 2 says: observation interaction can't reach the scalar
(conserved) direction. Conservation isn't imposed — it's what
two observations algebraically CAN'T do.

The deductive chain so far:

  P² = P                    (feedback-persistence)
  ├── eigenvalues ∈ {0,1}   (observation is binary per direction)
  ├── range ∩ ker = {0}     (clean split)
  ├── (I-P)² = I-P          (complement is an observation)
  │
  Two P² = P
  ├── PQ ⊆ range(P)         (filtering)
  ├── PQ=QP → (PQ)²=PQ      (compatibility → composition)
  ├── [P,Q] ≠ 0 ↔ ordering  (incompatibility = sequence matters)
  ├── [P,Q]: seen → unseen   (incompatibility crosses the boundary)
  │
  Pᵀ = P (self-adjointness)
  ├── [P,Q]ᵀ = -[P,Q]       (interaction is skew-symmetric)
  └── tr[P,Q] = 0            (interaction is invisible to scalar channel)

Next: what does having THREE observations force?
Or: what does the RANK of P force (why 3)?
-/

end Deductive
