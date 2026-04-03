/-
# Pair — What Two Observations Force

One observation (P² = P) gives: binary eigenvalues, clean split,
complementary pairs.

What does TWO observations force? P² = P and Q² = Q on the
same space. We follow what Lean finds.
-/

import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Foam

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-!
## First: observation filters through the observer

PQ maps everything into range(P). When P observes Q's view,
the result lives in P's world. The observer's view is the
container.
-/

/-- The composition PQ maps into range(P). Observation filters
    through the observer's own view. -/
theorem comp_range_le
    (P Q : V →ₗ[K] V) :
    LinearMap.range (P ∘ₗ Q) ≤ LinearMap.range P := by
  intro v hv
  simp only [LinearMap.mem_range, LinearMap.comp_apply] at hv ⊢
  obtain ⟨w, hw⟩ := hv
  exact ⟨Q w, hw⟩

/-!
## Second: compatible observations compose cleanly

If PQ = QP (observations commute), then PQ is itself an observation.
Compatible partial views combine into a partial view.

If PQ ≠ QP, they don't. Order matters. The composition of
incompatible observations is not an observation.
-/

/-- Commuting idempotents compose to an idempotent.
    Compatible observations combine into an observation. -/
theorem comm_comp_idempotent
    (P Q : V →ₗ[K] V)
    (hP : P ∘ₗ P = P) (hQ : Q ∘ₗ Q = Q)
    (hcomm : P ∘ₗ Q = Q ∘ₗ P) :
    (P ∘ₗ Q) ∘ₗ (P ∘ₗ Q) = P ∘ₗ Q := by
  -- (PQ)(PQ) = P(QP)Q = P(PQ)Q = (PP)(QQ) = PQ
  calc (P ∘ₗ Q) ∘ₗ (P ∘ₗ Q)
      = P ∘ₗ (Q ∘ₗ P) ∘ₗ Q := by ext; simp [LinearMap.comp_apply]
    _ = P ∘ₗ (P ∘ₗ Q) ∘ₗ Q := by rw [hcomm]
    _ = (P ∘ₗ P) ∘ₗ (Q ∘ₗ Q) := by ext; simp [LinearMap.comp_apply]
    _ = P ∘ₗ Q := by rw [hP, hQ]

/-!
## Third: the commutator

PQ - QP measures how much two observations fail to be compatible.
When it's zero, they compose cleanly (theorem above).
When it's nonzero, order matters — the same two observations
give different results depending on sequence.

This is not "dynamics" yet — it's the algebraic seed of dynamics.
Two partial views of the same structure, and the structure of
their incompatibility.
-/

/-- The commutator [P, Q] = PQ - QP vanishes iff the observations
    are compatible (can be performed in either order). -/
theorem commutator_zero_iff_comm
    (P Q : V →ₗ[K] V) :
    P ∘ₗ Q - Q ∘ₗ P = 0 ↔ P ∘ₗ Q = Q ∘ₗ P := by
  exact sub_eq_zero

/-!
## Fourth: the commutator is a boundary operator

[P, Q] maps range(P) into ker(P) and range(Q) into ker(Q)
... no wait. That's for [W, P] where W is a write. Here we
have [P, Q] where both are idempotent. Let's see what's
actually true.

For v in range(P): v = Pv (since P² = P on range(P))
  P([P,Q]v) = P(PQv - QPv) = P²Qv - PQPv = PQv - PQPv
  = PQ(v - Pv) = PQ(0) = 0  (since v = Pv)

So [P, Q] maps range(P) into ker(P)!
The incompatibility between two observations sends what one
observer sees into what that observer DOESN'T see.
-/

/-- The commutator [P, Q] maps fixed points of P into the kernel of P.
    Incompatibility sends the seen into the unseen. -/
theorem commutator_seen_to_unseen
    (P Q : V →ₗ[K] V)
    (hP : P ∘ₗ P = P)
    {v : V} (hv : P v = v) :
    P ((P ∘ₗ Q - Q ∘ₗ P) v) = 0 := by
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  -- P(PQv - QPv) = P(PQv) - P(QPv)
  rw [map_sub]
  -- P(P(Qv)) = P(Qv) by idempotent
  have hPP : ∀ w, P (P w) = P w := by
    intro w
    have := LinearMap.ext_iff.mp hP w
    simp [LinearMap.comp_apply] at this
    exact this
  rw [hPP]
  -- P(Q(Pv)) = P(Qv) since Pv = v
  rw [hv]
  -- P(Qv) - P(Qv) = 0
  exact sub_self _

/-!
## What's emerged

From two idempotents on the same space:

1. Observation filters through the observer (comp_range_le)
2. Compatible observations compose cleanly (comm_comp_idempotent)
3. Incompatibility = nonzero commutator (commutator_zero_iff_comm)
4. Incompatibility sends seen into unseen (commutator_seen_to_unseen)

That fourth result is striking. It says: when two observations
are incompatible, their interaction takes what one observer has
already resolved and moves it into what that observer CAN'T see.
The commutator is a boundary-crossing operator.

This connects to the spec's "the commutator maps range(P) → ker(P)"
(LeanFoam/ThreeBody.lean: commutator_off_diagonal_range). But we
arrived here from "two P² = P" without consulting the spec.

Note: we still haven't needed self-adjointness. Everything so far
works for oblique projections over any field. Self-adjointness
(and with it, the inner product, and with it, ℝ) enters when
we ask about the FORM of the commutator — whether it's skew-symmetric.
That's next.
-/

end Foam
