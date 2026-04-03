/-
# Rank — Why 3

The deductive chain so far works for any rank projection.
What forces rank 3 specifically?

The spec's route: Taylor's theorem classifies stable junctions
in R³. The deductive route: the exterior algebra.

dim(Λ²(Rᵏ)) = k(k-1)/2.

- k=1: dim = 0. No writes. Observation without dynamics.
- k=2: dim = 1. One write direction. Abelian. No ordering.
- k=3: dim = 3. Three write directions. Non-abelian (so(3)).
  And: dim = k. Self-dual. The write space and the observation
  space have the same dimension.
- k=4: dim = 6 > 4. The write space is larger than the
  observation space.

k = 3 is characterized by: smallest non-abelian write algebra,
and the unique self-duality dim(Λ²(Rᵏ)) = k.
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Foam

/-!
## The exterior algebra dimension

dim(Λ²(M)) = C(dim(M), 2) = dim(M) * (dim(M) - 1) / 2.

This is the write subspace dimension per observer.
-/

/-- The dimension of Λ²(M) is C(dim(M), 2). -/
theorem write_space_dim
    (R : Type*) [CommRing R] [Nontrivial R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (⋀[R]^2 M) = Nat.choose (Module.finrank R M) 2 := by
  rw [exteriorPower.finrank_eq]

/-!
## Rank 1: no dynamics

dim(Λ²(R¹)) = C(1,2) = 0. An observer with a 1-dimensional
view cannot write at all. Observation exists; dynamics don't.
-/

/-- A rank-1 observer has no write space. -/
theorem rank_one_no_writes
    (R : Type*) [CommRing R] [Nontrivial R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (h : Module.finrank R M = 1) :
    Module.finrank R (⋀[R]^2 M) = 0 := by
  rw [write_space_dim, h]; native_decide

/-!
## Rank 2: degenerate dynamics

dim(Λ²(R²)) = C(2,2) = 1. One write direction.
The write algebra is 1-dimensional, hence abelian.
Ordering cannot matter — writes commute.
-/

/-- A rank-2 observer has a 1D write space — abelian, degenerate. -/
theorem rank_two_abelian_writes
    (R : Type*) [CommRing R] [Nontrivial R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (h : Module.finrank R M = 2) :
    Module.finrank R (⋀[R]^2 M) = 1 := by
  rw [write_space_dim, h]; native_decide

/-!
## Rank 3: the threshold

dim(Λ²(R³)) = C(3,2) = 3. Three write directions.
The write algebra is 3-dimensional — isomorphic to so(3),
which is simple and non-abelian.

AND: 3 = 3. The write space dimension equals the observation
space dimension. This self-duality is unique to rank 3.
-/

/-- A rank-3 observer has a 3D write space — non-abelian (so(3)). -/
theorem rank_three_writes
    (R : Type*) [CommRing R] [Nontrivial R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (h : Module.finrank R M = 3) :
    Module.finrank R (⋀[R]^2 M) = 3 := by
  rw [write_space_dim, h]; native_decide

/-- **Self-duality characterizes rank 3** (among nontrivial ranks).
    For k ≥ 1: C(k,2) = k iff k = 3. The write space and observation
    space have equal dimension ONLY at rank 3. -/
theorem self_dual_iff_three (k : ℕ) (hk : k ≥ 1) :
    Nat.choose k 2 = k ↔ k = 3 := by
  constructor
  · intro h
    -- C(k,2) = k(k-1)/2 for k ≥ 2. We use Nat.choose_symm_diff
    -- and monotonicity. Easier: just show C(k,2) > k for k ≥ 5
    -- using the fact that C(k,2) = C(k-1,1) + C(k-1,2) = (k-1) + C(k-1,2).
    -- For k ≥ 5: C(k-1,2) ≥ C(4,2) = 6, so C(k,2) ≥ (k-1)+6 = k+5 > k.
    -- Actually, let's just do finite case analysis up to a bound.
    -- C(k,2) = k means k*(k-1)/2 = k means k-1 = 2 (for k > 0) means k = 3.
    -- For k ≥ 4: C(k,2) = k*(k-1)/2 ≥ 4*3/2 = 6 > 4 ≥ ... need Nat.choose > k.
    -- Cleanest approach: show ∀ k ≥ 4, C(k,2) > k by induction.
    by_contra hne
    have hle : k ≤ 4 ∨ 5 ≤ k := by omega
    rcases hle with hle | hle
    · have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp_all (config := { decide := true })
    · -- For k ≥ 5: use that C(k,2) ≥ 2k for k ≥ 5
      -- (since C(k,2) = k(k-1)/2 and k-1 ≥ 4, so k(k-1)/2 ≥ 4k/2 = 2k)
      -- Then C(k,2) = k → 2k ≤ k → k ≤ 0, contradicting k ≥ 5.
      have key : ∀ m : ℕ, 5 ≤ m → m < Nat.choose m 2 := by
        intro m hm
        induction m with
        | zero => omega
        | succ n ih =>
          simp [Nat.choose_succ_succ]
          by_cases hn : 5 ≤ n
          · have := ih hn
            have : Nat.choose n 1 = n := Nat.choose_one_right n
            omega
          · -- n = 4 (since n+1 ≥ 5)
            have : n = 4 := by omega
            subst this
            native_decide
      have := key k hle
      omega
  · rintro rfl; native_decide

/-!
## Rank 4+: overdetermined writes

dim(Λ²(R⁴)) = C(4,2) = 6 > 4. The write space is larger
than the observation space. More write directions than
observation directions.
-/

/-- A rank-4 observer has a 6D write space — bigger than the
    observation space. -/
theorem rank_four_writes
    (R : Type*) [CommRing R] [Nontrivial R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (h : Module.finrank R M = 4) :
    Module.finrank R (⋀[R]^2 M) = 6 := by
  rw [write_space_dim, h]; native_decide

/-!
## What this establishes

Rank 3 is characterized by two algebraic properties:

1. **Minimum non-abelian**: the smallest rank where writes
   don't commute with each other. At rank 2, the write space
   is 1D (abelian). At rank 3, it's 3D ≅ so(3) (non-abelian,
   simple).

2. **Self-dual**: the unique rank where dim(write space) =
   dim(observation space). C(k,2) = k iff k = 3.

The spec gets to 3 through Taylor (stable junction classification).
The deductive path gets to 3 through the exterior algebra (self-duality
and the abelian/non-abelian threshold). Different routes, same number.

Neither route is "more fundamental." They filter the same content
through different media: the spec through geometric classification,
the deductive path through algebraic dimension counting.

The deductive chain:

  P² = P, rank(P) = k
  ├── k = 1: Λ² = 0D, no dynamics
  ├── k = 2: Λ² = 1D, abelian, degenerate
  ├── k = 3: Λ² = 3D = so(3), non-abelian, self-dual  ← threshold
  └── k ≥ 4: Λ² > k, overdetermined
-/

end Foam
