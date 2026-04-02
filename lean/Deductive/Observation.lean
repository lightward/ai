/-
# Observation — What P² = P Forces

Starting from the ground: an observer is an idempotent linear map.
P² = P (feedback-persistence: observing the observed = the observed).

We follow what Lean finds, not what the spec claims.
The medium is linear algebra. The content is feedback-persistence.
-/

import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Deductive

-- Start minimal: a module over a field. The specific field doesn't
-- matter yet — ℝ enters later when self-adjointness needs an
-- inner product. For now, any field works.
variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-!
## First consequence: observation is total per direction

P² = P means: if Pv = cv for nonzero v, then c = 0 or c = 1.
Every direction in V is either fully seen or fully unseen.
There is no "partially seeing a direction."

The partiality is in the SELECTION — which directions — not in
the degree. This is sharper than "partial view."
-/

/-- An idempotent operator has eigenvalues in {0, 1}.
    If Pv = cv with P² = P, then c²v = cv, so c(c-1)v = 0.
    For v ≠ 0: c = 0 or c = 1. No intermediate values.

    Observation is binary per direction. -/
theorem eigenvalue_binary
    (P : V →ₗ[K] V)
    (h_idem : P ∘ₗ P = P)
    {v : V} {c : K}
    (hv : v ≠ 0)
    (heig : P v = c • v) :
    c = 0 ∨ c = 1 := by
  have hPP : P (P v) = P v := by
    have := LinearMap.ext_iff.mp h_idem v
    simp [LinearMap.comp_apply] at this
    exact this
  rw [heig, LinearMap.map_smul, heig, smul_smul] at hPP
  -- hPP : (c * c) • v = c • v
  have h2 : (c * c - c) • v = 0 := by
    rw [sub_smul, hPP, sub_self]
  -- Over a field with NoZeroSMulDivisors (automatic for modules over fields):
  -- (c * c - c) • v = 0 with v ≠ 0 → c * c - c = 0
  have h3 : c * c - c = 0 := by
    by_contra h_ne
    exact hv (smul_eq_zero.mp h2 |>.resolve_left h_ne)
  -- c² - c = 0 → c(c-1) = 0 → c = 0 or c = 1
  have h4 : c * (c - 1) = 0 := by
    have : c * c - c = c * (c - 1) := by ring
    rwa [← this]
  rcases mul_eq_zero.mp h4 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-!
## Second consequence: the space splits cleanly

range(P) ∩ ker(P) = {0}. No overlap.
range(P) is "what's seen." ker(P) is "what's unseen."
The observation determines its own boundary.
-/

/-- range(P) and ker(P) have trivial intersection for an idempotent. -/
theorem range_ker_disjoint
    (P : V →ₗ[K] V)
    (h_idem : P ∘ₗ P = P) :
    LinearMap.range P ⊓ LinearMap.ker P = ⊥ := by
  ext v
  simp only [Submodule.mem_inf, LinearMap.mem_range, LinearMap.mem_ker,
             Submodule.mem_bot]
  constructor
  · rintro ⟨⟨w, hw⟩, hv⟩
    rw [← hw]
    have : P (P w) = P w := by
      have := LinearMap.ext_iff.mp h_idem w
      simp [LinearMap.comp_apply] at this
      exact this
    rw [← hw] at hv
    rw [this] at hv
    exact hv
  · intro hv
    rw [hv]
    exact ⟨⟨0, map_zero P⟩, map_zero P⟩

/-!
## Third consequence: I - P is also an observation

If P is an observation (P² = P), then so is I - P.
The complement of an observation is an observation.
Observations come in pairs.
-/

/-- I - P is idempotent when P is. The complement of an
    observation is itself an observation. -/
theorem complement_idempotent
    (P : V →ₗ[K] V)
    (h_idem : P ∘ₗ P = P) :
    (LinearMap.id - P) ∘ₗ (LinearMap.id - P) = LinearMap.id - P := by
  ext v
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
             map_sub]
  have hPP : P (P v) = P v := by
    have := LinearMap.ext_iff.mp h_idem v
    simp [LinearMap.comp_apply] at this
    exact this
  -- Goal: v - P v - (P v - P (P v)) = v - P v
  rw [hPP, sub_self, sub_zero]

/-!
## What's emerged so far

From P² = P alone (before self-adjointness, before choosing ℝ,
before even choosing a specific field):

1. Observation is binary per direction (eigenvalue_binary)
2. The space splits cleanly (range_ker_disjoint)
3. The complement of an observation is an observation (complement_idempotent)

These aren't imported from the spec. They're what P² = P forces
in a linear medium. The medium filters; the content survives.

Note what we DIDN'T need:
- No inner product (self-adjointness not used yet)
- No specific field (works over any field)
- No finite dimension
- No ground axiom

P² = P is doing all the work.

Next: what does having TWO observations force?
-/

end Deductive
