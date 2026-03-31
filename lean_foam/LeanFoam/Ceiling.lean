/-
# Combinatorial Ceiling

N unitaries cannot all be pairwise maximally distant.

## The claim (from spec, "geometry" section)

"the achievable maximum is √(N/(2(N−1))) of the theoretical maximum,
depending only on N (from Cauchy-Schwarz + ‖ΣUᵢ‖² ≥ 0)."

## The derivation

For N equal-norm vectors with equal pairwise inner products c:
  ‖Σᵢ xᵢ‖² ≥ 0  →  N·a + N·(N-1)·c ≥ 0  →  c ≥ -a/(N-1)

For unitaries: a = d, D² = 2d - 2c, giving D² ≤ 2Nd/(N-1).
D_max² = 4d, so D/D_max ≤ √(N/(2(N-1))).
-/

import Mathlib.Analysis.InnerProductSpace.Basic

namespace FoamSpec

/-- The algebraic core of the combinatorial ceiling:
    if N · a + N · (N - 1) · c ≥ 0, then c ≥ -a / (N - 1).
    From ‖Σxᵢ‖² ≥ 0 expanded. -/
theorem combinatorial_ceiling_core
    {N a c : ℝ} (hN : 2 ≤ N)
    (h : N * a + N * (N - 1) * c ≥ 0) :
    c * (N - 1) ≥ -a := by
  have hN0 : (0 : ℝ) < N := by linarith
  nlinarith

/-- The distance form: D² ≤ 2·N·a/(N-1).
    For unitaries (a = d): the achievable maximum ratio is √(N/(2(N-1))).  -/
theorem combinatorial_ceiling_distance
    {N a D_sq : ℝ} (hN : 2 ≤ N)
    (h : N * a + N * (N - 1) * (a - D_sq / 2) ≥ 0) :
    D_sq * (N - 1) ≤ 2 * N * a := by
  -- h says: N*a + N*(N-1)*a - N*(N-1)*D_sq/2 ≥ 0
  -- i.e., N²*a ≥ N*(N-1)*D_sq/2
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  nlinarith [mul_pos hN0 hN1]

end FoamSpec
