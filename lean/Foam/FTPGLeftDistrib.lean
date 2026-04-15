/-
# Left distributivity (Part VII-D)
a · (b + c) = a·b + a·c

## Proof architecture (2026-04-13)

Single forward Desargues application, center σ_b on k = O⊔C.

### Setup
  s  = b + c           (von Staudt addition on l)
  σ_x = k ⊓ (x⊔E_I)   (perspectivity l → k, center E_I)
  d_a = (a⊔C) ⊓ m      (multiplication center on m)
  a·x = (σ_x ⊔ d_a) ⊓ l  (multiplication = perspectivity composition)

### Desargues configuration
  Center: σ_b on k.
  T1 = (C,  ab, U)   — C on k, ab on l, U on l⊓m
  T2 = (E, d_a, W')  — E on k⊓m, d_a on m,
                        W' = (σ_b⊔U) ⊓ (ac⊔E)

  Perspective from σ_b:
    C  ↔ E   via k (= C⊔E, contains σ_b)
    ab ↔ d_a via σ_b⊔d_a (multiplication line, contains ab)
    U  ↔ W'  via σ_b⊔U (contains W' by definition)

### Concurrence lemma (prerequisite)
  W' = (σ_b⊔U) ⊓ (ac⊔E) lies on σ_s⊔d_a.
  Therefore d_a⊔W' = σ_s⊔d_a, so (d_a⊔W')⊓l = a·s.

### Desargues axis
  1. (C⊔ab)  ⊓ (E⊔d_a)  = (ab⊔C) ⊓ m    — l-addition projection
  2. (C⊔U)   ⊓ (E⊔W')   = (ac⊔E) ⊓ q    — l-addition return center
  3. (ab⊔U)  ⊓ (d_a⊔W') = a·s            — the target

  Desargues: these three are collinear. Since a·s ∈ l:
    a·(b+c) = ((ab⊔C)⊓m ⊔ (ac⊔E)⊓q) ⊓ l = ab + ac.  ∎

## Note on multiplication order

The dilation_ext Γ c is a collineation for RIGHT multiplication x↦x·c.
Left multiplication x↦a·x is NOT a single collineation in the non-
commutative case. This is why left distrib requires a different proof
from right distrib (which used collineation directly).

## Status (session 108, 2026-04-15)
2 sorry (h_axis₂₃ skeleton compiling with 6 sub-sorry, h_desargues_conclusion).

### Sorry list
  - σ_b≠σ_s: PROVEN (session 107).
  - h_axis₂₃ (line ~1232): SKELETON COMPILING (session 108).
    Architecture: Level 2 Desargues using Q=σ_b to lift (s₂₃,E,R) out of R⊔m.
    ALL THREE axis conditions free at Level 2 (verified 180/180 in GF(7)).
    Recursion terminates. 6 sub-sorry remaining (mechanical + Desargues + projection).
  - h_desargues_conclusion (line ~1687): forward Desargues (~500 lines mechanical).

### Key insight (session 108): the recursion terminates

  h_axis₂₃ (the coplanarity da' ≤ ac⊔σ_s⊔E') is proved by a SECOND application
  of desargues_converse_nonplanar (already proven), this time in R⊔m:

  Level 2 (in R⊔m, rank 3 → lift to rank 4):
    T1 = (E', U', d_a) in R⊔m
    T2 = (s₂₃, E, R) in R⊔m (to be lifted)
    Lift T2 using Q = σ_b (outside R⊔m, in π):
      s₂₃'' on σ_b⊔s₂₃ (free choice via h_irred)
      E'' = (s₁₂⊔s₂₃'') ⊓ (σ_b⊔E)  — threaded through s₁₂
      R'' = (S₁₃⊔s₂₃'') ⊓ (σ_b⊔R)  — threaded through S₁₃
    Axis conditions:
      1. (E'⊔U') ⊓ (s₂₃''⊔E'') = s₁₂  ✓ FREE (modular law)
      2. (U'⊔d_a) ⊓ (E''⊔R'') = S₂₃   ✓ FREE (modular law)
      3. (E'⊔d_a) ⊓ (s₂₃''⊔R'') = S₁₃ ✓ FREE (modular law)
    Conclusion → vertex-joins concurrent → da' ∈ E'⊔s₂₃
    Project via σ_b back to R⊔m → da' ≤ E'⊔s₂₃ → h_axis₂₃

  Level 1 (original, uses h_axis₂₃ from Level 2):
    desargues_converse_nonplanar → W' ≤ σ_s⊔d_a → left distributivity

  WHY σ_b works: σ_b is the perspectivity center that Level 1 threading consumed
  (s₁₂ = (σ_b⊔ac)⊓m, E' threaded through s₁₂). Using it as the Level 2 lift
  direction means the Level 2 threading inherits Level 1's structure — the two
  levels are the same Desargues seen from ranks 3 and 4 respectively.

### Previous insights (sessions 106-107)
  - Billboard sprite: self-reference is representational (rank distinction dissolves it)
  - 2-of-3 structural invariant across architectures
  - Direct modular-law proof resists: composition of two perspectivity chains IS Desargues
  - det(E', s₂₃, da') = -ts₂u₂D + ts₂u₂D = 0 (identical cancellation, structural)
dilation_ext_fixes_m proven.
-/
import Foam.FTPGNeg

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-! ## Step 1: Dilation fixes m pointwise -/

/-- The dilation σ_a fixes points on m: for P on m with P ∉ l,
    dilation_ext Γ a P = P. Proof: (I⊔P)⊓m = P by line_direction
    (I ∉ m, P ≤ m). Then dilation_ext = (O⊔P) ⊓ (a⊔P) = P by
    modular_intersection (a ∉ O⊔P since P ∉ l). -/
theorem dilation_ext_fixes_m (Γ : CoordSystem L)
    {a P : L} (ha : IsAtom a) (hP : IsAtom P)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hP_on_m : P ≤ Γ.U ⊔ Γ.V)
    (ha_ne_O : a ≠ Γ.O) (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) :
    dilation_ext Γ a P = P := by
  unfold dilation_ext
  -- Step 1: (I⊔P)⊓m = P by line_direction (I ∉ m, P ≤ m)
  have hIP_inf_m : (Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V) = P :=
    line_direction Γ.hI Γ.hI_not_m hP_on_m
  rw [hIP_inf_m]
  -- Goal: (O⊔P) ⊓ (a⊔P) = P
  -- By modular_intersection: (P⊔O)⊓(P⊔a) = P when ¬ a ≤ P⊔O
  rw [show Γ.O ⊔ P = P ⊔ Γ.O from sup_comm _ _, show a ⊔ P = P ⊔ a from sup_comm _ _]
  have hO_ne_P : Γ.O ≠ P := fun h => hP_not_l (h ▸ le_sup_left)
  have ha_ne_P : a ≠ P := fun h => hP_not_l (h ▸ ha_on)
  have ha_not_PO : ¬ a ≤ P ⊔ Γ.O := by
    intro h
    -- a ≤ P⊔O and a ≤ l = O⊔U. So a ≤ l ⊓ (P⊔O).
    -- P ∉ l, O ≤ l, O ≤ P⊔O, so l ⊓ (P⊔O) = O by modular_intersection.
    -- Hence a ≤ O, so a = O. Contradiction.
    have hU_ne_P : Γ.U ≠ P := fun h' => hP_not_l (h' ▸ le_sup_right)
    have h_int : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ P) = Γ.O :=
      modular_intersection Γ.hO Γ.hU hP Γ.hOU hO_ne_P hU_ne_P hP_not_l
    have ha_le_O : a ≤ Γ.O := by
      have h' : a ≤ Γ.O ⊔ P := (sup_comm P Γ.O) ▸ h
      exact (le_inf ha_on h').trans h_int.le
    exact ha_ne_O ((Γ.hO.le_iff.mp ha_le_O).resolve_left ha.1)
  exact modular_intersection hP Γ.hO ha hO_ne_P.symm ha_ne_P.symm
    (Ne.symm ha_ne_O) ha_not_PO

/-! ## Non-planar converse Desargues

If two non-coplanar triangles have corresponding sides meeting on a
common line (the axis), then the joins of corresponding vertices are
concurrent. This is the converse of the non-planar Desargues theorem.

The proof uses three auxiliary planes ρ₁₂, ρ₁₃, ρ₂₃, each spanned by
two vertices of T1 and one of T2. The axis condition forces the
remaining T2 vertex into each plane. The concurrence point O lives in
all three planes, hence on all three vertex-joins. -/
theorem desargues_converse_nonplanar
    {a₁ a₂ a₃ b₁ b₂ b₃ : L}
    (ha₁ : IsAtom a₁) (ha₂ : IsAtom a₂) (ha₃ : IsAtom a₃)
    (hb₁ : IsAtom b₁) (hb₂ : IsAtom b₂) (hb₃ : IsAtom b₃)
    -- T1 non-degenerate (a₁ off the line a₂⊔a₃)
    (ha₁₂ : a₁ ≠ a₂) (ha₁₃ : a₁ ≠ a₃) (_ha₂₃ : a₂ ≠ a₃)
    (ha₁_not : ¬ a₁ ≤ a₂ ⊔ a₃)
    -- b_i not in πA = a₁⊔a₂⊔a₃ (non-coplanarity)
    (hb₁_not : ¬ b₁ ≤ a₁ ⊔ a₂ ⊔ a₃)
    (hb₂_not : ¬ b₂ ≤ a₁ ⊔ a₂ ⊔ a₃)
    (_hb₃_not : ¬ b₃ ≤ a₁ ⊔ a₂ ⊔ a₃)
    -- T2 non-degenerate
    (hb₁₂ : b₁ ≠ b₂) (hb₁₃ : b₁ ≠ b₃) (hb₂₃ : b₂ ≠ b₃)
    -- a₃ ≠ b₃ (vertex-join is a line)
    (_hab₃ : a₃ ≠ b₃)
    -- a₃⊔b₃ ⋖ ρ₁₃ (line covered by plane — derivable from non-degeneracy,
    -- but stated as hypothesis for modularity)
    (h_cov₁₃ : a₃ ⊔ b₃ ⋖ a₁ ⊔ a₃ ⊔ b₁)
    -- Axis: side-intersections are atoms (non-degenerate sides)
    (hs₁₂ : IsAtom ((a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂)))
    (hs₁₃ : IsAtom ((a₁ ⊔ a₃) ⊓ (b₁ ⊔ b₃)))
    (hs₂₃ : IsAtom ((a₂ ⊔ a₃) ⊓ (b₂ ⊔ b₃))) :
    -- Conclusion: vertex-joins concurrent
    (a₁ ⊔ b₁) ⊓ (a₂ ⊔ b₂) ≤ a₃ ⊔ b₃ := by
  -- ═══ Step 1: Auxiliary planes ═══
  set πA := a₁ ⊔ a₂ ⊔ a₃
  set ρ₁₂ := a₁ ⊔ a₂ ⊔ b₁  -- plane through a₁, a₂, b₁
  set ρ₁₃ := a₁ ⊔ a₃ ⊔ b₁  -- plane through a₁, a₃, b₁
  set ρ₂₃ := a₂ ⊔ a₃ ⊔ b₂  -- plane through a₂, a₃, b₂
  -- ═══ Helper: axis point forces b into ρ ═══
  -- If s = (a_i⊔a_j)⊓(b_i⊔b_j) is an atom, s ≤ ρ, b_i ≤ ρ, and s ≠ b_i,
  -- then b_j ≤ ρ (since b_i⊔s = b_i⊔b_j by CovBy, and both ≤ ρ).
  -- We apply this three times with different indices.
  have axis_forces : ∀ {p q r ρ : L}, IsAtom p → IsAtom q → p ≠ q →
      IsAtom ((r) ⊓ (p ⊔ q)) → (r) ⊓ (p ⊔ q) ≤ ρ → p ≤ ρ →
      (r) ⊓ (p ⊔ q) ≠ p →
      q ≤ ρ := by
    intro p q r ρ hp hq hpq hs hs_le hp_le hs_ne
    -- p ⊔ s = p ⊔ q (CovBy: s atom ≤ p⊔q, s ≠ p, p ⋖ p⊔q)
    have h_lt : p < p ⊔ r ⊓ (p ⊔ q) :=
      lt_of_le_of_ne le_sup_left (fun h =>
        hs_ne ((hp.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hs.1))
    have h_eq : p ⊔ r ⊓ (p ⊔ q) = p ⊔ q :=
      ((atom_covBy_join hp hq hpq).eq_or_eq h_lt.le
        (sup_le le_sup_left inf_le_right)).resolve_left (ne_of_gt h_lt)
    exact le_sup_right.trans (h_eq ▸ sup_le hp_le hs_le)
  -- ═══ Step 2: b₂ ∈ ρ₁₂ ═══
  have hb₂_in_ρ₁₂ : b₂ ≤ ρ₁₂ :=
    axis_forces hb₁ hb₂ hb₁₂ hs₁₂
      (inf_le_left.trans le_sup_left) le_sup_right
      (fun h => hb₁_not (h ▸ inf_le_left |>.trans le_sup_left))
  -- ═══ Step 3: b₃ ∈ ρ₁₃ ═══
  have hb₃_in_ρ₁₃ : b₃ ≤ ρ₁₃ :=
    axis_forces hb₁ hb₃ hb₁₃ hs₁₃
      (inf_le_left.trans (sup_le (le_sup_left.trans le_sup_left)
        (le_sup_right.trans le_sup_left)))
      le_sup_right
      (fun h => hb₁_not (h ▸ inf_le_left |>.trans
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right)))
  -- ═══ Step 4: b₃ ∈ ρ₂₃ ═══
  have hb₃_in_ρ₂₃ : b₃ ≤ ρ₂₃ :=
    axis_forces hb₂ hb₃ hb₂₃ hs₂₃
      (inf_le_left.trans le_sup_left) le_sup_right
      (fun h => hb₂_not (h ▸ inf_le_left |>.trans
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right)))
  -- ═══ Step 5: O ≤ ρ₁₃ and O ≤ ρ₂₃ ═══
  -- O = (a₁⊔b₁) ⊓ (a₂⊔b₂).
  -- a₁⊔b₁ ≤ ρ₁₃: a₁ ≤ ρ₁₃ and b₁ ≤ ρ₁₃.
  have hO_ρ₁₃ : (a₁ ⊔ b₁) ⊓ (a₂ ⊔ b₂) ≤ ρ₁₃ :=
    inf_le_left.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  -- a₂⊔b₂ ≤ ρ₂₃: a₂ ≤ ρ₂₃ and b₂ ≤ ρ₂₃.
  have hO_ρ₂₃ : (a₁ ⊔ b₁) ⊓ (a₂ ⊔ b₂) ≤ ρ₂₃ :=
    inf_le_right.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  -- ═══ Step 6: ρ₂₃ ⊓ ρ₁₃ ≥ a₃ ⊔ b₃ and ρ₂₃ ⊓ ρ₁₃ ≤ a₃ ⊔ b₃ ═══
  -- a₃ ≤ ρ₂₃ (via a₂⊔a₃ ≤ ρ₂₃) and a₃ ≤ ρ₁₃ (via a₁⊔a₃ ≤ ρ₁₃).
  -- b₃ ≤ ρ₂₃ (step 4) and b₃ ≤ ρ₁₃ (step 3).
  -- So a₃⊔b₃ ≤ ρ₂₃ ⊓ ρ₁₃.
  -- For equality: need ρ₂₃ ⊓ ρ₁₃ ≤ a₃⊔b₃ (the hard direction).
  -- This uses CovBy: ρ₁₃ and ρ₂₃ are planes, a₃⊔b₃ is a line in both.
  -- If ρ₁₃ ≠ ρ₂₃: two distinct planes → meet is a line.
  have ha₃_both : a₃ ≤ ρ₂₃ ⊓ ρ₁₃ := le_inf
    ((le_sup_right.trans le_sup_left : a₃ ≤ ρ₂₃))
    ((le_sup_right.trans le_sup_left : a₃ ≤ ρ₁₃))
  have hb₃_both : b₃ ≤ ρ₂₃ ⊓ ρ₁₃ := le_inf hb₃_in_ρ₂₃ hb₃_in_ρ₁₃
  have h_lb : a₃ ⊔ b₃ ≤ ρ₂₃ ⊓ ρ₁₃ := sup_le ha₃_both hb₃_both
  -- Upper bound: CovBy + ρ₂₃ ≠ ρ₁₃.
  -- a₃⊔b₃ ⋖ ρ₁₃ (hypothesis). ρ₂₃⊓ρ₁₃ ≤ ρ₁₃. ρ₂₃⊓ρ₁₃ ≠ ρ₁₃.
  -- By CovBy: ρ₂₃⊓ρ₁₃ = a₃⊔b₃.
  have h_ub : ρ₂₃ ⊓ ρ₁₃ ≤ a₃ ⊔ b₃ := by
    -- Show ρ₂₃⊓ρ₁₃ ≠ ρ₁₃ (otherwise a₂ ≤ ρ₁₃, contradicting non-degeneracy)
    have h_ne : ρ₂₃ ⊓ ρ₁₃ ≠ ρ₁₃ := by
      intro h_eq
      -- h_eq : ρ₂₃ ⊓ ρ₁₃ = ρ₁₃ means ρ₁₃ ≤ ρ₂₃
      have hρ₁₃_le : ρ₁₃ ≤ ρ₂₃ := inf_eq_left.mp (inf_comm ρ₂₃ ρ₁₃ ▸ h_eq)
      -- a₁ ≤ ρ₁₃ ≤ ρ₂₃ = a₂⊔a₃⊔b₂.
      have ha₁_ρ₂₃ : a₁ ≤ ρ₂₃ := (le_sup_left.trans le_sup_left : a₁ ≤ ρ₁₃).trans hρ₁₃_le
      -- a₁ ≤ ρ₂₃ = a₂⊔a₃⊔b₂ and a₁ ≤ πA = a₁⊔a₂⊔a₃.
      -- ρ₂₃ ⊓ πA ≥ a₂⊔a₃ (both ≤ ρ₂₃ and πA).
      -- By modular law (a₂⊔a₃ ≤ πA):
      -- πA ⊓ ρ₂₃ = πA ⊓ ((a₂⊔a₃)⊔b₂) = (a₂⊔a₃) ⊔ (πA⊓b₂)
      -- πA⊓b₂ = ⊥ (b₂ ∉ πA). So πA⊓ρ₂₃ = a₂⊔a₃.
      have hπA_ρ₂₃ : (a₁ ⊔ a₂ ⊔ a₃) ⊓ ρ₂₃ = a₂ ⊔ a₃ := by
        show (a₁ ⊔ a₂ ⊔ a₃) ⊓ (a₂ ⊔ a₃ ⊔ b₂) = a₂ ⊔ a₃
        have h_le : a₂ ⊔ a₃ ≤ a₁ ⊔ a₂ ⊔ a₃ :=
          sup_le (le_sup_right.trans le_sup_left) le_sup_right
        rw [inf_comm]
        -- Goal: (a₂ ⊔ a₃ ⊔ b₂) ⊓ (a₁ ⊔ a₂ ⊔ a₃) = a₂ ⊔ a₃
        rw [sup_inf_assoc_of_le b₂ h_le]
        -- Goal: (a₂ ⊔ a₃) ⊔ b₂ ⊓ (a₁ ⊔ a₂ ⊔ a₃) = a₂ ⊔ a₃
        have : b₂ ⊓ (a₁ ⊔ a₂ ⊔ a₃) = ⊥ :=
          (hb₂.le_iff.mp inf_le_left).resolve_right
            (fun h => hb₂_not (h ▸ inf_le_right))
        rw [this, sup_bot_eq]
      -- a₁ ≤ ρ₂₃ and a₁ ≤ πA, so a₁ ≤ πA⊓ρ₂₃ = a₂⊔a₃
      have ha₁_le_a₂a₃ : a₁ ≤ a₂ ⊔ a₃ :=
        (le_inf (le_sup_left.trans le_sup_left : a₁ ≤ a₁ ⊔ a₂ ⊔ a₃) ha₁_ρ₂₃).trans
          hπA_ρ₂₃.le
      -- a₁ ≤ a₂⊔a₃ contradicts non-degeneracy (would make T1 degenerate)
      -- a₁ atom ≤ a₂⊔a₃ → a₁ = a₂ or a₁ = a₃ (if a₂ ≠ a₃)
      exact ha₁_not ha₁_le_a₂a₃
    -- Apply CovBy: a₃⊔b₃ ≤ ρ₂₃⊓ρ₁₃ ≤ ρ₁₃, a₃⊔b₃ ⋖ ρ₁₃, ρ₂₃⊓ρ₁₃ ≠ ρ₁₃.
    exact ((h_cov₁₃.eq_or_eq h_lb inf_le_right).resolve_right h_ne).le
  -- ═══ Conclusion ═══
  exact (le_inf hO_ρ₂₃ hO_ρ₁₃).trans (le_antisymm h_lb h_ub ▸ le_refl _)

/-! ## The left distributivity theorem -/

/-- **Left distributivity: a · (b + c) = a·b + a·c.**

Single forward Desargues, center σ_b = (O⊔C)⊓(b⊔E_I) on k = O⊔C.
Triangles T1 = (C, ab, U) and T2 = (E, d_a, W') where W' = (σ_b⊔U)⊓(ac⊔E).
The Desargues axis passes through (ab⊔C)⊓m, (ac⊔E)⊓q, and a·(b+c),
giving a·(b+c) = ((ab⊔C)⊓m ⊔ (ac⊔E)⊓q) ⊓ l = ab + ac. -/
theorem coord_mul_left_distrib (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hbc : b ≠ c)
    -- Non-degeneracy conditions for the sum and products
    (hs_ne_O : coord_add Γ b c ≠ Γ.O) (hs_ne_U : coord_add Γ b c ≠ Γ.U)
    (hab_ne_O : coord_mul Γ a b ≠ Γ.O) (hab_ne_U : coord_mul Γ a b ≠ Γ.U)
    (hac_ne_O : coord_mul Γ a c ≠ Γ.O) (hac_ne_U : coord_mul Γ a c ≠ Γ.U)
    (hab_ne_ac : coord_mul Γ a b ≠ coord_mul Γ a c)
    (has_ne_O : coord_mul Γ a (coord_add Γ b c) ≠ Γ.O)
    (has_ne_U : coord_mul Γ a (coord_add Γ b c) ≠ Γ.U)
    (habac_ne_O : coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) ≠ Γ.O)
    (habac_ne_U : coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_mul Γ a (coord_add Γ b c) =
      coord_add Γ (coord_mul Γ a b) (coord_mul Γ a c) := by
  -- ═══════════════════════════════════════════════════════
  -- PROOF ARCHITECTURE (two independent pieces)
  --
  -- Piece 1 (Forward Desargues, center σ_b):
  --   T1=(C,ab,U), T2=(E,d_a,W') where W'=(σ_b⊔U)⊓(ac⊔E)
  --   Conclusion: (d_a⊔W')⊓l = ab+ac
  --
  -- Piece 2 (Concurrence — lattice computation):
  --   W' ≤ σ_s⊔d_a
  --   Therefore d_a⊔W' = σ_s⊔d_a, so (d_a⊔W')⊓l = a·s
  --
  -- Combination: a·s = (d_a⊔W')⊓l = ab+ac ∎
  -- ═══════════════════════════════════════════════════════
  set l := Γ.O ⊔ Γ.U with hl_def
  set m := Γ.U ⊔ Γ.V with hm_def
  set q := Γ.U ⊔ Γ.C with hq_def
  set k := Γ.O ⊔ Γ.C with hk_def
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ_def
  set s := coord_add Γ b c with hs_def
  set ab := coord_mul Γ a b with hab_def
  set ac := coord_mul Γ a c with hac_def
  -- Key intermediate atoms on the bridge k = O⊔C
  set σ_b := (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) with hσb_def  -- π₁(b)
  set σ_c := (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) with hσc_def  -- π₁(c)
  set σ_s := (Γ.O ⊔ Γ.C) ⊓ (s ⊔ Γ.E_I) with hσs_def  -- π₁(b+c)
  set d_a := (a ⊔ Γ.C) ⊓ m with hda_def                 -- multiplication center on m
  -- Desargues witness
  set W' := (σ_b ⊔ Γ.U) ⊓ (ac ⊔ Γ.E) with hW'_def
  -- ═══ Piece 2: Concurrence ═══
  -- W' = (σ_b⊔U) ⊓ (ac⊔E) lies on σ_s⊔d_a.
  -- Proof: converse planar Desargues via 3D lift.
  --   T1 = (σ_b, ac, σ_s) spans π.
  --   T2 = (U, E, d_a) on m (degenerate).
  --   Side-intersections trivially on m.
  --   Lift T2 to T2' outside π using R.
  --   Non-planar converse Desargues → lifted vertex-joins concurrent at O'.
  --   Project O' back to π → W on σ_b⊔U, ac⊔E, AND σ_s⊔d_a.
  have h_concurrence : W' ≤ σ_s ⊔ d_a := by
    -- ═══ Setup: Definitions and basic facts ═══
    have hac_eq : ac = (σ_c ⊔ d_a) ⊓ l := by
      simp only [hac_def, hσc_def, hda_def]; unfold coord_mul; rfl
    have hσb_k : σ_b ≤ k := inf_le_left
    have hσs_k : σ_s ≤ k := inf_le_left
    have hda_m : d_a ≤ m := inf_le_right
    have hE_eq : Γ.E = k ⊓ m := by simp only [hk_def, hm_def]; rfl
    have hE_k : Γ.E ≤ k := hE_eq ▸ inf_le_left
    have hE_m : Γ.E ≤ m := hE_eq ▸ inf_le_right
    have hac_l : ac ≤ l := hac_eq ▸ inf_le_right
    -- All key points are in π
    have hk_π : k ≤ π := sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane
    have hσb_π : σ_b ≤ π := hσb_k.trans hk_π
    have hσs_π : σ_s ≤ π := hσs_k.trans hk_π
    have hac_π : ac ≤ π := hac_l.trans le_sup_left
    have hU_π : Γ.U ≤ π := (le_sup_right : Γ.U ≤ l).trans le_sup_left
    have hm_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
    have hE_π : Γ.E ≤ π := hE_m.trans hm_π
    have hda_π : d_a ≤ π := hda_m.trans hm_π
    -- ═══ Step 1: Lift T2 = (U, E, d_a) off π ═══
    -- Pick U' on R⊔U not at R or U
    obtain ⟨U', hU'_atom, hU'_le, hU'_ne_R, hU'_ne_U⟩ :=
      h_irred R Γ.U hR Γ.hU (fun h => hR_not (h ▸ hU_π))
    -- d_a = (a⊔C) ⊓ m: two lines in π meet at an atom (perspect_atom).
    have hda_atom : IsAtom d_a := by
      have hAC : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
      have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
      exact perspect_atom Γ.hC ha hAC Γ.hU Γ.hV hUV Γ.hC_not_m
        (sup_le (ha_on.trans (le_sup_left.trans Γ.m_sup_C_eq_π.symm.le)) le_sup_right)
    -- ═══ Axis-threaded lifting ═══
    -- E' and da' are coupled through axis points to preserve side-intersections.
    -- s₁₂ = (σ_b⊔ac) ⊓ m (axis point), s₁₃ = k ⊓ m = E.
    set s₁₂ := (σ_b ⊔ ac) ⊓ m with hs₁₂_def
    set E' := (s₁₂ ⊔ U') ⊓ (R ⊔ Γ.E) with hE'_def
    set da' := (Γ.E ⊔ U') ⊓ (R ⊔ d_a) with hda'_def
    have hE'_le : E' ≤ R ⊔ Γ.E := inf_le_right
    have hda'_le : da' ≤ R ⊔ d_a := inf_le_right
    -- U' not in π
    have hU'_not_π : ¬ U' ≤ π := by
      intro h; exact hU'_ne_U ((Γ.hU.le_iff.mp
        (inf_sup_of_atom_not_le hR hR_not hU_π ▸ le_inf h hU'_le)).resolve_left
        hU'_atom.1)
    -- ═══ Shared non-degeneracy facts ═══
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have hac_atom : IsAtom ac :=
      coord_mul_atom Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U
    have hac_l : ac ≤ l := by
      show coord_mul Γ a c ≤ l; unfold coord_mul; exact inf_le_right
    have hσb_atom : IsAtom σ_b := by
      rw [show σ_b = (b ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) from inf_comm _ _]
      have hb_ne_EI : b ≠ Γ.E_I :=
        fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h ▸ Γ.hE_I_on_m))
      have hEI_sup_OC : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) = π := by
        have h_lt : Γ.O ⊔ Γ.C < Γ.E_I ⊔ (Γ.O ⊔ Γ.C) :=
          lt_of_le_of_ne le_sup_right (fun h => Γ.hE_I_not_OC (h ▸ le_sup_left))
        exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
          (sup_le (Γ.hE_I_on_m.trans hm_π) hk_π)).resolve_left (ne_of_gt h_lt)
      exact perspect_atom Γ.hE_I_atom hb hb_ne_EI Γ.hO Γ.hC hOC Γ.hE_I_not_OC
        (sup_comm (Γ.O ⊔ Γ.C) Γ.E_I ▸ hEI_sup_OC ▸
          sup_le (hb_on.trans le_sup_left) (Γ.hE_I_on_m.trans hm_π))
    have hkl_eq_O : k ⊓ l = Γ.O := by
      rw [inf_comm]; exact modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU
        (fun h => Γ.hC_not_l (h ▸ le_sup_left))
        (fun h => Γ.hC_not_l (h.symm.le.trans le_sup_right))
        Γ.hC_not_l
    have hσb_ne_ac : σ_b ≠ ac := by
      intro h
      exact hac_ne_O ((Γ.hO.le_iff.mp (hkl_eq_O ▸ le_inf (h ▸ hσb_k) hac_l
        )).resolve_left hac_atom.1)
    have hσb_not_m : ¬ σ_b ≤ m := by
      intro h
      -- σ_b ≤ k ⊓ m. k ⊓ m = E (both in E's definition). σ_b ≤ E → σ_b = E.
      -- Then σ_b ≤ b⊔E_I. (b⊔E_I)⊓m = E_I. σ_b ≤ E_I. E_I ≤ k. Contradiction.
      have hE_eq : m ⊓ k = Γ.E := by rw [inf_comm]; simp only [hk_def, hm_def]; rfl
      have hσb_le_E : σ_b ≤ Γ.E := hE_eq ▸ le_inf h hσb_k
      have hb_inf_m : b ⊓ m = ⊥ :=
        (hb.le_iff.mp inf_le_left).resolve_right
          (fun h' => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h' ▸ inf_le_right)))
      have hbEI_inf_m : (b ⊔ Γ.E_I) ⊓ m = Γ.E_I := by
        rw [sup_comm b Γ.E_I]
        have h1 := sup_inf_assoc_of_le b Γ.hE_I_on_m
        rw [h1, hb_inf_m]; simp
      have hσb_le_bEI : σ_b ≤ b ⊔ Γ.E_I := inf_le_right
      have hσb_le_EI : σ_b ≤ Γ.E_I := by
        have : σ_b ≤ (b ⊔ Γ.E_I) ⊓ m := le_inf hσb_le_bEI (hσb_le_E.trans hE_m)
        rw [hbEI_inf_m] at this; exact this
      exact Γ.hE_I_not_OC ((Γ.hE_I_atom.le_iff.mp hσb_le_EI).resolve_left
        hσb_atom.1 ▸ hσb_k)
    have hs₁₂_atom : IsAtom s₁₂ :=
      line_meets_m_at_atom hσb_atom hac_atom hσb_ne_ac
        (sup_le hσb_π hac_π) hm_π Γ.m_covBy_π hσb_not_m
    -- ═══ Axis-threading properties ═══
    have hE'_ne_E : E' ≠ Γ.E := by
      intro h_eq
      -- E ≤ s₁₂ ⊔ U' (from E = E' ≤ s₁₂ ⊔ U')
      have hE_le_s₁₂U' : Γ.E ≤ s₁₂ ⊔ U' := h_eq ▸ (inf_le_left : E' ≤ s₁₂ ⊔ U')
      -- U' ⊓ m = ⊥
      have hU'_inf_m : U' ⊓ m = ⊥ :=
        (hU'_atom.le_iff.mp inf_le_left).resolve_right
          (fun h => hU'_not_π (h ▸ inf_le_right |>.trans hm_π))
      -- (s₁₂ ⊔ U') ⊓ m = s₁₂ (modular law: s₁₂ ≤ m)
      have hproj : (s₁₂ ⊔ U') ⊓ m = s₁₂ := by
        calc (s₁₂ ⊔ U') ⊓ m = s₁₂ ⊔ U' ⊓ m := sup_inf_assoc_of_le U' inf_le_right
          _ = s₁₂ := by rw [hU'_inf_m]; simp
      -- E ≤ m, E ≤ s₁₂ ⊔ U' → E ≤ (s₁₂ ⊔ U') ⊓ m = s₁₂
      have hE_le_s₁₂ : Γ.E ≤ s₁₂ := hproj ▸ le_inf hE_le_s₁₂U' hE_m
      -- E ≤ σ_b ⊔ ac (from E ≤ s₁₂ ≤ σ_b ⊔ ac)
      have hE_le_σbac : Γ.E ≤ σ_b ⊔ ac := hE_le_s₁₂.trans inf_le_left
      -- k ⊓ (σ_b ⊔ ac) = σ_b (modular: σ_b ≤ k, ac ⊓ k = ⊥)
      have hac_atom := coord_mul_atom Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U
      have hac_not_k : ¬ ac ≤ k := by
        intro h_le
        have hkl : k ⊓ l = Γ.O := by
          rw [inf_comm]
          exact modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU
            (fun h => Γ.hC_not_l (h ▸ le_sup_left))
            (fun h => Γ.hC_not_l (h.symm.le.trans le_sup_right))
            Γ.hC_not_l
        exact hac_ne_O ((Γ.hO.le_iff.mp (hkl ▸ le_inf h_le hac_l)).resolve_left
          hac_atom.1)
      have hac_inf_k : ac ⊓ k = ⊥ := by
        rcases hac_atom.le_iff.mp inf_le_left with h | h
        · exact h
        · exfalso; exact hac_not_k (inf_eq_left.mp h)
      have hE_le_σb : Γ.E ≤ σ_b := by
        -- (σ_b ⊔ ac) ⊓ k = σ_b (modular law)
        have hmod : (σ_b ⊔ ac) ⊓ k = σ_b := by
          have h1 := sup_inf_assoc_of_le ac hσb_k
          rw [hac_inf_k] at h1; simp at h1; exact h1
        calc Γ.E ≤ (σ_b ⊔ ac) ⊓ k := le_inf hE_le_σbac hE_k
          _ = σ_b := hmod
      -- E ≤ σ_b, so σ_b ≤ m (from E ≤ m, and E,σ_b atoms → E = σ_b).
      -- σ_b ≤ (b⊔E_I) ⊓ m = E_I (modular, b ∉ m). σ_b ≤ k ∧ σ_b ≤ E_I → E_I ≤ k.
      -- But E_I ∉ k (hE_I_not_OC). Contradiction.
      -- For E ≤ σ_b → σ_b ≤ m: need σ_b ≥ E ≥ ⊥ and both atoms → σ_b = E → σ_b ≤ m.
      -- Use: E ≤ σ_b ≤ b ⊔ E_I. Also E ≤ m. So E ≤ (b ⊔ E_I) ⊓ m = E_I.
      -- But E ≠ E_I (if E = E_I then E_I ≤ k, contradicting hE_I_not_OC).
      -- Actually simpler: we have E ≤ σ_b and σ_b ≤ b ⊔ E_I and σ_b ≤ k.
      -- So E ≤ b ⊔ E_I. E ≤ m. (b ⊔ E_I) ⊓ m = E_I
      -- (modular: E_I ≤ m, b ∉ m). So E ≤ E_I.
      -- E = E_I (atoms). E_I ≤ k (from E ≤ k). But hE_I_not_OC. Done.
      have hb_inf_m : b ⊓ m = ⊥ :=
        (hb.le_iff.mp inf_le_left).resolve_right
          (fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h ▸ inf_le_right)))
      have hbEI_inf_m : (b ⊔ Γ.E_I) ⊓ m = Γ.E_I := by
        rw [sup_comm b Γ.E_I]
        have h1 := sup_inf_assoc_of_le b Γ.hE_I_on_m
        rw [h1, hb_inf_m]; simp
      have hE_le_bEI : Γ.E ≤ b ⊔ Γ.E_I := hE_le_σb.trans inf_le_right
      have hE_le_EI : Γ.E ≤ Γ.E_I := hbEI_inf_m ▸ le_inf hE_le_bEI hE_m
      have hE_eq_EI : Γ.E = Γ.E_I :=
        (Γ.hE_I_atom.le_iff.mp hE_le_EI).resolve_left Γ.hE_atom.1
      exact Γ.hE_I_not_OC (hE_eq_EI ▸ hE_k)
    have hE'_atom : IsAtom E' := by
      -- E' = (s₁₂⊔U') ⊓ (R⊔E). Two lines in R⊔m. Use line_meets_m_at_atom.
      -- Need: s₁₂ ≠ U' (s₁₂ ≤ m, U' ∉ m), s₁₂⊔U' ≤ R⊔m, R⊔E ≤ R⊔m,
      -- R⊔E ⋖ R⊔m, ¬ s₁₂ ≤ R⊔E.
      have hU'_inf_m : U' ⊓ m = ⊥ :=
        (hU'_atom.le_iff.mp inf_le_left).resolve_right
          (fun h => hU'_not_π (h ▸ inf_le_right |>.trans hm_π))
      have hs₁₂_ne_U' : s₁₂ ≠ U' := by
        intro h; apply hU'_not_π
        calc U' = s₁₂ := h.symm
          _ ≤ m := inf_le_right
          _ ≤ π := hm_π
      have hs₁₂U'_le : s₁₂ ⊔ U' ≤ R ⊔ m :=
        sup_le ((inf_le_right : s₁₂ ≤ m).trans le_sup_right) (hU'_le.trans
          (sup_le le_sup_left ((le_sup_left : Γ.U ≤ m).trans le_sup_right)))
      have hRE_le : R ⊔ Γ.E ≤ R ⊔ m := sup_le le_sup_left (hE_m.trans le_sup_right)
      -- (R⊔E) ⊓ m = E (modular law: E ≤ m, R ⊓ m = ⊥)
      have hR_inf_m : R ⊓ m = ⊥ :=
        (hR.le_iff.mp inf_le_left).resolve_right
          (fun h => hR_not (h ▸ inf_le_right |>.trans hm_π))
      have hRE_inf_m : (R ⊔ Γ.E) ⊓ m = Γ.E := by
        rw [sup_comm R Γ.E]
        have h1 := sup_inf_assoc_of_le R hE_m
        rw [h1, hR_inf_m]; simp
      -- R⊔E ⋖ R⊔m: U ⊓ (R⊔E) = ⊥, U ⊔ (R⊔E) = R⊔m
      have hRE_covBy : R ⊔ Γ.E ⋖ R ⊔ m := by
        have hU_not_RE : ¬ Γ.U ≤ R ⊔ Γ.E := by
          intro h
          have hU_le_E : Γ.U ≤ Γ.E := hRE_inf_m ▸ le_inf h (le_sup_left : Γ.U ≤ m)
          exact CoordSystem.hEU ((Γ.hE_atom.le_iff.mp hU_le_E).resolve_left Γ.hU.1).symm
        have hU_inf_RE : Γ.U ⊓ (R ⊔ Γ.E) = ⊥ :=
          (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun h => hU_not_RE (h ▸ inf_le_right))
        have hU_sup_RE : Γ.U ⊔ (R ⊔ Γ.E) = R ⊔ m := by
          apply le_antisymm
          · -- U ≤ R⊔m (via m), R ≤ R⊔m, E ≤ R⊔m (via m)
            exact sup_le ((le_sup_left : Γ.U ≤ m).trans le_sup_right)
              (sup_le le_sup_left (hE_m.trans le_sup_right))
          · -- R ≤ U⊔(R⊔E), m ≤ U⊔(R⊔E)
            apply sup_le (le_sup_left.trans le_sup_right)
            -- m: U ≤ left, V ≤ E⊔U ≤ left (EU_eq_m: E⊔U = U⊔V = m)
            have hV_le : Γ.V ≤ Γ.U ⊔ (R ⊔ Γ.E) := by
              have := CoordSystem.EU_eq_m (Γ := Γ)
              -- this : E ⊔ U = U ⊔ V = m. So V ≤ E ⊔ U.
              have hV_le_EU : Γ.V ≤ Γ.E ⊔ Γ.U := this.symm ▸ le_sup_right
              exact hV_le_EU.trans (sup_le (le_sup_right.trans le_sup_right) le_sup_left)
            exact sup_le le_sup_left hV_le
        exact hU_sup_RE ▸ covBy_sup_of_inf_covBy_left (hU_inf_RE ▸ Γ.hU.bot_covBy)
      -- ¬ s₁₂ ≤ R⊔E: s₁₂ ≤ m, (R⊔E)⊓m = E, so s₁₂ ≤ R⊔E → s₁₂ ≤ E → s₁₂ = E.
      -- But s₁₂ ≠ E (from hE'_ne_E proof: E ≤ σ_b⊔ac → ... → contradiction).
      have hac_inf_k : ac ⊓ k = ⊥ := by
        rcases hac_atom.le_iff.mp inf_le_left with h' | h'
        · exact h'
        · exfalso; exact hac_ne_O ((Γ.hO.le_iff.mp
            (hkl_eq_O ▸ le_inf (inf_eq_left.mp h') hac_l)).resolve_left hac_atom.1)
      have hσbac_inf_k : (σ_b ⊔ ac) ⊓ k = σ_b := by
        have h1 := sup_inf_assoc_of_le ac hσb_k
        rw [hac_inf_k] at h1; simp at h1; exact h1
      have hE_ne_s₁₂ : Γ.E ≠ s₁₂ := by
        intro h
        -- E = s₁₂ → E ≤ σ_b⊔ac and E ≤ k → E ≤ (σ_b⊔ac)⊓k = σ_b
        have hE_le_σb : Γ.E ≤ σ_b :=
          hσbac_inf_k ▸ le_inf (h.le.trans inf_le_left) hE_k
        -- E ≤ σ_b ≤ b⊔E_I, E ≤ m, (b⊔E_I)⊓m = E_I → E ≤ E_I → E_I ≤ k → contradiction
        have hb_inf_m : b ⊓ m = ⊥ :=
          (hb.le_iff.mp inf_le_left).resolve_right
            (fun h' => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h' ▸ inf_le_right)))
        have hbEI_inf_m : (b ⊔ Γ.E_I) ⊓ m = Γ.E_I := by
          rw [sup_comm b Γ.E_I]
          have h1 := sup_inf_assoc_of_le b Γ.hE_I_on_m
          rw [h1, hb_inf_m]; simp
        have hE_le_EI : Γ.E ≤ Γ.E_I := by
          have : Γ.E ≤ (b ⊔ Γ.E_I) ⊓ m :=
            le_inf (hE_le_σb.trans inf_le_right) hE_m
          rw [hbEI_inf_m] at this; exact this
        exact Γ.hE_I_not_OC ((Γ.hE_I_atom.le_iff.mp hE_le_EI).resolve_left
          Γ.hE_atom.1 ▸ hE_k)
      have hs₁₂_not_RE : ¬ s₁₂ ≤ R ⊔ Γ.E := by
        intro h
        exact hE_ne_s₁₂ ((Γ.hE_atom.le_iff.mp
          (hRE_inf_m ▸ le_inf h (inf_le_right : s₁₂ ≤ m))).resolve_left
          hs₁₂_atom.1).symm
      exact line_meets_m_at_atom hs₁₂_atom hU'_atom hs₁₂_ne_U'
        hs₁₂U'_le hRE_le hRE_covBy hs₁₂_not_RE
    have hE'_not_π : ¬ E' ≤ π := by
      intro h; exact hE'_ne_E ((Γ.hE_atom.le_iff.mp
        (inf_sup_of_atom_not_le hR hR_not hE_π ▸ le_inf h hE'_le)).resolve_left
        hE'_atom.1)
    have hda_ne_E : d_a ≠ Γ.E := by
      intro h
      -- d_a = E → (a⊔C)⊓m = (O⊔C)⊓m → a⊔C meets m at same point as O⊔C.
      -- E ≤ a⊔C. E ≤ O⊔C = k. (a⊔C)⊓k: modular with C ≤ both: (a⊔C)⊓(O⊔C) = C⊔(a⊓(O⊔C)).
      -- a⊓(O⊔C) = a⊓k. a ≤ l, a atom, a ∉ k (else a ≤ k⊓l = O, a = O, contradiction).
      -- So a⊓k = ⊥. (a⊔C)⊓k = C. E ≤ C. E = C. But C ∉ m and E ∈ m.
      have ha_inf_k : a ⊓ k = ⊥ := by
        rcases ha.le_iff.mp inf_le_left with h' | h'
        · exact h'
        · exfalso; exact ha_ne_O ((Γ.hO.le_iff.mp
            (hkl_eq_O ▸ le_inf (h' ▸ inf_le_right) ha_on)).resolve_left ha.1)
      have haC_inf_k : (a ⊔ Γ.C) ⊓ k = Γ.C := by
        show (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C
        rw [sup_comm a Γ.C, inf_comm]
        have h1 := sup_inf_assoc_of_le a (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)
        rw [ha_inf_k] at h1; simp at h1; rw [inf_comm] at h1; exact h1
      have hE_le_C : Γ.E ≤ Γ.C :=
        haC_inf_k ▸ le_inf (h ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)) hE_k
      exact Γ.hC_not_m ((Γ.hC.le_iff.mp hE_le_C).resolve_left Γ.hE_atom.1 ▸ hE_m)
    have hda'_ne_da : da' ≠ d_a := by
      intro h_eq
      -- d_a ≤ E⊔U'. (E⊔U')⊓m = E (modular). d_a ≤ E. d_a = E. Contradiction.
      have hU'_inf_m : U' ⊓ m = ⊥ :=
        (hU'_atom.le_iff.mp inf_le_left).resolve_right
          (fun h => hU'_not_π (h ▸ inf_le_right |>.trans hm_π))
      have hEU'_inf_m : (Γ.E ⊔ U') ⊓ m = Γ.E := by
        have h1 := sup_inf_assoc_of_le U' hE_m
        rw [hU'_inf_m] at h1; simp at h1; exact h1
      have hda_le_E : d_a ≤ Γ.E := by
        have : d_a ≤ (Γ.E ⊔ U') ⊓ m :=
          le_inf (h_eq ▸ (inf_le_left : da' ≤ Γ.E ⊔ U')) hda_m
        rw [hEU'_inf_m] at this; exact this
      exact hda_ne_E ((Γ.hE_atom.le_iff.mp hda_le_E).resolve_left hda_atom.1)
    have hda_ne_U : d_a ≠ Γ.U := by
      intro h
      -- d_a = U → U ≤ a⊔C. (a⊔C)⊓l = a (modular, a ≤ l, C⊓l = ⊥). U ≤ a. U = a.
      have hC_inf_l : Γ.C ⊓ l = ⊥ :=
        (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h' => Γ.hC_not_l (h' ▸ inf_le_right))
      have haC_inf_l : (a ⊔ Γ.C) ⊓ l = a := by
        have h1 := sup_inf_assoc_of_le Γ.C ha_on; rw [hC_inf_l] at h1; simp at h1; exact h1
      have hU_le_a : Γ.U ≤ a :=
        haC_inf_l ▸ le_inf (h ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)) (le_sup_right : Γ.U ≤ l)
      exact ha_ne_U ((ha.le_iff.mp hU_le_a).resolve_left Γ.hU.1).symm
    have hda'_atom : IsAtom da' := by
      -- da' = (E⊔U') ⊓ (R⊔d_a). Two lines in R⊔m. Mirror of hE'_atom.
      have hR_inf_m : R ⊓ m = ⊥ :=
        (hR.le_iff.mp inf_le_left).resolve_right
          (fun h => hR_not (h ▸ inf_le_right |>.trans hm_π))
      have hE_ne_U' : Γ.E ≠ U' := fun h => hU'_not_π (h ▸ hE_π)
      have hEU'_le : Γ.E ⊔ U' ≤ R ⊔ m :=
        sup_le (hE_m.trans le_sup_right) (hU'_le.trans
          (sup_le le_sup_left ((le_sup_left : Γ.U ≤ m).trans le_sup_right)))
      have hRda_le : R ⊔ d_a ≤ R ⊔ m := sup_le le_sup_left (hda_m.trans le_sup_right)
      -- (R⊔d_a)⊓m = d_a
      have hRda_inf_m : (R ⊔ d_a) ⊓ m = d_a := by
        rw [sup_comm R d_a]
        have h1 := sup_inf_assoc_of_le R hda_m; rw [hR_inf_m] at h1; simp at h1; exact h1
      -- R⊔d_a ⋖ R⊔m: U as witness
      have hU_not_Rda : ¬ Γ.U ≤ R ⊔ d_a := by
        intro h; exact hda_ne_U ((hda_atom.le_iff.mp
          (hRda_inf_m ▸ le_inf h (le_sup_left : Γ.U ≤ m))).resolve_left Γ.hU.1).symm
      have hRda_covBy : R ⊔ d_a ⋖ R ⊔ m := by
        have hU_inf_Rda : Γ.U ⊓ (R ⊔ d_a) = ⊥ :=
          (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun h => hU_not_Rda (h ▸ inf_le_right))
        have hUda_lt : Γ.U < Γ.U ⊔ d_a := by
          apply lt_of_le_of_ne le_sup_left; intro h'
          exact hda_ne_U ((Γ.hU.le_iff.mp (le_sup_right.trans h'.symm.le : d_a ≤ Γ.U)
            ).resolve_left hda_atom.1)
        have hUda_eq_m : Γ.U ⊔ d_a = m :=
          ((atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))).eq_or_eq
            hUda_lt.le (sup_le le_sup_left hda_m)).resolve_left (ne_of_gt hUda_lt)
        have hU_sup_Rda : Γ.U ⊔ (R ⊔ d_a) = R ⊔ m := by
          apply le_antisymm
          · exact sup_le ((le_sup_left : Γ.U ≤ m).trans le_sup_right) hRda_le
          · apply sup_le (le_sup_left.trans le_sup_right)
            calc m = Γ.U ⊔ d_a := hUda_eq_m.symm
              _ ≤ Γ.U ⊔ (R ⊔ d_a) := sup_le_sup_left le_sup_right _
        exact hU_sup_Rda ▸ covBy_sup_of_inf_covBy_left (hU_inf_Rda ▸ Γ.hU.bot_covBy)
      -- ¬ E ≤ R⊔d_a
      have hE_not_Rda : ¬ Γ.E ≤ R ⊔ d_a := by
        intro h; exact hda_ne_E ((hda_atom.le_iff.mp
          (hRda_inf_m ▸ le_inf h hE_m)).resolve_left Γ.hE_atom.1).symm
      exact line_meets_m_at_atom Γ.hE_atom hU'_atom hE_ne_U'
        hEU'_le hRda_le hRda_covBy hE_not_Rda
    have hda'_not_π : ¬ da' ≤ π := by
      intro h; exact hda'_ne_da ((hda_atom.le_iff.mp
        (inf_sup_of_atom_not_le hR hR_not hda_π ▸ le_inf h hda'_le)).resolve_left
        hda'_atom.1)
    -- ═══ Step 2: Apply desargues_converse_nonplanar ═══
    -- T1 = (σ_b, ac, σ_s), T2' = (U', E', da')
    -- Conclusion: (σ_b⊔U') ⊓ (ac⊔E') ≤ σ_s⊔da'
    have h_converse : (σ_b ⊔ U') ⊓ (ac ⊔ E') ≤ σ_s ⊔ da' := by
      -- ═══ Apply desargues_converse_nonplanar ═══
      -- T1 = (σ_b, ac, σ_s) in π,  T2' = (U', E', da') outside π
      have hs_atom : IsAtom s :=
        coord_add_atom Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U
      have hs_on : s ≤ l := inf_le_right
      have hσs_atom : IsAtom σ_s := by
        rw [show σ_s = (s ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) from inf_comm _ _]
        have hEI_sup_OC : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) = π := by
          have h_lt : Γ.O ⊔ Γ.C < Γ.E_I ⊔ (Γ.O ⊔ Γ.C) :=
            lt_of_le_of_ne le_sup_right (fun h => Γ.hE_I_not_OC (h ▸ le_sup_left))
          exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
            (sup_le (Γ.hE_I_on_m.trans hm_π) hk_π)).resolve_left (ne_of_gt h_lt)
        exact perspect_atom Γ.hE_I_atom hs_atom
          (fun h => hs_ne_U (Γ.atom_on_both_eq_U hs_atom hs_on (h ▸ Γ.hE_I_on_m)))
          Γ.hO Γ.hC hOC Γ.hE_I_not_OC
          (sup_comm (Γ.O ⊔ Γ.C) Γ.E_I ▸ hEI_sup_OC ▸
            sup_le (hs_on.trans le_sup_left) (Γ.hE_I_on_m.trans hm_π))
      have hσb_ne_σs : σ_b ≠ σ_s := by
        -- Perspectivity l→k center E_I is injective, so σ_b=σ_s → b=s.
        -- b=s means b+c=b, which forces c=O (group cancellation). Contradiction.
        intro h_eq_σ
        -- ═══ Part A: σ_b = σ_s → b = s (perspectivity l→k center E_I is injective) ═══
        have hσb_ne_EI : σ_b ≠ Γ.E_I := fun h => Γ.hE_I_not_OC (h ▸ hσb_k)
        have hb_ne_EI : b ≠ Γ.E_I :=
          fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h ▸ Γ.hE_I_on_m))
        have hs_ne_EI : s ≠ Γ.E_I :=
          fun h => hs_ne_U (Γ.atom_on_both_eq_U hs_atom hs_on (h ▸ Γ.hE_I_on_m))
        -- E_I < σ_b ⊔ E_I (σ_b ≠ E_I, both atoms)
        have hEI_lt : Γ.E_I < σ_b ⊔ Γ.E_I :=
          lt_of_le_of_ne le_sup_right (fun h =>
            hσb_ne_EI ((Γ.hE_I_atom.le_iff.mp
              (le_sup_left.trans h.symm.le)).resolve_left hσb_atom.1))
        -- CovBy: E_I ⋖ E_I⊔b. σ_b ≤ b⊔E_I. E_I < σ_b⊔E_I ≤ E_I⊔b. → σ_b⊔E_I = E_I⊔b.
        have hσbEI_bEI : σ_b ⊔ Γ.E_I = b ⊔ Γ.E_I := by
          rw [show b ⊔ Γ.E_I = Γ.E_I ⊔ b from sup_comm _ _]
          exact ((atom_covBy_join Γ.hE_I_atom hb hb_ne_EI.symm).eq_or_eq hEI_lt.le
            (sup_le ((inf_le_right : σ_b ≤ b ⊔ Γ.E_I).trans (sup_comm b Γ.E_I).le)
              le_sup_left)).resolve_left (ne_of_gt hEI_lt)
        -- Similarly σ_b⊔E_I = s⊔E_I (using σ_b = σ_s ≤ s⊔E_I)
        have hσbEI_sEI : σ_b ⊔ Γ.E_I = s ⊔ Γ.E_I := by
          rw [show s ⊔ Γ.E_I = Γ.E_I ⊔ s from sup_comm _ _]
          exact ((atom_covBy_join Γ.hE_I_atom hs_atom hs_ne_EI.symm).eq_or_eq hEI_lt.le
            (sup_le ((h_eq_σ ▸ (inf_le_right : σ_s ≤ s ⊔ Γ.E_I) : σ_b ≤ s ⊔ Γ.E_I).trans
              (sup_comm s Γ.E_I).le) le_sup_left)).resolve_left (ne_of_gt hEI_lt)
        -- b⊔E_I = s⊔E_I, so b and s are on the same perspectivity line
        have hbEI_eq : b ⊔ Γ.E_I = s ⊔ Γ.E_I := hσbEI_bEI.symm.trans hσbEI_sEI
        -- Both b, s ≤ (s⊔E_I)⊓l which is an atom (two lines in π meeting)
        have hb_le_meet : b ≤ (s ⊔ Γ.E_I) ⊓ l := le_inf (hbEI_eq ▸ le_sup_left) hb_on
        have hs_le_meet : s ≤ (s ⊔ Γ.E_I) ⊓ l := le_inf le_sup_left hs_on
        have h_meet_lt : (s ⊔ Γ.E_I) ⊓ l < s ⊔ Γ.E_I := by
          apply lt_of_le_of_ne inf_le_left; intro h'
          -- If (s⊔E_I)⊓l = s⊔E_I then l ≤ s⊔E_I. CovBy s ⋖ s⊔E_I and s < l ≤ s⊔E_I
          -- (s⊔E_I) ⊓ l = s⊔E_I → s⊔E_I ≤ l → E_I ≤ l. Contradiction.
          exact Γ.hE_I_not_l (le_sup_right.trans (h'.ge.trans inf_le_right))
        have h_meet_atom := line_height_two hs_atom Γ.hE_I_atom hs_ne_EI
          (lt_of_lt_of_le hs_atom.bot_lt hs_le_meet) h_meet_lt
        have hb_eq_s : b = s :=
          ((h_meet_atom.le_iff.mp hb_le_meet).resolve_left hb.1).trans
            ((h_meet_atom.le_iff.mp hs_le_meet).resolve_left hs_atom.1).symm
        -- ═══ Part B: b = coord_add Γ b c → c = O (pure modular law) ═══
        -- β = (b⊔C)⊓m, D = (c⊔E)⊓q. b = (β⊔D)⊓l → b ≤ β⊔D.
        -- CovBy chain: β ⋖ β⊔D, β < β⊔b ≤ β⊔D → β⊔b = β⊔D.
        -- β⊔b = b⊔C (β,b ≤ b⊔C, CovBy). D ≤ b⊔C.
        -- q ⊓ (b⊔C) = C (modular). D ≤ C. D = C.
        -- C ≤ c⊔E → C⊔E = k → c ≤ k⊓l = O. Contradiction with hc_ne_O.
        have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)
        have hc_ne_E : c ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hc_on)
        have hC_ne_E : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ hE_m)
        have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
        have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ le_sup_left)
        have hVC : Γ.V ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ le_sup_right)
        -- U ∉ k (if U ≤ k then U ≤ k⊓l = O, contradiction)
        have hU_not_k : ¬ Γ.U ≤ k := fun h =>
          Γ.hOU ((Γ.hO.le_iff.mp (hkl_eq_O ▸ le_inf h (le_sup_right : Γ.U ≤ l))
            ).resolve_left Γ.hU.1).symm
        -- O ∉ U⊔C (if O ≤ U⊔C then l ≤ q, CovBy forces l = q, C ≤ l)
        have hO_not_UC : ¬ Γ.O ≤ Γ.U ⊔ Γ.C := by
          intro hO_le
          have hl_le_q : l ≤ q := sup_le hO_le (show Γ.U ≤ q from le_sup_left)
          have hU_covBy_l : Γ.U ⋖ l := by
            rw [show l = Γ.U ⊔ Γ.O from sup_comm Γ.O Γ.U]
            exact atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm
          have hU_covBy_q : Γ.U ⋖ q := atom_covBy_join Γ.hU Γ.hC hUC
          have hl_eq_q : l = q := (hU_covBy_q.eq_or_eq hU_covBy_l.lt.le hl_le_q
            ).resolve_left (ne_of_gt hU_covBy_l.lt)
          exact Γ.hC_not_l ((show Γ.C ≤ q from le_sup_right).trans hl_eq_q.symm.le)
        -- b ∉ q (if b ≤ q then b ≤ l⊓q = U, contradiction)
        have hb_not_q : ¬ b ≤ q := by
          intro h_le
          have hlq : l ⊓ q = Γ.U := by
            rw [show l ⊓ q = q ⊓ l from inf_comm _ _]
            show (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.U
            rw [show Γ.O ⊔ Γ.U = Γ.U ⊔ Γ.O from sup_comm _ _]
            exact modular_intersection Γ.hU Γ.hC Γ.hO hUC Γ.hOU.symm hOC.symm
              (fun h => hO_not_UC h)
          exact hb_ne_U ((Γ.hU.le_iff.mp (hlq ▸ le_inf hb_on h_le)
            ).resolve_left hb.1)
        -- β = (b⊔C)⊓m is an atom
        have hβ_atom : IsAtom ((b ⊔ Γ.C) ⊓ m) :=
          perspect_atom Γ.hC hb hb_ne_C Γ.hU Γ.hV hUV Γ.hC_not_m
            (sup_le (hb_on.trans (le_sup_left.trans Γ.m_sup_C_eq_π.symm.le)) le_sup_right)
        -- E ∉ q (if E ≤ q then E ≤ k⊓q = C, E = C, C on m, contradiction)
        have hE_not_q : ¬ Γ.E ≤ q := by
          intro h_le
          have hkq : k ⊓ q = Γ.C := by
            show (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C) = Γ.C
            rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _,
                show Γ.U ⊔ Γ.C = Γ.C ⊔ Γ.U from sup_comm _ _]
            exact modular_intersection Γ.hC Γ.hO Γ.hU hOC.symm hUC.symm Γ.hOU
              (fun h => hU_not_k (h.trans (sup_comm Γ.C Γ.O).le))
          exact hC_ne_E.symm ((Γ.hC.le_iff.mp (hkq ▸ le_inf hE_k h_le)
            ).resolve_left Γ.hE_atom.1)
        -- D = (c⊔E)⊓q is an atom
        have hD_atom : IsAtom ((c ⊔ Γ.E) ⊓ q) := by
          -- C⊔E = k (C ⋖ k, C < C⊔E ≤ k → C⊔E = k by CovBy)
          have hC_covBy_k : Γ.C ⋖ k := by
            rw [show k = Γ.C ⊔ Γ.O from sup_comm Γ.O Γ.C]
            exact atom_covBy_join Γ.hC Γ.hO hOC.symm
          have hCE_eq_k : Γ.C ⊔ Γ.E = k :=
            (hC_covBy_k.eq_or_eq (atom_covBy_join Γ.hC Γ.hE_atom hC_ne_E).lt.le
              (sup_le le_sup_right hE_k)).resolve_left
              (ne_of_gt (atom_covBy_join Γ.hC Γ.hE_atom hC_ne_E).lt)
          -- Coplanarity: c⊔E ≤ q⊔E. O ≤ C⊔E = k. C ≤ q. E ≤ q⊔E. So k ≤ q⊔E. O ≤ q⊔E.
          have hk_le_qE : k ≤ q ⊔ Γ.E :=
            hCE_eq_k ▸ sup_le ((le_sup_right : Γ.C ≤ q).trans le_sup_left) le_sup_right
          have hO_le_qE : Γ.O ≤ q ⊔ Γ.E := (le_sup_left : Γ.O ≤ k).trans hk_le_qE
          exact perspect_atom Γ.hE_atom hc hc_ne_E Γ.hU Γ.hC hUC hE_not_q
            (sup_le (hc_on.trans (sup_le hO_le_qE
              ((le_sup_left : Γ.U ≤ q).trans le_sup_left))) le_sup_right)
        -- β ≠ b (β on m, b not on m since b ≠ U)
        have hβ_ne_b : (b ⊔ Γ.C) ⊓ m ≠ b :=
          fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h ▸ inf_le_right))
        -- β ≠ D: m⊓q = U. β = D → β ≤ m⊓q = U → β = U → U ≤ b⊔C → l ≤ b⊔C → C ∈ l.
        have hβ_ne_D : (b ⊔ Γ.C) ⊓ m ≠ (c ⊔ Γ.E) ⊓ q := by
          intro h
          have hmq : m ⊓ q = Γ.U :=
            modular_intersection Γ.hU Γ.hV Γ.hC hUV hUC hVC Γ.hC_not_m
          have hβ_le_U : (b ⊔ Γ.C) ⊓ m ≤ Γ.U :=
            hmq ▸ le_inf inf_le_right (h ▸ inf_le_right)
          have hβ_eq_U := (Γ.hU.le_iff.mp hβ_le_U).resolve_left hβ_atom.1
          have hU_le_bC : Γ.U ≤ b ⊔ Γ.C := hβ_eq_U ▸ inf_le_left
          -- l = b⊔U ≤ b⊔C (b, U ≤ b⊔C). Then CovBy b ⋖ b⊔C → l = b⊔C → C ≤ l.
          have hbU_eq_l : b ⊔ Γ.U = l :=
            ((line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hb hb_on).eq_or_eq
              (atom_covBy_join hb Γ.hU hb_ne_U).lt.le
              (sup_le hb_on (show Γ.U ≤ l from le_sup_right))).resolve_left
              (ne_of_gt (atom_covBy_join hb Γ.hU hb_ne_U).lt)
          have hl_le_bC : l ≤ b ⊔ Γ.C :=
            hbU_eq_l.symm.le.trans (sup_le le_sup_left hU_le_bC)
          -- CovBy: b < l ≤ b⊔C → l = b⊔C → C ≤ b⊔C = l
          have hl_eq_bC : l = b ⊔ Γ.C :=
            ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq
              (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hb hb_on).lt.le hl_le_bC
            ).resolve_left
              (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hb hb_on).lt)
          exact Γ.hC_not_l ((le_sup_right : Γ.C ≤ b ⊔ Γ.C).trans hl_eq_bC.symm.le)
        -- b ≤ β⊔D (from b = (β⊔D)⊓l, definitional unfolding of coord_add)
        have hb_le_βD : b ≤ (b ⊔ Γ.C) ⊓ m ⊔ (c ⊔ Γ.E) ⊓ q := by
          have : s ≤ (b ⊔ Γ.C) ⊓ m ⊔ (c ⊔ Γ.E) ⊓ q := by
            show coord_add Γ b c ≤ _; unfold coord_add; exact inf_le_left
          exact hb_eq_s.le.trans this
        -- CovBy chain: β ⋖ β⊔D. β < β⊔b ≤ β⊔D → β⊔b = β⊔D.
        have hβb_eq_βD : (b ⊔ Γ.C) ⊓ m ⊔ b =
            (b ⊔ Γ.C) ⊓ m ⊔ (c ⊔ Γ.E) ⊓ q := by
          have hβ_lt : (b ⊔ Γ.C) ⊓ m < (b ⊔ Γ.C) ⊓ m ⊔ b :=
            lt_of_le_of_ne le_sup_left (fun h =>
              hβ_ne_b ((hβ_atom.le_iff.mp (le_sup_right.trans h.symm.le)
                ).resolve_left hb.1).symm)
          exact ((atom_covBy_join hβ_atom hD_atom hβ_ne_D).eq_or_eq hβ_lt.le
            (sup_le le_sup_left hb_le_βD)).resolve_left (ne_of_gt hβ_lt)
        -- β⊔b = b⊔C (β,b ≤ b⊔C, CovBy b ⋖ b⊔C)
        have hβb_eq_bC : (b ⊔ Γ.C) ⊓ m ⊔ b = b ⊔ Γ.C := by
          have hb_lt : b < (b ⊔ Γ.C) ⊓ m ⊔ b :=
            lt_of_le_of_ne le_sup_right (fun h =>
              hβ_ne_b ((hb.le_iff.mp (le_sup_left.trans h.symm.le)
                ).resolve_left hβ_atom.1))
          exact ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq hb_lt.le
            (sup_le inf_le_left le_sup_left)).resolve_left (ne_of_gt hb_lt)
        -- D ≤ b⊔C (D ≤ β⊔D = β⊔b = b⊔C)
        have hD_le_bC : (c ⊔ Γ.E) ⊓ q ≤ b ⊔ Γ.C :=
          (le_sup_right : (c ⊔ Γ.E) ⊓ q ≤ _ ⊔ (c ⊔ Γ.E) ⊓ q).trans
            (hβb_eq_βD ▸ hβb_eq_bC).le
        -- q ⊓ (b⊔C) = C (modular_intersection: C ≤ both, b ∉ q)
        have hq_inf_bC : q ⊓ (b ⊔ Γ.C) = Γ.C := by
          show (Γ.U ⊔ Γ.C) ⊓ (b ⊔ Γ.C) = Γ.C
          rw [show Γ.U ⊔ Γ.C = Γ.C ⊔ Γ.U from sup_comm _ _,
              show b ⊔ Γ.C = Γ.C ⊔ b from sup_comm _ _]
          exact modular_intersection Γ.hC Γ.hU hb hUC.symm hb_ne_C.symm hb_ne_U.symm
            (fun h => hb_not_q (h.trans (sup_comm Γ.C Γ.U).le))
        -- D ≤ q ⊓ (b⊔C) = C. D = C (atoms).
        have hD_le_C : (c ⊔ Γ.E) ⊓ q ≤ Γ.C :=
          hq_inf_bC ▸ le_inf inf_le_right hD_le_bC
        have hD_eq_C : (c ⊔ Γ.E) ⊓ q = Γ.C :=
          (Γ.hC.le_iff.mp hD_le_C).resolve_left hD_atom.1
        -- C ≤ c⊔E → C⊔E = k → c⊔E = k → c ≤ k → c ≤ k⊓l = O
        have hC_le_cE : Γ.C ≤ c ⊔ Γ.E := hD_eq_C ▸ inf_le_left
        have hCE_eq_k : Γ.C ⊔ Γ.E = k := by
          have hC_covBy_k : Γ.C ⋖ k := by
            rw [show k = Γ.C ⊔ Γ.O from sup_comm Γ.O Γ.C]
            exact atom_covBy_join Γ.hC Γ.hO hOC.symm
          exact (hC_covBy_k.eq_or_eq (atom_covBy_join Γ.hC Γ.hE_atom hC_ne_E).lt.le
            (sup_le le_sup_right hE_k)).resolve_left
            (ne_of_gt (atom_covBy_join Γ.hC Γ.hE_atom hC_ne_E).lt)
        -- k ≤ c⊔E. CovBy E ⋖ c⊔E. E < k ≤ c⊔E. k = c⊔E. c ≤ k.
        have hk_le_cE : k ≤ c ⊔ Γ.E :=
          hCE_eq_k.symm.le.trans (sup_le hC_le_cE le_sup_right)
        have hcE_eq_k : c ⊔ Γ.E = k := by
          have hE_covBy_cE : Γ.E ⋖ c ⊔ Γ.E := by
            rw [show c ⊔ Γ.E = Γ.E ⊔ c from sup_comm _ _]
            exact atom_covBy_join Γ.hE_atom hc hc_ne_E.symm
          have hE_lt_k : Γ.E < k := by
            apply lt_of_le_of_ne hE_k; intro h
            -- E = k → O ≤ k = E → O = E → E on l. Contradiction.
            have hO_le_E : Γ.O ≤ Γ.E := (le_sup_left : Γ.O ≤ k).trans h.symm.le
            have hO_eq_E := (Γ.hE_atom.le_iff.mp hO_le_E).resolve_left Γ.hO.1
            exact CoordSystem.hE_not_l (hO_eq_E.symm.le.trans (le_sup_left : Γ.O ≤ l))
          exact ((hE_covBy_cE.eq_or_eq hE_lt_k.le hk_le_cE).resolve_left
            (ne_of_gt hE_lt_k)).symm
        have hc_le_k : c ≤ k := le_sup_left.trans hcE_eq_k.le
        exact hc_ne_O ((Γ.hO.le_iff.mp (hkl_eq_O ▸ le_inf hc_le_k hc_on)
          ).resolve_left hc.1)
      have hac_ne_σs : ac ≠ σ_s := by
        intro h; exact hac_ne_O ((Γ.hO.le_iff.mp
          (hkl_eq_O ▸ le_inf (h ▸ hσs_k) hac_l)).resolve_left hac_atom.1)
      have hσb_not_acσs : ¬ σ_b ≤ ac ⊔ σ_s := by
        intro h
        have hac_inf_k : ac ⊓ k = ⊥ := by
          rcases hac_atom.le_iff.mp inf_le_left with h' | h'
          · exact h'
          · exact absurd ((Γ.hO.le_iff.mp (hkl_eq_O ▸ le_inf (inf_eq_left.mp h') hac_l)
              ).resolve_left hac_atom.1) hac_ne_O
        -- (σ_s ⊔ ac) ⊓ k = σ_s (modular: σ_s ≤ k, ac ⊓ k = ⊥)
        have h_mod : (σ_s ⊔ ac) ⊓ k = σ_s := by
          calc (σ_s ⊔ ac) ⊓ k = σ_s ⊔ ac ⊓ k := sup_inf_assoc_of_le ac hσs_k
            _ = σ_s := by rw [hac_inf_k, sup_bot_eq]
        -- σ_b ≤ (ac ⊔ σ_s) ⊓ k. Rewrite ac ⊔ σ_s = σ_s ⊔ ac, apply h_mod.
        have h_σb_le_σs : σ_b ≤ σ_s := by
          have : σ_b ≤ (ac ⊔ σ_s) ⊓ k := le_inf h hσb_k
          rw [show ac ⊔ σ_s = σ_s ⊔ ac from sup_comm _ _, h_mod] at this
          exact this
        exact hσb_ne_σs ((hσs_atom.le_iff.mp h_σb_le_σs).resolve_left hσb_atom.1)
      have hπA_le_π : σ_b ⊔ ac ⊔ σ_s ≤ π := sup_le (sup_le hσb_π hac_π) hσs_π
      have hU'_not_πA : ¬ U' ≤ σ_b ⊔ ac ⊔ σ_s :=
        fun h => hU'_not_π (h.trans hπA_le_π)
      have hE'_not_πA : ¬ E' ≤ σ_b ⊔ ac ⊔ σ_s :=
        fun h => hE'_not_π (h.trans hπA_le_π)
      have hda'_not_πA : ¬ da' ≤ σ_b ⊔ ac ⊔ σ_s :=
        fun h => hda'_not_π (h.trans hπA_le_π)
      have hU'_ne_E' : U' ≠ E' := by
        intro h_eq
        -- U' ≤ R⊔U, E' ≤ R⊔E. If equal: U' ≤ (R⊔E) ⊓ (R⊔U).
        -- (R⊔E) ⊓ (R⊔U) = R (modular: R ≤ R⊔E, U ⊓ (R⊔E) = ⊥ since U ∉ R⊔E).
        have hR_inf_m : R ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
          (hR.le_iff.mp inf_le_left).resolve_right
            (fun h => hR_not (h ▸ inf_le_right |>.trans hm_π))
        have hU_not_RE : ¬ Γ.U ≤ R ⊔ Γ.E := by
          intro h
          have hRE_inf_m : (R ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.V) = Γ.E := by
            rw [show R ⊔ Γ.E = Γ.E ⊔ R from sup_comm _ _]
            calc (Γ.E ⊔ R) ⊓ (Γ.U ⊔ Γ.V) = Γ.E ⊔ R ⊓ (Γ.U ⊔ Γ.V) :=
                  sup_inf_assoc_of_le R hE_m
              _ = Γ.E := by rw [hR_inf_m, sup_bot_eq]
          exact CoordSystem.hEU ((Γ.hE_atom.le_iff.mp
            (hRE_inf_m ▸ le_inf h (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V))).resolve_left Γ.hU.1).symm
        have hU_inf_RE : Γ.U ⊓ (R ⊔ Γ.E) = ⊥ :=
          (Γ.hU.le_iff.mp inf_le_left).resolve_right
            (fun h => hU_not_RE (h ▸ inf_le_right))
        have hRE_inf_RU : (R ⊔ Γ.E) ⊓ (R ⊔ Γ.U) = R := by
          rw [show (R ⊔ Γ.E) ⊓ (R ⊔ Γ.U) = (R ⊔ Γ.U) ⊓ (R ⊔ Γ.E) from inf_comm _ _]
          calc (R ⊔ Γ.U) ⊓ (R ⊔ Γ.E) = R ⊔ Γ.U ⊓ (R ⊔ Γ.E) :=
                sup_inf_assoc_of_le Γ.U (le_sup_left : R ≤ R ⊔ Γ.E)
            _ = R := by rw [hU_inf_RE, sup_bot_eq]
        exact hU'_ne_R ((hR.le_iff.mp
          (hRE_inf_RU ▸ le_inf (h_eq ▸ hE'_le) hU'_le)).resolve_left hU'_atom.1)
      have hU'_ne_da' : U' ≠ da' := by
        intro h_eq
        -- U' ≤ R⊔U, da' ≤ R⊔d_a. (R⊔d_a) ⊓ (R⊔U) = R. U' ≤ R. U' = R. Contradiction.
        have hR_inf_m : R ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
          (hR.le_iff.mp inf_le_left).resolve_right
            (fun h => hR_not (h ▸ inf_le_right |>.trans hm_π))
        have hU_not_Rda : ¬ Γ.U ≤ R ⊔ d_a := by
          intro h
          have hRda_inf_m : (R ⊔ d_a) ⊓ (Γ.U ⊔ Γ.V) = d_a := by
            rw [show R ⊔ d_a = d_a ⊔ R from sup_comm _ _]
            calc (d_a ⊔ R) ⊓ (Γ.U ⊔ Γ.V) = d_a ⊔ R ⊓ (Γ.U ⊔ Γ.V) :=
                  sup_inf_assoc_of_le R hda_m
              _ = d_a := by rw [hR_inf_m, sup_bot_eq]
          exact hda_ne_U ((hda_atom.le_iff.mp
            (hRda_inf_m ▸ le_inf h (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V))).resolve_left Γ.hU.1).symm
        have hU_inf_Rda : Γ.U ⊓ (R ⊔ d_a) = ⊥ :=
          (Γ.hU.le_iff.mp inf_le_left).resolve_right
            (fun h => hU_not_Rda (h ▸ inf_le_right))
        have hRda_inf_RU : (R ⊔ d_a) ⊓ (R ⊔ Γ.U) = R := by
          rw [show (R ⊔ d_a) ⊓ (R ⊔ Γ.U) = (R ⊔ Γ.U) ⊓ (R ⊔ d_a) from inf_comm _ _]
          calc (R ⊔ Γ.U) ⊓ (R ⊔ d_a) = R ⊔ Γ.U ⊓ (R ⊔ d_a) :=
                sup_inf_assoc_of_le Γ.U (le_sup_left : R ≤ R ⊔ d_a)
            _ = R := by rw [hU_inf_Rda, sup_bot_eq]
        exact hU'_ne_R ((hR.le_iff.mp
          (hRda_inf_RU ▸ le_inf (h_eq ▸ hda'_le) hU'_le)).resolve_left hU'_atom.1)
      have hE'_ne_da' : E' ≠ da' := by
        intro h_eq
        -- E' ≤ s₁₂⊔U', da' ≤ E⊔U'. Two lines through U'.
        -- s₁₂ ≠ E (hE_ne_s₁₂), so (s₁₂⊔U') ⊓ (E⊔U') = U' (modular + CovBy).
        -- E' = U'. But U' ≤ R⊔U, E' ≤ R⊔E. (R⊔E)⊓(R⊔U) = R → U' = R. Contradiction.
        have hE'_le_both : E' ≤ (s₁₂ ⊔ U') ⊓ (Γ.E ⊔ U') :=
          le_inf inf_le_left (h_eq ▸ inf_le_left)
        -- Modular: (s₁₂⊔U') ⊓ (E⊔U') = U' ⊔ ((s₁₂⊔U')⊓E) [U' ≤ E⊔U']
        -- (s₁₂⊔U')⊓E: E atom. E ≤ s₁₂⊔U' → E ≤ (s₁₂⊔U')⊓π = s₁₂ → E = s₁₂.
        -- But hE_ne_s₁₂. So (s₁₂⊔U')⊓E = ⊥. Meet = U'.
        have hs₁₂_ne_U' : s₁₂ ≠ U' := by
          intro h; exact hU'_not_π (h ▸ (inf_le_right : s₁₂ ≤ Γ.U ⊔ Γ.V).trans hm_π)
        have hE_not_s₁₂U' : ¬ Γ.E ≤ s₁₂ ⊔ U' := by
          intro h
          -- E ≤ π, (s₁₂⊔U')⊓π = s₁₂ (modular: s₁₂ ≤ π, U' ⊓ π = ⊥)
          have hU'_inf_π : U' ⊓ π = ⊥ :=
            (hU'_atom.le_iff.mp inf_le_left).resolve_right
              (fun h' => hU'_not_π (h' ▸ inf_le_right))
          have h_proj : (s₁₂ ⊔ U') ⊓ π = s₁₂ := by
            rw [show s₁₂ ⊔ U' = U' ⊔ s₁₂ from sup_comm _ _, show U' ⊔ s₁₂ = s₁₂ ⊔ U' from sup_comm _ _]
            calc (s₁₂ ⊔ U') ⊓ π = s₁₂ ⊔ U' ⊓ π :=
                  sup_inf_assoc_of_le U' ((inf_le_right : s₁₂ ≤ Γ.U ⊔ Γ.V).trans hm_π)
              _ = s₁₂ := by rw [hU'_inf_π, sup_bot_eq]
          -- E = s₁₂ → E ≤ σ_b⊔ac ⊓ k = σ_b → E ≤ b⊔E_I → E_I on k. Contradiction.
          have hE_ne_s₁₂ : Γ.E ≠ s₁₂ := by
            intro h'
            have hac_inf_k' : ac ⊓ k = ⊥ := by
              rcases hac_atom.le_iff.mp inf_le_left with h'' | h''
              · exact h''
              · exact absurd ((Γ.hO.le_iff.mp (hkl_eq_O ▸ le_inf (inf_eq_left.mp h'') hac_l)
                  ).resolve_left hac_atom.1) hac_ne_O
            have hσbac_inf_k' : (σ_b ⊔ ac) ⊓ k = σ_b := by
              calc (σ_b ⊔ ac) ⊓ k = σ_b ⊔ ac ⊓ k := sup_inf_assoc_of_le ac hσb_k
                _ = σ_b := by rw [hac_inf_k', sup_bot_eq]
            have hE_le_σb : Γ.E ≤ σ_b :=
              hσbac_inf_k' ▸ le_inf (h'.le.trans inf_le_left) hE_k
            have hb_inf_m' : b ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
              (hb.le_iff.mp inf_le_left).resolve_right
                (fun h'' => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h'' ▸ inf_le_right)))
            have hbEI_inf_m' : (b ⊔ Γ.E_I) ⊓ (Γ.U ⊔ Γ.V) = Γ.E_I := by
              rw [show b ⊔ Γ.E_I = Γ.E_I ⊔ b from sup_comm _ _]
              calc (Γ.E_I ⊔ b) ⊓ (Γ.U ⊔ Γ.V) = Γ.E_I ⊔ b ⊓ (Γ.U ⊔ Γ.V) :=
                    sup_inf_assoc_of_le b Γ.hE_I_on_m
                _ = Γ.E_I := by rw [hb_inf_m', sup_bot_eq]
            have hE_le_EI : Γ.E ≤ Γ.E_I := by
              have : Γ.E ≤ (b ⊔ Γ.E_I) ⊓ (Γ.U ⊔ Γ.V) :=
                le_inf (hE_le_σb.trans inf_le_right) hE_m
              rw [hbEI_inf_m'] at this; exact this
            exact Γ.hE_I_not_OC ((Γ.hE_I_atom.le_iff.mp hE_le_EI).resolve_left
              Γ.hE_atom.1 ▸ hE_k)
          have hE_le_s₁₂ : Γ.E ≤ s₁₂ := h_proj ▸ le_inf h hE_π
          exact hE_ne_s₁₂ ((hs₁₂_atom.le_iff.mp hE_le_s₁₂).resolve_left Γ.hE_atom.1)
        have hE_inf_s₁₂U' : Γ.E ⊓ (s₁₂ ⊔ U') = ⊥ :=
          (Γ.hE_atom.le_iff.mp inf_le_left).resolve_right
            (fun h => hE_not_s₁₂U' (h ▸ inf_le_right))
        have h_meet : (s₁₂ ⊔ U') ⊓ (Γ.E ⊔ U') = U' := by
          rw [show (s₁₂ ⊔ U') ⊓ (Γ.E ⊔ U') = (Γ.E ⊔ U') ⊓ (s₁₂ ⊔ U') from inf_comm _ _,
              show Γ.E ⊔ U' = U' ⊔ Γ.E from sup_comm _ _]
          calc (U' ⊔ Γ.E) ⊓ (s₁₂ ⊔ U') = U' ⊔ Γ.E ⊓ (s₁₂ ⊔ U') :=
                sup_inf_assoc_of_le Γ.E (le_sup_right : U' ≤ s₁₂ ⊔ U')
            _ = U' := by rw [hE_inf_s₁₂U', sup_bot_eq]
        -- E' ≤ U'. E' atom. So E' = U'.
        have hE'_eq_U' : E' = U' :=
          (hU'_atom.le_iff.mp (h_meet ▸ hE'_le_both)).resolve_left hE'_atom.1
        -- But we proved U' ≠ E'. Contradiction.
        exact hU'_ne_E' hE'_eq_U'.symm
      have hσs_ne_da' : σ_s ≠ da' := fun h => hda'_not_π (h ▸ hσs_π)
      -- ═══ Shared structural facts ═══
      -- σ_b ⊔ σ_s = k (two distinct atoms on line k)
      have hσbσs_eq_k : σ_b ⊔ σ_s = k := by
        have h_lt : σ_b < σ_b ⊔ σ_s :=
          lt_of_le_of_ne le_sup_left (fun h => by
            have : σ_s ≤ σ_b := le_sup_right.trans h.symm.le
            exact hσb_ne_σs ((hσb_atom.le_iff.mp this).resolve_left hσs_atom.1).symm)
        have h_le : σ_b ⊔ σ_s ≤ k := sup_le hσb_k hσs_k
        have hσb_covBy_k : σ_b ⋖ k := by
          by_cases hσb_eq_O : σ_b = Γ.O
          · exact hσb_eq_O ▸ atom_covBy_join Γ.hO Γ.hC hOC
          · have hσb_inf_O : σ_b ⊓ Γ.O = ⊥ :=
              (hσb_atom.le_iff.mp inf_le_left).resolve_right
                (fun h => hσb_eq_O ((Γ.hO.le_iff.mp (h ▸ inf_le_right)).resolve_left hσb_atom.1))
            have hO_inf_σb : Γ.O ⊓ σ_b = ⊥ := inf_comm σ_b Γ.O ▸ hσb_inf_O
            have h_cov_σbO : σ_b ⋖ σ_b ⊔ Γ.O := by
              rw [show σ_b ⊔ Γ.O = Γ.O ⊔ σ_b from sup_comm _ _]
              exact covBy_sup_of_inf_covBy_left (hO_inf_σb ▸ Γ.hO.bot_covBy)
            have hO_lt : Γ.O < σ_b ⊔ Γ.O :=
              lt_of_le_of_ne le_sup_right (fun h => by
                exact hσb_eq_O ((Γ.hO.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left hσb_atom.1))
            have hσbO_eq_k : σ_b ⊔ Γ.O = k :=
              ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq hO_lt.le
                (sup_le hσb_k (le_sup_left : Γ.O ≤ k))).resolve_left (ne_of_gt hO_lt)
            exact hσbO_eq_k ▸ h_cov_σbO
        exact (hσb_covBy_k.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
      -- U' ⊔ da' = E ⊔ U' (da' on E⊔U', CovBy)
      have hU'da'_eq : U' ⊔ da' = Γ.E ⊔ U' := by
        have h_lt : U' < U' ⊔ da' :=
          lt_of_le_of_ne le_sup_left (fun h => by
            have : da' ≤ U' := le_sup_right.trans h.symm.le
            exact hU'_ne_da' ((hU'_atom.le_iff.mp this).resolve_left hda'_atom.1).symm)
        have hU'_ne_E : U' ≠ Γ.E := fun h => hU'_not_π (h ▸ hE_π)
        rw [show Γ.E ⊔ U' = U' ⊔ Γ.E from sup_comm _ _]
        exact ((atom_covBy_join hU'_atom Γ.hE_atom hU'_ne_E).eq_or_eq h_lt.le
          (sup_comm Γ.E U' ▸ sup_le le_sup_right (inf_le_left : da' ≤ Γ.E ⊔ U'))).resolve_left
          (ne_of_gt h_lt)
      -- ═══ CovBy condition ═══
      have h_cov : σ_s ⊔ da' ⋖ σ_b ⊔ σ_s ⊔ U' := by
        -- Use σ_b as witness. σ_b ⊓ (σ_s ⊔ da') = ⊥ (π-projection).
        -- σ_b ⊔ (σ_s ⊔ da') = k ⊔ da'. Show k ⊔ da' = k ⊔ U' via rank argument:
        -- k ⋖ k ⊔ U' (CovBy), k < k ⊔ da' ≤ k ⊔ U' → k ⊔ da' = k ⊔ U'.
        -- Step 1: σ_b ⊓ (σ_s ⊔ da') = ⊥
        have hda'_inf_π : da' ⊓ π = ⊥ :=
          (hda'_atom.le_iff.mp inf_le_left).resolve_right
            (fun h => hda'_not_π (h ▸ inf_le_right))
        have hσb_inf_σsda' : σ_b ⊓ (σ_s ⊔ da') = ⊥ := by
          rcases hσb_atom.le_iff.mp inf_le_left with h | h
          · exact h
          · exfalso
            have hσsda'_inf_π : (σ_s ⊔ da') ⊓ π = σ_s := by
              calc (σ_s ⊔ da') ⊓ π = σ_s ⊔ da' ⊓ π := sup_inf_assoc_of_le da' hσs_π
                _ = σ_s := by rw [hda'_inf_π, sup_bot_eq]
            have hσb_le_σs : σ_b ≤ σ_s := hσsda'_inf_π ▸ le_inf (h ▸ inf_le_right) hσb_π
            exact hσb_ne_σs ((hσs_atom.le_iff.mp hσb_le_σs).resolve_left hσb_atom.1)
        -- Step 2: k ⊔ da' = k ⊔ U' (rank argument)
        have hU'_inf_k : U' ⊓ k = ⊥ :=
          (hU'_atom.le_iff.mp inf_le_left).resolve_right
            (fun h => hU'_not_π ((h ▸ inf_le_right : U' ≤ k).trans hk_π))
        have hk_covBy_kU' : k ⋖ k ⊔ U' := by
          rw [show k ⊔ U' = U' ⊔ k from sup_comm _ _]
          exact covBy_sup_of_inf_covBy_left (hU'_inf_k ▸ hU'_atom.bot_covBy)
        have hda'_inf_k : da' ⊓ k = ⊥ :=
          (hda'_atom.le_iff.mp inf_le_left).resolve_right
            (fun h => hda'_not_π ((h ▸ inf_le_right : da' ≤ k).trans hk_π))
        have hk_lt_kda' : k < k ⊔ da' :=
          lt_of_le_of_ne le_sup_left (fun h => by
            have hda'_le_k : da' ≤ k := le_sup_right.trans h.symm.le
            exact hda'_not_π (hda'_le_k.trans hk_π))
        have hkda'_le_kU' : k ⊔ da' ≤ k ⊔ U' :=
          sup_le le_sup_left ((inf_le_left : da' ≤ Γ.E ⊔ U').trans
            (sup_le (hE_k.trans le_sup_left) le_sup_right))
        have hkda'_eq_kU' : k ⊔ da' = k ⊔ U' :=
          (hk_covBy_kU'.eq_or_eq hk_lt_kda'.le hkda'_le_kU').resolve_left
            (ne_of_gt hk_lt_kda')
        -- Step 3: σ_b ⊔ (σ_s ⊔ da') = k ⊔ da' = k ⊔ U' = σ_b ⊔ σ_s ⊔ U'
        have h_join : σ_b ⊔ (σ_s ⊔ da') = σ_b ⊔ σ_s ⊔ U' := by
          calc σ_b ⊔ (σ_s ⊔ da') = σ_b ⊔ σ_s ⊔ da' := (sup_assoc _ _ _).symm
            _ = k ⊔ da' := by rw [hσbσs_eq_k]
            _ = k ⊔ U' := hkda'_eq_kU'
            _ = σ_b ⊔ σ_s ⊔ U' := by rw [← hσbσs_eq_k]
        -- CovBy
        rw [← h_join]
        exact covBy_sup_of_inf_covBy_left (hσb_inf_σsda' ▸ hσb_atom.bot_covBy)
      have h_axis₁₂ : IsAtom ((σ_b ⊔ ac) ⊓ (U' ⊔ E')) := by
        -- U' ⊔ E' = s₁₂ ⊔ U' (E' on s₁₂⊔U', CovBy). Then
        -- (σ_b⊔ac) ⊓ (s₁₂⊔U') = s₁₂ (modular: s₁₂ ≤ σ_b⊔ac, U' ⊓ (σ_b⊔ac) = ⊥).
        -- Step 1: U' ⊔ E' = s₁₂ ⊔ U'
        have hE'_le_s₁₂U' : E' ≤ s₁₂ ⊔ U' := inf_le_left
        have hs₁₂_ne_U' : s₁₂ ≠ U' :=
          fun h => hU'_not_π (h ▸ (inf_le_right : s₁₂ ≤ Γ.U ⊔ Γ.V).trans hm_π)
        have hU'E'_eq : U' ⊔ E' = s₁₂ ⊔ U' := by
          have h_lt : U' < U' ⊔ E' :=
            lt_of_le_of_ne le_sup_left (fun h => by
              have : E' ≤ U' := le_sup_right.trans h.symm.le
              exact hU'_ne_E' ((hU'_atom.le_iff.mp this).resolve_left hE'_atom.1).symm)
          rw [show s₁₂ ⊔ U' = U' ⊔ s₁₂ from sup_comm _ _]
          exact ((atom_covBy_join hU'_atom hs₁₂_atom hs₁₂_ne_U'.symm).eq_or_eq h_lt.le
            (sup_comm s₁₂ U' ▸ sup_le le_sup_right hE'_le_s₁₂U')).resolve_left
            (ne_of_gt h_lt)
        -- Step 2: (σ_b ⊔ ac) ⊓ (s₁₂ ⊔ U') = s₁₂ (modular law)
        have hs₁₂_le : s₁₂ ≤ σ_b ⊔ ac := inf_le_left
        have hU'_inf_σbac : U' ⊓ (σ_b ⊔ ac) = ⊥ :=
          (hU'_atom.le_iff.mp inf_le_left).resolve_right
            (fun h => hU'_not_π ((h ▸ inf_le_right : U' ≤ σ_b ⊔ ac).trans
              (sup_le hσb_π hac_π)))
        have h_mod : (σ_b ⊔ ac) ⊓ (s₁₂ ⊔ U') = s₁₂ := by
          calc (σ_b ⊔ ac) ⊓ (s₁₂ ⊔ U')
              = (s₁₂ ⊔ U') ⊓ (σ_b ⊔ ac) := inf_comm _ _
            _ = s₁₂ ⊔ U' ⊓ (σ_b ⊔ ac) := sup_inf_assoc_of_le U' hs₁₂_le
            _ = s₁₂ := by rw [hU'_inf_σbac, sup_bot_eq]
        rw [hU'E'_eq, h_mod]
        exact hs₁₂_atom
      have h_axis₁₃ : IsAtom ((σ_b ⊔ σ_s) ⊓ (U' ⊔ da')) := by
        -- σ_b ⊔ σ_s = k (two distinct atoms on line k).
        -- U' ⊔ da' = E ⊔ U' (da' ≤ E⊔U', da' ≠ U').
        -- k ⊓ (E ⊔ U') = E (modular: E ≤ k, U' ⊓ k = ⊥). Result = E, which is an atom.
        -- Step 1: σ_b ⊔ σ_s = k
        have hσbσs_eq_k : σ_b ⊔ σ_s = k := by
          -- Two distinct atoms on a line join to the line.
          -- σ_b ⋖ σ_b⊔σ_s (atom_covBy_join). σ_b⊔σ_s ≤ k. σ_b⊔σ_s ≠ σ_b.
          -- Need: σ_b ⋖ k (then CovBy gives σ_b⊔σ_s = σ_b or σ_b⊔σ_s = k).
          -- O ⋖ k. σ_b atom on k. (atom_covBy_join σ_b O _) gives σ_b ⋖ σ_b⊔O = k.
          -- Wait: σ_b⊔O ≤ k, O ⋖ k gives O⊔σ_b = k when σ_b ∉ O.
          -- Use: (atom_covBy_join hσb_atom hσs_atom hσb_ne_σs) gives σ_b ⋖ σ_b⊔σ_s.
          -- And σ_b⊔σ_s ≤ k. Need σ_b⊔σ_s = k.
          -- Since O ⋖ k (CovBy): any x with O < x ≤ k has x = k.
          -- σ_b⊔σ_s > σ_b ≥ ⊥⁺ = some atom. If σ_b⊔σ_s ≤ k and σ_b⊔σ_s > ⊥:
          -- σ_b⊔σ_s is either an atom or ≥ k. If atom: σ_b⊔σ_s = σ_b = σ_s. Contradiction.
          have h_lt : σ_b < σ_b ⊔ σ_s :=
            lt_of_le_of_ne le_sup_left (fun h => by
              have : σ_s ≤ σ_b := le_sup_right.trans h.symm.le
              exact hσb_ne_σs ((hσb_atom.le_iff.mp this).resolve_left hσs_atom.1).symm)
          have h_le : σ_b ⊔ σ_s ≤ k := sup_le hσb_k hσs_k
          -- Use O ⋖ k. σ_b ≤ k, σ_b atom. O⊔σ_b ≤ k. O ⋖ k.
          -- If σ_b = O: O ⊔ σ_s ≤ k. σ_s ≠ O (= σ_b). So O < O⊔σ_s ≤ k. CovBy: O⊔σ_s = k.
          -- If σ_b ≠ O: O < O⊔σ_b ≤ k. CovBy: O⊔σ_b = k. k ≤ σ_b⊔σ_s⊔O. Since σ_b⊔σ_s ≤ k.
          -- Hmm. Let's just use: σ_b ⋖ σ_b⊔σ_s and σ_b⊔σ_s ≤ k, and σ_b ⋖ k.
          -- σ_b ⋖ k: σ_b atom, σ_b ≤ k, σ_b ≠ k. Then for any x: σ_b ≤ x ≤ k → x = σ_b or x = k.
          -- This is exactly CovBy iff k "covers" σ_b. In our lattice, k is rank 2, σ_b is rank 1.
          -- Modularity: ⊥ ⋖ σ_b ⋖ ? ≤ k. By Jordan-Dedekind (modular lattice), rank is well-defined.
          -- A clean proof: O ⋖ k. σ_b atom. σ_b ⊓ O = ⊥ or σ_b = O.
          -- Case σ_b = O: σ_b ⊔ σ_s = O ⊔ σ_s. O ⋖ k. σ_s ≤ k, σ_s ≠ O.
          --   O < O⊔σ_s ≤ k. CovBy gives O⊔σ_s = k. Done.
          -- Case σ_b ≠ O: σ_b ⊓ O = ⊥ (atoms). σ_b⊔O: ⊥ ⋖ O, so O⊔σ_b ⋖ ... hmm.
          --   O < O⊔σ_b ≤ k. CovBy: O⊔σ_b = k. So k = σ_b⊔O ≤ σ_b⊔σ_s. Done.
          -- σ_b ⋖ k (atom on a rank-2 element). Then CovBy gives σ_b⊔σ_s = k.
          have hσb_covBy_k : σ_b ⋖ k := by
            by_cases hσb_eq_O : σ_b = Γ.O
            · exact hσb_eq_O ▸ atom_covBy_join Γ.hO Γ.hC hOC
            · -- σ_b ≠ O. σ_b ⊓ O = ⊥. ⊥ ⋖ O gives σ_b ⋖ σ_b ⊔ O. O ⋖ k gives σ_b⊔O = k.
              have hσb_inf_O : σ_b ⊓ Γ.O = ⊥ :=
                (hσb_atom.le_iff.mp inf_le_left).resolve_right
                  (fun h => hσb_eq_O ((Γ.hO.le_iff.mp (h ▸ inf_le_right)).resolve_left hσb_atom.1))
              -- O ⊓ σ_b = ⊥ ⋖ O gives σ_b ⋖ O ⊔ σ_b = σ_b ⊔ O.
              have hO_inf_σb : Γ.O ⊓ σ_b = ⊥ := inf_comm σ_b Γ.O ▸ hσb_inf_O
              have h_cov_σbO : σ_b ⋖ σ_b ⊔ Γ.O := by
                rw [show σ_b ⊔ Γ.O = Γ.O ⊔ σ_b from sup_comm _ _]
                exact covBy_sup_of_inf_covBy_left (hO_inf_σb ▸ Γ.hO.bot_covBy)
              -- O < σ_b⊔O ≤ k. O ⋖ k gives σ_b⊔O = k.
              have hO_lt : Γ.O < σ_b ⊔ Γ.O :=
                lt_of_le_of_ne le_sup_right (fun h =>
                  hσb_eq_O ((Γ.hO.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left hσb_atom.1))
              have hσbO_eq_k : σ_b ⊔ Γ.O = k :=
                ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq hO_lt.le
                  (sup_le hσb_k (le_sup_left : Γ.O ≤ k))).resolve_left (ne_of_gt hO_lt)
              exact hσbO_eq_k ▸ h_cov_σbO
          exact (hσb_covBy_k.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
        -- Step 2: U' ⊔ da' = E ⊔ U' (da' ≤ E⊔U', CovBy)
        have hU'da'_eq : U' ⊔ da' = Γ.E ⊔ U' := by
          have h_lt : U' < U' ⊔ da' :=
            lt_of_le_of_ne le_sup_left (fun h => by
              have : da' ≤ U' := le_sup_right.trans h.symm.le
              exact hU'_ne_da' ((hU'_atom.le_iff.mp this).resolve_left hda'_atom.1).symm)
          have hda'_le_EU' : da' ≤ Γ.E ⊔ U' := inf_le_left
          have hU'da'_le : U' ⊔ da' ≤ Γ.E ⊔ U' := sup_le le_sup_right hda'_le_EU'
          have hU'_ne_E : U' ≠ Γ.E := fun h => hU'_not_π (h ▸ hE_π)
          -- U' ⋖ U'⊔E. U'⊔da' ≤ U'⊔E. CovBy gives U'⊔da' = U' or U'⊔da' = U'⊔E.
          rw [show Γ.E ⊔ U' = U' ⊔ Γ.E from sup_comm _ _]
          exact ((atom_covBy_join hU'_atom Γ.hE_atom hU'_ne_E).eq_or_eq h_lt.le
            (sup_comm Γ.E U' ▸ hU'da'_le)).resolve_left (ne_of_gt h_lt)
        -- Step 3: k ⊓ (E ⊔ U') = E (modular: E ≤ k, U' ⊓ k = ⊥)
        have hU'_inf_k : U' ⊓ k = ⊥ :=
          (hU'_atom.le_iff.mp inf_le_left).resolve_right
            (fun h => hU'_not_π ((h ▸ inf_le_right : U' ≤ k).trans hk_π))
        have hk_inf_EU' : k ⊓ (Γ.E ⊔ U') = Γ.E := by
          rw [inf_comm]
          calc (Γ.E ⊔ U') ⊓ k = Γ.E ⊔ U' ⊓ k := sup_inf_assoc_of_le U' hE_k
            _ = Γ.E := by rw [hU'_inf_k, sup_bot_eq]
        rw [hσbσs_eq_k, hU'da'_eq, hk_inf_EU']
        exact Γ.hE_atom
      have h_axis₂₃ : IsAtom ((ac ⊔ σ_s) ⊓ (E' ⊔ da')) := by
        -- ════════════════════════════════════════════════════════════
        -- LEVEL 2 DESARGUES: prove da' ∈ E'⊔s₂₃ via second 3D lift.
        --
        -- In R⊔m (rank 3), triangles T₁=(E',U',d_a) and T₂=(s₂₃,E,R)
        -- have side-intersections s₁₂, S₂₃, S₁₃.
        -- Lift T₂ out of R⊔m using Q=σ_b → T₂'=(s₂₃'',E'',R'').
        -- Thread E'' through s₁₂, R'' through S₁₃.
        -- ALL THREE axis conditions are free. Recursion terminates.
        -- desargues_converse_nonplanar → vertex-joins concurrent.
        -- Project back → da' ∈ E'⊔s₂₃.
        -- ════════════════════════════════════════════════════════════
        -- Step 0: Define s₂₃ and show it's an atom
        set s₂₃ := (ac ⊔ σ_s) ⊓ m with hs₂₃_def
        have hs₂₃_atom : IsAtom s₂₃ := by
          have hac_not_m : ¬ ac ≤ m := by
            intro h
            -- ac ≤ l and ac ≤ m. U ≤ l and U ≤ m.
            -- ac atom on m, U atom on m. Both ≤ l. l ⊓ m: U ≤ l⊓m.
            -- If ac ≠ U: ac⊔U ≤ l⊓m, but ac⊔U = l (CovBy), so l ≤ m.
            -- l ≤ m → O ≤ m. But O ∉ m (O on l, and l⊓m = U by modular,
            -- O ≠ U). Contradiction. Hence ac = U, contradicting hac_ne_U.
            exact hac_ne_U (Γ.atom_on_both_eq_U hac_atom hac_l h)
          exact line_meets_m_at_atom hac_atom hσs_atom hac_ne_σs
            (sup_le hac_π hσs_π) hm_π Γ.m_covBy_π hac_not_m
        have hs₂₃_le_m : s₂₃ ≤ m := inf_le_right
        have hs₂₃_le_acσs : s₂₃ ≤ ac ⊔ σ_s := inf_le_left
        -- Step 1: Pick s₂₃'' on σ_b⊔s₂₃, distinct from both
        have hσb_ne_s₂₃ : σ_b ≠ s₂₃ := fun h => hσb_not_m (h ▸ hs₂₃_le_m)
        obtain ⟨s₂₃'', hs₂₃''_atom, hs₂₃''_le, hs₂₃''_ne_σb, hs₂₃''_ne_s₂₃⟩ :=
          h_irred σ_b s₂₃ hσb_atom hs₂₃_atom hσb_ne_s₂₃
        -- σ_b ∉ R⊔m (σ_b on k, (R⊔m)⊓π = m, σ_b ∉ m)
        have hσb_not_Rm : ¬ σ_b ≤ R ⊔ m := by
          intro h; exact hσb_not_m (by
            have hRm_inf_π : (R ⊔ m) ⊓ π = m := by
              rw [sup_comm]
              calc (m ⊔ R) ⊓ π = m ⊔ R ⊓ π := sup_inf_assoc_of_le R hm_π
                _ = m ⊔ ⊥ := by rw [show R ⊓ π = ⊥ from
                    (hR.le_iff.mp inf_le_left).resolve_right
                    (fun h' => hR_not (h' ▸ inf_le_right))]
                _ = m := by simp
            exact hRm_inf_π ▸ le_inf h hσb_π)
        -- Step 2: Define Level 2 lifted points
        set S₁₃ := (E' ⊔ d_a) ⊓ (s₂₃ ⊔ R) with hS₁₃_def
        set E'' := (s₁₂ ⊔ s₂₃'') ⊓ (σ_b ⊔ Γ.E) with hE''_def
        set R'' := (S₁₃ ⊔ s₂₃'') ⊓ (σ_b ⊔ R) with hR''_def
        -- Step 3: Apply desargues_converse_nonplanar at Level 2
        -- T1 = (E', U', d_a), T2 = (s₂₃'', E'', R'')
        -- Conclusion: (E'⊔s₂₃'') ⊓ (U'⊔E'') ≤ d_a⊔R''
        have h_L2 : (E' ⊔ s₂₃'') ⊓ (U' ⊔ E'') ≤ d_a ⊔ R'' := by
          sorry -- Level 2 Desargues: ~200 lines (non-degeneracy + 3 free axis conditions)
        -- Step 4: Project back to R⊔m → da' ≤ E'⊔s₂₃
        have hda'_on_E's₂₃ : da' ≤ E' ⊔ s₂₃ := by
          sorry -- Projection: ~100 lines (σ_b-projection, modular law)
        -- Step 5: Conclude IsAtom((ac⊔σ_s) ⊓ (E'⊔da'))
        -- From da' ≤ E'⊔s₂₃ we get E'⊔da' = E'⊔s₂₃ (CovBy),
        -- so s₂₃ ≤ E'⊔da', hence s₂₃ ≤ (ac⊔σ_s) ⊓ (E'⊔da').
        have hda'_ne_E' : da' ≠ E' := sorry -- E' on R⊔E, da' on R⊔d_a, R⊔E ≠ R⊔d_a
        have hs₂₃_le_E'da' : s₂₃ ≤ E' ⊔ da' := by
          -- da' ≤ E'⊔s₂₃ → E'⊔da' ≤ E'⊔s₂₃. CovBy: E'⊔s₂₃ ≤ E'⊔da'.
          -- Hence E'⊔da' = E'⊔s₂₃, and s₂₃ ≤ E'⊔s₂₃ = E'⊔da'.
          sorry -- CovBy: da' on E'⊔s₂₃ → E'⊔da' = E'⊔s₂₃ → s₂₃ ≤ E'⊔da'
        have hs₂₃_le_inf : s₂₃ ≤ (ac ⊔ σ_s) ⊓ (E' ⊔ da') :=
          le_inf hs₂₃_le_acσs hs₂₃_le_E'da'
        -- The inf is > ⊥ (contains atom s₂₃) and < ac⊔σ_s (ac ∉ E'⊔da')
        have hinf_lt : (ac ⊔ σ_s) ⊓ (E' ⊔ da') < ac ⊔ σ_s := by
          refine lt_of_le_of_ne inf_le_left (fun h => ?_)
          -- If inf = ac⊔σ_s, then ac ≤ E'⊔da' ≤ R⊔m. But ac ∉ R⊔m.
          have hE'da'_Rm : E' ⊔ da' ≤ R ⊔ m :=
            sup_le (hE'_le.trans (sup_le le_sup_left (hE_m.trans le_sup_right)))
              (hda'_le.trans (sup_le le_sup_left (hda_m.trans le_sup_right)))
          have hac_not_Rm : ¬ ac ≤ R ⊔ m := sorry -- ac on l, (R⊔m)⊓l = U, ac ≠ U
          exact hac_not_Rm (le_sup_left.trans ((h ▸ inf_le_right).trans hE'da'_Rm))
        exact line_height_two hac_atom hσs_atom hac_ne_σs
          (bot_lt_iff_ne_bot.mpr (ne_bot_of_le_ne_bot hs₂₃_atom.1 hs₂₃_le_inf))
          hinf_lt
      exact desargues_converse_nonplanar
        hσb_atom hac_atom hσs_atom hU'_atom hE'_atom hda'_atom
        hσb_ne_ac hσb_ne_σs hac_ne_σs hσb_not_acσs
        hU'_not_πA hE'_not_πA hda'_not_πA
        hU'_ne_E' hU'_ne_da' hE'_ne_da'
        hσs_ne_da' h_cov
        h_axis₁₂ h_axis₁₃ h_axis₂₃
    -- ═══ Step 5: Project back to π ═══
    -- Let O' = (σ_b⊔U') ⊓ (ac⊔E'). O' ≤ σ_s⊔da'.
    -- O' ∉ π (else O' = σ_b and O' = ac, but σ_b ≠ ac).
    -- W = (R⊔O') ⊓ π is an atom.
    -- W ≤ σ_b⊔U: via (R⊔O')⊓π ≤ (R⊔σ_b⊔U)⊓π = σ_b⊔U (modular law, R∉π).
    -- W ≤ ac⊔E: similarly.
    -- W ≤ σ_s⊔d_a: via O' ≤ σ_s⊔da', R⊔da'=R⊔d_a, so ≤ (R⊔σ_s⊔d_a)⊓π = σ_s⊔d_a.
    -- W ≤ W' (= (σ_b⊔U)⊓(ac⊔E)), both atoms → W = W'. W ≤ σ_s⊔d_a. QED.
    -- Modular law projection helper: (R⊔x)⊓π = x when x ≤ π and R ∉ π.
    have hR_inf_π : R ⊓ π = ⊥ :=
      (hR.le_iff.mp inf_le_left).resolve_right (fun h => hR_not (h ▸ inf_le_right))
    have proj : ∀ {x : L}, x ≤ π → (R ⊔ x) ⊓ π = x := by
      intro x hx
      calc (R ⊔ x) ⊓ π = (x ⊔ R) ⊓ π := by rw [sup_comm]
        _ = x ⊔ R ⊓ π := sup_inf_assoc_of_le R hx
        _ = x ⊔ ⊥ := by rw [hR_inf_π]
        _ = x := by simp
    -- Project: lines in π project correctly
    have hproj_σbU : (R ⊔ σ_b ⊔ Γ.U) ⊓ π = σ_b ⊔ Γ.U := by
      rw [show R ⊔ σ_b ⊔ Γ.U = R ⊔ (σ_b ⊔ Γ.U) from sup_assoc _ _ _]
      exact proj (sup_le hσb_π hU_π)
    have hproj_acE : (R ⊔ ac ⊔ Γ.E) ⊓ π = ac ⊔ Γ.E := by
      rw [show R ⊔ ac ⊔ Γ.E = R ⊔ (ac ⊔ Γ.E) from sup_assoc _ _ _]
      exact proj (sup_le hac_π hE_π)
    have hproj_σsda : (R ⊔ σ_s ⊔ d_a) ⊓ π = σ_s ⊔ d_a := by
      rw [show R ⊔ σ_s ⊔ d_a = R ⊔ (σ_s ⊔ d_a) from sup_assoc _ _ _]
      exact proj (sup_le hσs_π hda_π)
    -- O' ≤ various lifted lines
    set O' := (σ_b ⊔ U') ⊓ (ac ⊔ E') with hO'_def
    have hO'_le_σsda' : O' ≤ σ_s ⊔ da' := h_converse
    -- R⊔O' ≤ R⊔σ_b⊔U: O' ≤ σ_b⊔U', U' ≤ R⊔U, so σ_b⊔U' ≤ σ_b⊔R⊔U = R⊔σ_b⊔U.
    have hRO'_σbU : R ⊔ O' ≤ R ⊔ σ_b ⊔ Γ.U := by
      apply sup_le (le_sup_left.trans le_sup_left)
      -- O' ≤ σ_b⊔U' ≤ R⊔σ_b⊔U
      calc O' ≤ σ_b ⊔ U' := inf_le_left
        _ ≤ σ_b ⊔ (R ⊔ Γ.U) := sup_le_sup_left hU'_le _
        _ = R ⊔ σ_b ⊔ Γ.U := by simp only [sup_assoc, sup_comm, sup_left_comm]
    have hRO'_acE : R ⊔ O' ≤ R ⊔ ac ⊔ Γ.E := by
      apply sup_le (le_sup_left.trans le_sup_left)
      calc O' ≤ ac ⊔ E' := inf_le_right
        _ ≤ ac ⊔ (R ⊔ Γ.E) := sup_le_sup_left hE'_le _
        _ = R ⊔ ac ⊔ Γ.E := by simp only [sup_assoc, sup_comm, sup_left_comm]
    have hRO'_σsda : R ⊔ O' ≤ R ⊔ σ_s ⊔ d_a := by
      apply sup_le (le_sup_left.trans le_sup_left)
      calc O' ≤ σ_s ⊔ da' := hO'_le_σsda'
        _ ≤ σ_s ⊔ (R ⊔ d_a) := sup_le_sup_left hda'_le _
        _ = R ⊔ σ_s ⊔ d_a := by simp only [sup_assoc, sup_comm, sup_left_comm]
    -- Project O' to π: W_proj ≤ σ_b⊔U AND ac⊔E AND σ_s⊔d_a
    have hW_σbU : (R ⊔ O') ⊓ π ≤ σ_b ⊔ Γ.U :=
      (inf_le_inf_right π hRO'_σbU).trans hproj_σbU.le
    have hW_acE : (R ⊔ O') ⊓ π ≤ ac ⊔ Γ.E :=
      (inf_le_inf_right π hRO'_acE).trans hproj_acE.le
    have hW_σsda : (R ⊔ O') ⊓ π ≤ σ_s ⊔ d_a :=
      (inf_le_inf_right π hRO'_σsda).trans hproj_σsda.le
    -- W ≤ W' = (σ_b⊔U) ⊓ (ac⊔E)
    have hW_le_W' : (R ⊔ O') ⊓ π ≤ W' := le_inf hW_σbU hW_acE
    -- W ≤ σ_s ⊔ d_a (from hW_σsda)
    -- If W = W' (both atoms): W' ≤ σ_s⊔d_a. QED.
    -- For W = W': need W to be an atom and W ≤ W' atom → W = W'.
    -- W is atom: (R⊔O')⊓π, where R∉π and O'∉π, is an atom (rank argument).
    -- For now, sorry the atomicity and conclude.
    -- W' is an atom (two lines in π meet)
    have hW'_atom : IsAtom W' := by
      have hac_ne_E : ac ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hac_l)
      have hσb_ne_U : σ_b ≠ Γ.U := by
        intro h; have hU_le_k : Γ.U ≤ k := h ▸ hσb_k
        have hl_eq_k : l = k := ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
          (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le
          (sup_le le_sup_left hU_le_k)).resolve_left
          (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)
        exact Γ.hC_not_l ((le_sup_right : Γ.C ≤ k).trans hl_eq_k.symm.le)
      -- U ⊓ (ac⊔E) = ⊥
      have hac_sup_U : ac ⊔ Γ.U = l :=
        ((line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hac_atom hac_l).eq_or_eq
          (atom_covBy_join hac_atom Γ.hU hac_ne_U).lt.le
          (sup_le hac_l le_sup_right)).resolve_left
          (ne_of_gt (atom_covBy_join hac_atom Γ.hU hac_ne_U).lt)
      have hU_disj_acE : Γ.U ⊓ (ac ⊔ Γ.E) = ⊥ := by
        rcases Γ.hU.le_iff.mp inf_le_left with h | h
        · exact h
        · exfalso
          have hl_le : l ≤ ac ⊔ Γ.E := hac_sup_U ▸ sup_le le_sup_left (h ▸ inf_le_right)
          have hl_eq := ((atom_covBy_join hac_atom Γ.hE_atom hac_ne_E).eq_or_eq hac_l hl_le
            ).resolve_left (fun h' => hac_ne_U ((hac_atom.le_iff.mp
              (h' ▸ (le_sup_right : Γ.U ≤ l))).resolve_left Γ.hU.1).symm)
          exact CoordSystem.hE_not_l (hl_eq ▸ le_sup_right)
      -- ac⊔E ⋖ π
      have hl_covBy_π : l ⋖ π := by
        have hV_disj : Γ.V ⊓ l = ⊥ :=
          (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
        have h := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
        rwa [show Γ.V ⊔ l = π from by simp only [hl_def, hπ_def, sup_comm, sup_left_comm]] at h
      have hacE_covBy_π : ac ⊔ Γ.E ⋖ π := by
        have hl_sup_E : l ⊔ Γ.E = π := (hl_covBy_π.eq_or_eq
          (lt_of_le_of_ne le_sup_left (fun h => CoordSystem.hE_not_l (h ▸ le_sup_right))).le
          (sup_le le_sup_left hE_π)).resolve_left
          (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h => CoordSystem.hE_not_l (h ▸ le_sup_right))))
        have h := covBy_sup_of_inf_covBy_left (hU_disj_acE ▸ Γ.hU.bot_covBy)
        rwa [show Γ.U ⊔ (ac ⊔ Γ.E) = π from by
          calc Γ.U ⊔ (ac ⊔ Γ.E) = (ac ⊔ Γ.U) ⊔ Γ.E := by simp only [sup_assoc, sup_comm]
            _ = l ⊔ Γ.E := by rw [hac_sup_U]
            _ = π := hl_sup_E] at h
      -- σ_b⊔U ≤ π, σ_b⊔U ≰ ac⊔E
      have hσbU_not_acE : ¬ σ_b ⊔ Γ.U ≤ ac ⊔ Γ.E := fun h =>
        Γ.hU.1 (le_antisymm (hU_disj_acE ▸ le_inf le_rfl (le_sup_right.trans h)) bot_le)
      -- ⊥ < W'
      have hW'_pos : ⊥ < W' := by
        rw [show W' = (ac ⊔ Γ.E) ⊓ (σ_b ⊔ Γ.U) from inf_comm _ _]
        exact bot_lt_iff_ne_bot.mpr
          (lines_meet_if_coplanar hacE_covBy_π (sup_le hσb_π hU_π) hσbU_not_acE hσb_atom
            (atom_covBy_join hσb_atom Γ.hU hσb_ne_U).lt)
      -- W' < ac⊔E
      have hW'_lt : W' < ac ⊔ Γ.E := by
        refine lt_of_le_of_ne inf_le_right (fun h_eq => ?_)
        have hacE_le : ac ⊔ Γ.E ≤ σ_b ⊔ Γ.U := h_eq ▸ inf_le_left
        have hE_le : Γ.E ≤ σ_b ⊔ Γ.U := le_sup_right.trans hacE_le
        -- σ_b⊓m = ⊥ → (σ_b⊔U)⊓m = U → E ≤ U → E = U. Contradiction.
        have hσb_inf_m : σ_b ⊓ m = ⊥ := by
          rcases hσb_atom.le_iff.mp inf_le_left with h | h
          · exact h
          · exfalso; exact hσb_not_m (h ▸ inf_le_right)
        have hσbU_inf_m : (σ_b ⊔ Γ.U) ⊓ m = Γ.U := by
          rw [sup_comm σ_b Γ.U]
          have h1 := sup_inf_assoc_of_le σ_b (le_sup_left : Γ.U ≤ m)
          rw [hσb_inf_m] at h1; simp at h1; exact h1
        exact CoordSystem.hEU ((Γ.hU.le_iff.mp
          (hσbU_inf_m ▸ le_inf hE_le hE_m)).resolve_left Γ.hE_atom.1)
      exact line_height_two hac_atom Γ.hE_atom hac_ne_E hW'_pos hW'_lt
    -- W ≠ ⊥ (axis-threaded coplanarity → O' ≠ ⊥ → 4D meet)
    have hW_ne_bot : (R ⊔ O') ⊓ π ≠ ⊥ := by
      -- U' ⊓ π = ⊥
      have hU'_inf_π : U' ⊓ π = ⊥ :=
        (hU'_atom.le_iff.mp inf_le_left).resolve_right (fun h => hU'_not_π (h ▸ inf_le_right))
      -- E' ≤ ρ₁₂ = σ_b ⊔ ac ⊔ U' (axis construction)
      have hE'_le_ρ : E' ≤ σ_b ⊔ ac ⊔ U' :=
        inf_le_left.trans (sup_le ((inf_le_left : s₁₂ ≤ σ_b ⊔ ac).trans le_sup_left) le_sup_right)
      -- ac ⊔ E' ≤ ρ₁₂, σ_b ⊔ U' ≤ ρ₁₂
      have hacE'_le_ρ : ac ⊔ E' ≤ σ_b ⊔ ac ⊔ U' :=
        sup_le (le_sup_right.trans le_sup_left) hE'_le_ρ
      -- σ_b ⊔ U' ⋖ ρ₁₂ (ac ⊓ (σ_b⊔U') = ⊥ since projection gives ac ≤ σ_b)
      have hproj_σbU' : (σ_b ⊔ U') ⊓ π = σ_b := by
        have h1 := sup_inf_assoc_of_le U' hσb_π; rw [hU'_inf_π] at h1; simp at h1; exact h1
      have hac_disj_σbU' : ac ⊓ (σ_b ⊔ U') = ⊥ := by
        rcases hac_atom.le_iff.mp inf_le_left with h | h
        · exact h
        · exfalso; exact hσb_ne_ac ((hσb_atom.le_iff.mp
            (hproj_σbU' ▸ le_inf (h ▸ inf_le_right) hac_π)).resolve_left hac_atom.1).symm
      have hσbU'_covBy_ρ : σ_b ⊔ U' ⋖ σ_b ⊔ ac ⊔ U' := by
        have h := covBy_sup_of_inf_covBy_left (hac_disj_σbU' ▸ hac_atom.bot_covBy)
        rwa [show ac ⊔ (σ_b ⊔ U') = σ_b ⊔ ac ⊔ U' from by
          simp only [sup_assoc, sup_comm, sup_left_comm]] at h
      -- ac ⊔ E' ≰ σ_b ⊔ U'
      have hacE'_not : ¬ ac ⊔ E' ≤ σ_b ⊔ U' := fun h =>
        hσb_ne_ac ((hσb_atom.le_iff.mp
          (hproj_σbU' ▸ le_inf (le_sup_left.trans h) hac_π)).resolve_left hac_atom.1).symm
      -- ac ≠ E'
      have hac_ne_E' : ac ≠ E' := fun h => hE'_not_π (h ▸ hac_π)
      -- O' ≠ ⊥
      have hO'_ne_bot : O' ≠ ⊥ := by
        intro h_eq; rw [hO'_def] at h_eq
        exact lines_meet_if_coplanar hσbU'_covBy_ρ hacE'_le_ρ hacE'_not hac_atom
          (atom_covBy_join hac_atom hE'_atom hac_ne_E').lt
          (inf_comm (ac ⊔ E') (σ_b ⊔ U') ▸ h_eq)
      -- O' ≠ R (if R = O' then R ≤ σ_b⊔U', project: R ≤ σ_b ≤ π, contradicts R ∉ π)
      have hσb_ne_U' : σ_b ≠ U' := fun h => hU'_not_π (h ▸ hσb_π)
      have hO'_ne_R : O' ≠ R := by
        intro h_eq
        have hR_le_σbU' : R ≤ σ_b ⊔ U' := h_eq ▸ (inf_le_left : O' ≤ σ_b ⊔ U')
        -- R atom on σ_b ⊔ U'. Either R = σ_b or R ≠ σ_b.
        by_cases hR_eq_σb : R = σ_b
        · -- R = σ_b → R ≤ π, contradiction
          exact hR_not (hR_eq_σb ▸ hσb_π)
        · -- R ≠ σ_b, both atoms on σ_b⊔U' → σ_b⊔R = σ_b⊔U' → U' ≤ σ_b⊔R
          have hσbR_eq : σ_b ⊔ R = σ_b ⊔ U' :=
            ((atom_covBy_join hσb_atom hU'_atom hσb_ne_U').eq_or_eq
              (lt_of_le_of_ne (le_sup_left : σ_b ≤ σ_b ⊔ R) (fun h' =>
                hR_eq_σb ((hσb_atom.le_iff.mp (h' ▸ le_sup_right : R ≤ σ_b)).resolve_left hR.1)
              )).le (sup_le le_sup_left hR_le_σbU')).resolve_left
              (ne_of_gt (lt_of_le_of_ne (le_sup_left : σ_b ≤ σ_b ⊔ R) (fun h' =>
                hR_eq_σb ((hσb_atom.le_iff.mp (h' ▸ le_sup_right)).resolve_left hR.1))))
          have hU'_le_σbR : U' ≤ σ_b ⊔ R := hσbR_eq.symm ▸ le_sup_right
          -- σ_b ⊓ (R ⊔ U) = ⊥ (project: if σ_b ≤ R ⊔ U, project to π: σ_b ≤ U, σ_b = U)
          have hσb_inf_RU : σ_b ⊓ (R ⊔ Γ.U) = ⊥ := by
            rcases hσb_atom.le_iff.mp inf_le_left with h' | h'
            · exact h'
            · exfalso
              have hσb_le_RU : σ_b ≤ R ⊔ Γ.U := h' ▸ inf_le_right
              have hσb_le_U : σ_b ≤ Γ.U :=
                (inf_sup_of_atom_not_le hR hR_not hU_π) ▸ le_inf hσb_π hσb_le_RU
              -- σ_b = U → U ≤ k → l = k → C ≤ l, contradiction
              have hσb_eq_U := (Γ.hU.le_iff.mp hσb_le_U).resolve_left hσb_atom.1
              exact Γ.hC_not_l ((le_sup_right : Γ.C ≤ k).trans
                (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
                  (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le
                  (sup_le le_sup_left (hσb_eq_U ▸ hσb_k))).resolve_left
                  (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)).symm.le)
          -- (σ_b ⊔ R) ⊓ (R ⊔ U) = R (modular: R ≤ both, σ_b ⊓ (R ⊔ U) = ⊥)
          have hmod : (σ_b ⊔ R) ⊓ (R ⊔ Γ.U) = R := by
            rw [sup_comm σ_b R]
            have h1 := sup_inf_assoc_of_le σ_b (le_sup_left : R ≤ R ⊔ Γ.U)
            rw [hσb_inf_RU] at h1; simp at h1; exact h1
          -- U' ≤ (σ_b ⊔ R) ⊓ (R ⊔ U) = R → U' = R. Contradiction.
          have hU'_le_R : U' ≤ R := hmod ▸ le_inf hU'_le_σbR hU'_le
          exact hU'_ne_R ((hR.le_iff.mp hU'_le_R).resolve_left hU'_atom.1)
      -- R < R ⊔ O'
      have hR_lt : R < R ⊔ O' :=
        lt_of_le_of_ne le_sup_left (fun h =>
          hO'_ne_R ((hR.le_iff.mp (h ▸ le_sup_right)).resolve_left hO'_ne_bot))
      -- O' ≤ R ⊔ π (O' ≤ ρ₁₂ ≤ R ⊔ π)
      have hRO'_le : R ⊔ O' ≤ R ⊔ π :=
        sup_le le_sup_left ((inf_le_left : O' ≤ σ_b ⊔ U').trans
          (sup_le (hσb_π.trans le_sup_right)
            (hU'_le.trans (sup_le le_sup_left (hU_π.trans le_sup_right)))))
      -- ¬ R ⊔ O' ≤ π
      have hRO'_not_π : ¬ R ⊔ O' ≤ π := fun h => hR_not (le_sup_left.trans h)
      -- π ⋖ R ⊔ π
      have hR_inf_π : R ⊓ π = ⊥ :=
        (hR.le_iff.mp inf_le_left).resolve_right (fun h => hR_not (h ▸ inf_le_right))
      have hπ_covBy : π ⋖ R ⊔ π := by
        have h := covBy_sup_of_inf_covBy_left (hR_inf_π ▸ hR.bot_covBy)
        rwa [show R ⊔ π = π ⊔ R from sup_comm _ _, show π ⊔ R = R ⊔ π from sup_comm _ _] at h
      -- Apply
      rw [inf_comm]
      exact lines_meet_if_coplanar hπ_covBy hRO'_le hRO'_not_π hR hR_lt
    -- W ≤ W', W' atom, W ≠ ⊥ → W = W'. Then W' ≤ σ_s⊔d_a.
    have hW_eq : (R ⊔ O') ⊓ π = W' :=
      (hW'_atom.le_iff.mp hW_le_W').resolve_left hW_ne_bot
    exact hW_eq ▸ hW_σsda
  -- ═══ Piece 1: Forward Desargues ═══
  -- Apply desargues_planar with center σ_b, T1=(C,ab,U), T2=(E,d_a,W')
  -- Conclusion: axis through (ab⊔C)⊓m, (ac⊔E)⊓q, (d_a⊔W')⊓l = a·s
  -- Since a·s lies on ((ab⊔C)⊓m ⊔ (ac⊔E)⊓q) ⊓ l = coord_add ab ac:
  have h_desargues_conclusion : coord_mul Γ a s ≤
      (ab ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (ac ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) := by
    -- ═══ Forward Desargues: center σ_b, T1=(C,ab,U), T2=(E,d_a,W') ═══
    -- ─── Step 1: Basic lattice facts ───
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have hk_π : k ≤ π := sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane
    have hm_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
    have hE_k : Γ.E ≤ k := show Γ.E ≤ Γ.O ⊔ Γ.C from CoordSystem.hE_le_OC
    have hE_m : Γ.E ≤ m := CoordSystem.hE_on_m
    have hE_π : Γ.E ≤ π := hE_m.trans hm_π
    have hσb_k : σ_b ≤ k := inf_le_left
    have hσb_π : σ_b ≤ π := hσb_k.trans hk_π
    have hda_m : d_a ≤ m := inf_le_right
    have hU_π : Γ.U ≤ π := (le_sup_right : Γ.U ≤ l).trans le_sup_left
    have hkl_eq_O : k ⊓ l = Γ.O := by
      rw [inf_comm]; exact modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU
        (fun h => Γ.hC_not_l (h ▸ le_sup_left))
        (fun h => Γ.hC_not_l (h.symm.le.trans le_sup_right)) Γ.hC_not_l
    have hab_atom : IsAtom ab :=
      coord_mul_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
    have hac_atom : IsAtom ac :=
      coord_mul_atom Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U
    have hab_on : ab ≤ l := (show coord_mul Γ a b ≤ Γ.O ⊔ Γ.U from inf_le_right)
    have hac_on : ac ≤ l := (show coord_mul Γ a c ≤ Γ.O ⊔ Γ.U from inf_le_right)
    have hab_π : ab ≤ π := hab_on.trans le_sup_left
    have hac_π : ac ≤ π := hac_on.trans le_sup_left
    have hac_ne_E : ac ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hac_on)
    have hac_not_m : ¬ ac ≤ m := fun h => hac_ne_U (Γ.atom_on_both_eq_U hac_atom hac_on h)
    have hσb_atom : IsAtom σ_b := by
      rw [show σ_b = (b ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) from inf_comm _ _]
      exact perspect_atom Γ.hE_I_atom hb
        (fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h ▸ Γ.hE_I_on_m)))
        Γ.hO Γ.hC hOC Γ.hE_I_not_OC
        (show b ⊔ Γ.E_I ≤ (Γ.O ⊔ Γ.C) ⊔ Γ.E_I from by
          have : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) = π := by
            have h_lt := lt_of_le_of_ne (le_sup_right : Γ.O ⊔ Γ.C ≤ Γ.E_I ⊔ (Γ.O ⊔ Γ.C))
              (fun h => Γ.hE_I_not_OC (h ▸ le_sup_left))
            exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
              (sup_le (Γ.hE_I_on_m.trans hm_π) hk_π)).resolve_left (ne_of_gt h_lt)
          rw [sup_comm] at this
          exact this ▸ sup_le (hb_on.trans le_sup_left) (Γ.hE_I_on_m.trans hm_π))
    have hda_atom : IsAtom d_a :=
      perspect_atom Γ.hC ha (fun h => Γ.hC_not_l (h ▸ ha_on)) Γ.hU Γ.hV
        (fun h => Γ.hV_off (h ▸ le_sup_right)) Γ.hC_not_m
        (sup_le (ha_on.trans (le_sup_left.trans Γ.m_sup_C_eq_π.symm.le)) le_sup_right)
    have hσb_not_m : ¬ σ_b ≤ m := by
      intro h
      have hb_inf_m : b ⊓ m = ⊥ := (hb.le_iff.mp inf_le_left).resolve_right
        (fun h' => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on (h' ▸ inf_le_right)))
      have hbEI_inf_m : (b ⊔ Γ.E_I) ⊓ m = Γ.E_I := by
        rw [sup_comm]; have h1 := sup_inf_assoc_of_le b Γ.hE_I_on_m
        rw [h1, hb_inf_m]; simp
      exact Γ.hE_I_not_OC ((Γ.hE_I_atom.le_iff.mp
        (hbEI_inf_m ▸ le_inf (inf_le_right : σ_b ≤ b ⊔ Γ.E_I) h)).resolve_left hσb_atom.1 ▸ hσb_k)
    have hσb_ne_U : σ_b ≠ Γ.U := fun h => hσb_not_m (h ▸ le_sup_left)
    have hda_ne_E : d_a ≠ Γ.E := by
      intro h
      have ha_inf_k : a ⊓ k = ⊥ := (ha.le_iff.mp inf_le_left).resolve_right
        (fun h' => ha_ne_O ((Γ.hO.le_iff.mp (hkl_eq_O ▸ le_inf (h' ▸ inf_le_right) ha_on)
          ).resolve_left ha.1))
      have : (a ⊔ Γ.C) ⊓ k = Γ.C := by
        rw [sup_comm, inf_comm]; have h1 := sup_inf_assoc_of_le a (le_sup_right : Γ.C ≤ k)
        rw [ha_inf_k] at h1; simp at h1; rw [inf_comm] at h1; exact h1
      exact Γ.hC_not_m ((Γ.hC.le_iff.mp
        (this ▸ le_inf (h ▸ inf_le_left) hE_k)).resolve_left Γ.hE_atom.1 ▸ hE_m)
    have hda_ne_U : d_a ≠ Γ.U := by
      intro h
      have : (a ⊔ Γ.C) ⊓ l = a := by
        have hC_inf_l : Γ.C ⊓ l = ⊥ := (Γ.hC.le_iff.mp inf_le_left).resolve_right
          (fun h' => Γ.hC_not_l (h' ▸ inf_le_right))
        have h1 := sup_inf_assoc_of_le Γ.C ha_on; rw [hC_inf_l] at h1; simp at h1; exact h1
      exact ha_ne_U ((ha.le_iff.mp
        (this ▸ le_inf (h ▸ inf_le_left) (le_sup_right : Γ.U ≤ l))).resolve_left Γ.hU.1).symm
    -- ─── Step 2: ac⊔E ⋖ π ───
    have hac_sup_U : ac ⊔ Γ.U = l :=
      ((line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hac_atom hac_on).eq_or_eq
        (atom_covBy_join hac_atom Γ.hU hac_ne_U).lt.le
        (sup_le hac_on le_sup_right)).resolve_left
        (ne_of_gt (atom_covBy_join hac_atom Γ.hU hac_ne_U).lt)
    have hU_disj_acE : Γ.U ⊓ (ac ⊔ Γ.E) = ⊥ := by
      rcases Γ.hU.le_iff.mp inf_le_left with h | h
      · exact h
      · exfalso
        have hl_le : l ≤ ac ⊔ Γ.E := hac_sup_U ▸ sup_le le_sup_left (h ▸ inf_le_right)
        have hl_eq : l = ac ⊔ Γ.E := ((atom_covBy_join hac_atom Γ.hE_atom hac_ne_E).eq_or_eq
          hac_on hl_le).resolve_left (fun h' => hac_ne_U ((hac_atom.le_iff.mp
            (h' ▸ (le_sup_right : Γ.U ≤ l))).resolve_left Γ.hU.1).symm)
        exact CoordSystem.hE_not_l (hl_eq ▸ le_sup_right)
    have hl_covBy_π : l ⋖ π := by
      have hV_disj : Γ.V ⊓ l = ⊥ := (Γ.hV.le_iff.mp inf_le_left).resolve_right
        (fun h => Γ.hV_off (h ▸ inf_le_right))
      have h := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
      rwa [show Γ.V ⊔ l = π from by
        show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V; simp only [sup_comm, sup_left_comm]] at h
    have hl_sup_E : l ⊔ Γ.E = π := (hl_covBy_π.eq_or_eq
      (lt_of_le_of_ne le_sup_left (fun h => CoordSystem.hE_not_l (h ▸ le_sup_right))).le
      (sup_le le_sup_left hE_π)).resolve_left
      (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h => CoordSystem.hE_not_l (h ▸ le_sup_right))))
    have hU_sup_acE_eq_π : Γ.U ⊔ (ac ⊔ Γ.E) = π :=
      calc Γ.U ⊔ (ac ⊔ Γ.E) = (ac ⊔ Γ.U) ⊔ Γ.E := by
            simp only [sup_assoc, sup_comm, sup_left_comm]
        _ = l ⊔ Γ.E := by rw [hac_sup_U]
        _ = π := hl_sup_E
    have hacE_covBy : ac ⊔ Γ.E ⋖ π :=
      hU_sup_acE_eq_π ▸ covBy_sup_of_inf_covBy_left (hU_disj_acE ▸ Γ.hU.bot_covBy)
    -- ─── Step 3: W' is an atom ───
    have hσbU_π : σ_b ⊔ Γ.U ≤ π := sup_le hσb_π hU_π
    have hσb_inf_m : σ_b ⊓ m = ⊥ := (hσb_atom.le_iff.mp inf_le_left).resolve_right
      (fun h => hσb_not_m (h ▸ inf_le_right))
    have hσbU_inf_m : (σ_b ⊔ Γ.U) ⊓ m = Γ.U := by
      rw [sup_comm]; have h1 := sup_inf_assoc_of_le σ_b (le_sup_left : Γ.U ≤ m)
      rw [hσb_inf_m] at h1; simp at h1; exact h1
    have hW'_atom : IsAtom W' := by
      have hW'_pos : ⊥ < W' := by
        rw [show W' = (ac ⊔ Γ.E) ⊓ (σ_b ⊔ Γ.U) from inf_comm _ _]
        exact bot_lt_iff_ne_bot.mpr (lines_meet_if_coplanar hacE_covBy hσbU_π
          (fun h => Γ.hU.1 (le_antisymm (hU_disj_acE ▸ le_inf le_rfl
            (le_sup_right.trans h)) bot_le))
          hσb_atom (atom_covBy_join hσb_atom Γ.hU hσb_ne_U).lt)
      have hW'_lt : W' < ac ⊔ Γ.E := by
        refine lt_of_le_of_ne inf_le_right (fun h_eq => ?_)
        have hacE_le_σbU : ac ⊔ Γ.E ≤ σ_b ⊔ Γ.U := h_eq ▸ inf_le_left
        have hE_le_σbU : Γ.E ≤ σ_b ⊔ Γ.U := le_sup_right.trans hacE_le_σbU
        exact CoordSystem.hEU ((Γ.hU.le_iff.mp
          (hσbU_inf_m ▸ le_inf hE_le_σbU hE_m)).resolve_left Γ.hE_atom.1)
      exact line_height_two hac_atom Γ.hE_atom hac_ne_E hW'_pos hW'_lt
    have hW'_le_acE : W' ≤ ac ⊔ Γ.E := inf_le_right
    have hW'_π : W' ≤ π := hW'_le_acE.trans (sup_le hac_π hE_π)
    have hacE_inf_m : (ac ⊔ Γ.E) ⊓ m = Γ.E := by
      rw [sup_comm]; have h1 := sup_inf_assoc_of_le ac hE_m
      rw [(hac_atom.le_iff.mp inf_le_left).resolve_right
        (fun h' => hac_not_m (h' ▸ inf_le_right))] at h1; simp at h1; exact h1
    have hW'_ne_E : W' ≠ Γ.E := by
      intro h; exact CoordSystem.hEU ((Γ.hU.le_iff.mp
        (hσbU_inf_m ▸ le_inf (h ▸ inf_le_left) hE_m)).resolve_left Γ.hE_atom.1)
    have hW'_ne_da : W' ≠ d_a := by
      intro h; exact hda_ne_E ((Γ.hE_atom.le_iff.mp
        (hacE_inf_m ▸ le_inf (h ▸ hW'_le_acE) hda_m)).resolve_left hda_atom.1)
    -- ─── Step 4: Apply desargues_planar and extract ───
    -- Remaining: verify ~35 hypotheses of desargues_planar, then extract.
    -- Key prerequisites still needed:
    --   σ_b ≠ C, σ_b⊔C = k (perspective condition for E)
    --   d_a ≤ σ_b⊔ab (perspective condition)
    --   Triangle planes = π, sides ⋖ π, distinctness conditions
    -- Then apply desargues_planar, simplify axis points
    -- (E⊔d_a = m, E⊔W' = ac⊔E, C⊔U = q, ab⊔U = l),
    -- and use collinear_of_common_bound.
    sorry
  -- ═══ Combination ═══
  -- coord_mul Γ a s ≤ addition_line ∧ coord_mul Γ a s ≤ l
  -- coord_add Γ ab ac = addition_line ⊓ l (by definition)
  -- Both are atoms on l on the addition line → equal
  have has_on : coord_mul Γ a s ≤ Γ.O ⊔ Γ.U := inf_le_right
  have has_atom : IsAtom (coord_mul Γ a s) :=
    coord_mul_atom Γ a s ha (coord_add_atom Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U)
      ha_on (show coord_add Γ b c ≤ Γ.O ⊔ Γ.U from inf_le_right)
      ha_ne_O hs_ne_O ha_ne_U hs_ne_U
  have habac_atom : IsAtom (coord_add Γ ab ac) :=
    coord_add_atom Γ ab ac
      (coord_mul_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U)
      (coord_mul_atom Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U)
      inf_le_right inf_le_right hab_ne_O hac_ne_O hab_ne_U hac_ne_U
  have habac_on : coord_add Γ ab ac ≤ Γ.O ⊔ Γ.U := inf_le_right
  -- coord_add Γ ab ac = ((ab⊔C)⊓m ⊔ (ac⊔E)⊓q) ⊓ l by definition
  have h_add_unfold : coord_add Γ ab ac =
      ((ab ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (ac ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U) := by
    unfold coord_add; rfl
  -- a·s ≤ addition_line and a·s ≤ l → a·s ≤ addition_line ⊓ l = ab+ac
  have has_le_sum : coord_mul Γ a s ≤
      ((ab ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (ac ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U) :=
    le_inf h_desargues_conclusion has_on
  -- Both atoms ≤ the same atom → equal
  rw [← h_add_unfold] at has_le_sum
  exact (habac_atom.le_iff.mp has_le_sum).resolve_left has_atom.1

end Foam.FTPGExplore
