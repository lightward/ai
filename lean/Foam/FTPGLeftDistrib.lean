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

## Status (session 103, 2026-04-14)
2 sorry (down from 5). Axis-threaded lifting fix applied (session 103).
  - desargues_converse_nonplanar: 0 sorry, PROVEN.
  - h_concurrence chain: PROVEN except h_converse instantiation.
    Axis-threaded lifting: E' and da' coupled through axis points on m.
    Atomicity (hda_atom, hW'_atom, hs₁₂_atom, hE'_atom, hda'_atom): PROVEN.
    Projection (hW_ne_bot → W' = (R⊔O')⊓π): PROVEN.
    Combination: 0 sorry, PROVEN.
  - h_converse: 1 sorry (instantiate desargues_converse_nonplanar, ~30 hypotheses).
  - h_desargues_conclusion: 1 sorry (forward Desargues, ~500 lines mechanical).
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
    have h_converse : (σ_b ⊔ U') ⊓ (ac ⊔ E') ≤ σ_s ⊔ da' := by sorry
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
      (ab ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (ac ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) := by sorry
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
