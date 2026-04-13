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

## Status
In progress. 1 sorry (main theorem). dilation_ext_fixes_m proven.
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
  -- ═══ Setup ═══
  set l := Γ.O ⊔ Γ.U with hl_def
  set m := Γ.U ⊔ Γ.V with hm_def
  set q := Γ.U ⊔ Γ.C with hq_def
  set k := Γ.O ⊔ Γ.C with hk_def  -- the "bridge" line O⊔C
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
  -- ═══ Architecture ═══
  -- Single forward Desargues, center σ_b on k.
  --   T1 = (C,  ab, U)    T2 = (E, d_a, W')
  --
  -- Perspective from σ_b:
  --   C  ↔ E    via k (C⊔E = k ∋ σ_b)
  --   ab ↔ d_a  via σ_b⊔d_a (the multiplication line, contains ab)
  --   U  ↔ W'   via σ_b⊔U (contains W' by concurrence lemma + definition)
  --
  -- Concurrence lemma: W' ≤ σ_s ⊔ d_a
  --   (the three lines σ_b⊔U, ac⊔E, and σ_s⊔d_a are concurrent at W')
  --   Therefore d_a⊔W' = σ_s⊔d_a, so (d_a⊔W')⊓l = a·s.
  --
  -- Desargues axis points:
  --   1. (C⊔ab)  ⊓ (E⊔d_a)  = (ab⊔C)⊓m     (l-addition projection)
  --   2. (C⊔U)   ⊓ (E⊔W')   = (ac⊔E)⊓q     (l-addition return center)
  --   3. (ab⊔U)  ⊓ (d_a⊔W') = a·s           (the target)
  --
  -- Conclusion: Desargues says 1,2,3 are collinear.
  --   a·s lies on (ab⊔C)⊓m ⊔ (ac⊔E)⊓q, and a·s ∈ l, so
  --   a·(b+c) = ((ab⊔C)⊓m ⊔ (ac⊔E)⊓q) ⊓ l = ab + ac.
  sorry

end Foam.FTPGExplore
