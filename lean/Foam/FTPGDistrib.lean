/-
# Right distributivity (Part VII)

(a + b) · c = a · c + b · c

## Proof architecture

### The dilation approach (Hartshorne §7)

The map x ↦ x·c on l factors as two perspectivities:
  x → D_x = (x⊔C)⊓m → x·c = (σ⊔D_x)⊓l

where σ = (O⊔C)⊓(c⊔E_I) is the "dilation center" on O⊔C.

This extends to off-line points via:
  dilation_ext Γ c P = (O⊔P) ⊓ (c ⊔ ((I⊔P)⊓m))

The proof chain:
1. dilation_ext preserves directions: (P⊔Q)⊓m = (σ_c(P)⊔σ_c(Q))⊓m
   (one Desargues application with center O)
2. "mul key identity": σ_c(C_a) = C'_{ac}
   where C_a = β(a) = (C⊔U)⊓(a⊔E) and C' = σ_c(C) = σ
3. Chain: σ_c(C_{a+b}) = σ_c(τ_a(C_b)) via key_identity
        = τ_{ac}(σ_c(C_b)) via direction preservation
        = τ_{ac}(C'_{bc}) via mul key identity
        = C'_{ac+bc} via generalized key_identity at C'
   Also: σ_c(C_{a+b}) = C'_{(a+b)c} via mul key identity
4. By translation_determined_by_param at C': (a+b)c = ac + bc

## Status

Architecture defined. Lemma statements with sorry.
-/

import Foam.FTPGMul

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-! ## The dilation extension

For an atom P in π, not on m, the dilation σ_c sends P to:
  (O⊔P) ⊓ (c ⊔ ((I⊔P)⊓m))

This is the unique point P' on the line O⊔P such that PP' has
the same direction (on m) as I⊔c.

In coordinates (O = origin, I = (1,0), C = (0,1)):
  σ_c(x, y) = (cx, cy)
-/

/-- The dilation σ_c extended to off-line points.
    For P not on m (and not O), this is the unique P' on O⊔P
    such that (I⊔P)⊓m = (c⊔P')⊓m (same "direction"). -/
noncomputable def dilation_ext (Γ : CoordSystem L) (c P : L) : L :=
  (Γ.O ⊔ P) ⊓ (c ⊔ ((Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V)))

/-! ## Dilation preserves directions

The key geometric property: for off-line P, Q, the dilation σ_c
maps the line P⊔Q to a parallel line σ_c(P)⊔σ_c(Q).

Proof: Desargues with center O, triangles (P, Q, I) and
(σ_c(P), σ_c(Q), c). The three pairs of corresponding sides
are parallel because:
  - (P⊔I) ∥ (σ_c(P)⊔c): both have direction (I⊔P)⊓m
  - (Q⊔I) ∥ (σ_c(Q)⊔c): both have direction (I⊔Q)⊓m
  - (P⊔Q) ∥ (σ_c(P)⊔σ_c(Q)): CONCLUSION
-/

/-- **Dilation preserves directions.**

    If P, Q are atoms in π not on m, and σ_c is the dilation,
    then (P⊔Q)⊓m = (σ_c(P)⊔σ_c(Q))⊓m.

    Proved by Desargues with center O: triangles (P, Q, I) and
    (σ_c(P), σ_c(Q), c) are perspective from O, and two pairs
    of sides are parallel (by construction of σ_c). Desargues
    forces the third pair to be parallel. -/
theorem dilation_preserves_direction (Γ : CoordSystem L)
    {P Q : L} (hP : IsAtom P) (hQ : IsAtom Q)
    (c : L) (hc : IsAtom c) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hQ_plane : Q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V) (hQ_not_m : ¬ Q ≤ Γ.U ⊔ Γ.V)
    (hP_ne_O : P ≠ Γ.O) (hQ_ne_O : Q ≠ Γ.O)
    (hPQ : P ≠ Q) (hP_ne_I : P ≠ Γ.I) (hQ_ne_I : Q ≠ Γ.I)
    -- σ_c(P) ≠ σ_c(Q) (non-degeneracy)
    (h_images_ne : dilation_ext Γ c P ≠ dilation_ext Γ c Q)
    -- Height ≥ 4 and irreducibility
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    (P ⊔ Q) ⊓ (Γ.U ⊔ Γ.V) =
      (dilation_ext Γ c P ⊔ dilation_ext Γ c Q) ⊓ (Γ.U ⊔ Γ.V) := by
  sorry

/-! ## The dilation agrees with coord_mul on l

For a on l, σ_c(C_a) and coord_mul relate via the "mul key identity."
-/

/-- The dilation of C is σ. -/
theorem dilation_ext_C (Γ : CoordSystem L)
    (c : L) (hc : IsAtom c) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U) :
    dilation_ext Γ c Γ.C = (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) := by
  -- dilation_ext Γ c C = (O⊔C) ⊓ (c ⊔ ((I⊔C)⊓m))
  -- And E_I = (I⊔C)⊓m by definition.
  unfold dilation_ext
  rfl

/-- **Mul key identity: the dilation of C_a equals C'_{ac}.**

    σ_c(C_a) = (σ⊔U) ⊓ (ac⊔E)

    where C_a = (C⊔U)⊓(a⊔E) is the β-image of a,
    σ = dilation_ext Γ c C, and ac = coord_mul Γ a c. -/
theorem dilation_mul_key_identity (Γ : CoordSystem L)
    (a c : L) (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    -- Height ≥ 4 and irreducibility
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    let C_a := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)
    let σ := dilation_ext Γ c Γ.C
    let ac := coord_mul Γ a c
    dilation_ext Γ c C_a = (σ ⊔ Γ.U) ⊓ (ac ⊔ Γ.E) := by
  sorry

/-- **Right distributivity: (a + b) · c = a·c + b·c.** -/
theorem coord_mul_right_distrib (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hab : a ≠ b)
    -- Non-degeneracy of a+b
    (hs_ne_O : coord_add Γ a b ≠ Γ.O) (hs_ne_U : coord_add Γ a b ≠ Γ.U)
    -- Non-degeneracy of products
    (hac_ne_O : coord_mul Γ a c ≠ Γ.O) (hac_ne_U : coord_mul Γ a c ≠ Γ.U)
    (hbc_ne_O : coord_mul Γ b c ≠ Γ.O) (hbc_ne_U : coord_mul Γ b c ≠ Γ.U)
    (hac_ne_bc : coord_mul Γ a c ≠ coord_mul Γ b c)
    -- Height ≥ 4 and irreducibility
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_mul Γ (coord_add Γ a b) c =
      coord_add Γ (coord_mul Γ a c) (coord_mul Γ b c) := by
  -- Architecture:
  -- Let C_a = β(a), C_b = β(b), σ = σ_c(C), C' = σ.
  -- 1. C_{a+b} = τ_a(C_b)                    [key_identity]
  -- 2. σ_c(C_{a+b}) = σ_c(τ_a(C_b))          [substitution]
  -- 3. σ_c(C_b) = C'_{bc}                     [mul_key_identity]
  -- 4. σ_c preserves directions               [dilation_preserves_direction]
  --    → σ_c(τ_a(C_b)) = τ_{ac}(σ_c(C_b))    [direction + structure]
  -- 5. = τ_{ac}(C'_{bc})                      [step 3]
  -- 6. = C'_{ac+bc}                           [key_identity at C']
  -- 7. σ_c(C_{a+b}) = C'_{(a+b)c}             [mul_key_identity]
  -- 8. C'_{(a+b)c} = C'_{ac+bc}               [steps 2,4,5,6,7]
  -- 9. (a+b)c = ac+bc                         [translation_determined_by_param at C']
  sorry

end Foam.FTPGExplore
