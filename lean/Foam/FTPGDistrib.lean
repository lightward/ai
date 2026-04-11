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
Modular proof architecture. Helper lemmas with sorry.
Session 70: decomposed monolith into independently-testable helpers.
-/
import Foam.FTPGMul
namespace Foam.FTPGExplore
universe u
variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]
/-! ## The dilation extension -/
/-- The dilation σ_c extended to off-line points.
    For P not on m (and not O), this is the unique P' on O⊔P
    such that (I⊔P)⊓m = (c⊔P')⊓m (same "direction"). -/
noncomputable def dilation_ext (Γ : CoordSystem L) (c P : L) : L :=
  (Γ.O ⊔ P) ⊓ (c ⊔ ((Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V)))
/-! ## Helper lemmas for dilation_ext
Each helper is independently testable. The main theorem
(dilation_preserves_direction) composes them.
-/
/-- The two lines defining σ_c(P) are distinct when P ∉ l and c ≠ O.
    Proof: if O⊔P = c⊔((I⊔P)⊓m), then c ≤ O⊔P. Since c ≤ l and P ∉ l,
    l ⊓ (O⊔P) = O (modular_intersection). So c ≤ O, c = O. ✗ -/
theorem dilation_ext_lines_ne (Γ : CoordSystem L)
    {P c : L} (hP : IsAtom P) (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hc_ne_O : c ≠ Γ.O)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_ne_O : P ≠ Γ.O) :
    Γ.O ⊔ P ≠ c ⊔ (Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V) := by
  intro h
  have hc_le_OP : c ≤ Γ.O ⊔ P := le_sup_left.trans h.symm.le
  have hc_le_O : c ≤ Γ.O := by
    have := le_inf hc_on hc_le_OP
    rwa [modular_intersection Γ.hO Γ.hU hP Γ.hOU (Ne.symm hP_ne_O)
      (fun h => hP_not_l (h ▸ le_sup_right)) hP_not_l] at this
  exact hc_ne_O ((Γ.hO.le_iff.mp hc_le_O).resolve_left hc.1)
/-- σ_c(P) is an atom when P ∉ l, P ∈ π, P ≠ O, c ≠ O, c on l, c ≠ U. -/
theorem dilation_ext_atom (Γ : CoordSystem L)
    {P c : L} (hP : IsAtom P) (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_ne_O : P ≠ Γ.O) (hP_ne_I : P ≠ Γ.I)
    (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V) :
    IsAtom (dilation_ext Γ c P) := by
  unfold dilation_ext
  set m := Γ.U ⊔ Γ.V
  set dir := (Γ.I ⊔ P) ⊓ m
  -- l ⋖ π (derived, not a CoordSystem method)
  have hl_covBy_π : Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
  -- dir is an atom on m
  have hdir_atom : IsAtom dir :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
  -- c ≠ dir (c not on m)
  have hc_not_m : ¬ c ≤ m := fun h => hc_ne_U (Γ.atom_on_both_eq_U hc hc_on h)
  have hc_ne_dir : c ≠ dir := fun h => hc_not_m (h ▸ inf_le_right)
  -- dir ∉ l: if dir ≤ l then dir = U (atom_on_both), U ≤ I⊔P, P ≤ l ✗
  have hdir_not_l : ¬ dir ≤ Γ.O ⊔ Γ.U := by
    sorry -- Route: atom_on_both_eq_U → U ≤ I⊔P → CovBy I⊔U ≤ I⊔P → P ≤ l ✗
  -- O⊔P ⋖ π: U ∉ O⊔P (else l ≤ O⊔P, P ≤ l ✗), O⊔P⊔U = l⊔P = π. line_covBy_plane.
  have hOP_covBy : Γ.O ⊔ P ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by sorry
  -- c⊔dir ⋖ π
  have hcdir_covBy : c ⊔ dir ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by sorry
  -- Lines distinct (proven helper)
  have h_ne := dilation_ext_lines_ne Γ hP hc hc_on hc_ne_O hP_not_l hP_ne_O
  -- Meet CovBy O⊔P
  have h_meet_covBy := (planes_meet_covBy hOP_covBy hcdir_covBy h_ne).1
  -- Meet ≠ ⊥
  have h_ne_bot : (Γ.O ⊔ P) ⊓ (c ⊔ dir) ≠ ⊥ := by
    intro h; rw [h] at h_meet_covBy
    -- ⊥ ⋖ O⊔P means O⊔P is an atom. But O < O⊔P (O ≠ P). Contradiction.
    have hO_lt : Γ.O < Γ.O ⊔ P := lt_of_le_of_ne le_sup_left
      (fun h' => (Ne.symm hP_ne_O) ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left hP.1).symm)
    exact h_meet_covBy.2 Γ.hO.bot_lt hO_lt
  exact line_height_two Γ.hO hP (Ne.symm hP_ne_O) (bot_lt_iff_ne_bot.mpr h_ne_bot) h_meet_covBy.lt
/-- σ_c(P) is in π. -/
theorem dilation_ext_plane (Γ : CoordSystem L)
    {P c : L} (hP : IsAtom P) (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    dilation_ext Γ c P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := by
  exact inf_le_left.trans (sup_le (le_sup_left.trans le_sup_left) hP_plane)
/-- σ_c(P) is not on m when P ∉ l, c ≠ I. -/
theorem dilation_ext_not_m (Γ : CoordSystem L)
    {P c : L} (hP : IsAtom P) (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_ne_O : P ≠ Γ.O)
    (hP_ne_I : P ≠ Γ.I) (hcI : c ≠ Γ.I) :
    ¬ dilation_ext Γ c P ≤ Γ.U ⊔ Γ.V := by
  sorry
/-- σ_c(P) ≠ c when P ∉ l, c ≠ O. -/
theorem dilation_ext_ne_c (Γ : CoordSystem L)
    {P c : L} (hP : IsAtom P) (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hc_ne_O : c ≠ Γ.O)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_ne_O : P ≠ Γ.O)
    (hσP_atom : IsAtom (dilation_ext Γ c P)) :
    dilation_ext Γ c P ≠ c := by
  intro h; apply hc_ne_O
  have hc_le_OP : c ≤ Γ.O ⊔ P := h ▸ (inf_le_left : dilation_ext Γ c P ≤ Γ.O ⊔ P)
  exact ((Γ.hO.le_iff.mp (le_inf hc_on hc_le_OP |>.trans
    (modular_intersection Γ.hO Γ.hU hP Γ.hOU (Ne.symm hP_ne_O)
      (fun h => hP_not_l (h ▸ le_sup_right)) hP_not_l).le)).resolve_left hc.1)
/-- σ_c(P) ≠ P when c ≠ I, P ∉ l. -/
theorem dilation_ext_ne_P (Γ : CoordSystem L)
    {P c : L} (hP : IsAtom P) (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_ne_O : P ≠ Γ.O)
    (hP_ne_I : P ≠ Γ.I) (hcI : c ≠ Γ.I) :
    dilation_ext Γ c P ≠ P := by
  sorry
/-- The input parallelism: (P⊔I)⊓m = (σ_c(P)⊔c)⊓m.
    Proof: σ_c(P)⊔c = c⊔((I⊔P)⊓m) by CovBy, then line_direction. -/
theorem dilation_ext_parallelism (Γ : CoordSystem L)
    {P c : L} (hP : IsAtom P) (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_ne_O : P ≠ Γ.O)
    (hP_ne_I : P ≠ Γ.I)
    (hσP_atom : IsAtom (dilation_ext Γ c P))
    (hσP_ne_c : dilation_ext Γ c P ≠ c) :
    (P ⊔ Γ.I) ⊓ (Γ.U ⊔ Γ.V) = (dilation_ext Γ c P ⊔ c) ⊓ (Γ.U ⊔ Γ.V) := by
  sorry
/-- Two directions are distinct when the source points are non-collinear with I. -/
theorem dilation_ext_directions_ne (Γ : CoordSystem L)
    {P Q : L} (hP : IsAtom P) (hQ : IsAtom Q)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hQ_plane : Q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_ne_I : P ≠ Γ.I) (hQ_ne_I : Q ≠ Γ.I) (hPQ : P ≠ Q)
    (hQ_not_IP : ¬ Q ≤ Γ.I ⊔ P) :
    (Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V) ≠ (Γ.I ⊔ Q) ⊓ (Γ.U ⊔ Γ.V) := by
  sorry
/-! ## The dilation agrees with coord_mul on l -/
/-- The dilation of C is σ. -/
theorem dilation_ext_C (Γ : CoordSystem L)
    (c : L) (hc : IsAtom c) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U) :
    dilation_ext Γ c Γ.C = (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) := by
  unfold dilation_ext
  rfl
/-! ## Dilation preserves directions (main theorem)
Desargues with center O, triangles (P, Q, I) and (σ_c(P), σ_c(Q), c).
Two input parallelisms from dilation_ext_parallelism.
Desargues forces the third. -/
/-- **Dilation preserves directions.**
    If P, Q are atoms in π not on m and not on l, then
    (P⊔Q)⊓m = (σ_c(P)⊔σ_c(Q))⊓m. -/
theorem dilation_preserves_direction (Γ : CoordSystem L)
    {P Q : L} (hP : IsAtom P) (hQ : IsAtom Q)
    (c : L) (hc : IsAtom c) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hQ_plane : Q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V) (hQ_not_m : ¬ Q ≤ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hQ_not_l : ¬ Q ≤ Γ.O ⊔ Γ.U)
    (hP_ne_O : P ≠ Γ.O) (hQ_ne_O : Q ≠ Γ.O)
    (hPQ : P ≠ Q) (hP_ne_I : P ≠ Γ.I) (hQ_ne_I : Q ≠ Γ.I)
    (h_images_ne : dilation_ext Γ c P ≠ dilation_ext Γ c Q)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    (P ⊔ Q) ⊓ (Γ.U ⊔ Γ.V) =
      (dilation_ext Γ c P ⊔ dilation_ext Γ c Q) ⊓ (Γ.U ⊔ Γ.V) := by
  sorry
/-! ## Mul key identity and right distributivity -/
/-- **Mul key identity: the dilation of C_a equals C'_{ac}.** -/
theorem dilation_mul_key_identity (Γ : CoordSystem L)
    (a c : L) (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
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
    (hs_ne_O : coord_add Γ a b ≠ Γ.O) (hs_ne_U : coord_add Γ a b ≠ Γ.U)
    (hac_ne_O : coord_mul Γ a c ≠ Γ.O) (hac_ne_U : coord_mul Γ a c ≠ Γ.U)
    (hbc_ne_O : coord_mul Γ b c ≠ Γ.O) (hbc_ne_U : coord_mul Γ b c ≠ Γ.U)
    (hac_ne_bc : coord_mul Γ a c ≠ coord_mul Γ b c)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_mul Γ (coord_add Γ a b) c =
      coord_add Γ (coord_mul Γ a c) (coord_mul Γ b c) := by
  sorry
end Foam.FTPGExplore
