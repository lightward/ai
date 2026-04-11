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
    intro h_le
    -- dir on l and m → dir = U
    have hdir_eq_U := Γ.atom_on_both_eq_U hdir_atom h_le inf_le_right
    -- U ≤ I⊔P
    have hU_le_IP : Γ.U ≤ Γ.I ⊔ P := hdir_eq_U ▸ (inf_le_left : dir ≤ Γ.I ⊔ P)
    -- I⊔U ≤ I⊔P, I ⋖ I⊔P (atom_covBy_join), I < I⊔U → I⊔U = I⊔P
    have hI_cov := atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I)
    have hIU_le := sup_le (le_sup_left : Γ.I ≤ Γ.I ⊔ P) hU_le_IP
    have hI_lt_IU : Γ.I < Γ.I ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h => Γ.hUI.symm ((Γ.hI.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hU.1).symm)
    -- CovBy: I < I⊔U ≤ I⊔P and I ⋖ I⊔P → I⊔U = I⊔P
    have hIU_eq := (hI_cov.eq_or_eq hI_lt_IU.le hIU_le).resolve_left (ne_of_gt hI_lt_IU)
    -- P ≤ I⊔P = I⊔U ≤ l (I, U both on l)
    exact hP_not_l (le_sup_right.trans (hIU_eq.symm.le.trans (sup_le Γ.hI_on le_sup_right)))
  -- O⊔P ⋖ π: U ∉ O⊔P (else l ≤ O⊔P, P ≤ l ✗), O⊔P⊔U = l⊔P = π. line_covBy_plane.
  have hOP_covBy : Γ.O ⊔ P ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    -- U ∉ O⊔P: if U ≤ O⊔P, O ⋖ O⊔U = l, O < O⊔P, CovBy → l = O⊔P → P ≤ l ✗
    have hU_not_OP : ¬ Γ.U ≤ Γ.O ⊔ P := by
      intro h
      have hO_lt_OP : Γ.O < Γ.O ⊔ P := lt_of_le_of_ne le_sup_left
        (fun h' => (Ne.symm hP_ne_O) ((Γ.hO.le_iff.mp
          (le_sup_right.trans h'.symm.le)).resolve_left hP.1).symm)
      -- l = O⊔U ≤ O⊔P (U ≤ O⊔P). O ⋖ O⊔P. O < l ≤ O⊔P. CovBy → l = O⊔P. P ≤ l.
      have hl_le_OP : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ P := sup_le le_sup_left h
      have hO_lt_l : Γ.O < Γ.O ⊔ Γ.U := (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
      have hl_eq_OP : Γ.O ⊔ Γ.U = Γ.O ⊔ P :=
        ((atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)).eq_or_eq hO_lt_l.le
          hl_le_OP).resolve_left (ne_of_gt hO_lt_l)
      exact hP_not_l (le_sup_right.trans hl_eq_OP.symm.le)
    -- O⊔P⊔U = l⊔P = π
    have hOPU_eq : Γ.O ⊔ P ⊔ Γ.U = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      rw [show Γ.O ⊔ P ⊔ Γ.U = (Γ.O ⊔ Γ.U) ⊔ P from by ac_rfl]
      have hl_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ P := lt_of_le_of_ne le_sup_left
        (fun h => hP_not_l (le_sup_right.trans h.symm.le))
      exact (hl_covBy_π.eq_or_eq hl_lt.le
        (sup_le hl_covBy_π.le hP_plane)).resolve_left (ne_of_gt hl_lt)
    rw [← hOPU_eq]
    exact line_covBy_plane Γ.hO hP Γ.hU (Ne.symm hP_ne_O) Γ.hOU
      (fun h => hU_not_OP (h ▸ le_sup_right)) hU_not_OP
  -- c⊔dir ⋖ π
  have hcdir_covBy : c ⊔ dir ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    -- O ∉ c⊔dir: if O ≤ c⊔dir, then O⊔c ≤ c⊔dir. O⊔c = l (O,c on l, O≠c).
    -- l ≤ c⊔dir ≤ π. l ⋖ π → c⊔dir = l ∨ c⊔dir = π.
    -- c⊔dir = l → dir ≤ l ✗. c⊔dir = π → c ⋖ π, but c < l < π contradicts c ⋖ π.
    have hO_not_cdir : ¬ Γ.O ≤ c ⊔ dir := by
      intro h
      have hOc_le : Γ.O ⊔ c ≤ c ⊔ dir := sup_le h le_sup_left
      have hO_lt_Oc : Γ.O < Γ.O ⊔ c := lt_of_le_of_ne le_sup_left
        (fun h' => (Ne.symm hc_ne_O) ((Γ.hO.le_iff.mp
          (le_sup_right.trans h'.symm.le)).resolve_left hc.1).symm)
      have hOc_eq_l : Γ.O ⊔ c = Γ.O ⊔ Γ.U :=
        ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt_Oc.le
          (sup_le le_sup_left hc_on)).resolve_left (ne_of_gt hO_lt_Oc)
      have hl_le : Γ.O ⊔ Γ.U ≤ c ⊔ dir := hOc_eq_l ▸ hOc_le
      have hcdir_le : c ⊔ dir ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
        sup_le (hc_on.trans le_sup_left) ((inf_le_right : dir ≤ m).trans Γ.m_covBy_π.le)
      rcases hl_covBy_π.eq_or_eq hl_le hcdir_le with h_eq | h_eq
      · -- c⊔dir = l → dir ≤ l ✗
        exact hdir_not_l (le_sup_right.trans h_eq.le)
      · -- c⊔dir = π → c ⋖ π. But c ≤ l < π, so c < l < π. c ⋖ π impossible.
        have hc_cov_π : c ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V :=
          h_eq ▸ atom_covBy_join hc hdir_atom hc_ne_dir
        -- c < l: if c = l then O ≤ c (O ≤ l), O = c (atoms), c = O. ✗
        have hc_lt_l : c < Γ.O ⊔ Γ.U := lt_of_le_of_ne hc_on
          (fun h' => hc_ne_O ((hc.le_iff.mp (le_sup_left.trans h'.symm.le)).resolve_left
            Γ.hO.1).symm)
        exact (hc_cov_π.eq_or_eq hc_lt_l.le hl_covBy_π.le).elim
          (fun h => absurd h.symm (ne_of_lt hc_lt_l))
          (fun h => absurd h (Ne.symm (ne_of_gt hl_covBy_π.lt)))
    -- c⊔dir⊔O = π: l ≤ c⊔dir⊔O (O,c → l), l⊔dir = π (dir ∉ l)
    have hcdirO_eq : c ⊔ dir ⊔ Γ.O = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      have hl_le : Γ.O ⊔ Γ.U ≤ c ⊔ dir ⊔ Γ.O := by
        have hO_lt_Oc : Γ.O < Γ.O ⊔ c := lt_of_le_of_ne le_sup_left
          (fun h' => (Ne.symm hc_ne_O) ((Γ.hO.le_iff.mp
            (le_sup_right.trans h'.symm.le)).resolve_left hc.1).symm)
        have hOc_eq_l : Γ.O ⊔ c = Γ.O ⊔ Γ.U :=
          ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt_Oc.le
            (sup_le le_sup_left hc_on)).resolve_left (ne_of_gt hO_lt_Oc)
        rw [← hOc_eq_l]; exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
      have hl_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ dir := lt_of_le_of_ne le_sup_left
        (fun h => hdir_not_l (le_sup_right.trans h.symm.le))
      have hldir_eq : (Γ.O ⊔ Γ.U) ⊔ dir = Γ.O ⊔ Γ.U ⊔ Γ.V :=
        (hl_covBy_π.eq_or_eq hl_lt.le (sup_le hl_covBy_π.le
          ((inf_le_right : dir ≤ m).trans Γ.m_covBy_π.le))).resolve_left (ne_of_gt hl_lt)
      exact le_antisymm
        (sup_le (sup_le (hc_on.trans le_sup_left)
          ((inf_le_right : dir ≤ m).trans Γ.m_covBy_π.le)) (le_sup_left.trans le_sup_left))
        (hldir_eq.symm.le.trans (sup_le hl_le (le_sup_right.trans le_sup_left)))
    rw [← hcdirO_eq]
    exact line_covBy_plane hc hdir_atom Γ.hO hc_ne_dir
      hc_ne_O (fun h => hO_not_cdir (h ▸ le_sup_right)) hO_not_cdir
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
  set m := Γ.U ⊔ Γ.V
  set dir := (Γ.I ⊔ P) ⊓ m
  have hσP_atom := dilation_ext_atom Γ hP hc hc_on hc_ne_O hc_ne_U hP_plane hP_not_l hP_ne_O
    hP_ne_I hP_not_m
  have hdir_atom : IsAtom dir :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
  have hc_not_m : ¬ c ≤ m := fun h => hc_ne_U (Γ.atom_on_both_eq_U hc hc_on h)
  intro h
  -- σP ≤ (c⊔dir)⊓m = dir (line_direction, c off m)
  have hσP_le_dir : dilation_ext Γ c P ≤ dir := by
    have hσP_le_cdir : dilation_ext Γ c P ≤ c ⊔ dir := inf_le_right
    calc dilation_ext Γ c P ≤ (c ⊔ dir) ⊓ m := le_inf hσP_le_cdir h
      _ = dir := by
          change (c ⊔ (Γ.I ⊔ P) ⊓ m) ⊓ m = (Γ.I ⊔ P) ⊓ m
          exact line_direction hc hc_not_m inf_le_right
  -- σP ≤ O⊔P (from definition)
  have hσP_le_OP : dilation_ext Γ c P ≤ Γ.O ⊔ P := inf_le_left
  -- σP ≤ I⊔P (from dir ≤ I⊔P)
  have hσP_le_IP : dilation_ext Γ c P ≤ Γ.I ⊔ P := hσP_le_dir.trans inf_le_left
  -- (O⊔P) ⊓ (I⊔P) = P (modular, P ∉ l)
  have hOP_IP_eq : (Γ.O ⊔ P) ⊓ (Γ.I ⊔ P) = P := by
    rw [sup_comm Γ.O P, sup_comm Γ.I P]
    -- (P⊔O)⊓(P⊔I) = P: I ∉ P⊔O since if I ≤ P⊔O then l = O⊔I ≤ P⊔O = O⊔P → P ≤ l ✗
    have hI_not_PO : ¬ Γ.I ≤ P ⊔ Γ.O := by
      intro h
      have hOI_le : Γ.O ⊔ Γ.I ≤ P ⊔ Γ.O := sup_le le_sup_right h
      have hO_lt : Γ.O < Γ.O ⊔ Γ.I := (atom_covBy_join Γ.hO Γ.hI Γ.hOI).lt
      -- O ⋖ O⊔P. O < O⊔I ≤ P⊔O = O⊔P. CovBy → O⊔I = O⊔P. P ≤ O⊔P = O⊔I ≤ l.
      have hOP_eq : Γ.O ⊔ P = P ⊔ Γ.O := sup_comm _ _
      have hO_cov_OP := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
      have hOI_eq_OP : Γ.O ⊔ Γ.I = Γ.O ⊔ P :=
        (hO_cov_OP.eq_or_eq hO_lt.le (hOP_eq ▸ hOI_le)).resolve_left (ne_of_gt hO_lt)
      exact hP_not_l (le_sup_right.trans (hOI_eq_OP.symm.le.trans
        (sup_le le_sup_left Γ.hI_on)))
    exact modular_intersection hP Γ.hO Γ.hI hP_ne_O hP_ne_I Γ.hOI hI_not_PO
  -- σP ≤ P, σP = P
  have hσP_eq_P : dilation_ext Γ c P = P := by
    have hσP_le_P : dilation_ext Γ c P ≤ P := by
      have := le_inf hσP_le_OP hσP_le_IP
      rwa [hOP_IP_eq] at this
    exact (hP.le_iff.mp hσP_le_P).resolve_left hσP_atom.1
  -- P ≤ c⊔dir (from σP = P ≤ c⊔dir)
  have hP_le_cdir : P ≤ c ⊔ dir := hσP_eq_P ▸ inf_le_right
  -- (I⊔P) ⊓ (P⊔c) = P (modular, I ≠ c since P ∉ l and I,c ∈ l)
  -- c ≠ P (P ∉ l, c on l)
  have hP_ne_c : P ≠ c := fun h => hP_not_l (h ▸ hc_on)
  have hIP_Pc_eq : (Γ.I ⊔ P) ⊓ (P ⊔ c) = P := by
    -- modular_intersection gives (P⊔I)⊓(P⊔c) = P, need (I⊔P)⊓(P⊔c) = P
    rw [sup_comm Γ.I P]
    have hc_not_PI : ¬ c ≤ P ⊔ Γ.I := by
      intro h
      have hI_le_PI : Γ.I ≤ P ⊔ Γ.I := le_sup_right
      have hIc_le : Γ.I ⊔ c ≤ P ⊔ Γ.I := sup_le hI_le_PI h
      have hI_lt_Ic : Γ.I < Γ.I ⊔ c := lt_of_le_of_ne le_sup_left
        (fun h' => hcI.symm ((Γ.hI.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          hc.1).symm)
      -- I ⋖ I⊔c ≤ P⊔I. I ⋖ P⊔I. I < I⊔c → I⊔c = P⊔I. c ≤ P⊔I.
      -- Then I⊔c ≤ l (I, c on l). I⊔c = P⊔I. P ≤ I⊔c ≤ l. ✗
      have hIc_eq := ((atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I) |> fun h =>
        show Γ.I ⋖ P ⊔ Γ.I from sup_comm Γ.I P ▸ h).eq_or_eq hI_lt_Ic.le
        hIc_le).resolve_left (ne_of_gt hI_lt_Ic)
      exact hP_not_l (le_sup_left.trans (hIc_eq.symm.le.trans (sup_le Γ.hI_on hc_on)))
    exact modular_intersection hP Γ.hI hc hP_ne_I hP_ne_c hcI.symm hc_not_PI
  -- dir ≤ P⊔c: P⊔c = c⊔dir (CovBy)
  have hPc_eq_cdir : P ⊔ c = c ⊔ dir := by
    -- P⊔c ≤ c⊔dir (P ≤ c⊔dir, c ≤ c⊔dir)
    have hPc_le : P ⊔ c ≤ c ⊔ dir := sup_le hP_le_cdir le_sup_left
    -- c⊔dir ≤ P⊔c: c ≤ P⊔c, dir ≤ P⊔c (dir ≤ I⊔P, and dir on c⊔dir ≤ ... hmm)
    -- Actually: c ⋖ c⊔dir (atom_covBy_join). c < P⊔c (P ≠ c). P⊔c ≤ ... no wait.
    -- Simpler: P ⋖ P⊔c. P < c⊔dir (P ≤ c⊔dir, P ≠ c so c⊔dir > P).
    -- Actually P ≠ c⊔dir? P is an atom, c⊔dir is a line. So P < c⊔dir.
    -- P ⋖ P⊔c. P < c⊔dir. P⊔c ≤ c⊔dir. CovBy: c⊔dir = P or c⊔dir = P⊔c.
    -- c⊔dir = P impossible (line ≠ atom). So c⊔dir = P⊔c. But we want P⊔c = c⊔dir.
    -- Actually we can just use le_antisymm if we also show c⊔dir ≤ P⊔c.
    -- c ≤ P⊔c (le_sup_right). dir ≤ P⊔c? dir = (I⊔P)⊓m. dir ≤ I⊔P. But dir ≤ P⊔c?
    -- Not obvious. Let me use CovBy instead.
    have hP_lt : P < P ⊔ c := lt_of_le_of_ne le_sup_left
      (fun h => hP_ne_c ((hP.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hc.1).symm)
    -- c ≠ dir (c off m, dir on m)
    have hc_ne_dir' : c ≠ dir := fun h' => hc_not_m (h' ▸ inf_le_right)
    have hP_lt_cdir : P < c ⊔ dir := lt_of_le_of_ne hP_le_cdir
      (fun h => hP_ne_c ((hP.le_iff.mp ((le_sup_left : c ≤ c ⊔ dir).trans h.symm.le)).resolve_left
        hc.1).symm)
    -- c ⋖ c⊔dir. c < P⊔c ≤ c⊔dir. CovBy: P⊔c = c ∨ P⊔c = c⊔dir.
    have hc_lt_Pc : c < P ⊔ c := lt_of_le_of_ne le_sup_right
      (fun h => hP_ne_c ((hc.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left hP.1))
    exact ((atom_covBy_join hc hdir_atom hc_ne_dir').eq_or_eq hc_lt_Pc.le hPc_le).resolve_left
      (ne_of_gt hc_lt_Pc)
  -- dir ≤ (I⊔P) ⊓ (P⊔c) = P
  have hdir_le_P : dir ≤ P := by
    have := le_inf (inf_le_left : dir ≤ Γ.I ⊔ P) (le_sup_right.trans hPc_eq_cdir.symm.le : dir ≤ P ⊔ c)
    rwa [hIP_Pc_eq] at this
  -- dir ≤ P ⊓ m = ⊥. Contradiction.
  have hPm : P ⊓ m = ⊥ := (hP.le_iff.mp inf_le_left).resolve_right
    (fun h => hP_not_m (h ▸ inf_le_right))
  exact hdir_atom.1 (le_antisymm (hPm ▸ le_inf hdir_le_P (inf_le_right : dir ≤ m)) bot_le)
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
  set m := Γ.U ⊔ Γ.V
  set dir := (Γ.I ⊔ P) ⊓ m
  -- dir is an atom
  have hdir_atom : IsAtom dir :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
  -- c not on m
  have hc_not_m : ¬ c ≤ m := fun h => hc_ne_U (Γ.atom_on_both_eq_U hc hc_on h)
  have hc_ne_dir : c ≠ dir := fun h => hc_not_m (h ▸ inf_le_right)
  -- σP ≤ c⊔dir (from definition, inf_le_right)
  have hσP_le : dilation_ext Γ c P ≤ c ⊔ dir := inf_le_right
  -- σP⊔c = c⊔dir: c ⋖ c⊔dir (atom_covBy_join), c < σP⊔c ≤ c⊔dir → σP⊔c = c⊔dir
  have hc_lt_σPc : c < dilation_ext Γ c P ⊔ c := lt_of_le_of_ne le_sup_right
    (fun h => hσP_ne_c ((hc.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left
      hσP_atom.1))
  have hσPc_le : dilation_ext Γ c P ⊔ c ≤ c ⊔ dir := sup_le hσP_le le_sup_left
  have hσPc_eq : dilation_ext Γ c P ⊔ c = c ⊔ dir :=
    ((atom_covBy_join hc hdir_atom hc_ne_dir).eq_or_eq hc_lt_σPc.le hσPc_le).resolve_left
      (ne_of_gt hc_lt_σPc)
  -- (σP⊔c)⊓m = dir = (I⊔P)⊓m: line_direction (c off m, dir on m)
  rw [hσPc_eq, sup_comm, line_direction hc hc_not_m (inf_le_right : dir ≤ m)]
/-- Two directions are distinct when the source points are non-collinear with I. -/
theorem dilation_ext_directions_ne (Γ : CoordSystem L)
    {P Q : L} (hP : IsAtom P) (hQ : IsAtom Q)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hQ_plane : Q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_ne_I : P ≠ Γ.I) (hQ_ne_I : Q ≠ Γ.I) (hPQ : P ≠ Q)
    (hQ_not_IP : ¬ Q ≤ Γ.I ⊔ P) :
    (Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V) ≠ (Γ.I ⊔ Q) ⊓ (Γ.U ⊔ Γ.V) := by
  set m := Γ.U ⊔ Γ.V
  intro h_eq
  -- d := (I⊔P)⊓m = (I⊔Q)⊓m. d ≤ (I⊔P) ⊓ (I⊔Q) = I (modular, Q ∉ I⊔P). d ≤ m. d ≤ I⊓m = ⊥.
  have hd_atom : IsAtom ((Γ.I ⊔ P) ⊓ m) :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
  have hd_le_IP : (Γ.I ⊔ P) ⊓ m ≤ Γ.I ⊔ P := inf_le_left
  have hd_le_IQ : (Γ.I ⊔ P) ⊓ m ≤ Γ.I ⊔ Q := h_eq ▸ inf_le_left
  -- (I⊔P) ⊓ (I⊔Q) = I (modular_intersection: I, P, Q non-collinear since Q ∉ I⊔P)
  have hd_le_I : (Γ.I ⊔ P) ⊓ m ≤ Γ.I := by
    have := le_inf hd_le_IP hd_le_IQ
    rwa [modular_intersection Γ.hI hP hQ (Ne.symm hP_ne_I) (Ne.symm hQ_ne_I) hPQ hQ_not_IP]
      at this
  have hd_le_m : (Γ.I ⊔ P) ⊓ m ≤ m := inf_le_right
  have hIm_eq : Γ.I ⊓ m = ⊥ :=
    (Γ.hI.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hI_not_m (h ▸ inf_le_right))
  exact hd_atom.1 (le_antisymm (hIm_eq ▸ le_inf hd_le_I hd_le_m) bot_le)
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
