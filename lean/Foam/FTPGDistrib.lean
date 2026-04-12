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
dilation_preserves_direction PROVEN (3 cases: c=I, collinear, generic Desargues).
dilation_mul_key_identity PROVEN (3 cases: c=I, a=I via DPD, generic Desargues center C).
  a=I case: DPD on (C, C_a) gives direction U, CovBy gives DE ≤ σ⊔U, atom equality.
coord_mul_right_distrib: 1 sorry.
  Proof architecture (verified in coordinates, needs converse Desargues):
  Converse Desargues on T1=(C,sc,ac), T2=(U,E,e_bc), axis=m
  where sc=(a+b)c, e_bc=(O⊔β(bc))⊓m. Axis points d_sc, U, d_ac all on m.
  Gives: β(sc) = q⊓(ac⊔e_bc) = pc(O,ac,β(bc),m).
  Then key_identity: pc(O,ac,β(bc),m) = β(ac+bc).
  Then β-injectivity (translation_determined_by_param): sc = ac+bc. QED.
-/
import Foam.FTPGMul
import Foam.FTPGAssoc
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
  -- If σP = P, then P ≤ c⊔dir. Same chain as not_m: dir ≤ P⊓m = ⊥. ✗
  intro h
  set m := Γ.U ⊔ Γ.V
  set dir := (Γ.I ⊔ P) ⊓ m
  have hdir_atom : IsAtom dir :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
  have hc_not_m : ¬ c ≤ m := fun h => hc_ne_U (Γ.atom_on_both_eq_U hc hc_on h)
  have hc_ne_dir : c ≠ dir := fun h' => hc_not_m (h' ▸ inf_le_right)
  have hP_ne_c : P ≠ c := fun h' => hP_not_l (h' ▸ hc_on)
  -- P ≤ c⊔dir
  have hP_le_cdir : P ≤ c ⊔ dir := h ▸ (inf_le_right : dilation_ext Γ c P ≤ c ⊔ dir)
  -- P⊔c = c⊔dir (CovBy on c ⋖ c⊔dir)
  have hPc_le : P ⊔ c ≤ c ⊔ dir := sup_le hP_le_cdir le_sup_left
  have hc_lt_Pc : c < P ⊔ c := lt_of_le_of_ne le_sup_right
    (fun h' => hP_ne_c ((hc.le_iff.mp (le_sup_left.trans h'.symm.le)).resolve_left hP.1))
  have hPc_eq : P ⊔ c = c ⊔ dir :=
    ((atom_covBy_join hc hdir_atom hc_ne_dir).eq_or_eq hc_lt_Pc.le hPc_le).resolve_left
      (ne_of_gt hc_lt_Pc)
  -- (I⊔P) ⊓ (P⊔c) = P (modular: I, c on l, P ∉ l)
  have hc_not_PI : ¬ c ≤ P ⊔ Γ.I := by
    intro h'
    have hIc_le : Γ.I ⊔ c ≤ P ⊔ Γ.I := sup_le le_sup_right h'
    have hI_lt : Γ.I < Γ.I ⊔ c := lt_of_le_of_ne le_sup_left
      (fun h'' => hcI.symm ((Γ.hI.le_iff.mp (le_sup_right.trans h''.symm.le)).resolve_left
        hc.1).symm)
    -- I ⋖ I⊔P (= P⊔I). I < I⊔c ≤ P⊔I. CovBy → I⊔c = P⊔I. c ≤ l. P ≤ I⊔c ≤ l. ✗
    have hI_cov_PI : Γ.I ⋖ P ⊔ Γ.I := sup_comm Γ.I P ▸ atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I)
    have hIc_eq : Γ.I ⊔ c = P ⊔ Γ.I :=
      (hI_cov_PI.eq_or_eq hI_lt.le hIc_le).resolve_left (ne_of_gt hI_lt)
    exact hP_not_l (le_sup_left.trans (hIc_eq.symm.le.trans (sup_le Γ.hI_on hc_on)))
  have hIP_Pc_eq : (Γ.I ⊔ P) ⊓ (P ⊔ c) = P := by
    rw [sup_comm Γ.I P]
    exact modular_intersection hP Γ.hI hc hP_ne_I hP_ne_c hcI.symm hc_not_PI
  have hdir_le_P : dir ≤ P := by
    have := le_inf (inf_le_left : dir ≤ Γ.I ⊔ P)
      (le_sup_right.trans hPc_eq.symm.le : dir ≤ P ⊔ c)
    rwa [hIP_Pc_eq] at this
  have hPm : P ⊓ m = ⊥ := (hP.le_iff.mp inf_le_left).resolve_right
    (fun h' => hP_not_m (h' ▸ inf_le_right))
  exact hdir_atom.1 (le_antisymm (hPm ▸ le_inf hdir_le_P (inf_le_right : dir ≤ m)) bot_le)
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
  set m := Γ.U ⊔ Γ.V
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set σP := dilation_ext Γ c P
  set σQ := dilation_ext Γ c Q
  -- ═══ Case 1: c = I (identity dilation) ═══
  by_cases hcI : c = Γ.I
  · subst hcI
    -- When c = I, show σ_I(P) = P
    -- Direction d_P = (I⊔P)⊓m
    have hd_P_atom : IsAtom ((Γ.I ⊔ P) ⊓ m) :=
      line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
        (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
    have hI_ne_dir : Γ.I ≠ (Γ.I ⊔ P) ⊓ m :=
      fun h => Γ.hI_not_m (h ▸ inf_le_right)
    -- I ⊔ ((I⊔P)⊓m) = I ⊔ P
    have hIdir_eq : Γ.I ⊔ (Γ.I ⊔ P) ⊓ m = Γ.I ⊔ P := by
      have h_lt : Γ.I < Γ.I ⊔ (Γ.I ⊔ P) ⊓ m := by
        apply lt_of_le_of_ne le_sup_left
        intro h
        exact hI_ne_dir ((Γ.hI.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hd_P_atom.1).symm
      exact ((atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I)).eq_or_eq h_lt.le
        (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
    -- I not on line P⊔O (if so, O⊔I ≤ P⊔O = line containing O,
    -- both lines with O on both, CovBy forces O⊔I = P⊔O, so P ≤ O⊔I = l ✗)
    have hI_not_PO : ¬ Γ.I ≤ P ⊔ Γ.O := by
      intro hI_le
      have hOI_le : Γ.O ⊔ Γ.I ≤ P ⊔ Γ.O := sup_le le_sup_right hI_le
      have hO_lt : Γ.O < Γ.O ⊔ Γ.I := (atom_covBy_join Γ.hO Γ.hI Γ.hOI).lt
      have hOI_eq : Γ.O ⊔ Γ.I = P ⊔ Γ.O :=
        ((sup_comm P Γ.O ▸ atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)).eq_or_eq hO_lt.le
          (sup_comm P Γ.O ▸ hOI_le)).resolve_left (ne_of_gt hO_lt)
      have hP_le_OI : P ≤ Γ.O ⊔ Γ.I := le_sup_left.trans hOI_eq.symm.le
      exact hP_not_l (hP_le_OI.trans (sup_le le_sup_left Γ.hI_on))
    -- σ_I(P) = (O⊔P) ⊓ (I⊔P) = P
    have hσP_eq : σP = P := by
      show (Γ.O ⊔ P) ⊓ (Γ.I ⊔ (Γ.I ⊔ P) ⊓ m) = P
      rw [hIdir_eq, sup_comm Γ.O P, sup_comm Γ.I P]
      exact modular_intersection hP Γ.hO Γ.hI hP_ne_O hP_ne_I Γ.hOI hI_not_PO
    -- Same for Q
    have hd_Q_atom : IsAtom ((Γ.I ⊔ Q) ⊓ m) :=
      line_meets_m_at_atom Γ.hI hQ (Ne.symm hQ_ne_I)
        (sup_le (Γ.hI_on.trans le_sup_left) hQ_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
    have hI_ne_dirQ : Γ.I ≠ (Γ.I ⊔ Q) ⊓ m :=
      fun h => Γ.hI_not_m (h ▸ inf_le_right)
    have hIdirQ_eq : Γ.I ⊔ (Γ.I ⊔ Q) ⊓ m = Γ.I ⊔ Q := by
      have h_lt : Γ.I < Γ.I ⊔ (Γ.I ⊔ Q) ⊓ m := by
        apply lt_of_le_of_ne le_sup_left
        intro h
        exact hI_ne_dirQ ((Γ.hI.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hd_Q_atom.1).symm
      exact ((atom_covBy_join Γ.hI hQ (Ne.symm hQ_ne_I)).eq_or_eq h_lt.le
        (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt h_lt)
    have hI_not_QO : ¬ Γ.I ≤ Q ⊔ Γ.O := by
      intro hI_le
      have hOI_le : Γ.O ⊔ Γ.I ≤ Q ⊔ Γ.O := sup_le le_sup_right hI_le
      have hO_lt : Γ.O < Γ.O ⊔ Γ.I := (atom_covBy_join Γ.hO Γ.hI Γ.hOI).lt
      have hOI_eq : Γ.O ⊔ Γ.I = Q ⊔ Γ.O :=
        ((sup_comm Q Γ.O ▸ atom_covBy_join Γ.hO hQ (Ne.symm hQ_ne_O)).eq_or_eq hO_lt.le
          (sup_comm Q Γ.O ▸ hOI_le)).resolve_left (ne_of_gt hO_lt)
      have hQ_le_OI : Q ≤ Γ.O ⊔ Γ.I := le_sup_left.trans hOI_eq.symm.le
      exact hQ_not_l (hQ_le_OI.trans (sup_le le_sup_left Γ.hI_on))
    have hσQ_eq : σQ = Q := by
      show (Γ.O ⊔ Q) ⊓ (Γ.I ⊔ (Γ.I ⊔ Q) ⊓ m) = Q
      rw [hIdirQ_eq, sup_comm Γ.O Q, sup_comm Γ.I Q]
      exact modular_intersection hQ Γ.hO Γ.hI hQ_ne_O hQ_ne_I Γ.hOI hI_not_QO
    rw [hσP_eq, hσQ_eq]
  -- ═══ Case 2: c ≠ I ═══
  · -- Common infrastructure
    have hc_not_m : ¬ c ≤ m := fun h => hc_ne_U (Γ.atom_on_both_eq_U hc hc_on h)
    have hσP_atom : IsAtom σP := dilation_ext_atom Γ hP hc hc_on hc_ne_O hc_ne_U
      hP_plane hP_not_l hP_ne_O hP_ne_I hP_not_m
    have hσQ_atom : IsAtom σQ := dilation_ext_atom Γ hQ hc hc_on hc_ne_O hc_ne_U
      hQ_plane hQ_not_l hQ_ne_O hQ_ne_I hQ_not_m
    have hσP_ne_c : σP ≠ c := dilation_ext_ne_c Γ hP hc hc_on hc_ne_O hP_not_l hP_ne_O hσP_atom
    have hσQ_ne_c : σQ ≠ c := dilation_ext_ne_c Γ hQ hc hc_on hc_ne_O hQ_not_l hQ_ne_O hσQ_atom
    -- Directions
    set d_P := (Γ.I ⊔ P) ⊓ m
    set d_Q := (Γ.I ⊔ Q) ⊓ m
    have hd_P_atom : IsAtom d_P :=
      line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
        (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
    have hd_Q_atom : IsAtom d_Q :=
      line_meets_m_at_atom Γ.hI hQ (Ne.symm hQ_ne_I)
        (sup_le (Γ.hI_on.trans le_sup_left) hQ_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
    -- Parallelisms from dilation_ext_parallelism
    have h_par_P : (P ⊔ Γ.I) ⊓ m = (σP ⊔ c) ⊓ m :=
      dilation_ext_parallelism Γ hP hc hc_on hc_ne_O hc_ne_U hP_plane hP_not_m
        hP_not_l hP_ne_O hP_ne_I hσP_atom hσP_ne_c
    have h_par_Q : (Q ⊔ Γ.I) ⊓ m = (σQ ⊔ c) ⊓ m :=
      dilation_ext_parallelism Γ hQ hc hc_on hc_ne_O hc_ne_U hQ_plane hQ_not_m
        hQ_not_l hQ_ne_O hQ_ne_I hσQ_atom hσQ_ne_c
    -- Rewrite parallelisms: d_P = (σP⊔c)⊓m, d_Q = (σQ⊔c)⊓m
    have h_par_P' : d_P = (σP ⊔ c) ⊓ m := by
      show (Γ.I ⊔ P) ⊓ m = (σP ⊔ c) ⊓ m; rw [sup_comm Γ.I P]; exact h_par_P
    have h_par_Q' : d_Q = (σQ ⊔ c) ⊓ m := by
      show (Γ.I ⊔ Q) ⊓ m = (σQ ⊔ c) ⊓ m; rw [sup_comm Γ.I Q]; exact h_par_Q
    -- σP ≤ c⊔d_P, σQ ≤ c⊔d_Q (from definition)
    have hσP_le_cd : σP ≤ c ⊔ d_P := inf_le_right
    have hσQ_le_cd : σQ ≤ c ⊔ d_Q := inf_le_right
    -- σP ≤ O⊔P, σQ ≤ O⊔Q
    have hσP_le_OP : σP ≤ Γ.O ⊔ P := inf_le_left
    have hσQ_le_OQ : σQ ≤ Γ.O ⊔ Q := inf_le_left
    -- ═══ Case 2a: Q ≤ I⊔P (collinear with I) ═══
    by_cases hQ_col : Q ≤ Γ.I ⊔ P
    · -- I⊔Q = I⊔P (by CovBy)
      have hI_lt_IQ : Γ.I < Γ.I ⊔ Q := lt_of_le_of_ne le_sup_left
        (fun h => hQ_ne_I ((Γ.hI.le_iff.mp (h ▸ le_sup_right)).resolve_left hQ.1))
      have hIQ_eq_IP : Γ.I ⊔ Q = Γ.I ⊔ P :=
        ((atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I)).eq_or_eq hI_lt_IQ.le
          (sup_le le_sup_left hQ_col)).resolve_left (ne_of_gt hI_lt_IQ)
      -- d_Q = d_P
      have hd_eq : d_Q = d_P := by show (Γ.I ⊔ Q) ⊓ m = (Γ.I ⊔ P) ⊓ m; rw [hIQ_eq_IP]
      -- P⊔Q = I⊔P
      have hPQ_le : P ⊔ Q ≤ Γ.I ⊔ P := sup_le le_sup_right hQ_col
      have hP_lt_PQ : P < P ⊔ Q := lt_of_le_of_ne le_sup_left
        (fun h => hPQ ((hP.le_iff.mp (h ▸ le_sup_right)).resolve_left hQ.1).symm)
      have hPQ_eq_IP : P ⊔ Q = Γ.I ⊔ P := by
        rw [sup_comm Γ.I P]
        exact ((atom_covBy_join hP Γ.hI hP_ne_I).eq_or_eq hP_lt_PQ.le
          (hPQ_le.trans (le_of_eq (sup_comm Γ.I P)))).resolve_left (ne_of_gt hP_lt_PQ)
      -- (P⊔Q)⊓m = d_P
      have hPQ_m : (P ⊔ Q) ⊓ m = d_P := by rw [hPQ_eq_IP]
      -- σQ ≤ c⊔d_P
      have hσQ_le_cdP : σQ ≤ c ⊔ d_P := hd_eq ▸ hσQ_le_cd
      -- σP⊔σQ ≤ c⊔d_P
      have hσPQ_le : σP ⊔ σQ ≤ c ⊔ d_P := sup_le hσP_le_cd hσQ_le_cdP
      -- c ≠ d_P
      have hc_ne_d : c ≠ d_P := fun h => hc_not_m (h ▸ inf_le_right)
      -- σP⊔σQ = c⊔d_P (line ≤ line, by CovBy)
      have hσPQ_eq : σP ⊔ σQ = c ⊔ d_P := by
        have hσP_lt : σP < σP ⊔ σQ := lt_of_le_of_ne le_sup_left
          (fun h => h_images_ne ((hσP_atom.le_iff.mp (h ▸ le_sup_right)).resolve_left hσQ_atom.1).symm)
        have hσP_cov := line_covers_its_atoms hc hd_P_atom hc_ne_d hσP_atom hσP_le_cd
        exact (hσP_cov.eq_or_eq hσP_lt.le hσPQ_le).resolve_left (ne_of_gt hσP_lt)
      -- (σP⊔σQ)⊓m = d_P
      have hσPQ_m : (σP ⊔ σQ) ⊓ m = d_P := by
        rw [hσPQ_eq]; exact line_direction hc hc_not_m (inf_le_right : d_P ≤ m)
      rw [hPQ_m, hσPQ_m]
    -- ═══ Case 2b: Q ∉ I⊔P (non-collinear with I) ═══
    · -- Sub-case: Q ≤ O⊔P (collinear with O)
      by_cases hQ_colO : Q ≤ Γ.O ⊔ P
      · -- O⊔Q = O⊔P
        have hO_lt_OQ : Γ.O < Γ.O ⊔ Q := lt_of_le_of_ne le_sup_left
          (fun h => hQ_ne_O ((Γ.hO.le_iff.mp (h ▸ le_sup_right)).resolve_left hQ.1))
        have hOQ_eq_OP : Γ.O ⊔ Q = Γ.O ⊔ P :=
          ((atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)).eq_or_eq hO_lt_OQ.le
            (sup_le le_sup_left hQ_colO)).resolve_left (ne_of_gt hO_lt_OQ)
        -- P⊔Q = O⊔P
        have hP_lt_PQ : P < P ⊔ Q := lt_of_le_of_ne le_sup_left
          (fun h => hPQ ((hP.le_iff.mp (h ▸ le_sup_right)).resolve_left hQ.1).symm)
        have hPQ_eq_OP : P ⊔ Q = Γ.O ⊔ P := by
          rw [sup_comm Γ.O P]
          exact ((atom_covBy_join hP Γ.hO hP_ne_O).eq_or_eq hP_lt_PQ.le
            (sup_le le_sup_left (hQ_colO.trans (sup_comm Γ.O P).le))).resolve_left
            (ne_of_gt hP_lt_PQ)
        -- σP ≤ O⊔P, σQ ≤ O⊔Q = O⊔P
        have hσQ_le_OP : σQ ≤ Γ.O ⊔ P := hOQ_eq_OP ▸ hσQ_le_OQ
        have hσPQ_le_OP : σP ⊔ σQ ≤ Γ.O ⊔ P := sup_le hσP_le_OP hσQ_le_OP
        -- σP⊔σQ = O⊔P
        have hσPQ_eq_OP : σP ⊔ σQ = Γ.O ⊔ P := by
          have hσP_lt : σP < σP ⊔ σQ := lt_of_le_of_ne le_sup_left
            (fun h => h_images_ne ((hσP_atom.le_iff.mp (h ▸ le_sup_right)).resolve_left hσQ_atom.1).symm)
          have hσP_cov := line_covers_its_atoms Γ.hO hP (Ne.symm hP_ne_O) hσP_atom hσP_le_OP
          exact (hσP_cov.eq_or_eq hσP_lt.le hσPQ_le_OP).resolve_left (ne_of_gt hσP_lt)
        rw [hPQ_eq_OP, hσPQ_eq_OP]
      -- ═══ Case 2c: Q ∉ I⊔P, Q ∉ O⊔P (generic — Desargues) ═══
      · -- ═══ Case 2c: Q ∉ I⊔P, Q ∉ O⊔P (generic — Desargues) ═══
        have hσP_ne_P : σP ≠ P := dilation_ext_ne_P Γ hP hc hc_on hc_ne_O hc_ne_U
          hP_plane hP_not_m hP_not_l hP_ne_O hP_ne_I hcI
        have hσQ_ne_Q : σQ ≠ Q := dilation_ext_ne_P Γ hQ hc hc_on hc_ne_O hc_ne_U
          hQ_plane hQ_not_m hQ_not_l hQ_ne_O hQ_ne_I hcI
        have hσP_not_m : ¬ σP ≤ m := dilation_ext_not_m Γ hP hc hc_on hc_ne_O hc_ne_U
          hP_plane hP_not_m hP_not_l hP_ne_O hP_ne_I hcI
        have hσQ_not_m : ¬ σQ ≤ m := dilation_ext_not_m Γ hQ hc hc_on hc_ne_O hc_ne_U
          hQ_plane hQ_not_m hQ_not_l hQ_ne_O hQ_ne_I hcI
        have hσP_plane : σP ≤ π := dilation_ext_plane Γ hP hc hc_on hP_plane
        have hσQ_plane : σQ ≤ π := dilation_ext_plane Γ hQ hc hc_on hQ_plane
        have hd_ne : d_P ≠ d_Q := dilation_ext_directions_ne Γ hP hQ hP_plane hQ_plane
          hP_not_m hP_ne_I hQ_ne_I hPQ hQ_col
        have hOI_eq_l : Γ.O ⊔ Γ.I = Γ.O ⊔ Γ.U := by
          have hO_lt : Γ.O < Γ.O ⊔ Γ.I := (atom_covBy_join Γ.hO Γ.hI Γ.hOI).lt
          exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
            (sup_le le_sup_left Γ.hI_on)).resolve_left (ne_of_gt hO_lt)
        have hc_le_OI : c ≤ Γ.O ⊔ Γ.I := hOI_eq_l.symm ▸ hc_on
        -- Non-degeneracy (sorry for now, fill in later)
        have hOc_eq_l : Γ.O ⊔ c = Γ.O ⊔ Γ.U := by
          have hO_lt : Γ.O < Γ.O ⊔ c := by
            apply lt_of_le_of_ne le_sup_left; intro h'
            exact hc_ne_O ((Γ.hO.le_iff.mp (h' ▸ le_sup_right)).resolve_left hc.1)
          exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
            (sup_le le_sup_left hc_on)).resolve_left (ne_of_gt hO_lt)
        have U_forces (X : L) (hX : IsAtom X) (hXI : X ≠ Γ.I)
            (hd : (Γ.I ⊔ X) ⊓ m = Γ.U) : X ≤ Γ.O ⊔ Γ.U := by
          have hU_le : Γ.U ≤ Γ.I ⊔ X := hd ▸ inf_le_left
          have hI_lt : Γ.I < Γ.I ⊔ Γ.U := by
            apply lt_of_le_of_ne le_sup_left; intro h
            exact Γ.hUI ((Γ.hI.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hU.1)
          have hIU_eq : Γ.I ⊔ Γ.U = Γ.I ⊔ X :=
            ((atom_covBy_join Γ.hI hX (Ne.symm hXI)).eq_or_eq hI_lt.le
              (sup_le le_sup_left hU_le)).resolve_left (ne_of_gt hI_lt)
          exact le_sup_right.trans (hIU_eq.symm.le.trans (sup_le Γ.hI_on le_sup_right))
        have hO_ne_σP : Γ.O ≠ σP := by
          intro h; apply hP_not_l
          have hd : d_P = (Γ.O ⊔ c) ⊓ m := by rw [h_par_P']; congr 1; rw [h]
          rw [hOc_eq_l, Γ.l_inf_m_eq_U] at hd
          exact U_forces P hP hP_ne_I hd
        have hO_ne_σQ : Γ.O ≠ σQ := by
          intro h; apply hQ_not_l
          have hd : d_Q = (Γ.O ⊔ c) ⊓ m := by rw [h_par_Q']; congr 1; rw [h]
          rw [hOc_eq_l, Γ.l_inf_m_eq_U] at hd
          exact U_forces Q hQ hQ_ne_I hd
        have hσP_not_l : ¬ σP ≤ Γ.O ⊔ Γ.U := by
          intro h
          have hle : σP ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ P) := le_inf h hσP_le_OP
          rw [modular_intersection Γ.hO Γ.hU hP Γ.hOU (Ne.symm hP_ne_O)
            (fun h' => hP_not_l (h' ▸ le_sup_right)) hP_not_l] at hle
          exact hO_ne_σP ((Γ.hO.le_iff.mp hle).resolve_left hσP_atom.1).symm
        have hσQ_not_l : ¬ σQ ≤ Γ.O ⊔ Γ.U := by
          intro h
          have hle : σQ ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Q) := le_inf h hσQ_le_OQ
          rw [modular_intersection Γ.hO Γ.hU hQ Γ.hOU (Ne.symm hQ_ne_O)
            (fun h' => hQ_not_l (h' ▸ le_sup_right)) hQ_not_l] at hle
          exact hO_ne_σQ ((Γ.hO.le_iff.mp hle).resolve_left hσQ_atom.1).symm
        -- I < O⊔I (helper for side distinctness)
        have hI_lt_OI : Γ.I < Γ.O ⊔ Γ.I := by
          apply lt_of_le_of_ne le_sup_right; intro h
          exact Γ.hOI ((Γ.hI.le_iff.mp (h ▸ le_sup_left)).resolve_left Γ.hO.1)
        -- l_le_XI_contra: O⊔I ≤ X⊔I implies X ≤ l (CovBy argument)
        have l_le_contra (X : L) (hX : IsAtom X) (hXI : X ≠ Γ.I) :
            Γ.O ⊔ Γ.I ≤ X ⊔ Γ.I → X ≤ Γ.O ⊔ Γ.U := by
          intro hle
          have hOI_eq : Γ.O ⊔ Γ.I = X ⊔ Γ.I :=
            ((sup_comm Γ.I X ▸ atom_covBy_join Γ.hI hX (Ne.symm hXI)).eq_or_eq
              hI_lt_OI.le hle).resolve_left (ne_of_gt hI_lt_OI)
          exact le_sup_left.trans (hOI_eq.symm.le.trans (hOI_eq_l ▸ le_rfl))
        have hPI_ne_σPc : P ⊔ Γ.I ≠ σP ⊔ c := by
          intro h; apply hcI
          have hle_I : Γ.I ≤ (P ⊔ Γ.I) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_right Γ.hI_on
          have hle_c : c ≤ (P ⊔ Γ.I) ⊓ (Γ.O ⊔ Γ.U) := le_inf (h.symm ▸ le_sup_right) hc_on
          have h_lt : (P ⊔ Γ.I) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
            apply lt_of_le_of_ne inf_le_right; intro h'
            exact hP_not_l (l_le_contra P hP hP_ne_I (hOI_eq_l ▸ h'.symm ▸ inf_le_left))
          have h_atom := line_height_two Γ.hO Γ.hU Γ.hOU
            (lt_of_lt_of_le Γ.hI.bot_lt hle_I) h_lt
          exact ((h_atom.le_iff.mp hle_c).resolve_left hc.1).trans
            ((h_atom.le_iff.mp hle_I).resolve_left Γ.hI.1).symm
        have hQI_ne_σQc : Q ⊔ Γ.I ≠ σQ ⊔ c := by
          intro h; apply hcI
          have hle_I : Γ.I ≤ (Q ⊔ Γ.I) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_right Γ.hI_on
          have hle_c : c ≤ (Q ⊔ Γ.I) ⊓ (Γ.O ⊔ Γ.U) := le_inf (h.symm ▸ le_sup_right) hc_on
          have h_lt : (Q ⊔ Γ.I) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
            apply lt_of_le_of_ne inf_le_right; intro h'
            exact hQ_not_l (l_le_contra Q hQ hQ_ne_I (hOI_eq_l ▸ h'.symm ▸ inf_le_left))
          have h_atom := line_height_two Γ.hO Γ.hU Γ.hOU
            (lt_of_lt_of_le Γ.hI.bot_lt hle_I) h_lt
          exact ((h_atom.le_iff.mp hle_c).resolve_left hc.1).trans
            ((h_atom.le_iff.mp hle_I).resolve_left Γ.hI.1).symm
        have hPQ_ne_σPQ : P ⊔ Q ≠ σP ⊔ σQ := by
          intro h
          have hσP_le_PQ : σP ≤ P ⊔ Q := le_sup_left.trans h.symm.le
          have hO_not_PQ : ¬ Γ.O ≤ P ⊔ Q := by
            intro h'
            have hP_lt : P < P ⊔ Γ.O := by
              apply lt_of_le_of_ne le_sup_left; intro h''
              exact hP_ne_O ((hP.le_iff.mp (h'' ▸ le_sup_right)).resolve_left Γ.hO.1).symm
            have hPO_eq : P ⊔ Γ.O = P ⊔ Q :=
              ((atom_covBy_join hP hQ hPQ).eq_or_eq hP_lt.le
                (sup_comm Γ.O P ▸ sup_le h' le_sup_left)).resolve_left (ne_of_gt hP_lt)
            exact hQ_colO (le_sup_right.trans (hPO_eq.symm.le.trans (sup_comm P Γ.O ▸ le_rfl)))
          have hPQ_PO_eq : (P ⊔ Q) ⊓ (P ⊔ Γ.O) = P :=
            modular_intersection hP hQ Γ.hO hPQ hP_ne_O hQ_ne_O hO_not_PQ
          have hσP_le_P : σP ≤ P := by
            have := le_inf hσP_le_PQ (sup_comm Γ.O P ▸ hσP_le_OP : σP ≤ P ⊔ Γ.O)
            rwa [hPQ_PO_eq] at this
          exact hσP_ne_P ((hP.le_iff.mp hσP_le_P).resolve_left hσP_atom.1)
        have hO_not_PI : ¬ Γ.O ≤ P ⊔ Γ.I := by
          intro h'
          exact hP_not_l (l_le_contra P hP hP_ne_I (sup_le h' le_sup_right))
        have hQ_not_PI : ¬ Q ≤ P ⊔ Γ.I :=
          fun h' => hQ_col (h'.trans (sup_le le_sup_right le_sup_left))
        have hPQI_eq : P ⊔ Q ⊔ Γ.I = π := by
          -- P⊔I is a line; O ∉ P⊔I; P⊔I⊔O contains l⊔P = π; so P⊔I ⋖ π
          -- Then Q ∉ P⊔I; P⊔I < P⊔I⊔Q ≤ π; CovBy → P⊔I⊔Q = π = P⊔Q⊔I
          have hPIO_eq : P ⊔ Γ.I ⊔ Γ.O = π := by
            -- l = O⊔I ≤ P⊔I⊔O (O and I both there)
            have hl_le : Γ.O ⊔ Γ.U ≤ P ⊔ Γ.I ⊔ Γ.O := by
              rw [← hOI_eq_l]; exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
            -- l ⋖ π, P ∉ l → l⊔P = π
            have hl_covBy : Γ.O ⊔ Γ.U ⋖ π := by
              have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
                (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
              have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
              rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from sup_comm _ _] at this
            have hl_lt : Γ.O ⊔ Γ.U < Γ.O ⊔ Γ.U ⊔ P := lt_of_le_of_ne le_sup_left
              (fun h => hP_not_l (h ▸ le_sup_right))
            have hlP_eq : Γ.O ⊔ Γ.U ⊔ P = π :=
              (hl_covBy.eq_or_eq hl_lt.le (sup_le (show Γ.O ⊔ Γ.U ≤ π from le_sup_left) hP_plane)).resolve_left
                (ne_of_gt hl_lt)
            -- l⊔P ≤ P⊔I⊔O (l ≤ PIO, P ≤ PIO)
            exact le_antisymm (sup_le (sup_le hP_plane (Γ.hI_on.trans (show Γ.O ⊔ Γ.U ≤ π from le_sup_left)))
              (le_sup_left.trans (show Γ.O ⊔ Γ.U ≤ π from le_sup_left)))
              (hlP_eq ▸ sup_le hl_le (le_sup_left.trans le_sup_left))
          have hPI_covBy : P ⊔ Γ.I ⋖ π := by
            rw [← hPIO_eq]; exact line_covBy_plane hP Γ.hI Γ.hO hP_ne_I hP_ne_O Γ.hOI.symm hO_not_PI
          have hPI_lt : P ⊔ Γ.I < (P ⊔ Γ.I) ⊔ Q := lt_of_le_of_ne le_sup_left
            (fun h => hQ_not_PI (h ▸ le_sup_right))
          have hPIQ_le : (P ⊔ Γ.I) ⊔ Q ≤ π := sup_le (sup_le hP_plane
            (Γ.hI_on.trans (show Γ.O ⊔ Γ.U ≤ π from le_sup_left))) hQ_plane
          calc P ⊔ Q ⊔ Γ.I = (P ⊔ Γ.I) ⊔ Q := by ac_rfl
            _ = π := (hPI_covBy.eq_or_eq hPI_lt.le hPIQ_le).resolve_left (ne_of_gt hPI_lt)
        have hσPQc_eq : σP ⊔ σQ ⊔ c = π := by
          -- σP ∉ l. l ⋖ π. l⊔σP = π. O ∉ σP⊔c (else O, c on l∩(σP⊔c), l ≠ σP⊔c, atom, O=c ✗).
          -- σP⊔c⊔O = π (contains l⊔σP). σP⊔c ⋖ π.
          -- σQ ∉ σP⊔c (if σQ ≤ σP⊔c then σQ⊔c = σP⊔c, (σQ⊔c)⊓m = (σP⊔c)⊓m = d_P, but also = d_Q, d_P≠d_Q ✗).
          -- σP⊔c⊔σQ = π. QED.
          have hl_covBy : Γ.O ⊔ Γ.U ⋖ π := by
            have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
              (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
            have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
            rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from sup_comm _ _] at this
          -- l⊔σP = π
          have hlσP_eq : Γ.O ⊔ Γ.U ⊔ σP = π := by
            have hl_lt : Γ.O ⊔ Γ.U < Γ.O ⊔ Γ.U ⊔ σP := lt_of_le_of_ne le_sup_left
              (fun h => hσP_not_l (h ▸ le_sup_right))
            exact (hl_covBy.eq_or_eq hl_lt.le (sup_le (show Γ.O ⊔ Γ.U ≤ π from le_sup_left) hσP_plane)).resolve_left
              (ne_of_gt hl_lt)
          -- O ∉ σP⊔c
          have hO_not_σPc : ¬ Γ.O ≤ σP ⊔ c := by
            intro h
            -- O, c both on l and on σP⊔c. σP ∉ l → σP⊔c ≠ l. l⊓(σP⊔c) is atom. O = c. ✗
            have hσPc_ne_l : σP ⊔ c ≠ Γ.O ⊔ Γ.U := by
              intro heq; exact hσP_not_l (le_sup_left.trans heq.le)
            have hO_le : Γ.O ≤ (Γ.O ⊔ Γ.U) ⊓ (σP ⊔ c) := le_inf (show Γ.O ≤ Γ.O ⊔ Γ.U from le_sup_left) h
            have hc_le : c ≤ (Γ.O ⊔ Γ.U) ⊓ (σP ⊔ c) := le_inf hc_on le_sup_right
            have h_ne_bot : (Γ.O ⊔ Γ.U) ⊓ (σP ⊔ c) ≠ ⊥ := fun h' => Γ.hO.1 (le_bot_iff.mp (h' ▸ hO_le))
            -- If l = l⊓(σP⊔c), then l ≤ σP⊔c. O ⋖ σP⊔c (line_covers_its_atoms).
            -- O < l ≤ σP⊔c, CovBy → l = σP⊔c → σP ≤ l ✗
            have h_lt : (Γ.O ⊔ Γ.U) ⊓ (σP ⊔ c) < Γ.O ⊔ Γ.U := by
              apply lt_of_le_of_ne inf_le_left; intro h'
              have hl_le : Γ.O ⊔ Γ.U ≤ σP ⊔ c := h'.symm ▸ inf_le_right
              have hO_cov := line_covers_its_atoms hσP_atom hc hσP_ne_c Γ.hO
                (le_sup_left.trans hl_le)
              have hl_eq : Γ.O ⊔ Γ.U = σP ⊔ c :=
                (hO_cov.eq_or_eq (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le hl_le).resolve_left
                  (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)
              exact hσP_not_l (le_sup_left.trans hl_eq.symm.le)
            have h_atom := line_height_two Γ.hO Γ.hU Γ.hOU (bot_lt_iff_ne_bot.mpr h_ne_bot) h_lt
            exact hc_ne_O ((h_atom.le_iff.mp hO_le).resolve_left Γ.hO.1 ▸
              (h_atom.le_iff.mp hc_le).resolve_left hc.1)
          -- σP⊔c⊔O = π
          have hσPcO_eq : σP ⊔ c ⊔ Γ.O = π := by
            have hl_le : Γ.O ⊔ Γ.U ≤ σP ⊔ c ⊔ Γ.O := by
              rw [← hOc_eq_l]; exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
            exact le_antisymm (sup_le (sup_le hσP_plane (hc_on.trans (show Γ.O ⊔ Γ.U ≤ π from le_sup_left)))
              (le_sup_left.trans (show Γ.O ⊔ Γ.U ≤ π from le_sup_left)))
              (hlσP_eq ▸ sup_le hl_le (le_sup_left.trans le_sup_left))
          -- σP⊔c ⋖ π
          have hσPc_covBy : σP ⊔ c ⋖ π := by
            rw [← hσPcO_eq]; exact line_covBy_plane hσP_atom hc Γ.hO hσP_ne_c
              (Ne.symm hO_ne_σP) hc_ne_O hO_not_σPc
          -- σQ ∉ σP⊔c
          have hσQ_not_σPc : ¬ σQ ≤ σP ⊔ c := by
            intro h
            -- σQ ≤ σP⊔c. So σQ⊔c ≤ σP⊔c (line ≤ line → equal). (σQ⊔c)⊓m = (σP⊔c)⊓m.
            -- But (σP⊔c)⊓m = d_P and (σQ⊔c)⊓m = d_Q. So d_P = d_Q. ✗
            have hσQc_le : σQ ⊔ c ≤ σP ⊔ c := sup_le h le_sup_right
            have hσQ_cov := line_covers_its_atoms hσP_atom hc hσP_ne_c hσQ_atom h
            have hσQc_eq : σQ ⊔ c = σP ⊔ c :=
              (hσQ_cov.eq_or_eq le_sup_left (sup_le h le_sup_right)).resolve_left
                (fun h' => hσQ_ne_c ((hσQ_atom.le_iff.mp (h' ▸ le_sup_right)).resolve_left hc.1).symm)
            have : d_P = d_Q := h_par_P'.trans (hσQc_eq ▸ h_par_Q'.symm)
            exact hd_ne this
          -- σP⊔c < σP⊔c⊔σQ ≤ π → σP⊔c⊔σQ = π
          have hσPc_lt : σP ⊔ c < (σP ⊔ c) ⊔ σQ := lt_of_le_of_ne le_sup_left
            (fun h => hσQ_not_σPc (h ▸ le_sup_right))
          have hσPcQ_le : (σP ⊔ c) ⊔ σQ ≤ π := sup_le (sup_le hσP_plane
            (hc_on.trans (show Γ.O ⊔ Γ.U ≤ π from le_sup_left))) hσQ_plane
          calc σP ⊔ σQ ⊔ c = (σP ⊔ c) ⊔ σQ := by ac_rfl
            _ = π := (hσPc_covBy.eq_or_eq hσPc_lt.le hσPcQ_le).resolve_left (ne_of_gt hσPc_lt)
        -- Sides CovBy π
        have hI_not_PQ : ¬ Γ.I ≤ P ⊔ Q := by
          intro h'
          -- I ≤ P⊔Q and P ≤ P⊔Q. So I⊔P ≤ P⊔Q. Both lines. CovBy → I⊔P = P⊔Q. Q ≤ I⊔P. ✗
          have hIP_le : Γ.I ⊔ P ≤ P ⊔ Q := sup_le h' le_sup_left
          have hP_lt : P < P ⊔ Q := by
            apply lt_of_le_of_ne le_sup_left; intro h''
            exact hPQ ((hP.le_iff.mp (h'' ▸ le_sup_right)).resolve_left hQ.1).symm
          have hP_lt_IP : P < Γ.I ⊔ P := by
            apply lt_of_le_of_ne le_sup_right; intro h''
            exact hP_ne_I ((hP.le_iff.mp (h'' ▸ le_sup_left)).resolve_left Γ.hI.1).symm
          have hIP_eq := ((atom_covBy_join hP hQ hPQ).eq_or_eq le_sup_right
            hIP_le).resolve_left (ne_of_gt hP_lt_IP)
          exact hQ_col (le_sup_right.trans hIP_eq.symm.le)
        have hPQ_cov : P ⊔ Q ⋖ π := by
          rw [← hPQI_eq]
          exact line_covBy_plane hP hQ Γ.hI hPQ hP_ne_I hQ_ne_I hI_not_PQ
        have hPI_cov : P ⊔ Γ.I ⋖ π := by
          rw [← hPQI_eq, show P ⊔ Q ⊔ Γ.I = P ⊔ Γ.I ⊔ Q from by ac_rfl]
          exact line_covBy_plane hP Γ.hI hQ hP_ne_I hPQ hQ_ne_I.symm hQ_not_PI
        have hP_not_QI : ¬ P ≤ Q ⊔ Γ.I := by
          intro h'
          -- P ≤ Q⊔I, I ≤ Q⊔I, so P⊔I ≤ Q⊔I. I ⋖ Q⊔I (CovBy). I < P⊔I ≤ Q⊔I.
          -- CovBy → P⊔I = Q⊔I. Q ≤ Q⊔I = P⊔I = I⊔P. ✗
          have hPI_le : Γ.I ⊔ P ≤ Q ⊔ Γ.I := sup_le le_sup_right h'
          have hI_lt_IP : Γ.I < Γ.I ⊔ P := by
            apply lt_of_le_of_ne le_sup_left; intro h''
            exact hP_ne_I ((Γ.hI.le_iff.mp (h'' ▸ le_sup_right)).resolve_left hP.1)
          have hIP_eq : Γ.I ⊔ P = Q ⊔ Γ.I :=
            ((sup_comm Γ.I Q ▸ atom_covBy_join Γ.hI hQ (Ne.symm hQ_ne_I)).eq_or_eq
              hI_lt_IP.le hPI_le).resolve_left (ne_of_gt hI_lt_IP)
          exact hQ_col (le_sup_left.trans (hIP_eq.symm.le))
        have hQI_cov : Q ⊔ Γ.I ⋖ π := by
          rw [← hPQI_eq, show P ⊔ Q ⊔ Γ.I = Q ⊔ Γ.I ⊔ P from by ac_rfl]
          exact line_covBy_plane hQ Γ.hI hP hQ_ne_I hPQ.symm hP_ne_I.symm hP_not_QI
        -- Apply Desargues
        obtain ⟨axis, haxis_le, haxis_ne, hPQ_axis, hPI_axis, hQI_axis⟩ :=
          desargues_planar Γ.hO hP hQ Γ.hI hσP_atom hσQ_atom hc
            ((le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U).trans (le_sup_left : Γ.O ⊔ Γ.U ≤ π))
            hP_plane hQ_plane (Γ.hI_on.trans ((le_sup_left : Γ.O ⊔ Γ.U ≤ π)))
            hσP_plane hσQ_plane (hc_on.trans ((le_sup_left : Γ.O ⊔ Γ.U ≤ π)))
            hσP_le_OP hσQ_le_OQ hc_le_OI
            hPQ hP_ne_I hQ_ne_I h_images_ne hσP_ne_c hσQ_ne_c
            hPQ_ne_σPQ hPI_ne_σPc hQI_ne_σQc
            hPQI_eq hσPQc_eq
            (Ne.symm hP_ne_O) (Ne.symm hQ_ne_O) Γ.hOI
            hO_ne_σP hO_ne_σQ hc_ne_O.symm
            hσP_ne_P.symm hσQ_ne_Q.symm (fun h => hcI h.symm)
            R hR hR_not h_irred
            hPQ_cov hPI_cov hQI_cov
        -- d_P, d_Q ≤ axis
        have hd_P_axis : d_P ≤ axis :=
          le_trans (le_inf (sup_comm Γ.I P ▸ inf_le_left : d_P ≤ P ⊔ Γ.I)
            (h_par_P'.le.trans inf_le_left)) hPI_axis
        have hd_Q_axis : d_Q ≤ axis :=
          le_trans (le_inf (sup_comm Γ.I Q ▸ inf_le_left : d_Q ≤ Q ⊔ Γ.I)
            (h_par_Q'.le.trans inf_le_left)) hQI_axis
        -- axis = m
        have hdPQ_eq_m : d_P ⊔ d_Q = m := by
          have hd_lt : d_P < d_P ⊔ d_Q := by
            apply lt_of_le_of_ne le_sup_left; intro h'
            exact hd_ne ((hd_P_atom.le_iff.mp (h' ▸ le_sup_right)).resolve_left hd_Q_atom.1).symm
          exact ((line_covers_its_atoms Γ.hU Γ.hV
            (fun h => Γ.hV_off (h ▸ le_sup_right)) hd_P_atom inf_le_right).eq_or_eq hd_lt.le
            (sup_le inf_le_right inf_le_right)).resolve_left (ne_of_gt hd_lt)
        have hm_le_axis : m ≤ axis := hdPQ_eq_m ▸ sup_le hd_P_axis hd_Q_axis
        have haxis_eq_m : axis = m :=
          (Γ.m_covBy_π.eq_or_eq hm_le_axis haxis_le).resolve_right haxis_ne
        -- Conclude
        have hPQ_σPQ_le_m : (P ⊔ Q) ⊓ (σP ⊔ σQ) ≤ m := haxis_eq_m ▸ hPQ_axis
        have hPQ_m_atom : IsAtom ((P ⊔ Q) ⊓ m) :=
          line_meets_m_at_atom hP hQ hPQ (sup_le hP_plane hQ_plane)
            Γ.m_covBy_π.le Γ.m_covBy_π hP_not_m
        have hσPQ_m_atom : IsAtom ((σP ⊔ σQ) ⊓ m) :=
          line_meets_m_at_atom hσP_atom hσQ_atom h_images_ne
            (sup_le hσP_plane hσQ_plane) Γ.m_covBy_π.le Γ.m_covBy_π hσP_not_m
        -- Two coplanar lines meet nontrivially
        have h_meet_ne : (P ⊔ Q) ⊓ (σP ⊔ σQ) ≠ ⊥ := by
          have hσP_lt : σP < σP ⊔ σQ := by
            apply lt_of_le_of_ne le_sup_left; intro h'
            exact h_images_ne ((hσP_atom.le_iff.mp
              (le_sup_right.trans h'.symm.le)).resolve_left hσQ_atom.1).symm
          have hσPQ_not_PQ : ¬ (σP ⊔ σQ) ≤ P ⊔ Q := by
            intro h'
            -- σP⊔σQ ≤ P⊔Q. Both lines. CovBy: σP ⋖ σP⊔σQ. If σP⊔σQ < P⊔Q:
            -- P ⋖ P⊔Q. σP⊔σQ ≤ P (CovBy). σP ≤ P, σP = P. ✗
            -- If σP⊔σQ = P⊔Q: ✗
            rcases eq_or_lt_of_le h' with h_eq | h_lt
            · exact hPQ_ne_σPQ h_eq.symm
            · have h_atom_σPQ := line_height_two hP hQ hPQ
                (lt_of_lt_of_le hσP_atom.bot_lt (le_sup_left : σP ≤ σP ⊔ σQ)) h_lt
              have hσP_eq := (h_atom_σPQ.le_iff.mp (le_sup_left : σP ≤ σP ⊔ σQ)).resolve_left hσP_atom.1
              exact h_images_ne ((hσP_atom.le_iff.mp (le_sup_right.trans hσP_eq.symm.le)).resolve_left hσQ_atom.1).symm
          exact lines_meet_if_coplanar hPQ_cov (sup_le hσP_plane hσQ_plane)
            hσPQ_not_PQ hσP_atom hσP_lt
        -- (P⊔Q) ⊓ (σP⊔σQ) < P⊔Q
        have h_int_lt : (P ⊔ Q) ⊓ (σP ⊔ σQ) < P ⊔ Q := by
          apply lt_of_le_of_ne inf_le_left; intro h'
          -- h' : inf = P⊔Q, so P⊔Q ≤ σP⊔σQ.
          have hPQ_le : P ⊔ Q ≤ σP ⊔ σQ := h' ▸ inf_le_right
          -- P⊔Q and σP⊔σQ are both lines. P⊔Q ≤ σP⊔σQ.
          -- If P⊔Q < σP⊔σQ: σP ⋖ σP⊔σQ, P⊔Q ≤ σP. P ≤ σP, P = σP. ✗
          rcases eq_or_lt_of_le hPQ_le with h_eq | h_lt
          · exact hPQ_ne_σPQ h_eq
          · -- P⊔Q < σP⊔σQ. P < P⊔Q. So ⊥ < P⊔Q < σP⊔σQ.
            -- line_height_two on σP⊔σQ: P⊔Q is an atom. But P < P⊔Q. ✗
            have hP_lt_PQ : P < P ⊔ Q := by
              apply lt_of_le_of_ne le_sup_left; intro h''
              exact hPQ ((hP.le_iff.mp (h'' ▸ le_sup_right)).resolve_left hQ.1).symm
            have h_atom_PQ := line_height_two hσP_atom hσQ_atom h_images_ne
              (lt_of_lt_of_le hP.bot_lt le_sup_left) h_lt
            have hP_eq := (h_atom_PQ.le_iff.mp le_sup_left).resolve_left hP.1
            -- P = P⊔Q means Q ≤ P, Q = P. ✗
            exact hPQ ((hP.le_iff.mp (le_sup_right.trans hP_eq.symm.le)).resolve_left hQ.1).symm
        have h_int_atom : IsAtom ((P ⊔ Q) ⊓ (σP ⊔ σQ)) :=
          line_height_two hP hQ hPQ (bot_lt_iff_ne_bot.mpr h_meet_ne) h_int_lt
        -- The intersection ≤ both (P⊔Q)⊓m and (σP⊔σQ)⊓m, which are atoms
        have h1 := (hPQ_m_atom.le_iff.mp (le_inf inf_le_left hPQ_σPQ_le_m)).resolve_left
          h_int_atom.1
        have h2 := (hσPQ_m_atom.le_iff.mp (le_inf inf_le_right hPQ_σPQ_le_m)).resolve_left
          h_int_atom.1
        exact h1.symm.trans h2
/-- When c = I, the dilation is the identity: σ_I(P) = P for any P in π off l. -/
theorem dilation_ext_identity (Γ : CoordSystem L)
    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) :
    dilation_ext Γ Γ.I P = P := by
  unfold dilation_ext
  -- Step 1: I ⊔ (I⊔P)⊓m = I⊔P via modular law
  have hI_sup_dir : Γ.I ⊔ (Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V) = Γ.I ⊔ P := by
    rw [inf_comm, ← sup_inf_assoc_of_le (Γ.U ⊔ Γ.V) (le_sup_left : Γ.I ≤ Γ.I ⊔ P)]
    have hIm_eq : Γ.I ⊔ (Γ.U ⊔ Γ.V) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      have hm_lt : Γ.U ⊔ Γ.V < Γ.I ⊔ (Γ.U ⊔ Γ.V) := lt_of_le_of_ne le_sup_right
        (fun h => Γ.hI_not_m (le_sup_left.trans h.symm.le))
      exact (Γ.m_covBy_π.eq_or_eq hm_lt.le
        (sup_le (Γ.hI_on.trans le_sup_left) Γ.m_covBy_π.le)).resolve_left (ne_of_gt hm_lt)
    rw [hIm_eq, inf_eq_right.mpr (sup_le (Γ.hI_on.trans le_sup_left) hP_plane)]
  rw [hI_sup_dir]
  -- Step 2: (O⊔P) ⊓ (I⊔P) = P via modular_intersection
  have hP_ne_O : P ≠ Γ.O := fun h => hP_not_l (h ▸ le_sup_left)
  have hP_ne_I : P ≠ Γ.I := fun h => hP_not_l (h ▸ Γ.hI_on)
  have hI_not_PO : ¬ Γ.I ≤ P ⊔ Γ.O := by
    intro h
    have hO_lt : Γ.O < P ⊔ Γ.O := lt_of_le_of_ne le_sup_right
      (fun h' => hP_ne_O ((Γ.hO.le_iff.mp (le_sup_left.trans h'.symm.le)).resolve_left hP.1))
    have hOI_le : Γ.O ⊔ Γ.I ≤ P ⊔ Γ.O := sup_le le_sup_right h
    have hO_covBy_PO : Γ.O ⋖ P ⊔ Γ.O :=
      sup_comm Γ.O P ▸ atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
    have hOI_eq_PO := (hO_covBy_PO.eq_or_eq
      (atom_covBy_join Γ.hO Γ.hI Γ.hOI).lt.le hOI_le).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hO Γ.hI Γ.hOI).lt)
    -- O⊔I = P⊔O. O⊔U is l. O ⋖ O⊔U. O ⋖ O⊔I. CovBy → O⊔I = O⊔U.
    have hOI_eq_l : Γ.O ⊔ Γ.I = Γ.O ⊔ Γ.U :=
      ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq
        (atom_covBy_join Γ.hO Γ.hI Γ.hOI).lt.le
        (sup_le le_sup_left Γ.hI_on)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hO Γ.hI Γ.hOI).lt)
    -- P ≤ P⊔O = O⊔I = O⊔U = l
    exact hP_not_l (le_sup_left.trans (hOI_eq_PO.symm.le.trans hOI_eq_l.le))
  rw [sup_comm Γ.O P, sup_comm Γ.I P]
  exact modular_intersection hP Γ.hO Γ.hI hP_ne_O hP_ne_I Γ.hOI hI_not_PO
/-- C_a = (U⊔C) ⊓ (a⊔E) is an atom when a is an atom on l, a ≠ O, a ≠ U. -/
theorem beta_atom (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    IsAtom ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) := by
  set q := Γ.U ⊔ Γ.C
  set m := Γ.U ⊔ Γ.V
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  have ha_ne_E : a ≠ Γ.E := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on (h ▸ Γ.hE_on_m))
  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  -- q ⋖ π
  have hqm_eq_U : q ⊓ m = Γ.U := by
    change (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [this, sup_bot_eq]
  have hq_covBy : q ⋖ π := by
    have h_inf : m ⊓ q ⋖ m := by rw [inf_comm, hqm_eq_U]; exact atom_covBy_join Γ.hU Γ.hV hUV
    have h1 := covBy_sup_of_inf_covBy_left h_inf
    have hmq : m ⊔ q = m ⊔ Γ.C := by
      show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
      rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
    have hmC : m ⊔ Γ.C = π :=
      (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
        (sup_le Γ.m_covBy_π.le Γ.hC_plane)).resolve_left
        (ne_of_gt (lt_of_le_of_ne le_sup_left
          (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
    rwa [hmq, hmC] at h1
  -- a⊔E ⋖ π
  have haE_covBy : a ⊔ Γ.E ⋖ π := by
    have hO_not_aE : ¬ Γ.O ≤ a ⊔ Γ.E := by
      intro hO_le
      -- O⊔a = l
      have hO_lt_Oa : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
        (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
      have hOa_eq_l : Γ.O ⊔ a = Γ.O ⊔ Γ.U :=
        ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt_Oa.le
          (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt hO_lt_Oa)
      -- l ≤ a⊔E
      have hl_le : Γ.O ⊔ Γ.U ≤ a ⊔ Γ.E := hOa_eq_l ▸ sup_le hO_le le_sup_left
      -- a < l, a ⋖ a⊔E, l ≤ a⊔E → l = a⊔E → E ≤ l ✗
      have ha_lt_l : a < Γ.O ⊔ Γ.U :=
        (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt
      exact Γ.hE_not_l (le_sup_right.trans
        (((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_on hl_le).resolve_left
          (ne_of_gt ha_lt_l)).symm.le)
    have h_covBy := line_covBy_plane ha Γ.hE_atom Γ.hO ha_ne_E ha_ne_O
      (fun h => Γ.hE_not_l (h ▸ le_sup_left)) hO_not_aE
    -- a⊔E⊔O = π: l = O⊔a ≤ a⊔E⊔O, E ≤ a⊔E⊔O. l⊔E = π (l ⋖ π, E not on l).
    have haEO_eq : a ⊔ Γ.E ⊔ Γ.O = π := by
      have hl_le : Γ.O ⊔ Γ.U ≤ a ⊔ Γ.E ⊔ Γ.O := by
        have hOa_le : Γ.O ⊔ a ≤ a ⊔ Γ.E ⊔ Γ.O :=
          sup_le le_sup_right (le_sup_left.trans le_sup_left)
        have hOa_eq : Γ.O ⊔ a = Γ.O ⊔ Γ.U :=
          ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq
            (lt_of_le_of_ne le_sup_left (fun h => ha_ne_O
              ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))).le
            (sup_le le_sup_left ha_on)).resolve_left
            (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h => ha_ne_O
              ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))))
        exact hOa_eq ▸ hOa_le
      have hE_le : Γ.E ≤ a ⊔ Γ.E ⊔ Γ.O := le_sup_right.trans le_sup_left
      -- l ⋖ π. l < l⊔E = π. l ≤ a⊔E⊔O. E ≤ a⊔E⊔O. π = l⊔E ≤ a⊔E⊔O.
      have hl_lt_lE : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ Γ.E := lt_of_le_of_ne le_sup_left
        (fun h => Γ.hE_not_l (le_sup_right.trans h.symm.le))
      have hlE_eq : (Γ.O ⊔ Γ.U) ⊔ Γ.E = π := by
        have hl_covBy : Γ.O ⊔ Γ.U ⋖ π := by
          have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
            (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
          exact show Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V from
            sup_comm (Γ.O ⊔ Γ.U) Γ.V ▸ covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
        exact (hl_covBy.eq_or_eq hl_lt_lE.le
          (sup_le le_sup_left (Γ.hE_on_m.trans Γ.m_covBy_π.le))).resolve_left
          (ne_of_gt hl_lt_lE)
      exact le_antisymm
        (sup_le (sup_le (ha_on.trans le_sup_left) (Γ.hE_on_m.trans Γ.m_covBy_π.le))
          (show Γ.O ≤ π from le_sup_left.trans le_sup_left))
        (hlE_eq ▸ sup_le hl_le hE_le)
    rwa [haEO_eq] at h_covBy
  -- U not on a⊔E
  have hU_not_aE : ¬ Γ.U ≤ a ⊔ Γ.E := by
    intro h
    have ha_lt : a < a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h' => ha_ne_U ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1).symm)
    have haU_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt.le
        (sup_le le_sup_left h)).resolve_left (ne_of_gt ha_lt)
    exact Γ.hE_not_l (le_sup_right.trans (haU_eq.symm.le.trans (sup_le ha_on le_sup_right)))
  exact line_meets_m_at_atom Γ.hU Γ.hC hUC
    (sup_le (le_sup_right.trans (le_sup_left : Γ.O ⊔ Γ.U ≤ π)) Γ.hC_plane)
    haE_covBy.le haE_covBy hU_not_aE
/-- C_a = (U⊔C) ⊓ (a⊔E) is not on l. -/
theorem beta_not_l (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    ¬ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.O ⊔ Γ.U := by
  set C_a := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)
  have hCa_atom := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have ha_ne_E : a ≠ Γ.E := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on (h ▸ Γ.hE_on_m))
  have ha_not_m : ¬ a ≤ Γ.U ⊔ Γ.V := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  intro h
  have hlq : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U := by
    rw [inf_comm, sup_comm Γ.U Γ.C]
    exact line_direction Γ.hC Γ.hC_not_l (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U)
  have hCa_eq_U : C_a = Γ.U :=
    (Γ.hU.le_iff.mp (le_inf h (inf_le_left : C_a ≤ Γ.U ⊔ Γ.C) |>.trans hlq.le)).resolve_left
      hCa_atom.1
  have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := hCa_eq_U ▸ (inf_le_right : C_a ≤ a ⊔ Γ.E)
  have ha_lt : a < a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
    (fun h' => ha_ne_U ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1).symm)
  have haU_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
    ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt.le
      (sup_le le_sup_left hU_le_aE)).resolve_left (ne_of_gt ha_lt)
  exact Γ.hE_not_l (le_sup_right.trans (haU_eq.symm.le.trans (sup_le ha_on le_sup_right)))
/-- C_a in π. -/
theorem beta_plane (Γ : CoordSystem L)
    {a : L} (ha_on : a ≤ Γ.O ⊔ Γ.U) :
    (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
  inf_le_left.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
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
  intro C_a σ ac
  -- ═══ Case split: c = I (identity dilation) vs c ≠ I ═══
  by_cases hcI : c = Γ.I
  · -- c = I: dilation is identity, σ = C, ac = a, both sides equal C_a
    subst hcI
    have hσ_eq : σ = Γ.C := dilation_ext_identity Γ Γ.hC Γ.hC_plane Γ.hC_not_l
    have hac_eq : ac = a := coord_mul_right_one Γ a ha ha_on
    rw [hσ_eq, hac_eq, sup_comm Γ.C Γ.U]
    exact dilation_ext_identity Γ (beta_atom Γ ha ha_on ha_ne_O ha_ne_U)
      (beta_plane Γ ha_on) (beta_not_l Γ ha ha_on ha_ne_O ha_ne_U)
  -- c ≠ I: the main proof via Desargues
  set l := Γ.O ⊔ Γ.U with hl_def
  set m := Γ.U ⊔ Γ.V with hm_def
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ_def
  -- ═══ Basic infrastructure ═══
  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have ha_ne_E : a ≠ Γ.E := fun h => ha_not_m (h ▸ Γ.hE_on_m)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hIC : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  -- l ⋖ π
  have hl_covBy : l ⋖ π := by
    change Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
    have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have h := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from sup_comm _ _] at h
  -- O⊔a = l
  have hOa_eq_l : Γ.O ⊔ a = l := by
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq
      (lt_of_le_of_ne le_sup_left (fun h => ha_ne_O
        ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))).le
      (sup_le le_sup_left ha_on)).resolve_left
      (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h => ha_ne_O
        ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))))
  -- (U⊔C) ⊓ m = U
  have hqm_eq_U : (Γ.U ⊔ Γ.C) ⊓ m = Γ.U := by
    change (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
    calc (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U ⊔ Γ.C ⊓ (Γ.U ⊔ Γ.V) :=
          sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)
      _ = Γ.U := by
          have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
            (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
          rw [this, sup_bot_eq]
  -- a⊔E ⋖ π
  have haE_covBy : a ⊔ Γ.E ⋖ π := by
    have hO_not_aE : ¬ Γ.O ≤ a ⊔ Γ.E := by
      intro hO_le
      have hl_le : l ≤ a ⊔ Γ.E := hOa_eq_l ▸ sup_le hO_le le_sup_left
      have ha_lt_l : a < l := (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt
      exact Γ.hE_not_l (le_sup_right.trans
        (((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_on hl_le).resolve_left
          (ne_of_gt ha_lt_l)).symm.le)
    have haEO_eq : a ⊔ Γ.E ⊔ Γ.O = π := by
      have hl_le : l ≤ a ⊔ Γ.E ⊔ Γ.O := by
        rw [← hOa_eq_l]; exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
      have hl_lt : l < l ⊔ Γ.E := lt_of_le_of_ne le_sup_left
        (fun h' => Γ.hE_not_l (le_sup_right.trans h'.symm.le))
      have hlE_eq : l ⊔ Γ.E = π :=
        (hl_covBy.eq_or_eq hl_lt.le (sup_le hl_covBy.le (Γ.hE_on_m.trans Γ.m_covBy_π.le))).resolve_left
          (ne_of_gt hl_lt)
      exact le_antisymm
        (sup_le (sup_le (ha_on.trans le_sup_left) (Γ.hE_on_m.trans Γ.m_covBy_π.le))
          (show Γ.O ≤ π from le_sup_left.trans le_sup_left))
        (hlE_eq ▸ sup_le hl_le (le_sup_right.trans le_sup_left))
    rw [← haEO_eq]
    exact line_covBy_plane ha Γ.hE_atom Γ.hO ha_ne_E ha_ne_O
      (fun h' => Γ.hE_not_l (h' ▸ le_sup_left)) hO_not_aE
  -- d_a and its properties
  set d_a := (a ⊔ Γ.C) ⊓ m with hda_def
  have hda_atom : IsAtom d_a :=
    line_meets_m_at_atom ha Γ.hC ha_ne_C
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane)
      Γ.m_covBy_π.le Γ.m_covBy_π ha_not_m
  -- C_a facts
  have hCa_le_q : C_a ≤ Γ.U ⊔ Γ.C := inf_le_left
  have hCa_le_aE : C_a ≤ a ⊔ Γ.E := inf_le_right
  have hCa_atom : IsAtom C_a := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hCa_not_l : ¬ C_a ≤ l := beta_not_l Γ ha ha_on ha_ne_O ha_ne_U
  have hCa_not_m : ¬ C_a ≤ m := by
    intro h
    have hCa_eq_E : C_a = Γ.E :=
      (Γ.hE_atom.le_iff.mp (le_inf hCa_le_aE h |>.trans
        (line_direction ha ha_not_m Γ.hE_on_m).le)).resolve_left hCa_atom.1
    have hE_le_q : Γ.E ≤ Γ.U ⊔ Γ.C := hCa_eq_E ▸ hCa_le_q
    exact Γ.hEU ((Γ.hU.le_iff.mp (le_inf hE_le_q Γ.hE_on_m |>.trans
      hqm_eq_U.le)).resolve_left Γ.hE_atom.1)
  have hCa_plane : C_a ≤ π := beta_plane Γ ha_on
  have hCa_ne_O : C_a ≠ Γ.O := fun h => hCa_not_l (h ▸ le_sup_left)
  have hCa_ne_I : C_a ≠ Γ.I := fun h => hCa_not_l (h ▸ Γ.hI_on)
  have hCa_ne_U : C_a ≠ Γ.U := fun h => hCa_not_l (h ▸ le_sup_right)
  have hCa_ne_C : C_a ≠ Γ.C := by
    intro h
    -- C_a = C → C ≤ a⊔E. (a⊔E)⊓m = E (line_direction). C ≤ a⊔E, C ≤ l? No, C∉l.
    -- But C ≤ a⊔E and C ≤ q = U⊔C. So C ≤ (a⊔E)⊓(U⊔C) = C_a = C. Tautology.
    -- Need: C on a⊔E → (a⊔E)⊓l = a (direction). C on l? No. Then C on a⊔E means
    -- a⊔C ≤ a⊔E. CovBy: a ⋖ a⊔C (atom join). a < a⊔C ≤ a⊔E. CovBy a⋖a⊔E → a⊔C = a⊔E.
    -- Direction: (a⊔C)⊓m = d_a = (a⊔E)⊓m = E (line_direction). d_a = E.
    -- But d_a = (a⊔C)⊓m and E = (O⊔C)⊓m. If d_a = E then same direction through C.
    -- CovBy: C ⋖ C⊔E = C⊔d_a. C⊔d_a ≤ a⊔C (d_a = (a⊔C)⊓m ≤ a⊔C). C⊔E ≤ O⊔C.
    -- So C⊔E ≤ (a⊔C) ⊓ (O⊔C). But a⊔C and O⊔C share C.
    -- modular: (C⊔a)⊓(C⊔O) = C (mod_intersection, O∉C⊔a? If O ≤ a⊔C then l ≤ a⊔C,
    -- direction (a⊔C)⊓m ≤ a⊔C. C ≤ l → false). So C⊔E ≤ C → E ≤ C → E = C.
    -- But E ≠ C: E on m, C not on m. ✗.
    have hC_le_aE : Γ.C ≤ a ⊔ Γ.E := h ▸ hCa_le_aE
    have ha_lt_aC : a < a ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h' => ha_ne_C ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hC.1).symm)
    have haC_eq_aE : a ⊔ Γ.C = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt_aC.le
        (sup_le le_sup_left hC_le_aE)).resolve_left (ne_of_gt ha_lt_aC)
    -- (a⊔C)⊓m = d_a. (a⊔E)⊓m = E. a⊔C = a⊔E → d_a = E.
    have hda_eq_E : d_a = Γ.E := by
      have h1 : d_a = (a ⊔ Γ.E) ⊓ m := by rw [← haC_eq_aE]
      rw [h1]; exact line_direction ha ha_not_m Γ.hE_on_m
    -- E = d_a ≤ a⊔C, E on m. (a⊔C)⊓(O⊔C) = C (modular, O∉a⊔C).
    -- E ≤ O⊔C: E = (O⊔C)⊓m ≤ O⊔C. ✓
    -- C⊔E ≤ a⊔C ⊓ O⊔C = C. So E ≤ C → E = C.
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      -- O ≤ a⊔C. l = O⊔a ≤ a⊔C. a ⋖ a⊔C. a < l ≤ a⊔C. CovBy → l = a⊔C. C ≤ l. ✗.
      have hl_le : l ≤ a ⊔ Γ.C := hOa_eq_l ▸ (sup_le hle le_sup_left : Γ.O ⊔ a ≤ a ⊔ Γ.C)
      have ha_lt_l : a < l := (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt
      exact Γ.hC_not_l (le_sup_right.trans
        (((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq ha_on hl_le).resolve_left
          (ne_of_gt ha_lt_l)).symm.le)
    have hE_le_C : Γ.E ≤ Γ.C := by
      have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := hda_eq_E ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
      have hE_le_OC : Γ.E ≤ Γ.O ⊔ Γ.C := inf_le_left
      have hmod := modular_intersection Γ.hC ha Γ.hO ha_ne_C.symm hOC.symm ha_ne_O
        (show ¬ Γ.O ≤ Γ.C ⊔ a from sup_comm a Γ.C ▸ hO_not_aC)
      -- (C⊔a)⊓(C⊔O) = C. E ≤ C⊔a and E ≤ C⊔O. So E ≤ (C⊔a)⊓(C⊔O) = C.
      calc Γ.E ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.O) :=
            le_inf (sup_comm a Γ.C ▸ hE_le_aC) (sup_comm Γ.O Γ.C ▸ hE_le_OC)
        _ = Γ.C := hmod
    exact (fun hEC : Γ.E ≠ Γ.C => hEC ((Γ.hC.le_iff.mp hE_le_C).resolve_left Γ.hE_atom.1))
      (fun h' => Γ.hC_not_m (h' ▸ Γ.hE_on_m))
  -- σ properties
  have hσ_atom : IsAtom σ :=
    dilation_ext_atom Γ Γ.hC hc hc_on hc_ne_O hc_ne_U
      Γ.hC_plane Γ.hC_not_l (Ne.symm hOC) (Ne.symm hIC) Γ.hC_not_m
  have hσ_on_OC : σ ≤ Γ.O ⊔ Γ.C := by
    change (Γ.O ⊔ Γ.C) ⊓ (c ⊔ (Γ.I ⊔ Γ.C) ⊓ m) ≤ Γ.O ⊔ Γ.C; exact inf_le_left
  have hσ_on_cEI : σ ≤ c ⊔ Γ.E_I := by
    change (Γ.O ⊔ Γ.C) ⊓ (c ⊔ (Γ.I ⊔ Γ.C) ⊓ m) ≤ c ⊔ Γ.E_I; exact inf_le_right
  have hσ_plane : σ ≤ π := dilation_ext_plane Γ Γ.hC hc hc_on Γ.hC_plane
  -- σ not on m
  have hσ_not_m : ¬ σ ≤ m := by
    change ¬ dilation_ext Γ c Γ.C ≤ Γ.U ⊔ Γ.V
    exact dilation_ext_not_m Γ Γ.hC hc hc_on hc_ne_O hc_ne_U
      Γ.hC_plane Γ.hC_not_m Γ.hC_not_l (Ne.symm hOC) (Ne.symm hIC) hcI
  -- σ not on l
  have hσ_not_l : ¬ σ ≤ l := by
    intro h
    have hOCl : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O := by
      change (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.O
      rw [sup_comm Γ.O Γ.C]
      exact inf_comm (Γ.O ⊔ Γ.U) (Γ.C ⊔ Γ.O) ▸
        line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
    have hσ_eq_O : σ = Γ.O := (Γ.hO.le_iff.mp ((le_inf hσ_on_OC h).trans hOCl.le)).resolve_left hσ_atom.1
    have hO_le_cEI : Γ.O ≤ c ⊔ Γ.E_I := hσ_eq_O.symm ▸ hσ_on_cEI
    have hcEI_l : (c ⊔ Γ.E_I) ⊓ l = c := by
      change (c ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = c; rw [sup_comm c Γ.E_I]
      exact line_direction Γ.hE_I_atom Γ.hE_I_not_l hc_on
    exact hc_ne_O ((hc.le_iff.mp (le_inf hO_le_cEI (show Γ.O ≤ l from le_sup_left)
      |>.trans hcEI_l.le)).resolve_left Γ.hO.1).symm
  -- ═══ Case split on a = I ═══
  by_cases haI : a = Γ.I
  · -- a = I: degenerate case. Use dilation_preserves_direction on C and C_a.
    subst haI
    -- ac = I · c = c
    have hac_eq : ac = c := coord_mul_left_one Γ c hc hc_on hc_ne_U
    rw [hac_eq]
    -- I⊔C_a = I⊔E (C_a ≤ I⊔E by definition, C_a ≠ I, CovBy)
    have hICa_eq_IE : Γ.I ⊔ C_a = Γ.I ⊔ Γ.E := by
      have h_lt : Γ.I < Γ.I ⊔ C_a := lt_of_le_of_ne le_sup_left
        (fun h => hCa_ne_I ((Γ.hI.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hCa_atom.1))
      exact ((atom_covBy_join Γ.hI Γ.hE_atom ha_ne_E).eq_or_eq h_lt.le
        (sup_le le_sup_left (inf_le_right : C_a ≤ Γ.I ⊔ Γ.E))).resolve_left (ne_of_gt h_lt)
    -- (I⊔C_a)⊓m = E
    have hdir : (Γ.I ⊔ C_a) ⊓ m = Γ.E := by
      rw [hICa_eq_IE]; exact line_direction Γ.hI ha_not_m Γ.hE_on_m
    -- Simplify dilation_ext Γ c C_a = (O⊔C_a)⊓(c⊔E)
    have hDE_eq : dilation_ext Γ c C_a = (Γ.O ⊔ C_a) ⊓ (c ⊔ Γ.E) := by
      show (Γ.O ⊔ C_a) ⊓ (c ⊔ (Γ.I ⊔ C_a) ⊓ m) = (Γ.O ⊔ C_a) ⊓ (c ⊔ Γ.E); rw [hdir]
    -- dilation_ext Γ c C_a is an atom
    have hDE_atom : IsAtom (dilation_ext Γ c C_a) :=
      dilation_ext_atom Γ hCa_atom hc hc_on hc_ne_O hc_ne_U hCa_plane hCa_not_l
        hCa_ne_O hCa_ne_I hCa_not_m
    -- C_a ∉ O⊔C (needed for image distinctness)
    have hCa_not_OC : ¬ C_a ≤ Γ.O ⊔ Γ.C := by
      intro hle
      -- (O⊔C)⊓(U⊔C) = C by modular_intersection
      have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
        intro h'; exact Γ.hC_not_l (le_sup_right.trans
          (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
            (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU Γ.hO le_sup_left).lt.le
            (sup_le le_sup_left h')).resolve_left
            (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU Γ.hO le_sup_left).lt)).symm.le)
      have hOCq : (Γ.C ⊔ Γ.O) ⊓ (Γ.C ⊔ Γ.U) = Γ.C :=
        modular_intersection Γ.hC Γ.hO Γ.hU hOC.symm hUC.symm Γ.hOU
          (sup_comm Γ.O Γ.C ▸ hU_not_OC)
      exact hCa_ne_C ((Γ.hC.le_iff.mp ((le_inf hle hCa_le_q).trans
        (show (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C) ≤ Γ.C from
          sup_comm Γ.O Γ.C ▸ sup_comm Γ.U Γ.C ▸ hOCq.le))).resolve_left hCa_atom.1)
    -- σ ≠ dilation_ext Γ c C_a (if equal, both ≤ (O⊔C)⊓(O⊔C_a) = O, σ=O, σ on l ✗)
    have hσ_ne_DE : σ ≠ dilation_ext Γ c C_a := by
      intro h
      have h1 : σ ≤ Γ.O ⊔ C_a := by rw [h]; unfold dilation_ext; exact inf_le_left
      have hmod : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ C_a) = Γ.O :=
        modular_intersection Γ.hO Γ.hC hCa_atom hOC hCa_ne_O.symm
          (Ne.symm hCa_ne_C) hCa_not_OC
      exact hσ_not_l (((Γ.hO.le_iff.mp ((le_inf hσ_on_OC h1).trans hmod.le)).resolve_left
        hσ_atom.1) ▸ (show Γ.O ≤ l from le_sup_left))
    -- C⊔C_a = q (both on q = U⊔C, distinct atoms on q, CovBy)
    have hCCa_eq_q : Γ.C ⊔ C_a = Γ.U ⊔ Γ.C := by
      have hC_lt : Γ.C < Γ.C ⊔ C_a := lt_of_le_of_ne le_sup_left
        (fun h => hCa_ne_C ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hCa_atom.1))
      exact ((sup_comm Γ.C Γ.U ▸ atom_covBy_join Γ.hC Γ.hU (Ne.symm hUC) :
        Γ.C ⋖ Γ.U ⊔ Γ.C).eq_or_eq hC_lt.le
        (sup_le le_sup_right hCa_le_q)).resolve_left (ne_of_gt hC_lt)
    -- Apply dilation_preserves_direction with P = C, Q = C_a
    have hDPD := dilation_preserves_direction Γ Γ.hC hCa_atom c hc hc_on hc_ne_O hc_ne_U
      Γ.hC_plane hCa_plane Γ.hC_not_m hCa_not_m Γ.hC_not_l hCa_not_l
      (Ne.symm hOC) hCa_ne_O (Ne.symm hCa_ne_C) (Ne.symm hIC) hCa_ne_I
      hσ_ne_DE R hR hR_not h_irred
    -- hDPD: (C⊔C_a)⊓m = (σ⊔DE)⊓m. LHS = q⊓m = U. So U = (σ⊔DE)⊓m.
    rw [hCCa_eq_q, hqm_eq_U] at hDPD
    -- hDPD : Γ.U = (σ ⊔ dilation_ext Γ c C_a) ⊓ m
    -- U ≤ σ ⊔ DE
    have hU_le_σDE : Γ.U ≤ σ ⊔ dilation_ext Γ c C_a :=
      (le_of_eq hDPD).trans inf_le_left
    -- σ⊔U = σ⊔DE (CovBy: σ ⋖ σ⊔DE, σ < σ⊔U ≤ σ⊔DE → equal)
    have hσ_ne_U : σ ≠ Γ.U := fun h => hσ_not_l (h ▸ (le_sup_right : Γ.U ≤ l))
    have hσU_eq_σDE : σ ⊔ Γ.U = σ ⊔ dilation_ext Γ c C_a := by
      have hσ_lt : σ < σ ⊔ Γ.U := lt_of_le_of_ne le_sup_left
        (fun h => hσ_ne_U ((hσ_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          Γ.hU.1).symm)
      exact ((atom_covBy_join hσ_atom hDE_atom hσ_ne_DE).eq_or_eq hσ_lt.le
        (sup_le le_sup_left hU_le_σDE)).resolve_left (ne_of_gt hσ_lt)
    -- DE ≤ σ⊔U
    have hDE_le_σU : dilation_ext Γ c C_a ≤ σ ⊔ Γ.U :=
      le_sup_right.trans hσU_eq_σDE.symm.le
    -- DE ≤ c⊔E
    have hDE_le_cE : dilation_ext Γ c C_a ≤ c ⊔ Γ.E :=
      hDE_eq ▸ inf_le_right
    -- DE ≤ (σ⊔U)⊓(c⊔E)
    have hDE_le : dilation_ext Γ c C_a ≤ (σ ⊔ Γ.U) ⊓ (c ⊔ Γ.E) :=
      le_inf hDE_le_σU hDE_le_cE
    -- (σ⊔U)⊓(c⊔E) is an atom (meet of two distinct lines)
    -- (σ⊔U)⊓(c⊔E) is an atom (meet of two distinct lines)
    have hRHS_atom : IsAtom ((σ ⊔ Γ.U) ⊓ (c ⊔ Γ.E)) := by
      apply line_height_two hσ_atom Γ.hU hσ_ne_U
      · exact lt_of_lt_of_le hDE_atom.bot_lt hDE_le
      · apply lt_of_le_of_ne inf_le_left; intro heq
        -- heq : (σ⊔U)⊓(c⊔E) = σ⊔U → σ⊔U ≤ c⊔E → U ≤ c⊔E → U ≤ (c⊔E)⊓l = c → U=c ✗
        have hσU_le : σ ⊔ Γ.U ≤ c ⊔ Γ.E := inf_eq_left.mp heq
        have hU_le_c : Γ.U ≤ c := by
          have h1 : Γ.U ≤ (c ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) :=
            le_inf (le_sup_right.trans hσU_le) le_sup_right
          rw [sup_comm c Γ.E] at h1
          exact h1.trans (line_direction Γ.hE_atom Γ.hE_not_l hc_on).le
        exact hc_ne_U ((hc.le_iff.mp hU_le_c).resolve_left Γ.hU.1).symm
    -- atom ≤ atom → equal
    exact (hRHS_atom.le_iff.mp hDE_le).resolve_left hDE_atom.1
  -- From here: a ≠ I
  -- G = (a⊔E)⊓(I⊔C)
  set G := (a ⊔ Γ.E) ⊓ (Γ.I ⊔ Γ.C) with hG_def
  have hG_le_aE : G ≤ a ⊔ Γ.E := inf_le_left
  have hG_le_IC : G ≤ Γ.I ⊔ Γ.C := inf_le_right
  have hG_plane : G ≤ π := inf_le_left.trans haE_covBy.le
  -- a ≠ I, so a not on I⊔C (if a ≤ I⊔C then a ≤ l⊓(I⊔C) = I → a = I ✗)
  have ha_not_IC : ¬ a ≤ Γ.I ⊔ Γ.C := by
    intro h
    have hlIC : (Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.C) = Γ.I := by
      rw [inf_comm, sup_comm Γ.I Γ.C]
      exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on
    exact haI ((Γ.hI.le_iff.mp ((le_inf ha_on h).trans hlIC.le)).resolve_left ha.1)
  have hIC_covBy : Γ.I ⊔ Γ.C ⋖ π := by
    have hO_not_IC : ¬ Γ.O ≤ Γ.I ⊔ Γ.C := by
      intro h
      have hlIC : (Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.C) = Γ.I := by
        rw [inf_comm, sup_comm Γ.I Γ.C]
        exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on
      exact Γ.hOI ((Γ.hI.le_iff.mp ((le_inf (show Γ.O ≤ Γ.O ⊔ Γ.U from le_sup_left) h).trans
        hlIC.le)).resolve_left Γ.hO.1)
    have hOI_eq_l : Γ.O ⊔ Γ.I = l :=
      ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq
        (lt_of_le_of_ne le_sup_left (fun h' => Γ.hOI
          ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hI.1).symm)).le
        (sup_le le_sup_left Γ.hI_on)).resolve_left
        (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h' => Γ.hOI
          ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hI.1).symm)))
    have h_covBy_ICO := line_covBy_plane Γ.hI Γ.hC Γ.hO hIC (Ne.symm Γ.hOI)
      (Ne.symm hOC) hO_not_IC  -- I⊔C ⋖ I⊔C⊔O
    -- I⊔C⊔O = π
    have hICO_eq : Γ.I ⊔ Γ.C ⊔ Γ.O = π := by
      have h_le_π : Γ.I ⊔ Γ.C ⊔ Γ.O ≤ π :=
        sup_le (sup_le (Γ.hI_on.trans le_sup_left) Γ.hC_plane) (show Γ.O ≤ π from le_sup_left.trans le_sup_left)
      have hIC_lt : Γ.I ⊔ Γ.C < Γ.I ⊔ Γ.C ⊔ Γ.O := h_covBy_ICO.lt
      exact le_antisymm h_le_π (by
        -- I⊔C ⋖ I⊔C⊔O ≤ π. Also I⊔C ⋖ π (from the fact that I⊔C⊔O ≤ π and I⊔C < I⊔C⊔O).
        -- CovBy I⊔C ⋖ I⊔C⊔O. I⊔C⊔O ≤ π. If I⊔C⊔O < π, then I⊔C < I⊔C⊔O < π.
        -- But I⊔C has height 2, I⊔C⊔O has height 3. π has height 3. So I⊔C⊔O = π.
        -- Formally: I⊔C ⋖ I⊔C⊔O and I⊔C⊔O ≤ π. I⊔C < I⊔C⊔O. If I⊔C⊔O < π,
        -- then from covBy_sup... we'd need another covering. Actually:
        -- V ∉ I⊔C⊔O → π = I⊔C⊔O⊔V which is > I⊔C⊔O. But we know I⊔C⊔O ≤ π.
        -- Simpler: I⊔C⊔O is a plane. It contains l (via O⊔I = l). It contains E (E ≤ m ≤ π).
        -- Wait, E ≤ π but does E ≤ I⊔C⊔O? Only if I⊔C⊔O = π.
        -- Use: hl_covBy : l ⋖ π. l ≤ I⊔C⊔O (from hOI_eq_l ▸). l < I⊔C⊔O (E_I ≤ I⊔C, so...).
        -- Actually: I⊔C ≥ I. l = O⊔I ≤ I⊔C⊔O.
        -- l ⋖ π. l ≤ I⊔C⊔O ≤ π. If l = I⊔C⊔O → C ≤ l → false.
        -- l < I⊔C⊔O (C∉l, C ≤ I⊔C⊔O). CovBy → I⊔C⊔O = π.
        have hl_le : l ≤ Γ.I ⊔ Γ.C ⊔ Γ.O :=
          hOI_eq_l ▸ sup_le le_sup_right (le_sup_left.trans le_sup_left)
        have hl_lt : l < Γ.I ⊔ Γ.C ⊔ Γ.O := lt_of_le_of_ne hl_le
          (fun h' => Γ.hC_not_l ((le_sup_right.trans le_sup_left).trans h'.symm.le))
        exact ((hl_covBy.eq_or_eq hl_lt.le h_le_π).resolve_left (ne_of_gt hl_lt)).symm.le)
    rwa [hICO_eq] at h_covBy_ICO
  have hG_atom : IsAtom G :=
    line_meets_m_at_atom ha Γ.hE_atom ha_ne_E
      (sup_le (ha_on.trans le_sup_left) (Γ.hE_on_m.trans Γ.m_covBy_π.le))
      hIC_covBy.le hIC_covBy ha_not_IC
  have hG_not_l : ¬ G ≤ l := by
    intro h
    have hlIC : (Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.C) = Γ.I := by
      rw [inf_comm, sup_comm Γ.I Γ.C]
      exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on
    have hG_eq_I : G = Γ.I :=
      (Γ.hI.le_iff.mp ((le_inf h hG_le_IC).trans hlIC.le)).resolve_left hG_atom.1
    have hI_le_aE : Γ.I ≤ a ⊔ Γ.E := hG_eq_I ▸ hG_le_aE
    have ha_lt_aI : a < a ⊔ Γ.I := lt_of_le_of_ne le_sup_left
      (fun h' => haI ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hI.1).symm)
    have haI_eq_aE : a ⊔ Γ.I = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt_aI.le
        (sup_le le_sup_left hI_le_aE)).resolve_left (ne_of_gt ha_lt_aI)
    exact Γ.hE_not_l (le_sup_right.trans (haI_eq_aE.symm.le.trans (sup_le ha_on Γ.hI_on)))
  have hG_not_m : ¬ G ≤ m := by
    intro h
    have hG_eq_E : G = Γ.E :=
      (Γ.hE_atom.le_iff.mp (le_inf hG_le_aE h |>.trans
        (line_direction ha ha_not_m Γ.hE_on_m).le)).resolve_left hG_atom.1
    have hE_le_IC : Γ.E ≤ Γ.I ⊔ Γ.C := hG_eq_E ▸ hG_le_IC
    have hE_eq_EI : Γ.E = Γ.E_I :=
      (Γ.hE_I_atom.le_iff.mp (le_inf hE_le_IC Γ.hE_on_m)).resolve_left Γ.hE_atom.1
    have hC_ne_E : Γ.C ≠ Γ.E := fun h' => Γ.hC_not_m (h' ▸ Γ.hE_on_m)
    have hC_lt_CE : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h' => hC_ne_E ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hE_atom.1).symm)
    have hCE_eq_OC : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C :=
      ((sup_comm Γ.C Γ.O ▸ atom_covBy_join Γ.hC Γ.hO (Ne.symm hOC) : Γ.C ⋖ Γ.O ⊔ Γ.C).eq_or_eq
        hC_lt_CE.le (sup_le le_sup_right (inf_le_left : Γ.E ≤ Γ.O ⊔ Γ.C))).resolve_left
        (ne_of_gt hC_lt_CE)
    have hC_ne_EI : Γ.C ≠ Γ.E_I := fun h' => Γ.hC_not_m (h' ▸ Γ.hE_I_on_m)
    have hC_lt_CEI : Γ.C < Γ.C ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
      (fun h' => hC_ne_EI ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hE_I_atom.1).symm)
    have hCEI_eq_IC : Γ.C ⊔ Γ.E_I = Γ.I ⊔ Γ.C :=
      ((sup_comm Γ.C Γ.I ▸ atom_covBy_join Γ.hC Γ.hI (Ne.symm hIC) : Γ.C ⋖ Γ.I ⊔ Γ.C).eq_or_eq
        hC_lt_CEI.le (sup_le le_sup_right Γ.hE_I_le_IC)).resolve_left
        (ne_of_gt hC_lt_CEI)
    have hOC_eq_IC : Γ.O ⊔ Γ.C = Γ.I ⊔ Γ.C := by
      calc Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.E := hCE_eq_OC.symm
        _ = Γ.C ⊔ Γ.E_I := by rw [hE_eq_EI]
        _ = Γ.I ⊔ Γ.C := hCEI_eq_IC
    have hlIC : l ⊓ (Γ.I ⊔ Γ.C) = Γ.I := by
      change (Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.C) = Γ.I
      rw [inf_comm, sup_comm Γ.I Γ.C]
      exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on
    exact Γ.hOI ((Γ.hI.le_iff.mp (le_inf (le_sup_left.trans hOC_eq_IC.le)
      (show Γ.O ≤ l from le_sup_left) |>.trans (inf_comm l _ ▸ hlIC).le)).resolve_left Γ.hO.1)
  have hG_ne_O : G ≠ Γ.O := fun h => hG_not_l (h ▸ le_sup_left)
  have hG_ne_I : G ≠ Γ.I := by
    intro h
    have hI_le_aE : Γ.I ≤ a ⊔ Γ.E := h ▸ hG_le_aE
    have ha_lt_aI : a < a ⊔ Γ.I := lt_of_le_of_ne le_sup_left
      (fun h' => haI ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hI.1).symm)
    have haI_eq_aE : a ⊔ Γ.I = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt_aI.le
        (sup_le le_sup_left hI_le_aE)).resolve_left (ne_of_gt ha_lt_aI)
    exact Γ.hE_not_l (le_sup_right.trans (haI_eq_aE.symm.le.trans (sup_le ha_on Γ.hI_on)))
  have hG_ne_C : G ≠ Γ.C := by
    intro h
    have hC_le_aE : Γ.C ≤ a ⊔ Γ.E := h ▸ hG_le_aE
    have ha_lt_aC : a < a ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h' => ha_ne_C ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hC.1).symm)
    have haC_eq_aE : a ⊔ Γ.C = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt_aC.le
        (sup_le le_sup_left hC_le_aE)).resolve_left (ne_of_gt ha_lt_aC)
    -- a⊔C = a⊔E → (a⊔C)⊓m = (a⊔E)⊓m = E. d_a = E.
    -- E ≤ a⊔C and E ≤ O⊔C. (C⊔a)⊓(C⊔O) = C (modular, O∉a⊔C). E ≤ C → E = C. ✗
    have hda_eq_E : d_a = Γ.E := by
      have h1 : d_a = (a ⊔ Γ.E) ⊓ m := by rw [← haC_eq_aE]
      rw [h1]; exact line_direction ha ha_not_m Γ.hE_on_m
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      have hl_le : l ≤ a ⊔ Γ.C := hOa_eq_l ▸ (sup_le hle le_sup_left : Γ.O ⊔ a ≤ a ⊔ Γ.C)
      exact Γ.hC_not_l (le_sup_right.trans
        (((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq ha_on hl_le).resolve_left
          (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)).symm.le)
    have hE_le_C : Γ.E ≤ Γ.C := by
      have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := hda_eq_E ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
      have hmod := modular_intersection Γ.hC ha Γ.hO ha_ne_C.symm hOC.symm ha_ne_O
        (show ¬ Γ.O ≤ Γ.C ⊔ a from sup_comm a Γ.C ▸ hO_not_aC)
      calc Γ.E ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.O) :=
            le_inf (sup_comm a Γ.C ▸ hE_le_aC) (sup_comm Γ.O Γ.C ▸ (CoordSystem.hE_le_OC : Γ.E ≤ Γ.O ⊔ Γ.C))
        _ = Γ.C := hmod
    have hE_eq_C := (Γ.hC.le_iff.mp hE_le_C).resolve_left Γ.hE_atom.1
    exact Γ.hC_not_m (hE_eq_C ▸ Γ.hE_on_m)
  -- a⊔G = a⊔E
  have haG_eq_aE : a ⊔ G = a ⊔ Γ.E := by
    have h_lt : a < a ⊔ G := lt_of_le_of_ne le_sup_left
      (fun h => hG_not_l ((ha.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hG_atom.1 ▸ ha_on))
    exact ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left hG_le_aE)).resolve_left (ne_of_gt h_lt)
  -- I⊔G = I⊔C
  have hIG_eq_IC : Γ.I ⊔ G = Γ.I ⊔ Γ.C := by
    have hI_lt : Γ.I < Γ.I ⊔ G := lt_of_le_of_ne le_sup_left
      (fun h => hG_ne_I ((Γ.hI.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hG_atom.1))
    exact ((atom_covBy_join Γ.hI Γ.hC hIC).eq_or_eq hI_lt.le
      (sup_le le_sup_left hG_le_IC)).resolve_left (ne_of_gt hI_lt)
  -- C⊔G = I⊔C
  have hCG_eq_IC : Γ.C ⊔ G = Γ.I ⊔ Γ.C := by
    have hC_lt : Γ.C < Γ.C ⊔ G := lt_of_le_of_ne le_sup_left
      (fun h => hG_ne_C ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hG_atom.1))
    have : Γ.C ⋖ Γ.I ⊔ Γ.C := sup_comm Γ.C Γ.I ▸ atom_covBy_join Γ.hC Γ.hI (Ne.symm hIC)
    exact (this.eq_or_eq hC_lt.le (sup_le le_sup_right hG_le_IC)).resolve_left
      (ne_of_gt hC_lt)
  -- (I⊔G)⊓m = E_I
  have hIG_dir : (Γ.I ⊔ G) ⊓ m = Γ.E_I := by
    change (Γ.I ⊔ G) ⊓ (Γ.U ⊔ Γ.V) = (Γ.I ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V); rw [hIG_eq_IC]
  -- σ_c(G) = (O⊔G)⊓(c⊔E_I)
  have hσcG_eq : dilation_ext Γ c G = (Γ.O ⊔ G) ⊓ (c ⊔ Γ.E_I) := by
    change (Γ.O ⊔ G) ⊓ (c ⊔ (Γ.I ⊔ G) ⊓ m) = (Γ.O ⊔ G) ⊓ (c ⊔ Γ.E_I); rw [hIG_dir]
  -- σ⊔E_I = c⊔E_I
  have hσEI_eq_cEI : σ ⊔ Γ.E_I = c ⊔ Γ.E_I := by
    have hc_ne_EI : c ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hc_on)
    by_cases hσc : σ = c
    · rw [hσc]
    · have hc_lt : c < c ⊔ σ := lt_of_le_of_ne le_sup_left
        (fun h => hσc ((hc.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hσ_atom.1))
      have hcσ_eq : c ⊔ σ = c ⊔ Γ.E_I :=
        ((atom_covBy_join hc Γ.hE_I_atom hc_ne_EI).eq_or_eq hc_lt.le
          (sup_le le_sup_left hσ_on_cEI)).resolve_left (ne_of_gt hc_lt)
      have hσ_ne_EI' : σ ≠ Γ.E_I := fun h' => hσ_not_m (h' ▸ Γ.hE_I_on_m)
      have hσ_cov := line_covers_its_atoms hc Γ.hE_I_atom hc_ne_EI hσ_atom hσ_on_cEI
      have hσ_lt : σ < σ ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
        (fun h' => hσ_ne_EI' ((hσ_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_I_atom.1).symm)
      exact (hσ_cov.eq_or_eq hσ_lt.le (sup_le hσ_on_cEI le_sup_right)).resolve_left
        (ne_of_gt hσ_lt)
  -- Side computations
  have hside1 : (Γ.O ⊔ a) ⊓ (σ ⊔ d_a) = ac := by
    rw [hOa_eq_l, inf_comm]; rfl
  have hda_ne_EI : d_a ≠ Γ.E_I := by
    intro h
    -- d_a = E_I → (a⊔C)⊓m = (I⊔C)⊓m → same direction from C → a = I
    -- (a⊔C)⊓m = d_a = E_I = (I⊔C)⊓m.
    -- C ⋖ C⊔d_a ≤ a⊔C. C ⋖ C⊔E_I ≤ I⊔C.
    -- d_a = E_I → C⊔d_a = C⊔E_I → same line through C.
    -- C⊔d_a ≤ a⊔C (d_a ≤ a⊔C). C⊔E_I ≤ I⊔C.
    -- If C⊔d_a = C⊔E_I then a⊔C shares a line with I⊔C through C.
    -- modular: (C⊔a)⊓l = a (C∉l, a on l). (C⊔I)⊓l = I.
    -- C⊔a = C⊔I → a = (C⊔a)⊓l = (C⊔I)⊓l = I. But a ≠ I. ✗.
    have hC_ne_da : Γ.C ≠ d_a := fun h' => Γ.hC_not_m (h' ▸ inf_le_right)
    have hC_lt_Cda : Γ.C < Γ.C ⊔ d_a := lt_of_le_of_ne le_sup_left
      (fun h' => hC_ne_da ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left hda_atom.1).symm)
    have hCda_le_aC : Γ.C ⊔ d_a ≤ a ⊔ Γ.C := sup_le le_sup_right (inf_le_left : d_a ≤ a ⊔ Γ.C)
    have hC_ne_EI : Γ.C ≠ Γ.E_I := fun h' => Γ.hC_not_m (h' ▸ Γ.hE_I_on_m)
    have hC_lt_CEI : Γ.C < Γ.C ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
      (fun h' => hC_ne_EI ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hE_I_atom.1).symm)
    have hCEI_le_IC : Γ.C ⊔ Γ.E_I ≤ Γ.I ⊔ Γ.C := sup_le le_sup_right Γ.hE_I_le_IC
    have hCda_eq_CEI : Γ.C ⊔ d_a = Γ.C ⊔ Γ.E_I := by rw [h]
    -- C⊔d_a = C⊔E_I ≤ I⊔C. Also C⊔d_a ≤ a⊔C.
    -- CovBy: C ⋖ C⊔d_a = C⊔E_I. C < C⊔a (ha_ne_C).
    -- C⊔d_a ≤ a⊔C. CovBy C ⋖ a⊔C (atom_covBy_join C a). C⊔d_a = a⊔C.
    have hCa_cov : Γ.C ⋖ a ⊔ Γ.C :=
      sup_comm Γ.C a ▸ atom_covBy_join Γ.hC ha (Ne.symm ha_ne_C)
    have hCda_eq_aC : Γ.C ⊔ d_a = a ⊔ Γ.C :=
      (hCa_cov.eq_or_eq hC_lt_Cda.le hCda_le_aC).resolve_left (ne_of_gt hC_lt_Cda)
    have hIC_cov : Γ.C ⋖ Γ.I ⊔ Γ.C :=
      sup_comm Γ.C Γ.I ▸ atom_covBy_join Γ.hC Γ.hI (Ne.symm hIC)
    have hCEI_eq_IC : Γ.C ⊔ Γ.E_I = Γ.I ⊔ Γ.C :=
      (hIC_cov.eq_or_eq hC_lt_CEI.le hCEI_le_IC).resolve_left (ne_of_gt hC_lt_CEI)
    -- a⊔C = C⊔d_a = C⊔E_I = I⊔C
    have haC_eq_IC : a ⊔ Γ.C = Γ.I ⊔ Γ.C :=
      hCda_eq_aC.symm.trans (hCda_eq_CEI.trans hCEI_eq_IC)
    -- (C⊔a)⊓l = a, (C⊔I)⊓l = I. a⊔C = I⊔C → a = I.
    have hCa_dir : (a ⊔ Γ.C) ⊓ l = a := by
      show (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = a
      rw [sup_comm a Γ.C]; exact line_direction Γ.hC Γ.hC_not_l ha_on
    have hCI_dir : (Γ.I ⊔ Γ.C) ⊓ l = Γ.I := by
      show (Γ.I ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.I
      rw [sup_comm Γ.I Γ.C]; exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on
    have : a = Γ.I := by
      calc a = (a ⊔ Γ.C) ⊓ l := hCa_dir.symm
        _ = (Γ.I ⊔ Γ.C) ⊓ l := by rw [haC_eq_IC]
        _ = Γ.I := hCI_dir
    exact haI this
  have hdaEI_eq_m : d_a ⊔ Γ.E_I = m := by
    have hda_lt : d_a < d_a ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
      (fun h => hda_ne_EI ((hda_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_I_atom.1).symm)
    have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
    exact ((line_covers_its_atoms Γ.hU Γ.hV hUV
      hda_atom (inf_le_right : d_a ≤ m)).eq_or_eq hda_lt.le
      (sup_le (inf_le_right : d_a ≤ m) Γ.hE_I_on_m)).resolve_left (ne_of_gt hda_lt)
  have hside2 : (a ⊔ G) ⊓ (d_a ⊔ Γ.E_I) = Γ.E := by
    rw [haG_eq_aE, hdaEI_eq_m]; exact line_direction ha ha_not_m Γ.hE_on_m
  have hside3 : (Γ.O ⊔ G) ⊓ (σ ⊔ Γ.E_I) = dilation_ext Γ c G := by
    rw [hσEI_eq_cEI, ← hσcG_eq]
  -- ═══ Spanning ═══
  have hσ_le_CO : σ ≤ Γ.C ⊔ Γ.O := sup_comm Γ.O Γ.C ▸ hσ_on_OC
  have hda_le_Ca : d_a ≤ Γ.C ⊔ a := sup_comm a Γ.C ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
  have hEI_le_CG : Γ.E_I ≤ Γ.C ⊔ G := Γ.hE_I_le_IC.trans hCG_eq_IC.symm.le
  have hda_plane : d_a ≤ π := (inf_le_right : d_a ≤ m).trans Γ.m_covBy_π.le
  have hOaG_eq_π : Γ.O ⊔ a ⊔ G = π := by
    rw [hOa_eq_l]
    have hl_lt : l < l ⊔ G := lt_of_le_of_ne le_sup_left
      (fun h => hG_not_l (le_sup_right.trans h.symm.le))
    exact (hl_covBy.eq_or_eq hl_lt.le (sup_le hl_covBy.le hG_plane)).resolve_left
      (ne_of_gt hl_lt)
  have hσdaEI_eq_π : σ ⊔ d_a ⊔ Γ.E_I = π := by
    -- σ off m. d_a on m. E_I on m. d_a⊔E_I = m. σ⊔m = π (σ off m, m ⋖ π).
    rw [sup_assoc, hdaEI_eq_m]
    have hm_lt : m < σ ⊔ m := lt_of_le_of_ne le_sup_right
      (fun h => hσ_not_m (le_sup_left.trans h.symm.le))
    exact (Γ.m_covBy_π.eq_or_eq hm_lt.le (sup_le hσ_plane Γ.m_covBy_π.le)).resolve_left
      (ne_of_gt hm_lt)
  have hOa_covBy : Γ.O ⊔ a ⋖ π := hOa_eq_l ▸ hl_covBy
  have hOG_covBy : Γ.O ⊔ G ⋖ π := by
    have ha_not_OG : ¬ a ≤ Γ.O ⊔ G := by
      intro h
      have hl_le : l ≤ Γ.O ⊔ G := hOa_eq_l ▸ sup_le le_sup_left h
      have hO_cov := atom_covBy_join Γ.hO hG_atom (Ne.symm hG_ne_O)
      have hO_lt_l := (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
      have hl_eq_OG := (hO_cov.eq_or_eq hO_lt_l.le hl_le).resolve_left (ne_of_gt hO_lt_l)
      exact hG_not_l (le_sup_right.trans hl_eq_OG.symm.le)
    rw [← hOaG_eq_π]
    have h_covBy := line_covBy_plane Γ.hO hG_atom ha (Ne.symm hG_ne_O) (Ne.symm ha_ne_O)
      (fun h => hG_not_l (h ▸ ha_on)) ha_not_OG
    convert h_covBy using 1; ac_rfl
  have haG_covBy : a ⊔ G ⋖ π := haG_eq_aE ▸ haE_covBy
  have ha_ne_G : a ≠ G := fun h => hG_not_l (h ▸ ha_on)
  have hσ_ne_da : σ ≠ d_a := fun h => hσ_not_m (h ▸ inf_le_right)
  have hσ_ne_EI : σ ≠ Γ.E_I := fun h => hσ_not_m (h ▸ Γ.hE_I_on_m)
  have hOa_ne_σda : Γ.O ⊔ a ≠ σ ⊔ d_a := by
    rw [hOa_eq_l]; intro h; exact hσ_not_l (le_sup_left.trans h.symm.le)
  have hOG_ne_σEI : Γ.O ⊔ G ≠ σ ⊔ Γ.E_I := by
    rw [hσEI_eq_cEI]
    intro h
    have hO_le_cEI : Γ.O ≤ c ⊔ Γ.E_I := le_sup_left.trans h.le
    have hcEI_l : (c ⊔ Γ.E_I) ⊓ l = c := by
      change (c ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = c; rw [sup_comm c Γ.E_I]
      exact line_direction Γ.hE_I_atom Γ.hE_I_not_l hc_on
    exact hc_ne_O ((hc.le_iff.mp (le_inf hO_le_cEI (show Γ.O ≤ l from le_sup_left)
      |>.trans hcEI_l.le)).resolve_left Γ.hO.1).symm
  have haG_ne_daEI : a ⊔ G ≠ d_a ⊔ Γ.E_I := by
    rw [haG_eq_aE, hdaEI_eq_m]; intro h; exact ha_not_m (le_sup_left.trans h.le)
  have hC_ne_da : Γ.C ≠ d_a := fun h => Γ.hC_not_m (h ▸ inf_le_right)
  have hC_ne_σ : Γ.C ≠ σ := by
    intro h
    exact (dilation_ext_ne_P Γ Γ.hC hc hc_on hc_ne_O hc_ne_U
      Γ.hC_plane Γ.hC_not_m Γ.hC_not_l (Ne.symm hOC) (Ne.symm hIC) hcI) h.symm
  have hO_ne_σ : Γ.O ≠ σ := by
    intro h; apply hc_ne_O
    have hO_le_cEI : Γ.O ≤ c ⊔ Γ.E_I := h ▸ hσ_on_cEI
    have hcEI_l : (c ⊔ Γ.E_I) ⊓ l = c := by
      change (c ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = c
      rw [sup_comm c Γ.E_I]
      exact line_direction Γ.hE_I_atom Γ.hE_I_not_l hc_on
    exact ((hc.le_iff.mp (le_inf hO_le_cEI (show Γ.O ≤ l from le_sup_left)
      |>.trans hcEI_l.le)).resolve_left Γ.hO.1).symm
  have ha_ne_da : a ≠ d_a := fun h => ha_not_m (h ▸ inf_le_right)
  have hG_ne_EI : G ≠ Γ.E_I := fun h => hG_not_m (h ▸ Γ.hE_I_on_m)
  -- ═══ Desargues application ═══
  obtain ⟨axis, haxis_le, haxis_ne, hax1, hax2, hax3⟩ :=
    desargues_planar Γ.hC Γ.hO ha hG_atom hσ_atom hda_atom Γ.hE_I_atom
      Γ.hC_plane (show Γ.O ≤ π from le_sup_left.trans le_sup_left)
      (ha_on.trans le_sup_left) hG_plane hσ_plane hda_plane
      (Γ.hE_I_on_m.trans Γ.m_covBy_π.le)
      hσ_le_CO hda_le_Ca hEI_le_CG
      (Ne.symm ha_ne_O) (Ne.symm hG_ne_O) ha_ne_G
      hσ_ne_da hσ_ne_EI hda_ne_EI
      hOa_ne_σda hOG_ne_σEI haG_ne_daEI
      hOaG_eq_π hσdaEI_eq_π
      (Ne.symm hOC) (Ne.symm ha_ne_C) (Ne.symm hG_ne_C)
      hC_ne_σ hC_ne_da (fun h => Γ.hC_not_m (h ▸ Γ.hE_I_on_m))
      hO_ne_σ ha_ne_da hG_ne_EI
      R hR hR_not h_irred
      hOa_covBy hOG_covBy haG_covBy
  -- Extract: σ_c(G) ≤ ac ⊔ E
  have hσcG_le_acE : dilation_ext Γ c G ≤ ac ⊔ Γ.E := by
    have hac_le : ac ≤ axis := hside1 ▸ hax1
    have hE_le : Γ.E ≤ axis := hside2 ▸ hax3
    have hσcG_le : dilation_ext Γ c G ≤ axis := hside3 ▸ hax2
    -- ac ⊔ E ≤ axis. axis ≤ π, axis ≠ π. ac⊔E is a line.
    -- ac and E are atoms. ac on l, E on m. ac ≠ E (ac not on m).
    have hac_atom : IsAtom ac := by
      -- ac = (σ⊔d_a) ⊓ l. Two lines in π, distinct → meet at atom.
      -- d_a ≠ U
      have hda_ne_U' : d_a ≠ Γ.U := by
        intro h
        have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := h ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
        have haCl : (a ⊔ Γ.C) ⊓ l = a := by
          change (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = a
          rw [sup_comm a Γ.C]; exact line_direction Γ.hC Γ.hC_not_l ha_on
        exact ha_ne_U ((ha.le_iff.mp (le_inf hU_le_aC (show Γ.U ≤ l from le_sup_right)
          |>.trans haCl.le)).resolve_left Γ.hU.1).symm
      -- U ∉ σ⊔d_a (if U ≤ σ⊔d_a then d_a⊔U = m ≤ σ⊔d_a, σ⊔m = π ≤ σ⊔d_a = π,
      -- σ ⋖ π, planes_meet_covBy(σ,l,π): ⊥ ⋖ l, contradicts O on l)
      have hU_not_σda : ¬ Γ.U ≤ σ ⊔ d_a := by
        intro hU_le
        have hdaU_le : d_a ⊔ Γ.U ≤ σ ⊔ d_a := sup_le le_sup_right hU_le
        have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
        have hdaU_eq_m : d_a ⊔ Γ.U = m := by
          have hda_lt : d_a < d_a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
            (fun h' => hda_ne_U' ((hda_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
              Γ.hU.1).symm)
          exact ((line_covers_its_atoms Γ.hU Γ.hV hUV hda_atom
            (inf_le_right : d_a ≤ m)).eq_or_eq hda_lt.le
            (sup_le (inf_le_right : d_a ≤ m) le_sup_left)).resolve_left (ne_of_gt hda_lt)
        have hm_le_σda : m ≤ σ ⊔ d_a := hdaU_eq_m ▸ hdaU_le
        have hσm_eq_π : σ ⊔ m = π := by
          have hm_lt : m < σ ⊔ m := lt_of_le_of_ne le_sup_right
            (fun h => hσ_not_m (le_sup_left.trans h.symm.le))
          exact (Γ.m_covBy_π.eq_or_eq hm_lt.le (sup_le hσ_plane Γ.m_covBy_π.le)).resolve_left
            (ne_of_gt hm_lt)
        have hσda_eq_π : σ ⊔ d_a = π :=
          le_antisymm (sup_le hσ_plane hda_plane)
            (hσm_eq_π ▸ sup_le le_sup_left hm_le_σda)
        have hσ_covBy_π : σ ⋖ π := hσda_eq_π ▸ atom_covBy_join hσ_atom hda_atom hσ_ne_da
        have hσ_ne_l : (σ : L) ≠ l := fun h => hσ_not_l (h.symm ▸ le_refl _)
        have ⟨_, h2⟩ := planes_meet_covBy hσ_covBy_π hl_covBy hσ_ne_l
        have hσl_bot : σ ⊓ l = ⊥ :=
          (hσ_atom.le_iff.mp inf_le_left).resolve_right (fun h => hσ_not_l (h ▸ inf_le_right))
        exact (hσl_bot ▸ h2).2 Γ.hO.bot_lt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
      -- σ⊔d_a ⋖ π
      have hσda_covBy : σ ⊔ d_a ⋖ π := by
        have hdaU_eq_m : d_a ⊔ Γ.U = m := by
          have hda_lt : d_a < d_a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
            (fun h' => hda_ne_U' ((hda_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
              Γ.hU.1).symm)
          have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
          exact ((line_covers_its_atoms Γ.hU Γ.hV hUV hda_atom
            (inf_le_right : d_a ≤ m)).eq_or_eq hda_lt.le
            (sup_le (inf_le_right : d_a ≤ m) le_sup_left)).resolve_left (ne_of_gt hda_lt)
        have hσdaU_eq_π : σ ⊔ d_a ⊔ Γ.U = π := by
          rw [sup_assoc, hdaU_eq_m]
          have hm_lt : m < σ ⊔ m := lt_of_le_of_ne le_sup_right
            (fun h => hσ_not_m (le_sup_left.trans h.symm.le))
          exact (Γ.m_covBy_π.eq_or_eq hm_lt.le (sup_le hσ_plane Γ.m_covBy_π.le)).resolve_left
            (ne_of_gt hm_lt)
        rw [← hσdaU_eq_π]
        exact line_covBy_plane hσ_atom hda_atom Γ.hU hσ_ne_da
          (fun h => hU_not_σda (h ▸ le_sup_left)) hda_ne_U' hU_not_σda
      -- planes_meet_covBy → (σ⊔d_a)⊓l ⋖ l
      have hσda_ne_l : σ ⊔ d_a ≠ l := (hOa_eq_l ▸ hOa_ne_σda).symm
      have ⟨_, hmeet_covBy_l⟩ := planes_meet_covBy hσda_covBy hl_covBy hσda_ne_l
      -- (σ⊔d_a)⊓l ≠ ⊥ (else ⊥ ⋖ l, but O on l)
      have hmeet_ne_bot : (σ ⊔ d_a) ⊓ l ≠ ⊥ := fun h =>
        (h ▸ hmeet_covBy_l).2 Γ.hO.bot_lt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
      exact line_height_two Γ.hO Γ.hU Γ.hOU
        (bot_lt_iff_ne_bot.mpr hmeet_ne_bot) hmeet_covBy_l.lt
    have hac_on : ac ≤ l := by show coord_mul Γ a c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
    have hac_ne_E : ac ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hac_on)
    have hac_lt : ac < ac ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hac_ne_E ((hac_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_atom.1).symm)
    have hacE_le : ac ⊔ Γ.E ≤ axis := sup_le hac_le hE_le
    -- axis ⋖ π (it's < π and a line). CovBy: ac ⋖ ac⊔E ≤ axis ≤ π.
    -- If axis = π contradiction with haxis_ne.
    -- ac⊔E ≤ axis. axis < π. ac < ac⊔E ≤ axis.
    -- axis is height 2 (line): need to show.
    -- ac⊔E is a line (CovBy). If ac⊔E < axis then axis is height ≥ 3.
    -- But axis ≤ π and π has height 3 (plane). If axis = π contradiction.
    -- ac⊔E < axis < π. But ac ⋖ ac⊔E (atom CovBy). ac < ac⊔E < axis < π.
    -- That's 4 levels: ac (height 1), ac⊔E (height 2), axis (height ≥ 3), π (height 3).
    -- axis ≤ π and axis has height ≥ 3 → axis = π. ✗.
    -- So ac⊔E = axis.
    -- ac⊔E ≤ axis. ac⊔E ⋖ π. axis ≤ π, axis ≠ π. CovBy → ac⊔E = axis or axis = π. axis ≠ π.
    -- ac⊔E ≤ axis < π. ac⊔E ⋖ π. CovBy → ac⊔E = axis.
    have haxis_lt : axis < π := lt_of_le_of_ne haxis_le haxis_ne
    have hacE_eq_axis : ac ⊔ Γ.E = axis := by
      -- ac ∉ m (if ac on both l and m then ac = U, but U ∉ σ⊔d_a)
      have hac_not_m : ¬ ac ≤ m := by
        intro h
        -- l⊓m = U
        have hO_not_m : ¬ Γ.O ≤ m := fun hOm =>
          Γ.hOU (Γ.atom_on_both_eq_U Γ.hO (show Γ.O ≤ l from le_sup_left) hOm)
        have hlm_eq_U : l ⊓ m = Γ.U := by
          change (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
          exact line_direction Γ.hO hO_not_m le_sup_left
        have hac_eq_U : ac = Γ.U :=
          (Γ.hU.le_iff.mp (le_inf hac_on h |>.trans hlm_eq_U.le)).resolve_left hac_atom.1
        -- ac = U, so U ≤ σ⊔d_a (since ac ≤ σ⊔d_a). But U ∉ σ⊔d_a (from hac_atom proof).
        -- Need to re-derive. U ≤ σ⊔d_a → d_a⊔U = m → σ∉m → σ⊔m = π → σ⊔d_a = π → σ ⋖ π →
        -- planes_meet(σ,l,π): ⊥ ⋖ l, but O < l. ✗.
        have hU_le_σda : Γ.U ≤ σ ⊔ d_a := hac_eq_U ▸ (inf_le_left : ac ≤ σ ⊔ d_a)
        have hda_ne_U'' : d_a ≠ Γ.U := by
          intro hd; exact ha_ne_U ((ha.le_iff.mp (le_inf
            (hd ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C) : Γ.U ≤ a ⊔ Γ.C)
            (show Γ.U ≤ l from le_sup_right) |>.trans
            (show (a ⊔ Γ.C) ⊓ l = a from by
              change (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = a
              rw [sup_comm a Γ.C]; exact line_direction Γ.hC Γ.hC_not_l ha_on).le)).resolve_left Γ.hU.1).symm
        have hUV : Γ.U ≠ Γ.V := fun hh => Γ.hV_off (hh ▸ le_sup_right)
        have hdaU_eq_m : d_a ⊔ Γ.U = m := by
          have hda_lt : d_a < d_a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
            (fun h' => hda_ne_U'' ((hda_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
              Γ.hU.1).symm)
          exact ((line_covers_its_atoms Γ.hU Γ.hV hUV hda_atom
            (inf_le_right : d_a ≤ m)).eq_or_eq hda_lt.le
            (sup_le (inf_le_right : d_a ≤ m) le_sup_left)).resolve_left (ne_of_gt hda_lt)
        have hm_le_σda : m ≤ σ ⊔ d_a := hdaU_eq_m ▸ sup_le le_sup_right hU_le_σda
        have hσm_eq_π : σ ⊔ m = π := by
          have hm_lt : m < σ ⊔ m := lt_of_le_of_ne le_sup_right
            (fun hh => hσ_not_m (le_sup_left.trans hh.symm.le))
          exact (Γ.m_covBy_π.eq_or_eq hm_lt.le (sup_le hσ_plane Γ.m_covBy_π.le)).resolve_left
            (ne_of_gt hm_lt)
        have hσda_eq_π : σ ⊔ d_a = π :=
          le_antisymm (sup_le hσ_plane hda_plane) (hσm_eq_π ▸ sup_le le_sup_left hm_le_σda)
        have hσ_covBy_π : σ ⋖ π := hσda_eq_π ▸ atom_covBy_join hσ_atom hda_atom hσ_ne_da
        have hσ_ne_l : (σ : L) ≠ l := fun hh => hσ_not_l (hh.symm ▸ le_refl _)
        have ⟨_, h2⟩ := planes_meet_covBy hσ_covBy_π hl_covBy hσ_ne_l
        have hσl_bot : σ ⊓ l = ⊥ :=
          (hσ_atom.le_iff.mp inf_le_left).resolve_right (fun hh => hσ_not_l (hh ▸ inf_le_right))
        exact (hσl_bot ▸ h2).2 Γ.hO.bot_lt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
      -- ac⊔E ⋖ π: E = (ac⊔E)⊓m (line_direction). E ⋖ m. covBy_sup → ac⊔E ⋖ m⊔(ac⊔E) = π.
      have hmacE_eq_E : m ⊓ (ac ⊔ Γ.E) = Γ.E := by
        rw [inf_comm]; exact line_direction hac_atom hac_not_m Γ.hE_on_m
      have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
      have hE_covBy_m : Γ.E ⋖ m := line_covers_its_atoms Γ.hU Γ.hV hUV Γ.hE_atom Γ.hE_on_m
      have hacE_m_eq_π : m ⊔ (ac ⊔ Γ.E) = π := by
        -- m ⊔ (ac ⊔ E) = m ⊔ ac (since E ≤ m). ac ∉ m. m ⋖ π. m < m⊔ac ≤ π.
        have hmacE_eq_mac : m ⊔ (ac ⊔ Γ.E) = m ⊔ ac := by
          apply le_antisymm
          · exact sup_le le_sup_left (sup_le le_sup_right (Γ.hE_on_m.trans le_sup_left))
          · exact sup_le le_sup_left (le_sup_left.trans le_sup_right)
        rw [hmacE_eq_mac]
        have hm_lt : m < m ⊔ ac := lt_of_le_of_ne le_sup_left
          (fun h => hac_not_m (le_sup_right.trans h.symm.le))
        exact (Γ.m_covBy_π.eq_or_eq hm_lt.le
          (sup_le Γ.m_covBy_π.le (hac_on.trans le_sup_left))).resolve_left (ne_of_gt hm_lt)
      have hmacE_covBy_m : m ⊓ (ac ⊔ Γ.E) ⋖ m := by rw [hmacE_eq_E]; exact hE_covBy_m
      have hacE_covBy_π : ac ⊔ Γ.E ⋖ π := by
        rw [← hacE_m_eq_π]
        exact covBy_sup_of_inf_covBy_left hmacE_covBy_m
      exact (hacE_covBy_π.eq_or_eq hacE_le haxis_le).resolve_right haxis_ne |>.symm
    exact hσcG_le.trans hacE_eq_axis.symm.le
  -- ═══ Part A: σ_c(C_a) ≤ σ ⊔ U ═══
  have hPartA : dilation_ext Γ c C_a ≤ σ ⊔ Γ.U := by
    -- C_a ∉ O⊔C
    have hCa_not_OC : ¬ C_a ≤ Γ.O ⊔ Γ.C := by
      intro h
      have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
        intro hU
        have hl_le_OC : l ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left hU
        have hO_lt_l : Γ.O < l := (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
        have hl_eq_OC : l = Γ.O ⊔ Γ.C :=
          ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq hO_lt_l.le hl_le_OC).resolve_left
            (ne_of_gt hO_lt_l)
        exact Γ.hC_not_l (le_sup_right.trans hl_eq_OC.symm.le)
      -- (U⊔C)⊓(O⊔C) = C via modular law
      have hqOC_eq_C : (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm Γ.U Γ.C, sup_comm Γ.O Γ.C]
        calc (Γ.C ⊔ Γ.U) ⊓ (Γ.C ⊔ Γ.O) = Γ.C ⊔ Γ.U ⊓ (Γ.C ⊔ Γ.O) :=
              sup_inf_assoc_of_le Γ.U (le_sup_left : Γ.C ≤ Γ.C ⊔ Γ.O)
          _ = Γ.C := by
              have : Γ.U ⊓ (Γ.C ⊔ Γ.O) = ⊥ :=
                (Γ.hU.le_iff.mp inf_le_left).resolve_right
                  (fun h' => hU_not_OC (sup_comm Γ.C Γ.O ▸ (h' ▸ inf_le_right)))
              rw [this, sup_bot_eq]
      exact hCa_ne_C ((Γ.hC.le_iff.mp (le_inf hCa_le_q h |>.trans hqOC_eq_C.le)).resolve_left
        hCa_atom.1)
    -- σ ≠ σ(C_a): if equal, σ ≤ (O⊔C)⊓(O⊔C_a) = O (modular). σ = O. ✗.
    have hσ_ne_σCa : σ ≠ dilation_ext Γ c C_a := by
      intro heq
      have hσ_le_OCa : σ ≤ Γ.O ⊔ C_a := heq ▸ (inf_le_left : dilation_ext Γ c C_a ≤ Γ.O ⊔ C_a)
      have hOCOCa_eq_O : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ C_a) = Γ.O :=
        modular_intersection Γ.hO Γ.hC hCa_atom hOC (Ne.symm hCa_ne_O) (Ne.symm hCa_ne_C)
          hCa_not_OC
      exact hO_ne_σ ((Γ.hO.le_iff.mp (le_inf hσ_on_OC hσ_le_OCa |>.trans
        hOCOCa_eq_O.le)).resolve_left hσ_atom.1).symm
    -- C⊔C_a = U⊔C, direction = U
    have hCCa_eq_UC : Γ.C ⊔ C_a = Γ.U ⊔ Γ.C := by
      have hC_lt : Γ.C < Γ.C ⊔ C_a := lt_of_le_of_ne le_sup_left
        (fun h' => hCa_ne_C ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          hCa_atom.1))
      exact ((sup_comm Γ.C Γ.U ▸ atom_covBy_join Γ.hC Γ.hU hUC.symm).eq_or_eq hC_lt.le
        (sup_le le_sup_right hCa_le_q)).resolve_left (ne_of_gt hC_lt)
    have hCCa_dir : (Γ.C ⊔ C_a) ⊓ m = Γ.U := hCCa_eq_UC ▸ hqm_eq_U
    -- DPD
    have hdpd := dilation_preserves_direction Γ Γ.hC hCa_atom c hc hc_on hc_ne_O hc_ne_U
      Γ.hC_plane hCa_plane Γ.hC_not_m hCa_not_m Γ.hC_not_l hCa_not_l
      (Ne.symm hOC) hCa_ne_O (Ne.symm hCa_ne_C) (Ne.symm hIC) hCa_ne_I
      hσ_ne_σCa R hR hR_not h_irred
    -- (σ⊔σ(C_a))⊓m = U. So U ≤ σ⊔σ(C_a).
    have hU_le : Γ.U ≤ σ ⊔ dilation_ext Γ c C_a := by
      have : (σ ⊔ dilation_ext Γ c C_a) ⊓ m = Γ.U := by rw [← hdpd, hCCa_dir]
      exact this ▸ inf_le_left
    -- σ⊔U ≤ σ⊔σ(C_a). σ ⋖ σ⊔σ(C_a). CovBy → σ⊔U = σ⊔σ(C_a). σ(C_a) ≤ σ⊔U.
    have hσU_le : σ ⊔ Γ.U ≤ σ ⊔ dilation_ext Γ c C_a := sup_le le_sup_left hU_le
    have hσ_ne_U : σ ≠ Γ.U := fun h => hσ_not_m (show σ ≤ m from h ▸ le_sup_left)
    have hσ_lt : σ < σ ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h => hσ_ne_U ((hσ_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hU.1).symm)
    have hσCa_atom := dilation_ext_atom Γ hCa_atom hc hc_on hc_ne_O hc_ne_U
      hCa_plane hCa_not_l hCa_ne_O hCa_ne_I hCa_not_m
    have hσU_eq : σ ⊔ Γ.U = σ ⊔ dilation_ext Γ c C_a :=
      ((atom_covBy_join hσ_atom hσCa_atom hσ_ne_σCa).eq_or_eq hσ_lt.le hσU_le).resolve_left
        (ne_of_gt hσ_lt)
    exact hσU_eq ▸ le_sup_right
  -- ═══ Part B: σ_c(C_a) ≤ ac ⊔ E ═══
  have hPartB : dilation_ext Γ c C_a ≤ ac ⊔ Γ.E := by
    -- G ≠ C_a: if G = C_a then G ≤ (I⊔C)⊓(U⊔C) = C. G = C. ✗.
    have hG_ne_Ca : G ≠ C_a := by
      intro h
      have hI_not_UC : ¬ Γ.I ≤ Γ.U ⊔ Γ.C := by
        intro hI_le
        have hqlI : (Γ.U ⊔ Γ.C) ⊓ l = Γ.U := by
          change (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.U
          calc (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.U ⊔ Γ.C ⊓ (Γ.O ⊔ Γ.U) :=
                sup_inf_assoc_of_le Γ.C (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U)
            _ = Γ.U := by
                have : Γ.C ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
                  (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h' => Γ.hC_not_l (h' ▸ inf_le_right))
                rw [this, sup_bot_eq]
        have hI_eq_U : Γ.I = Γ.U :=
          (Γ.hU.le_iff.mp (le_inf hI_le Γ.hI_on |>.trans hqlI.le)).resolve_left Γ.hI.1
        exact Γ.hI_not_m (hI_eq_U ▸ le_sup_left)
      have hICUC_eq_C : (Γ.I ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C) = Γ.C := by
        rw [sup_comm Γ.I Γ.C, sup_comm Γ.U Γ.C]
        calc (Γ.C ⊔ Γ.I) ⊓ (Γ.C ⊔ Γ.U) = Γ.C ⊔ Γ.I ⊓ (Γ.C ⊔ Γ.U) :=
              sup_inf_assoc_of_le Γ.I (le_sup_left : Γ.C ≤ Γ.C ⊔ Γ.U)
          _ = Γ.C := by
              have : Γ.I ⊓ (Γ.C ⊔ Γ.U) = ⊥ :=
                (Γ.hI.le_iff.mp inf_le_left).resolve_right
                  (fun h' => hI_not_UC (sup_comm Γ.U Γ.C ▸ (h' ▸ inf_le_right)))
              rw [this, sup_bot_eq]
      exact hG_ne_C ((Γ.hC.le_iff.mp (le_inf hG_le_IC (h ▸ hCa_le_q) |>.trans
        hICUC_eq_C.le)).resolve_left hG_atom.1)
    -- G⊔C_a = a⊔E (both on a⊔E, CovBy)
    have hGCa_eq_aE : G ⊔ C_a = a ⊔ Γ.E := by
      have hG_lt_GCa : G < G ⊔ C_a := lt_of_le_of_ne le_sup_left
        (fun h' => hG_ne_Ca ((hG_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          hCa_atom.1).symm)
      have hGCa_le_aE : G ⊔ C_a ≤ a ⊔ Γ.E := sup_le hG_le_aE hCa_le_aE
      have ha_lt_aE : a < a ⊔ Γ.E := lt_of_le_of_ne le_sup_left
        (fun h' => ha_ne_E ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_atom.1).symm)
      -- G ⋖ G⊔C_a (atom join). G ≤ a⊔E. G⊔C_a ≤ a⊔E. a ⋖ a⊔E.
      -- G < G⊔C_a ≤ a⊔E. Need to show a < G⊔C_a or similar.
      -- Both G and C_a are on a⊔E. G⊔C_a ≤ a⊔E. Also a ≤ a⊔E.
      -- If G⊔C_a = a⊔E, done. If G⊔C_a < a⊔E, then G < G⊔C_a < a⊔E.
      -- But G ⋖ G⊔C_a (atom covBy). And G ⋖ a⊔E (G on a⊔E, atom).
      -- G < G⊔C_a ≤ a⊔E. G ⋖ a⊔E → G⊔C_a = a⊔E or G⊔C_a = G. Not G. So = a⊔E.
      have hG_covBy_aE : G ⋖ a ⊔ Γ.E :=
        line_covers_its_atoms ha Γ.hE_atom ha_ne_E hG_atom hG_le_aE
      exact (hG_covBy_aE.eq_or_eq hG_lt_GCa.le hGCa_le_aE).resolve_left (ne_of_gt hG_lt_GCa)
    -- (G⊔C_a)⊓m = E
    have hGCa_dir : (G ⊔ C_a) ⊓ m = Γ.E := by
      rw [hGCa_eq_aE]; exact line_direction ha ha_not_m Γ.hE_on_m
    -- σ(G) ≠ σ(C_a): modular_intersection gives (O⊔G)⊓(O⊔C_a) = O, so if equal then = O.
    have hσG_ne_σCa : dilation_ext Γ c G ≠ dilation_ext Γ c C_a := by
      intro heq
      -- C_a ∉ O⊔G (if C_a ≤ O⊔G, modular gives C_a ≤ G, C_a = G, ✗)
      have hCa_not_OG : ¬ C_a ≤ Γ.O ⊔ G := by
        intro hle
        have hO_not_aE : ¬ Γ.O ≤ a ⊔ Γ.E := by
          intro hO_le
          have hl_le : l ≤ a ⊔ Γ.E := by
            show Γ.O ⊔ Γ.U ≤ a ⊔ Γ.E
            calc Γ.O ⊔ Γ.U = Γ.O ⊔ a := hOa_eq_l.symm
              _ ≤ a ⊔ Γ.E := sup_le hO_le le_sup_left
          have ha_lt_l := (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt
          exact Γ.hE_not_l (le_sup_right.trans
            (((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt_l.le hl_le).resolve_left
              (ne_of_gt ha_lt_l)).symm.le)
        -- modular_intersection G a O: (G⊔a)⊓(G⊔O) = G. O ∉ G⊔a.
        have hO_not_aG : ¬ Γ.O ≤ a ⊔ G := fun h => hO_not_aE (haG_eq_aE ▸ h)
        have hGaGO_eq_G : (G ⊔ a) ⊓ (G ⊔ Γ.O) = G :=
          modular_intersection hG_atom ha Γ.hO (Ne.symm ha_ne_G) hG_ne_O ha_ne_O
            (fun h => hO_not_aG (sup_comm G a ▸ h))
        have hCa_le_Ga : C_a ≤ G ⊔ a :=
          hCa_le_aE.trans (haG_eq_aE.symm ▸ sup_comm a G ▸ le_refl (a ⊔ G))
        have hCa_le_GO : C_a ≤ G ⊔ Γ.O := sup_comm Γ.O G ▸ hle
        exact hG_ne_Ca.symm ((hG_atom.le_iff.mp
          (le_inf hCa_le_Ga hCa_le_GO |>.trans hGaGO_eq_G.le)).resolve_left hCa_atom.1)
      have hσG_atom := dilation_ext_atom Γ hG_atom hc hc_on hc_ne_O hc_ne_U
        hG_plane hG_not_l hG_ne_O hG_ne_I hG_not_m
      have hOGOCa_eq_O : (Γ.O ⊔ G) ⊓ (Γ.O ⊔ C_a) = Γ.O :=
        modular_intersection Γ.hO hG_atom hCa_atom (Ne.symm hG_ne_O) (Ne.symm hCa_ne_O)
          hG_ne_Ca hCa_not_OG
      have hσG_le_OG : dilation_ext Γ c G ≤ Γ.O ⊔ G := inf_le_left
      have hσG_le_OCa : dilation_ext Γ c G ≤ Γ.O ⊔ C_a := by
        calc dilation_ext Γ c G = dilation_ext Γ c C_a := heq
          _ ≤ Γ.O ⊔ C_a := inf_le_left
      -- dilation_ext Γ c G ≤ O, so = O or = ⊥. Not ⊥ (atom). So = O. But σ ≠ O.
      -- Wait, this is dilation_ext Γ c G, not σ. σ = dilation_ext Γ c C.
      -- The goal is False. We have heq : dilation_ext Γ c G = dilation_ext Γ c C_a.
      -- dilation_ext Γ c G ≤ (O⊔G)⊓(O⊔C_a) = O. So it's O. dilation_ext Γ c G = O.
      -- But dilation_ext_ne_P says dilation_ext ≠ P (the original point).
      -- Actually dilation_ext Γ c G ≠ G (from dilation_ext_ne_P, if applicable).
      -- But we showed dilation_ext Γ c G = O. And G ≠ O. So dilation_ext = O ≠ G.
      -- That doesn't immediately help unless we know dilation_ext ≠ O.
      -- Actually: dilation_ext Γ c G = (O⊔G) ⊓ (c⊔...). It's ≤ O⊔G.
      -- If = O, then O ≤ c⊔dir. dir = (I⊔G)⊓m. O on l. c on l.
      -- O ≤ c⊔dir. c ⋖ c⊔dir. O ≤ c⊔dir means c⊔dir ≥ O. c⊔O ≤ c⊔dir.
      -- This would need more work. Let me use a different contradiction.
      -- The point is dilation_ext Γ c G is an atom (hσG_atom). It's ≤ O. So = O.
      -- But G ≠ O (hG_ne_O). And dilation_ext Γ c G on O⊔G. If dilation_ext = O, fine.
      -- Now dilation_ext Γ c G ≠ G (dilation_ext_ne_P). So O ≠ G. Already known.
      -- Hmm, dilation_ext = O doesn't immediately give a contradiction.
      -- But: dilation_ext Γ c G = O means O ≤ c⊔((I⊔G)⊓m). O on l, c on l.
      -- (I⊔G)⊓m is on m. O not on m. O ≤ c⊔dir. c on l, dir on m.
      -- If O = c, done (hc_ne_O). If O ≠ c, c⊔O = l. dir ≤ c⊔dir. c⊔dir ≥ O, c.
      -- c⊔dir ≥ l. But c ⋖ c⊔dir (c atom, dir atom, c ≠ dir). c < l ≤ c⊔dir.
      -- CovBy: l = c⊔dir. dir ≤ l. dir on m. dir ≤ l⊓m = U. dir atom: dir = U or ⊥.
      -- dir atom → dir = U. (I⊔G)⊓m = U. But we showed this might equal something else.
      -- This is getting complex. Let me just show the dilation_ext ≠ O via properties.
      -- dilation_ext_ne_P gives dilation_ext ≠ G. We need ≠ O.
      -- Actually we can just show: if dilation_ext Γ c G = O, then...
      -- Actually, easier: use that hσG_atom is an atom and ≤ O.
      have hσG_eq_O : dilation_ext Γ c G = Γ.O :=
        (Γ.hO.le_iff.mp (le_inf hσG_le_OG hσG_le_OCa |>.trans hOGOCa_eq_O.le)).resolve_left
          hσG_atom.1
      -- dilation_ext Γ c G = O. O ≤ c⊔((I⊔G)⊓m) = c⊔E_I (since I⊔G = I⊔C).
      -- (c⊔E_I)⊓l = c (line_direction, E_I∉l, c on l). O ≤ c. O = c. hc_ne_O. ✗.
      have hO_le_cEI : Γ.O ≤ c ⊔ Γ.E_I := by
        have : dilation_ext Γ c G ≤ c ⊔ ((Γ.I ⊔ G) ⊓ m) := inf_le_right
        rw [hIG_dir] at this; rw [hσG_eq_O] at this; exact this
      have hcEI_l : (c ⊔ Γ.E_I) ⊓ l = c := by
        change (c ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = c
        rw [sup_comm c Γ.E_I]
        exact line_direction Γ.hE_I_atom Γ.hE_I_not_l hc_on
      exact hc_ne_O ((hc.le_iff.mp (le_inf hO_le_cEI (show Γ.O ≤ l from le_sup_left) |>.trans
        hcEI_l.le)).resolve_left Γ.hO.1).symm
    -- DPD: (G⊔C_a)⊓m = (σ(G)⊔σ(C_a))⊓m = E
    have hσG_atom := dilation_ext_atom Γ hG_atom hc hc_on hc_ne_O hc_ne_U
      hG_plane hG_not_l hG_ne_O hG_ne_I hG_not_m
    have hdpd := dilation_preserves_direction Γ hG_atom hCa_atom c hc hc_on hc_ne_O hc_ne_U
      hG_plane hCa_plane hG_not_m hCa_not_m hG_not_l hCa_not_l
      hG_ne_O hCa_ne_O hG_ne_Ca hG_ne_I hCa_ne_I
      hσG_ne_σCa R hR hR_not h_irred
    -- E ≤ σ(G)⊔σ(C_a)
    have hE_le : Γ.E ≤ dilation_ext Γ c G ⊔ dilation_ext Γ c C_a := by
      have h : (dilation_ext Γ c G ⊔ dilation_ext Γ c C_a) ⊓ m = Γ.E := by
        rw [← hdpd, hGCa_dir]
      exact h ▸ inf_le_left
    -- σ(G) ⋖ σ(G)⊔σ(C_a). σ(G)⊔E ≤ σ(G)⊔σ(C_a). CovBy → σ(G)⊔E = σ(G)⊔σ(C_a).
    have hσG_ne_E : dilation_ext Γ c G ≠ Γ.E := fun h =>
      dilation_ext_not_m Γ hG_atom hc hc_on hc_ne_O hc_ne_U
        hG_plane hG_not_m hG_not_l hG_ne_O hG_ne_I hcI (h ▸ Γ.hE_on_m)
    have hσG_lt : dilation_ext Γ c G < dilation_ext Γ c G ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hσG_ne_E ((hσG_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have hσCa_atom := dilation_ext_atom Γ hCa_atom hc hc_on hc_ne_O hc_ne_U
      hCa_plane hCa_not_l hCa_ne_O hCa_ne_I hCa_not_m
    have hσGE_eq : dilation_ext Γ c G ⊔ Γ.E = dilation_ext Γ c G ⊔ dilation_ext Γ c C_a :=
      ((atom_covBy_join hσG_atom hσCa_atom hσG_ne_σCa).eq_or_eq hσG_lt.le
        (sup_le le_sup_left hE_le)).resolve_left (ne_of_gt hσG_lt)
    exact (hσGE_eq ▸ le_sup_right : dilation_ext Γ c C_a ≤ dilation_ext Γ c G ⊔ Γ.E).trans
      (sup_le hσcG_le_acE le_sup_right)
  -- ═══ Combine ═══
  have hLHS_atom : IsAtom (dilation_ext Γ c C_a) :=
    dilation_ext_atom Γ hCa_atom hc hc_on hc_ne_O hc_ne_U
      hCa_plane hCa_not_l hCa_ne_O hCa_ne_I hCa_not_m
  have hRHS_atom : IsAtom ((σ ⊔ Γ.U) ⊓ (ac ⊔ Γ.E)) := by
    -- ⊥ < meet: dilation_ext Γ c C_a is an atom ≤ (σ⊔U)⊓(ac⊔E)
    have hbot_lt : ⊥ < (σ ⊔ Γ.U) ⊓ (ac ⊔ Γ.E) :=
      lt_of_lt_of_le hLHS_atom.bot_lt (le_inf hPartA hPartB)
    -- meet < σ⊔U: if (σ⊔U)⊓(ac⊔E) = σ⊔U then σ⊔U ≤ ac⊔E, so l-directions match:
    -- (σ⊔U)⊓l = U and (ac⊔E)⊓l = ac, giving U = ac, U ≤ σ⊔d_a, contradiction.
    have hlt : (σ ⊔ Γ.U) ⊓ (ac ⊔ Γ.E) < σ ⊔ Γ.U := by
      apply lt_of_le_of_ne inf_le_left
      intro h
      -- h : (σ⊔U) ⊓ (ac⊔E) = σ⊔U → σ⊔U ≤ ac⊔E
      have hσU_le_acE : σ ⊔ Γ.U ≤ ac ⊔ Γ.E := h ▸ inf_le_right
      have hac_on' : ac ≤ l := show coord_mul Γ a c ≤ Γ.O ⊔ Γ.U from inf_le_right
      have hσUl : (σ ⊔ Γ.U) ⊓ l = Γ.U :=
        line_direction hσ_atom hσ_not_l (show Γ.U ≤ l from le_sup_right)
      have hacEl : (ac ⊔ Γ.E) ⊓ l = ac := by
        change (ac ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = ac
        rw [sup_comm ac Γ.E]
        exact line_direction Γ.hE_atom Γ.hE_not_l hac_on'
      have hU_eq_ac : Γ.U = ac := by
        have hU_le_ac : Γ.U ≤ ac :=
          hσUl ▸ inf_le_inf_right l hσU_le_acE |>.trans hacEl.le
        -- U ≤ ac ≤ l. CovBy U ⋖ l. ac = U or ac = l.
        -- If ac = l: l ≤ σ⊔d_a → σ∉l → σ⊔l ≤ σ⊔d_a → σ⊔l = π → σ⊔d_a = π → ✗ (same chain).
        have hU_covBy_l : Γ.U ⋖ l := by
          show Γ.U ⋖ Γ.O ⊔ Γ.U
          rw [sup_comm]; exact atom_covBy_join Γ.hU Γ.hO (Ne.symm Γ.hOU)
        exact ((hU_covBy_l.eq_or_eq hU_le_ac (show ac ≤ l from inf_le_right)).resolve_right (by
          intro hac_eq_l
          -- ac = l → l ≤ σ⊔d_a (since ac ≤ σ⊔d_a) → same contradiction chain
          have hl_le_σda : l ≤ σ ⊔ d_a := hac_eq_l ▸ (inf_le_left : ac ≤ σ ⊔ d_a)
          have hσ_le_σda : σ ≤ σ ⊔ d_a := le_sup_left
          have hl_lt_σl : l < σ ⊔ l := lt_of_le_of_ne le_sup_right
            (fun hh => hσ_not_l (le_sup_left.trans hh.symm.le))
          have hσl_eq_π : σ ⊔ l = π :=
            (hl_covBy.eq_or_eq hl_lt_σl.le (sup_le hσ_plane hl_covBy.le)).resolve_left
              (ne_of_gt hl_lt_σl)
          have hπ_le_σda : π ≤ σ ⊔ d_a := hσl_eq_π ▸ sup_le le_sup_left hl_le_σda
          have hσda_eq_π : σ ⊔ d_a = π := le_antisymm (sup_le hσ_plane hda_plane) hπ_le_σda
          have hσ_covBy' : σ ⋖ π := hσda_eq_π ▸ atom_covBy_join hσ_atom hda_atom hσ_ne_da
          have ⟨_, h2'⟩ := planes_meet_covBy hσ_covBy' hl_covBy
            (fun hh => hσ_not_l (hh.symm ▸ le_refl _))
          exact (((hσ_atom.le_iff.mp inf_le_left).resolve_right
            (fun hh => hσ_not_l (hh ▸ inf_le_right))) ▸ h2').2 Γ.hO.bot_lt
            (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)).symm
      -- U = ac ≤ σ⊔d_a. Contradiction via same argument as before.
      have hU_le_σda : Γ.U ≤ σ ⊔ d_a := hU_eq_ac ▸ (inf_le_left : ac ≤ σ ⊔ d_a)
      -- d_a⊔U = m → m ≤ σ⊔d_a → σ⊔m = π → σ⊔d_a = π → σ ⋖ π → ⊥ ⋖ l → O < l. ✗.
      have hda_ne_U' : d_a ≠ Γ.U := by
        intro hd
        have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := hd ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
        have haCl : (a ⊔ Γ.C) ⊓ l = a := by
          change (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = a
          rw [sup_comm a Γ.C]; exact line_direction Γ.hC Γ.hC_not_l ha_on
        exact ha_ne_U ((ha.le_iff.mp (le_inf hU_le_aC (show Γ.U ≤ l from le_sup_right)
          |>.trans haCl.le)).resolve_left Γ.hU.1).symm
      have hUV : Γ.U ≠ Γ.V := fun hh => Γ.hV_off (hh ▸ le_sup_right)
      have hdaU_eq_m : d_a ⊔ Γ.U = m := by
        have hda_lt : d_a < d_a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
          (fun h' => hda_ne_U' ((hda_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
            Γ.hU.1).symm)
        exact ((line_covers_its_atoms Γ.hU Γ.hV hUV hda_atom
          (inf_le_right : d_a ≤ m)).eq_or_eq hda_lt.le
          (sup_le (inf_le_right : d_a ≤ m) le_sup_left)).resolve_left (ne_of_gt hda_lt)
      have hm_le : m ≤ σ ⊔ d_a := hdaU_eq_m ▸ sup_le le_sup_right hU_le_σda
      have hσm_eq_π' : σ ⊔ m = π := by
        have hm_lt : m < σ ⊔ m := lt_of_le_of_ne le_sup_right
          (fun hh => hσ_not_m (le_sup_left.trans hh.symm.le))
        exact (Γ.m_covBy_π.eq_or_eq hm_lt.le (sup_le hσ_plane Γ.m_covBy_π.le)).resolve_left
          (ne_of_gt hm_lt)
      have hσda_eq_π : σ ⊔ d_a = π := le_antisymm (sup_le hσ_plane hda_plane)
        (hσm_eq_π' ▸ sup_le le_sup_left hm_le)
      have hσ_covBy : σ ⋖ π := hσda_eq_π ▸ atom_covBy_join hσ_atom hda_atom hσ_ne_da
      have ⟨_, h2⟩ := planes_meet_covBy hσ_covBy hl_covBy
        (fun hh => hσ_not_l (hh.symm ▸ le_refl _))
      exact (((hσ_atom.le_iff.mp inf_le_left).resolve_right
        (fun hh => hσ_not_l (hh ▸ inf_le_right))) ▸ h2).2 Γ.hO.bot_lt
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
    -- Use line_height_two on σ⊔U
    have hσ_ne_U' : σ ≠ Γ.U := fun h => hσ_not_m (show σ ≤ m from h ▸ le_sup_left)
    exact line_height_two hσ_atom Γ.hU hσ_ne_U' hbot_lt hlt
  exact (hRHS_atom.le_iff.mp (le_inf hPartA hPartB)).resolve_left hLHS_atom.1
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
  -- ═══ Setup ═══
  set l := Γ.O ⊔ Γ.U with hl_def
  set m := Γ.U ⊔ Γ.V with hm_def
  set q := Γ.U ⊔ Γ.C with hq_def
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ_def
  set s := coord_add Γ a b with hs_def
  set ac := coord_mul Γ a c with hac_def
  set bc := coord_mul Γ b c with hbc_def
  set sc := coord_mul Γ s c with hsc_def
  -- Key objects (β-images)
  set C_b := (Γ.U ⊔ Γ.C) ⊓ (b ⊔ Γ.E) with hCb_def  -- β(b)
  set C_s := (Γ.U ⊔ Γ.C) ⊓ (s ⊔ Γ.E) with hCs_def  -- β(s)
  set σ := dilation_ext Γ c Γ.C with hσ_def           -- dilation center
  set e_b := (Γ.O ⊔ C_b) ⊓ m with heb_def            -- direction O→C_b
  -- C_{bc} as parallelogram completion (to match key_identity format)
  set C_bc := parallelogram_completion Γ.O bc Γ.C m with hCbc_def  -- β(bc) = pc(O, bc, C, m)
  -- (We prove C_bc = q ⊓ (bc ⊔ E) later, after establishing infrastructure.)
  -- C'_{bc} and C'_{sc} from mul_key_identity
  -- dilation_ext maps C_b → C'_{bc} = (σ⊔U)⊓(bc⊔E)
  -- dilation_ext maps C_s → C'_{sc} = (σ⊔U)⊓(sc⊔E)
  -- ═══ The goal is: sc = coord_add Γ ac bc ═══
  -- Proof: Show β(sc) = β(ac+bc) on q, then recover via E-perspectivity.
  -- β(sc) = q ⊓ (sc⊔E). We show this equals pc(O, ac, C_bc, m),
  -- which equals β(ac+bc) by key_identity.
  -- The key step uses forward Desargues (center O) on
  --   T1=(C, a, C_s), T2=(σ, ac, C'_sc)
  -- to get (a⊔C_s)⊓m = (ac⊔C'_sc)⊓m, hence β(sc) on ac⊔e_b.
  -- ═══ Step 0: Basic infrastructure ═══
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hl_covBy : l ⋖ π := by
    rw [show l = Γ.O ⊔ Γ.U from rfl]; rw [show π = Γ.O ⊔ Γ.U ⊔ Γ.V from rfl]
    have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hIC : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  -- Atoms on l
  have hs_atom : IsAtom s := coord_add_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
  have hs_on : s ≤ l := by show coord_add Γ a b ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hac_atom : IsAtom ac := sorry -- coord_mul produces an atom (from non-degeneracy hyps)
  have hac_on : ac ≤ l := by show coord_mul Γ a c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hbc_atom : IsAtom bc := sorry -- coord_mul produces an atom
  have hbc_on : bc ≤ l := by show coord_mul Γ b c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hsc_atom : IsAtom sc := sorry -- coord_mul produces an atom
  have hsc_on : sc ≤ l := by show coord_mul Γ s c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hacbc_atom : IsAtom (coord_add Γ ac bc) := sorry -- coord_add produces an atom
  have hacbc_on : coord_add Γ ac bc ≤ l := by
    show coord_add Γ (coord_mul Γ a c) (coord_mul Γ b c) ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  -- β-images on q
  have hCb_atom : IsAtom C_b := beta_atom Γ hb hb_on hb_ne_O hb_ne_U
  have hCs_atom : IsAtom C_s := beta_atom Γ hs_atom hs_on hs_ne_O hs_ne_U
  have hCb_on_q : C_b ≤ q := inf_le_left
  have hCs_on_q : C_s ≤ q := inf_le_left
  have hCb_not_l : ¬ C_b ≤ l := beta_not_l Γ hb hb_on hb_ne_O hb_ne_U
  have hCs_not_l : ¬ C_s ≤ l := beta_not_l Γ hs_atom hs_on hs_ne_O hs_ne_U
  have hCb_plane : C_b ≤ π := beta_plane Γ hb_on
  have hCs_plane : C_s ≤ π := beta_plane Γ hs_on
  -- l ⊓ m = U, l ⊓ q = U, q ⊓ m = U
  have hlm_eq_U : l ⊓ m = Γ.U := by
    show (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
    rw [show Γ.O ⊔ Γ.U = Γ.U ⊔ Γ.O from sup_comm _ _,
        sup_inf_assoc_of_le Γ.O (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have : Γ.O ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hO_not_m (h ▸ inf_le_right))
    rw [this, sup_bot_eq]
  have hlq_eq_U : l ⊓ q = Γ.U := by
    rw [show l = Γ.O ⊔ Γ.U from rfl, show q = Γ.U ⊔ Γ.C from rfl]
    rw [show Γ.O ⊔ Γ.U = Γ.U ⊔ Γ.O from sup_comm _ _,
        sup_inf_assoc_of_le Γ.O (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.C)]
    have : Γ.O ⊓ (Γ.U ⊔ Γ.C) = ⊥ := by
      rcases Γ.hO.le_iff.mp inf_le_left with h | h
      · exact h
      · -- h : O⊓(U⊔C) = O → O ≤ U⊔C → O⊔U ≤ U⊔C → l ≤ q → C ≤ q = l (if l=q). ✗.
        exfalso
        have hO_le_UC : Γ.O ≤ Γ.U ⊔ Γ.C := h ▸ inf_le_right
        have hl_le_UC : Γ.O ⊔ Γ.U ≤ Γ.U ⊔ Γ.C := sup_le hO_le_UC le_sup_left
        -- l ≤ U⊔C ≤ π. l ⋖ π. So l = U⊔C or U⊔C = π.
        have hUC_le_π : Γ.U ⊔ Γ.C ≤ π :=
          sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane
        rcases hl_covBy.eq_or_eq hl_le_UC hUC_le_π with h1 | h2
        · exact Γ.hC_not_l ((le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C).trans h1.le)
        · -- U⊔C = π. m⊔C = π (since U ≤ m). m ⋖ π, so m⊔C ≤ π, and m ⋖ π.
          -- m_sup_C_eq_π: m ⊔ C = π. We already know this.
          -- l ≤ U⊔C = π. l ⋖ π. This is consistent.
          -- But: l = O⊔U ≤ U⊔C = π. CovBy gives l = U⊔C or U⊔C = π.
          -- We're in case U⊔C = π. So l ≤ π. Fine, but we need ⊥.
          -- Actually: O⊔U ≤ U⊔C. U ⋖ O⊔U (atom_covBy_join). U ≤ U⊔C.
          -- So O ≤ U⊔C. O is atom. U⊔C is the line q.
          -- U⊔C = π means q = π, which contradicts C being off l.
          -- No wait, let me use: O ≤ U⊔C and U⊔C = π means just O ≤ π, trivially true.
          -- The contradiction: U⊔C = π means C⊔V ≤ π = U⊔C, so V ≤ U⊔C.
          -- V ≤ U⊔C and V ≤ U⊔V = m. V ≤ (U⊔C)⊓m. (U⊔C)⊓m = U (by hqm below).
          -- But we haven't proven qm = U yet. Let's prove it here:
          -- (U⊔C)⊓(U⊔V) = U ⊔ C⊓(U⊔V) [modular, U ≤ U⊔V]
          -- C⊓(U⊔V) = ⊥ [C is atom, C ∉ m]. So = U.
          have hC_inf_m : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
            (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun hh => Γ.hC_not_m (hh ▸ inf_le_right))
          have hUCm : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
            rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V), hC_inf_m, sup_bot_eq]
          -- V ≤ U⊔C (since U⊔C = π and V ≤ π).
          have hV_le_UC : Γ.V ≤ Γ.U ⊔ Γ.C := (le_sup_right : Γ.V ≤ π).trans h2.symm.le
          -- V ≤ (U⊔C) ⊓ (U⊔V) = U.
          have hV_le_U : Γ.V ≤ Γ.U := le_inf hV_le_UC (le_sup_right : Γ.V ≤ Γ.U ⊔ Γ.V)
            |>.trans hUCm.le
          exact hUV ((Γ.hU.le_iff.mp hV_le_U).resolve_left Γ.hV.1).symm
    rw [this, sup_bot_eq]
  have hqm_eq_U : q ⊓ m = Γ.U := by
    rw [show q = Γ.U ⊔ Γ.C from rfl, show m = Γ.U ⊔ Γ.V from rfl]
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [this, sup_bot_eq]
  -- E facts
  have hE_inf_l : Γ.E ⊓ l = ⊥ :=
    (Γ.hE_atom.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hE_not_l (h ▸ inf_le_right))
  -- C_bc beta form: pc(O, bc, C, m) = q ⊓ (bc ⊔ E)
  have hObc_eq_l : Γ.O ⊔ bc = l := by
    have hO_lt : Γ.O < Γ.O ⊔ bc := lt_of_le_of_ne le_sup_left
      (fun h => hbc_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hbc_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hbc_on)).resolve_left (ne_of_gt hO_lt)
  have hCbc_eq_beta : C_bc = q ⊓ (bc ⊔ Γ.E) := by
    show parallelogram_completion Γ.O bc Γ.C m = q ⊓ (bc ⊔ Γ.E)
    show (Γ.C ⊔ (Γ.O ⊔ bc) ⊓ m) ⊓ (bc ⊔ (Γ.O ⊔ Γ.C) ⊓ m) = q ⊓ (bc ⊔ Γ.E)
    rw [hObc_eq_l, hlm_eq_U, show Γ.C ⊔ Γ.U = q from by
      rw [show q = Γ.U ⊔ Γ.C from rfl]; exact sup_comm _ _]
    rfl
  have hCbc_atom : IsAtom C_bc := hCbc_eq_beta ▸ beta_atom Γ hbc_atom hbc_on hbc_ne_O hbc_ne_U
  have hCbc_on_q : C_bc ≤ q := hCbc_eq_beta ▸ inf_le_left
  -- ═══ Helper: pc(O, x, C, m) = q ⊓ (x ⊔ E) when O⊔x = l ═══
  have pc_eq_beta : ∀ (x : L), Γ.O ⊔ x = l →
      parallelogram_completion Γ.O x Γ.C m = q ⊓ (x ⊔ Γ.E) := by
    intro x hOx_eq_l
    show (Γ.C ⊔ (Γ.O ⊔ x) ⊓ m) ⊓ (x ⊔ (Γ.O ⊔ Γ.C) ⊓ m) = q ⊓ (x ⊔ Γ.E)
    rw [hOx_eq_l, hlm_eq_U]
    rw [show Γ.C ⊔ Γ.U = q from by rw [show q = Γ.U ⊔ Γ.C from rfl]; exact sup_comm _ _]
    rfl
  -- O⊔x = l helpers
  have hOb_eq_l : Γ.O ⊔ b = l := by
    have hO_lt : Γ.O < Γ.O ⊔ b := lt_of_le_of_ne le_sup_left
      (fun h => hb_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hb.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hb_on)).resolve_left (ne_of_gt hO_lt)
  have hOs_eq_l : Γ.O ⊔ s = l := by
    have hO_lt : Γ.O < Γ.O ⊔ s := lt_of_le_of_ne le_sup_left
      (fun h => hs_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hs_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hs_on)).resolve_left (ne_of_gt hO_lt)
  -- C_b = pc(O, b, C, m) and C_s = pc(O, s, C, m)
  have hCb_eq_pc : C_b = parallelogram_completion Γ.O b Γ.C m := (pc_eq_beta b hOb_eq_l).symm
  have hCs_eq_pc : C_s = parallelogram_completion Γ.O s Γ.C m := (pc_eq_beta s hOs_eq_l).symm
  -- ═══ Step 1: key_identity — C_s = pc(O, a, C_b, m) ═══
  -- This says the β-image of a+b equals the translation of β(b) by a.
  have h_ki : parallelogram_completion Γ.O a C_b m = C_s := by
    rw [hCb_eq_pc, hCs_eq_pc]
    exact key_identity Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U hab R hR hR_not h_irred
  -- From key_identity: C_s = (C_b⊔U) ⊓ (a⊔e_b) where e_b = (O⊔C_b)⊓m
  -- So C_s ≤ a⊔e_b
  have hCs_le_a_eb : C_s ≤ a ⊔ e_b := by
    rw [← h_ki]; unfold parallelogram_completion
    simp only [show (Γ.O ⊔ a) ⊓ m = Γ.U from by
      rw [show (Γ.O ⊔ a) = l from by
        have : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
          (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
        exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq this.le
          (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt this)
      ]; exact hlm_eq_U]
    exact inf_le_right
  -- ═══ Step 2: mul_key_identity — σ_c(C_b) = C'_{bc}, σ_c(C_s) = C'_{sc} ═══
  set C'_bc := dilation_ext Γ c C_b with hC'bc_def
  set C'_sc := dilation_ext Γ c C_s with hC'sc_def
  -- mul_key_identity for b
  have h_mki_b : C'_bc = (σ ⊔ Γ.U) ⊓ (bc ⊔ Γ.E) :=
    dilation_mul_key_identity Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U R hR hR_not h_irred
  -- mul_key_identity for s
  have h_mki_s : C'_sc = (σ ⊔ Γ.U) ⊓ (sc ⊔ Γ.E) :=
    dilation_mul_key_identity Γ s c hs_atom hc hs_on hc_on hs_ne_O hc_ne_O hs_ne_U hc_ne_U R hR hR_not h_irred
  -- ═══ Step 3: Direction preservation via DPD on (C_b, C_s) ═══
  -- dilation_preserves_direction gives (C_b⊔C_s)⊓m = (C'_bc⊔C'_sc)⊓m
  -- But both C_b, C_s on q, so (C_b⊔C_s)⊓m ≤ q⊓m = U. Not useful directly.
  -- Instead, we use DPD on the pair (Γ.C, C_s) to get:
  -- (C⊔C_s)⊓m = (σ⊔C'_sc)⊓m, i.e., U = U (trivial since both ≤ q, σ⊔U).
  -- The KEY direction equation comes from DPD on (C_b, C_s)...
  -- Actually, the useful fact is from DPD on (C, a) — but a is on l.
  -- We use a DIFFERENT approach: direct Desargues.
  -- ═══ Step 3 (revised): Show β(sc) = pc(O, ac, C_bc, m) ═══
  -- β(sc) = C_sc := q ⊓ (sc ⊔ E). We need: C_sc = (C_bc ⊔ U) ⊓ (ac ⊔ e_bc)
  -- where e_bc = (O ⊔ C_bc) ⊓ m.
  set C_sc := q ⊓ (sc ⊔ Γ.E) with hCsc_def
  set e_bc := (Γ.O ⊔ C_bc) ⊓ m with hebc_def
  -- e_b direction: (O⊔C_b)⊓m
  have heb_atom : IsAtom e_b := by
    rw [show e_b = (Γ.O ⊔ C_b) ⊓ m from rfl]
    exact line_meets_m_at_atom Γ.hO hCb_atom (Ne.symm (fun h => hCb_not_l (h ▸ le_sup_left)))
      (sup_le (show Γ.O ≤ π from le_sup_left.trans le_sup_left) hCb_plane) hm_le_π Γ.m_covBy_π Γ.hO_not_m
  have hCbc_plane : C_bc ≤ π := hCbc_eq_beta ▸ beta_plane Γ hbc_on
  have hCbc_not_l : ¬ C_bc ≤ l := hCbc_eq_beta ▸ beta_not_l Γ hbc_atom hbc_on hbc_ne_O hbc_ne_U
  have hO_ne_Cbc : Γ.O ≠ C_bc := fun h => hCbc_not_l (h ▸ le_sup_left)
  have hebc_atom : IsAtom e_bc := by
    exact line_meets_m_at_atom Γ.hO hCbc_atom hO_ne_Cbc
      (sup_le (show Γ.O ≤ π from le_sup_left.trans le_sup_left) hCbc_plane) hm_le_π Γ.m_covBy_π Γ.hO_not_m
  -- pc(O, ac, C_bc, m) = (C_bc⊔U) ⊓ (ac⊔e_bc) since (O⊔ac)⊓m = U
  have hOac_eq_l : Γ.O ⊔ ac = l := by
    have hO_lt : Γ.O < Γ.O ⊔ ac := lt_of_le_of_ne le_sup_left
      (fun h => hac_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hac_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hac_on)).resolve_left (ne_of_gt hO_lt)
  have hpc_eq : parallelogram_completion Γ.O ac C_bc m =
      (C_bc ⊔ Γ.U) ⊓ (ac ⊔ e_bc) := by
    show (C_bc ⊔ (Γ.O ⊔ ac) ⊓ m) ⊓ (ac ⊔ (Γ.O ⊔ C_bc) ⊓ m) = (C_bc ⊔ Γ.U) ⊓ (ac ⊔ e_bc)
    rw [hOac_eq_l, hlm_eq_U]
  -- Since C_bc ≤ q and U ≤ q, C_bc⊔U = q (if C_bc ≠ U)
  have hCbc_ne_U : C_bc ≠ Γ.U := by
    intro h
    -- C_bc = U means q ⊓ (bc⊔E) = U. U ≤ bc⊔E. Since U ≤ q already.
    -- bc ≤ l, E ≤ m. (bc⊔E)⊓l = bc (by line_direction, E not on l, bc on l).
    -- U ≤ bc⊔E and U ≤ l → U ≤ (bc⊔E)⊓l = bc. U atom: U = bc or ⊥ = bc.
    -- bc atom, so bc = U. Contradicts hbc_ne_U.
    have hU_le_bcE : Γ.U ≤ bc ⊔ Γ.E := by
      rw [← h, hCbc_eq_beta]; exact inf_le_right
    have hbcEl : (bc ⊔ Γ.E) ⊓ l = bc := by
      change (bc ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = bc; rw [sup_comm bc Γ.E]
      exact line_direction Γ.hE_atom Γ.hE_not_l hbc_on
    have hU_le_bc : Γ.U ≤ bc := by
      have hU_le_inf : Γ.U ≤ (bc ⊔ Γ.E) ⊓ l :=
        le_inf hU_le_bcE (show Γ.U ≤ l from le_sup_right)
      exact hU_le_inf.trans hbcEl.le
    exact hbc_ne_U ((hbc_atom.le_iff.mp hU_le_bc).resolve_left Γ.hU.1).symm
  have hCbcU_eq_q : C_bc ⊔ Γ.U = q := by
    rw [sup_comm]
    have hCbc_le_q : C_bc ≤ q := hCbc_on_q
    -- U < U⊔C_bc since C_bc ≠ U
    have hCbc_lt : Γ.U < Γ.U ⊔ C_bc := by
      apply lt_of_le_of_ne le_sup_left
      intro h; apply hCbc_ne_U
      exact ((Γ.hU.le_iff.mp (le_sup_right.trans h.symm.le : C_bc ≤ Γ.U)).resolve_left
        hCbc_atom.1)
    rw [show q = Γ.U ⊔ Γ.C from rfl]
    exact ((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq hCbc_lt.le
      (sup_le le_sup_left hCbc_le_q)).resolve_left (ne_of_gt hCbc_lt)
  -- So pc(O, ac, C_bc, m) = q ⊓ (ac ⊔ e_bc)
  have hpc_eq' : parallelogram_completion Γ.O ac C_bc m = q ⊓ (ac ⊔ e_bc) := by
    rw [hpc_eq, hCbcU_eq_q]
  -- ═══ KEY STEP: Show C_sc = q ⊓ (ac ⊔ e_bc) ═══
  -- This is the core of distributivity. We show (sc⊔E)⊓q = (ac⊔e_bc)⊓q.
  -- Strategy: Use dilation_preserves_direction on (Γ.C, C_b) to get
  -- (C⊔C_b)⊓m = (σ⊔C'_bc)⊓m. Since C⊔C_b = q, this gives q⊓m = (σ⊔C'_bc)⊓m,
  -- i.e., U = (σ⊔C'_bc)⊓m. Then C'_bc ≤ σ⊔U means σ⊔C'_bc ≤ σ⊔U, and
  -- (σ⊔U)⊓m = U. This is trivially true.
  --
  -- Instead, consider the multiplication map: sc = (σ⊔D_s)⊓l where D_s = (s⊔C)⊓m.
  -- Similarly ac = (σ⊔D_a)⊓l, bc = (σ⊔D_b)⊓l where D_a = (a⊔C)⊓m, D_b = (b⊔C)⊓m.
  -- And s = a+b, so from key_identity: C_s = pc(O, a, C_b, m).
  --
  -- The equation β(sc) = q⊓(ac⊔e_bc) uses the interaction between
  -- the addition and multiplication constructions.
  -- We prove this via the following chain:
  --   C_sc = q⊓(sc⊔E)     [definition of β]
  --        = q⊓(ac⊔e_bc)   [core identity, proven via Desargues below]
  --
  -- CORE IDENTITY: (sc⊔E)⊓q = (ac⊔e_bc)⊓q
  -- Both sides are atoms on q. It suffices to show they're equal.
  -- Proof: apply desargues_planar with center O to triangles
  --   T1 = (Γ.C, a, C_s)  and  T2 = (σ, ac, C'_sc)
  -- where σ = dilation_ext Γ c C, C'_sc = dilation_ext Γ c C_s.
  -- Perspectivity from O:
  --   σ ≤ O⊔C (dilation_ext defn), ac ≤ O⊔a = l, C'_sc ≤ O⊔C_s (dilation_ext defn).
  -- Desargues gives: the three side-intersection points are collinear.
  -- Two of them are on m, so the axis is m, and the third gives
  --   (a⊔C_s) ⊓ (ac⊔C'_sc) ≤ m.
  -- Since C_s ≤ a⊔e_b, (a⊔C_s)⊓m ≤ (a⊔e_b)⊓m = e_b.
  -- So (ac⊔C'_sc)⊓m = e_b.
  -- Since C'_sc ≤ σ⊔U and C'_sc ≤ sc⊔E, C'_sc ≤ (σ⊔U)⊓(sc⊔E).
  -- And (ac⊔C'_sc)⊓m = e_b means C'_sc lies on ac⊔e_b.
  -- Similarly, C'_bc ≤ O⊔C_b, so O⊔C'_bc ≤ O⊔C_b, (O⊔C'_bc)⊓m ≤ (O⊔C_b)⊓m = e_b.
  -- With some work: e_bc = e_b.
  -- Then: q⊓(sc⊔E) has (sc⊔E)⊓m = ... and q⊓(ac⊔e_bc) has (ac⊔e_bc)⊓m = e_bc = e_b.
  -- Both atoms on q with the same m-direction must be equal.
  -- (This last step uses that q⊓m = U and the modular law.)
  --
  -- For now, sorry this core identity:
  have h_core : C_sc = q ⊓ (ac ⊔ e_bc) := by
    -- ═══ Proof outline ═══
    -- 1. Forward Desargues (center O, T1=(C,a,C_s), T2=(σ,ac,C'_sc))
    --    gives axis containing d_a and U on m, so axis = m.
    --    Third axis point: (a⊔C_s)⊓(ac⊔C'_sc) on m.
    --    Since (a⊔C_s)⊓m = e_b, we get e_b ≤ ac⊔C'_sc.
    -- 2. Hence C'_sc ≤ ac⊔e_b (since ac⊔C'_sc = ac⊔e_b as lines).
    -- 3. C'_sc = (σ⊔U)⊓(ac⊔e_b) = pc(O,ac,C'_bc,m).
    -- 4. well_defined + key_identity → pc(O,ac,C'_bc,m) = (σ⊔U)⊓((ac+bc)⊔E).
    -- 5. Combined with h_mki_s: (σ⊔U)⊓(sc⊔E) = (σ⊔U)⊓((ac+bc)⊔E).
    -- 6. E ∉ σ⊔U → perspectivity injectivity → sc = ac+bc.
    -- 7. C_sc = q⊓(sc⊔E) = q⊓((ac+bc)⊔E) = q⊓(ac⊔e_bc).
    -- ═══ Infrastructure for Desargues ═══
    -- σ = dilation_ext Γ c C properties
    have hσ_atom : IsAtom σ :=
      dilation_ext_atom Γ Γ.hC hc hc_on hc_ne_O hc_ne_U
        Γ.hC_plane Γ.hC_not_l (Ne.symm (fun h => Γ.hC_not_l (h ▸ le_sup_left)))
        (fun h => Γ.hC_not_l (h ▸ Γ.hI_on)) Γ.hC_not_m
    have hσ_on_OC : σ ≤ Γ.O ⊔ Γ.C := by
      show dilation_ext Γ c Γ.C ≤ Γ.O ⊔ Γ.C; unfold dilation_ext; exact inf_le_left
    have hσ_plane : σ ≤ π := dilation_ext_plane Γ Γ.hC hc hc_on Γ.hC_plane
    have hσ_not_m : ¬ σ ≤ m := by
      by_cases hcI : c = Γ.I
      · -- c = I: σ = C, and C ∉ m
        subst hcI; rw [show σ = Γ.C from dilation_ext_identity Γ Γ.hC Γ.hC_plane Γ.hC_not_l]
        exact Γ.hC_not_m
      · exact dilation_ext_not_m Γ Γ.hC hc hc_on hc_ne_O hc_ne_U
          Γ.hC_plane Γ.hC_not_m Γ.hC_not_l (Ne.symm (fun h => Γ.hC_not_l (h ▸ le_sup_left)))
          (fun h => Γ.hC_not_l (h ▸ Γ.hI_on)) hcI
    have hσ_not_l : ¬ σ ≤ l := by
      intro hσl
      -- σ ≤ l and σ ≤ O⊔C → σ ≤ l⊓(O⊔C) = O (modular) → σ = O → O ≤ c⊔E_I → c = O ✗
      sorry -- non-degeneracy: σ ∉ l
    -- C'_sc properties
    have hC'sc_atom : IsAtom C'_sc := sorry -- dilation_ext preserves atoms
    have hC'sc_plane : C'_sc ≤ π := dilation_ext_plane Γ hCs_atom hc hc_on hCs_plane
    have hC'sc_not_m : ¬ C'_sc ≤ m := sorry -- dilation_ext not on m
    have hC'sc_not_l : ¬ C'_sc ≤ l := sorry -- dilation_ext not on l
    -- C'_sc ≤ O⊔C_s (from dilation_ext definition)
    have hC'sc_le_OCs : C'_sc ≤ Γ.O ⊔ C_s := by
      show dilation_ext Γ c C_s ≤ Γ.O ⊔ C_s; unfold dilation_ext; exact inf_le_left
    -- C'_sc ≤ σ⊔U (from h_mki_s)
    have hC'sc_le_σU : C'_sc ≤ σ ⊔ Γ.U := h_mki_s ▸ inf_le_left
    -- C'_sc ≤ sc⊔E (from h_mki_s)
    have hC'sc_le_scE : C'_sc ≤ sc ⊔ Γ.E := h_mki_s ▸ inf_le_right
    -- C'_bc properties
    have hC'bc_atom : IsAtom C'_bc := sorry -- dilation_ext preserves atoms
    -- C'_bc ≤ O⊔C_b (from dilation_ext definition)
    have hC'bc_le_OCb : C'_bc ≤ Γ.O ⊔ C_b := by
      show dilation_ext Γ c C_b ≤ Γ.O ⊔ C_b; unfold dilation_ext; exact inf_le_left
    -- C'_bc ≤ σ⊔U (from h_mki_b)
    have hC'bc_le_σU : C'_bc ≤ σ ⊔ Γ.U := h_mki_b ▸ inf_le_left
    -- C'_bc ≤ bc⊔E (from h_mki_b)
    have hC'bc_le_bcE : C'_bc ≤ bc ⊔ Γ.E := h_mki_b ▸ inf_le_right
    -- ═══ Step 1: Forward Desargues — axis points on m ═══
    -- d_a = (a⊔C)⊓m = (σ⊔ac)⊓m (the common direction)
    have hd_a : (a ⊔ Γ.C) ⊓ m = (σ ⊔ ac) ⊓ m := by
      -- ac = (σ⊔d_a)⊓l where d_a = (a⊔C)⊓m, so σ⊔ac = σ⊔d_a.
      -- (σ⊔ac)⊓m = (σ⊔d_a)⊓m = d_a (line_direction, σ not on m).
      -- And (a⊔C)⊓m = d_a. So both sides equal d_a.
      sorry -- direction match: (a⊔C)⊓m = (σ⊔ac)⊓m
    -- Desargues application: center O, T1=(C, a, C_s), T2=(σ, ac, C'_sc)
    -- Perspectivity from O:
    --   σ ≤ O⊔C ✓ (hσ_on_OC)
    --   ac ≤ O⊔a = l ✓ (both on l)
    --   C'_sc ≤ O⊔C_s ✓ (hC'sc_le_OCs)
    -- Axis point 1: (C⊔a)⊓(σ⊔ac) ≤ m
    have haxis1_on_m : (Γ.C ⊔ a) ⊓ (σ ⊔ ac) ≤ m := by
      -- Both (C⊔a)⊓m and (σ⊔ac)⊓m equal d_a.
      -- So (C⊔a) and (σ⊔ac) both contain d_a.
      -- (C⊔a)⊓(σ⊔ac) ≥ d_a, and the intersection ≤ (C⊔a)⊓m = d_a (if C⊔a ≠ σ⊔ac).
      -- Result: (C⊔a)⊓(σ⊔ac) = d_a ≤ m.
      sorry -- axis point 1 on m
    -- Axis point 2: (C⊔C_s)⊓(σ⊔C'_sc) ≤ m
    have haxis2_on_m : (Γ.C ⊔ C_s) ⊓ (σ ⊔ C'_sc) ≤ m := by
      -- C⊔C_s = q (both on q, C ≠ C_s). q⊓m = U.
      -- σ⊔C'_sc ≤ σ⊔U (since C'_sc ≤ σ⊔U). And (σ⊔U)⊓m = U (line_direction).
      -- So both pass through U.
      -- (q)⊓(σ⊔C'_sc) ≥ U ≥ ⊥. The intersection ≤ q⊓m = U.
      -- Hence (C⊔C_s)⊓(σ⊔C'_sc) ≤ U ≤ m.
      have hCCs_eq_q : Γ.C ⊔ C_s = q := by
        rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C]
        have hCs_ne_C : C_s ≠ Γ.C := sorry -- C_s ≠ C (non-degeneracy)
        have hC_lt : Γ.C < Γ.C ⊔ C_s := lt_of_le_of_ne le_sup_left
          (fun h => hCs_ne_C (((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hCs_atom.1)))
        have hCs_on_q' : C_s ≤ Γ.C ⊔ Γ.U := by rw [sup_comm]; exact hCs_on_q
        exact ((atom_covBy_join Γ.hC Γ.hU (Ne.symm (fun h => Γ.hC_not_l (h ▸ le_sup_right)))).eq_or_eq
          hC_lt.le (sup_le le_sup_left hCs_on_q')).resolve_left (ne_of_gt hC_lt)
      -- Both sides pass through U. Show intersection ≤ U ≤ m.
      -- C⊔C_s = q, q⊓m = U.  σ⊔C'_sc ≤ σ⊔U, (σ⊔U)⊓m = U.
      -- q⊓(σ⊔U) = U (both lines pass through U, and q⊓(σ⊔U) ≤ q⊓m = U since σ⊔U,q distinct lines).
      -- (C⊔C_s)⊓(σ⊔C'_sc) ≤ q⊓(σ⊔U) = U ≤ m.
      sorry -- axis point 2 on m (both sides pass through U)
    -- ═══ Step 1b: Desargues gives third axis point on m ═══
    -- Apply desargues_planar: the three axis points are collinear on a common line.
    -- Two are on m (axis points 1 and 2), so the axis = m, and the third is on m too.
    have haxis3_on_m : (a ⊔ C_s) ⊓ (ac ⊔ C'_sc) ≤ m := by
      -- By desargues_planar with center O, T1=(C,a,C_s), T2=(σ,ac,C'_sc):
      -- ∃ axis, axis ≤ π ∧ axis ≠ π ∧ three points ≤ axis.
      -- Two of the points are on m (axis points 1 and 2), and both are atoms on m.
      -- So axis ≥ d_a and axis ≥ U. If d_a ≠ U: axis ≥ d_a⊔U = m (CovBy).
      -- axis ≤ π and axis ≠ π. m ≤ axis ≤ π, m ⋖ π: axis = m.
      -- Third point ≤ axis = m.
      sorry -- Desargues application: third axis point on m
    -- ═══ Step 1c: Extract direction equation ═══
    -- (a⊔C_s)⊓m = e_b (from hCs_le_a_eb: C_s ≤ a⊔e_b)
    have haCs_eq_aeb : a ⊔ C_s = a ⊔ e_b := by
      -- C_s ≤ a⊔e_b (hCs_le_a_eb). a ≤ a⊔e_b. So a⊔C_s ≤ a⊔e_b.
      -- a⊔C_s is a line (a ≠ C_s since a on l, C_s not on l). a⊔e_b is a line.
      -- CovBy: a⊔C_s ≤ a⊔e_b. a < a⊔C_s. So a⊔C_s = a⊔e_b.
      have ha_ne_Cs : a ≠ C_s := fun h => hCs_not_l (h ▸ ha_on)
      have ha_ne_eb : a ≠ e_b := by
        intro h; exact (fun hle => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on hle))
          (h ▸ inf_le_right : a ≤ m)
      have ha_lt : a < a ⊔ C_s := lt_of_le_of_ne le_sup_left
        (fun h => ha_ne_Cs ((ha.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hCs_atom.1).symm)
      have h_le : a ⊔ C_s ≤ a ⊔ e_b := sup_le le_sup_left hCs_le_a_eb
      exact ((atom_covBy_join ha heb_atom ha_ne_eb).eq_or_eq ha_lt.le h_le).resolve_left
        (ne_of_gt ha_lt)
    have haCs_dir : (a ⊔ C_s) ⊓ m = e_b := by
      rw [haCs_eq_aeb]
      have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
      exact line_direction ha ha_not_m (inf_le_right : e_b ≤ m)
    -- (ac⊔C'_sc)⊓m ≤ (a⊔C_s)⊓m = e_b (from axis point 3 on m)
    -- Since (a⊔C_s)⊓(ac⊔C'_sc) ≤ m:
    -- The intersection ≤ (a⊔C_s) ∩ m and ≤ (ac⊔C'_sc) ∩ m.
    -- So ≤ (a⊔C_s)⊓m = e_b. Also ≤ (ac⊔C'_sc)⊓m.
    -- The intersection is non-bot (from Desargues), so it's an atom on m.
    -- Being ≤ e_b (atom), it equals e_b. So e_b ≤ (ac⊔C'_sc).
    have heb_le_acC'sc : e_b ≤ ac ⊔ C'_sc := by
      -- (a⊔C_s)⊓(ac⊔C'_sc) is non-bot and ≤ (a⊔C_s)⊓m = e_b and ≤ ac⊔C'_sc.
      -- So e_b ≤ ac⊔C'_sc (since the intersection atom is e_b).
      sorry -- e_b ≤ ac⊔C'_sc (from Desargues axis + direction match)
    -- ═══ Step 2: C'_sc ≤ ac⊔e_b ═══
    have hC'sc_le_aceb : C'_sc ≤ ac ⊔ e_b := by
      -- e_b ≤ ac⊔C'_sc, so ac⊔e_b ≤ ac⊔C'_sc. Both are lines in π.
      -- ac ≠ C'_sc (ac on l, C'_sc not on l), so ac⊔C'_sc is a line.
      -- ac ≠ e_b (ac on l, e_b on m, ac ≠ U), so ac⊔e_b is a line.
      -- ac⊔e_b ≤ ac⊔C'_sc. CovBy: ac⊔e_b = ac⊔C'_sc. So C'_sc ≤ ac⊔e_b.
      have hac_ne_eb : ac ≠ e_b := by
        intro h; exact (fun hle => hac_ne_U (Γ.atom_on_both_eq_U hac_atom hac_on hle))
          (h ▸ inf_le_right : ac ≤ m)
      have hac_ne_C'sc : ac ≠ C'_sc := fun h => hC'sc_not_l (h ▸ hac_on)
      have hac_lt : ac < ac ⊔ e_b := lt_of_le_of_ne le_sup_left
        (fun h => hac_ne_eb ((hac_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          heb_atom.1).symm)
      have h_le : ac ⊔ e_b ≤ ac ⊔ C'_sc := sup_le le_sup_left heb_le_acC'sc
      have hac_lt' : ac < ac ⊔ C'_sc := lt_of_le_of_ne le_sup_left
        (fun h => hac_ne_C'sc ((hac_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hC'sc_atom.1).symm)
      have h_eq : ac ⊔ e_b = ac ⊔ C'_sc :=
        ((atom_covBy_join hac_atom hC'sc_atom hac_ne_C'sc).eq_or_eq hac_lt.le h_le).resolve_left
          (ne_of_gt hac_lt)
      exact h_eq ▸ le_sup_right
    -- ═══ Step 3: C'_sc = (σ⊔U) ⊓ (ac ⊔ e_b) ═══
    -- C'_sc ≤ σ⊔U and C'_sc ≤ ac⊔e_b. Both are atoms.
    -- (σ⊔U)⊓(ac⊔e_b) is an atom (two distinct lines in π meeting).
    -- C'_sc ≤ (σ⊔U)⊓(ac⊔e_b) → C'_sc = (σ⊔U)⊓(ac⊔e_b) (atom equality).
    have hC'sc_eq_meet : C'_sc = (σ ⊔ Γ.U) ⊓ (ac ⊔ e_b) := by
      have h_le : C'_sc ≤ (σ ⊔ Γ.U) ⊓ (ac ⊔ e_b) := le_inf hC'sc_le_σU hC'sc_le_aceb
      have h_meet_atom : IsAtom ((σ ⊔ Γ.U) ⊓ (ac ⊔ e_b)) := sorry -- meet of distinct lines is atom
      exact (h_meet_atom.le_iff.mp h_le).resolve_left hC'sc_atom.1
    -- ═══ Step 3b: This equals pc(O, ac, C'_bc, m) ═══
    -- pc(O, ac, C'_bc, m) = (C'_bc⊔(O⊔ac)⊓m) ⊓ (ac⊔(O⊔C'_bc)⊓m)
    --   = (C'_bc⊔U) ⊓ (ac⊔(O⊔C'_bc)⊓m)
    -- Now (O⊔C'_bc)⊓m = (O⊔C_b)⊓m = e_b (since O⊔C'_bc = O⊔C_b)
    -- And C'_bc⊔U = σ⊔U (since C'_bc ≤ σ⊔U, C'_bc ≠ U)
    -- So pc(O, ac, C'_bc, m) = (σ⊔U) ⊓ (ac ⊔ e_b) = C'_sc.
    have hOC'bc_eq_OCb : Γ.O ⊔ C'_bc = Γ.O ⊔ C_b := by
      -- C'_bc ≤ O⊔C_b (from dilation_ext definition).
      -- O ≠ C'_bc (C'_bc not on l, O on l). O⊔C'_bc is a line.
      -- O⊔C'_bc ≤ O⊔C_b. O < O⊔C'_bc. CovBy: O⊔C'_bc = O⊔C_b.
      have hO_ne_C'bc : Γ.O ≠ C'_bc := sorry -- O ≠ C'_bc (non-degeneracy)
      have hO_ne_Cb : Γ.O ≠ C_b := fun h => hCb_not_l (h ▸ le_sup_left)
      have hO_lt : Γ.O < Γ.O ⊔ C'_bc := lt_of_le_of_ne le_sup_left
        (fun h => hO_ne_C'bc ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hC'bc_atom.1).symm)
      exact ((atom_covBy_join Γ.hO hCb_atom hO_ne_Cb).eq_or_eq hO_lt.le
        (sup_le le_sup_left hC'bc_le_OCb)).resolve_left (ne_of_gt hO_lt)
    have heb_eq : (Γ.O ⊔ C'_bc) ⊓ m = e_b := by
      rw [hOC'bc_eq_OCb]
    have hC'bc_ne_U : C'_bc ≠ Γ.U := sorry -- C'_bc ≠ U (non-degeneracy)
    have hC'bcU_eq_σU : C'_bc ⊔ Γ.U = σ ⊔ Γ.U := by
      -- C'_bc ≤ σ⊔U. C'_bc ≠ U. So C'_bc⊔U: U < U⊔C'_bc. CovBy U ⋖ σ⊔U.
      -- U⊔C'_bc ≤ σ⊔U. CovBy gives U⊔C'_bc = σ⊔U.
      have hσ_ne_U : σ ≠ Γ.U := fun h => hσ_not_m (h ▸ le_sup_left)
      have hU_lt : Γ.U < Γ.U ⊔ C'_bc := lt_of_le_of_ne le_sup_left
        (fun h => hC'bc_ne_U (((Γ.hU.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hC'bc_atom.1)))
      rw [sup_comm C'_bc Γ.U, sup_comm σ Γ.U]
      exact ((atom_covBy_join Γ.hU hσ_atom (Ne.symm hσ_ne_U)).eq_or_eq hU_lt.le
        (sup_le le_sup_left (sup_comm Γ.U σ ▸ hC'bc_le_σU))).resolve_left (ne_of_gt hU_lt)
    -- ═══ Step 4: well_defined + key_identity computation ═══
    -- key_identity for (ac, bc): pc(O, ac, C_bc, m) = pc(O, ac+bc, C, m)
    have h_ki_mul_local : parallelogram_completion Γ.O ac C_bc m =
        parallelogram_completion Γ.O (coord_add Γ ac bc) Γ.C m :=
      key_identity Γ ac bc hac_atom hbc_atom hac_on hbc_on hac_ne_O hbc_ne_O
        hac_ne_U hbc_ne_U hac_ne_bc R hR hR_not h_irred
    -- pc(O, ac+bc, C, m) = q ⊓ ((ac+bc)⊔E)
    have hacbc_ne_O_local : coord_add Γ ac bc ≠ Γ.O := sorry -- non-degeneracy
    have hOacbc_eq_l_local : Γ.O ⊔ coord_add Γ ac bc = l := by
      have hO_lt : Γ.O < Γ.O ⊔ coord_add Γ ac bc := lt_of_le_of_ne le_sup_left
        (fun h => hacbc_ne_O_local ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hacbc_atom.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
        (sup_le le_sup_left hacbc_on)).resolve_left (ne_of_gt hO_lt)
    have hCacbc_eq_beta_local : parallelogram_completion Γ.O (coord_add Γ ac bc) Γ.C m =
        q ⊓ (coord_add Γ ac bc ⊔ Γ.E) := pc_eq_beta (coord_add Γ ac bc) hOacbc_eq_l_local
    -- So pc(O, ac, C_bc, m) = q ⊓ ((ac+bc)⊔E)
    have hpc_acbc : parallelogram_completion Γ.O ac C_bc m =
        q ⊓ (coord_add Γ ac bc ⊔ Γ.E) := by
      rw [h_ki_mul_local, hCacbc_eq_beta_local]
    -- pc(O, ac, C_bc, m) = q⊓(ac⊔e_bc) [hpc_eq']
    -- So q⊓(ac⊔e_bc) = q⊓((ac+bc)⊔E)
    have hq_eq : q ⊓ (ac ⊔ e_bc) = q ⊓ (coord_add Γ ac bc ⊔ Γ.E) := by
      rw [← hpc_eq', hpc_acbc]
    -- ═══ Step 5: well_defined → C'_sc = (σ⊔U)⊓((ac+bc)⊔E) ═══
    -- We showed C'_sc = (σ⊔U)⊓(ac⊔e_b) [hC'sc_eq_meet].
    -- We need: (σ⊔U)⊓(ac⊔e_b) = (σ⊔U)⊓((ac+bc)⊔E).
    -- Use parallelogram_completion_well_defined:
    --   pc(O, ac, C'_bc, m) = pc(C_bc, pc(O, ac, C_bc, m), C'_bc, m)
    -- LHS = (σ⊔U)⊓(ac⊔e_b) = C'_sc [step 3].
    -- RHS: d = (C_bc⊔pc(O,ac,C_bc,m))⊓m = q⊓m = U (both on q).
    --       e = (C_bc⊔C'_bc)⊓m = (bc⊔E)⊓m = E (both on bc⊔E, line_direction).
    --   = (C'_bc⊔U)⊓(pc(O,ac,C_bc,m)⊔E)
    --   = (σ⊔U)⊓(q⊓((ac+bc)⊔E)⊔E)
    --   = (σ⊔U)⊓((ac+bc)⊔E)  [since q⊓((ac+bc)⊔E)⊔E = (ac+bc)⊔E by recover-style argument]
    -- So C'_sc = (σ⊔U)⊓((ac+bc)⊔E).
    -- For now, sorry this step and focus on the consequence.
    have hC'sc_eq_acbc : C'_sc = (σ ⊔ Γ.U) ⊓ (coord_add Γ ac bc ⊔ Γ.E) := by
      sorry -- well_defined + computation: C'_sc = (σ⊔U)⊓((ac+bc)⊔E)
    -- ═══ Step 6: Perspectivity injectivity → sc = ac+bc ═══
    -- From h_mki_s: C'_sc = (σ⊔U) ⊓ (sc⊔E)
    -- From step 5: C'_sc = (σ⊔U) ⊓ ((ac+bc)⊔E)
    -- So (σ⊔U) ⊓ (sc⊔E) = (σ⊔U) ⊓ ((ac+bc)⊔E).
    -- E ∉ σ⊔U (since E on m, (σ⊔U)⊓m = U, and E ≠ U).
    -- Two lines through E (sc⊔E and (ac+bc)⊔E) meeting σ⊔U at the same atom.
    -- If the lines are distinct, the intersections with σ⊔U are distinct (since E ∉ σ⊔U).
    -- Contradiction. So sc⊔E = (ac+bc)⊔E. Hence sc = ac+bc.
    have hsc_eq_acbc : sc = coord_add Γ ac bc := by
      -- From the two expressions for C'_sc:
      have h_eq : (σ ⊔ Γ.U) ⊓ (sc ⊔ Γ.E) = (σ ⊔ Γ.U) ⊓ (coord_add Γ ac bc ⊔ Γ.E) := by
        rw [← h_mki_s, hC'sc_eq_acbc]
      -- E ∉ σ⊔U
      have hE_not_σU : ¬ Γ.E ≤ σ ⊔ Γ.U := by
        intro hle
        -- E ≤ σ⊔U and E ≤ m → E ≤ (σ⊔U)⊓m = U (by line_direction, σ∉m)
        have hσU_dir : (σ ⊔ Γ.U) ⊓ m = Γ.U :=
          line_direction hσ_atom hσ_not_m (le_sup_left : Γ.U ≤ m)
        have hE_le_U : Γ.E ≤ Γ.U := (le_inf hle Γ.hE_on_m).trans hσU_dir.le
        exact Γ.hEU ((Γ.hU.le_iff.mp hE_le_U).resolve_left Γ.hE_atom.1)
      -- If sc⊔E ≠ (ac+bc)⊔E: two different lines through E meet σ⊔U at same atom.
      -- But E ∉ σ⊔U, so the two lines through E can't meet σ⊔U at the same point
      -- (by modular_intersection or direct argument).
      by_contra hne
      -- sc ≠ ac+bc. sc⊔E and (ac+bc)⊔E are different lines through E.
      have h_lines_ne : sc ⊔ Γ.E ≠ coord_add Γ ac bc ⊔ Γ.E := by
        intro heq
        -- (sc⊔E)⊓l = sc and ((ac+bc)⊔E)⊓l = ac+bc
        have hsc_l : (sc ⊔ Γ.E) ⊓ l = sc := by
          change (sc ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = sc; rw [sup_comm sc Γ.E]
          exact line_direction Γ.hE_atom Γ.hE_not_l hsc_on
        have hacbc_l : (coord_add Γ ac bc ⊔ Γ.E) ⊓ l = coord_add Γ ac bc := by
          change (coord_add Γ ac bc ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = coord_add Γ ac bc
          rw [sup_comm (coord_add Γ ac bc) Γ.E]
          exact line_direction Γ.hE_atom Γ.hE_not_l hacbc_on
        exact hne (hsc_l.symm.trans (heq ▸ hacbc_l))
      -- Two distinct lines through E meet σ⊔U at C'_sc. Since E ∉ σ⊔U,
      -- the intersection of the two lines is E. But C'_sc ≤ both lines and C'_sc ≠ E.
      -- C'_sc ≤ sc⊔E and C'_sc ≤ (ac+bc)⊔E → C'_sc ≤ (sc⊔E)⊓((ac+bc)⊔E).
      -- The intersection of two distinct lines in a plane is an atom.
      -- (sc⊔E)⊓((ac+bc)⊔E) ≥ E (E on both). If the intersection is a line,
      -- the lines are equal. ✗ So intersection is an atom. Being ≥ E: = E.
      -- So C'_sc ≤ E. C'_sc atom: C'_sc = E. But E on m and C'_sc ∉ m. ✗.
      have hC'sc_le_both : C'_sc ≤ (sc ⊔ Γ.E) ⊓ (coord_add Γ ac bc ⊔ Γ.E) :=
        le_inf hC'sc_le_scE (hC'sc_eq_acbc ▸ inf_le_right)
      -- (sc⊔E) ⊓ ((ac+bc)⊔E) is an atom or ⊥. Both lines contain E, so ≥ E.
      -- So intersection ≥ E. If intersection is a line (= sc⊔E = (ac+bc)⊔E), contradiction.
      -- So intersection is E.
      have h_meet_eq_E : (sc ⊔ Γ.E) ⊓ (coord_add Γ ac bc ⊔ Γ.E) = Γ.E := by
        sorry -- meet of two distinct lines through E equals E
      -- C'_sc ≤ E → C'_sc = E → C'_sc on m. Contradiction.
      have hC'sc_le_E : C'_sc ≤ Γ.E := hC'sc_le_both.trans h_meet_eq_E.le
      exact hC'sc_not_m ((Γ.hE_atom.le_iff.mp hC'sc_le_E).resolve_left hC'sc_atom.1 ▸ Γ.hE_on_m)
    -- ═══ Step 7: Conclude ═══
    -- C_sc = q⊓(sc⊔E) and sc = ac+bc, so C_sc = q⊓((ac+bc)⊔E) = q⊓(ac⊔e_bc).
    show C_sc = q ⊓ (ac ⊔ e_bc)
    rw [show C_sc = q ⊓ (sc ⊔ Γ.E) from rfl, hsc_eq_acbc, ← hq_eq]
  -- ═══ Step 4: key_identity for (ac, bc) ═══
  -- key_identity: pc(O, ac, C_bc, m) = pc(O, coord_add ac bc, C, m)
  -- where C_bc = pc(O, bc, C, m) by definition.
  have h_ki_mul : parallelogram_completion Γ.O ac C_bc m =
      parallelogram_completion Γ.O (coord_add Γ ac bc) Γ.C m :=
    key_identity Γ ac bc hac_atom hbc_atom hac_on hbc_on hac_ne_O hbc_ne_O
      hac_ne_U hbc_ne_U hac_ne_bc R hR hR_not h_irred
  -- ═══ Helper: pc(O, x, C, m) = q ⊓ (x ⊔ E) when O⊔x = l ═══
  have pc_eq_beta : ∀ (x : L), Γ.O ⊔ x = l →
      parallelogram_completion Γ.O x Γ.C m = q ⊓ (x ⊔ Γ.E) := by
    intro x hOx_eq_l
    unfold parallelogram_completion
    -- Goal after unfold: (have d := (O⊔x)⊓m; have e := (O⊔C)⊓m; (C⊔d)⊓(x⊔e)) = q⊓(x⊔E)
    -- (O⊔x)⊓m = l⊓m = U (since O⊔x = l).
    -- (O⊔C)⊓m = E (by definition of E).
    -- (C⊔U) = q (since q = U⊔C, by sup_comm).
    show (Γ.C ⊔ (Γ.O ⊔ x) ⊓ m) ⊓ (x ⊔ (Γ.O ⊔ Γ.C) ⊓ m) = q ⊓ (x ⊔ Γ.E)
    rw [hOx_eq_l, hlm_eq_U]
    rw [show Γ.C ⊔ Γ.U = q from by rw [show q = Γ.U ⊔ Γ.C from rfl]; exact sup_comm _ _]
    rfl
  -- C_bc as β: C_bc = q ⊓ (bc ⊔ E)
  have hObc_eq_l : Γ.O ⊔ bc = l := by
    have hO_lt : Γ.O < Γ.O ⊔ bc := lt_of_le_of_ne le_sup_left
      (fun h => hbc_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hbc_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hbc_on)).resolve_left (ne_of_gt hO_lt)
  have hCbc_eq_beta : C_bc = q ⊓ (bc ⊔ Γ.E) := pc_eq_beta bc hObc_eq_l
  -- C_{ac+bc} as β
  have hacbc_ne_O : coord_add Γ ac bc ≠ Γ.O := sorry -- non-degeneracy
  have hacbc_ne_U : coord_add Γ ac bc ≠ Γ.U := sorry -- non-degeneracy
  have hOacbc_eq_l : Γ.O ⊔ coord_add Γ ac bc = l := by
    have hO_lt : Γ.O < Γ.O ⊔ coord_add Γ ac bc := lt_of_le_of_ne le_sup_left
      (fun h => hacbc_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hacbc_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hacbc_on)).resolve_left (ne_of_gt hO_lt)
  have hCacbc_eq_beta : parallelogram_completion Γ.O (coord_add Γ ac bc) Γ.C m =
      q ⊓ (coord_add Γ ac bc ⊔ Γ.E) := pc_eq_beta (coord_add Γ ac bc) hOacbc_eq_l
  -- ═══ Step 5: Combine — β(sc) = β(ac+bc) ═══
  have h_beta_eq : C_sc = q ⊓ (coord_add Γ ac bc ⊔ Γ.E) := by
    rw [h_core, ← hpc_eq', h_ki_mul, hCacbc_eq_beta]
  -- ═══ Step 6: Recover via E-perspectivity — sc = ac+bc ═══
  -- Recovery lemma: (β(x) ⊔ E) ⊓ l = x for any atom x on l with x ≠ O, x ≠ U
  have recover : ∀ (x : L), IsAtom x → x ≤ l → x ≠ Γ.O → x ≠ Γ.U →
      (q ⊓ (x ⊔ Γ.E) ⊔ Γ.E) ⊓ l = x := by
    intro x hx hx_l hx_ne_O hx_ne_U
    -- β(x) = q ⊓ (x⊔E). Show (β(x)⊔E)⊓l = x.
    -- β(x) ≤ x⊔E (inf_le_right). So β(x)⊔E ≤ x⊔E.
    -- Also x ≤ β(x)⊔E (from x ≤ π = q⊔E, and x ≤ x⊔E, modular law).
    -- So β(x)⊔E = x⊔E. Then (x⊔E)⊓l = x by modular law (E⊓l = ⊥).
    have hbx_le_xE : q ⊓ (x ⊔ Γ.E) ⊔ Γ.E ≤ x ⊔ Γ.E :=
      sup_le (inf_le_right) le_sup_right
    have hxE_le_bxE : x ⊔ Γ.E ≤ q ⊓ (x ⊔ Γ.E) ⊔ Γ.E := by
      -- By modular law: (q⊓(x⊔E))⊔E = (q⊔E) ⊓ (x⊔E) [since E ≤ x⊔E]
      -- q⊔E = π, x⊔E ≤ π, so RHS = x⊔E. Hence x⊔E ≤ (q⊓(x⊔E))⊔E.
      have hqE_eq_π : q ⊔ Γ.E = π := by
        have hE_not_q : ¬ Γ.E ≤ q := fun hle =>
          Γ.hEU ((Γ.hU.le_iff.mp (hqm_eq_U ▸ le_inf hle Γ.hE_on_m)).resolve_left Γ.hE_atom.1)
        have hq_covBy_π : q ⋖ π := by
          have h_inf : m ⊓ q ⋖ m := by
            rw [inf_comm, hqm_eq_U]
            exact atom_covBy_join Γ.hU Γ.hV hUV
          have hmq : m ⊔ q = π := by
            have : m ⊔ q = m ⊔ Γ.C := by
              show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
              rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
            rw [this]
            exact (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
              (sup_le hm_le_π Γ.hC_plane)).resolve_left
              (ne_of_gt (lt_of_le_of_ne le_sup_left
                (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
          exact hmq ▸ covBy_sup_of_inf_covBy_left h_inf
        have hq_lt : q < q ⊔ Γ.E := lt_of_le_of_ne le_sup_left
          (fun h => hE_not_q (le_sup_right.trans h.symm.le))
        exact (hq_covBy_π.eq_or_eq hq_lt.le
          (sup_le (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
            (Γ.hE_on_m.trans hm_le_π))).resolve_left (ne_of_gt hq_lt)
      -- x⊔E ≤ π (since x ≤ l ≤ π and E ≤ m ≤ π)
      have hxE_le_π : x ⊔ Γ.E ≤ π := sup_le (hx_l.trans le_sup_left) (Γ.hE_on_m.trans hm_le_π)
      -- (q⊓(x⊔E))⊔E = (E⊔q)⊓(x⊔E) by modular law (E ≤ x⊔E)
      -- sup_inf_assoc_of_le: a ≤ c → (a⊔b)⊓c = a ⊔ b⊓c
      -- With a=E, b=q, c=x⊔E: (E⊔q)⊓(x⊔E) = E ⊔ q⊓(x⊔E)
      -- So E ⊔ q⊓(x⊔E) = (E⊔q)⊓(x⊔E) = (q⊔E)⊓(x⊔E) = π⊓(x⊔E) = x⊔E
      have h_mod : Γ.E ⊔ q ⊓ (x ⊔ Γ.E) = (Γ.E ⊔ q) ⊓ (x ⊔ Γ.E) :=
        (sup_inf_assoc_of_le q (le_sup_right : Γ.E ≤ x ⊔ Γ.E)).symm
      rw [sup_comm (q ⊓ (x ⊔ Γ.E)) Γ.E, h_mod, sup_comm Γ.E q, hqE_eq_π]
      exact le_inf hxE_le_π (le_refl _)
    have h_eq : q ⊓ (x ⊔ Γ.E) ⊔ Γ.E = x ⊔ Γ.E := le_antisymm hbx_le_xE hxE_le_bxE
    rw [h_eq, sup_inf_assoc_of_le Γ.E hx_l, hE_inf_l, sup_bot_eq]
  have hsc_ne_O : sc ≠ Γ.O := sorry -- sc = coord_mul s c ≠ O (non-degeneracy)
  have hsc_ne_U : sc ≠ Γ.U := sorry -- sc ≠ U (non-degeneracy)
  -- Final calc using beta-injectivity (recover pattern)
  calc sc
      = (q ⊓ (sc ⊔ Γ.E) ⊔ Γ.E) ⊓ l := (recover sc hsc_atom hsc_on hsc_ne_O hsc_ne_U).symm
    _ = (q ⊓ (coord_add Γ ac bc ⊔ Γ.E) ⊔ Γ.E) ⊓ l := by
        show (C_sc ⊔ Γ.E) ⊓ l = (q ⊓ (coord_add Γ ac bc ⊔ Γ.E) ⊔ Γ.E) ⊓ l
        rw [h_beta_eq]
    _ = coord_add Γ ac bc := recover (coord_add Γ ac bc) hacbc_atom hacbc_on hacbc_ne_O hacbc_ne_U
end Foam.FTPGExplore
