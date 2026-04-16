/-
# Dilation extension and direction preservation (Part VII-A)
The dilation σ_c extended to off-line points:
  dilation_ext Γ c P = (O⊔P) ⊓ (c ⊔ ((I⊔P)⊓m))
## Contents
- `dilation_ext` definition
- Helper lemmas: lines_ne, atom, plane, not_m, ne_c, ne_P, parallelism, directions_ne
- `dilation_ext_C`: dilation of C is σ
- `dilation_preserves_direction`: (P⊔Q)⊓m = (σ_c(P)⊔σ_c(Q))⊓m
  3 cases: c=I identity, collinear, generic forward Desargues center O
- `dilation_ext_identity`: σ_I(P) = P
- `dilation_ext_fixes_m`: σ_a fixes points on m (P ≤ m, P ∉ l → σ_a(P) = P)
## Status
ALL PROVEN, 0 sorry.
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
    (_hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V) :
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
    {P c : L} (_hP : IsAtom P) (_hc : IsAtom c)
    (_hc_on : c ≤ Γ.O ⊔ Γ.U) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
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
    (_hσP_atom : IsAtom (dilation_ext Γ c P)) :
    dilation_ext Γ c P ≠ c := by
  intro h; apply hc_ne_O
  have hc_le_OP : c ≤ Γ.O ⊔ P := h ▸ (inf_le_left : dilation_ext Γ c P ≤ Γ.O ⊔ P)
  exact ((Γ.hO.le_iff.mp (le_inf hc_on hc_le_OP |>.trans
    (modular_intersection Γ.hO Γ.hU hP Γ.hOU (Ne.symm hP_ne_O)
      (fun h => hP_not_l (h ▸ le_sup_right)) hP_not_l).le)).resolve_left hc.1)
/-- σ_c(P) ≠ P when c ≠ I, P ∉ l. -/
theorem dilation_ext_ne_P (Γ : CoordSystem L)
    {P c : L} (hP : IsAtom P) (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (_hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (_hP_ne_O : P ≠ Γ.O)
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
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (_hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (_hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (_hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (_hP_ne_O : P ≠ Γ.O)
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
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (_hQ_plane : Q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (_hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
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
    (c : L) (_hc : IsAtom c) (_hc_on : c ≤ Γ.O ⊔ Γ.U)
    (_hc_ne_O : c ≠ Γ.O) (_hc_ne_U : c ≠ Γ.U) :
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

/-! ## Dilation fixes m pointwise -/

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

end Foam.FTPGExplore
