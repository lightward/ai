/-
# Coordinatization — von Staudt addition and its algebraic properties

Builds coordinates on a projective line from the incidence geometry
and Desargues' theorem proven in FTPGExplore.lean.

## What's here

1. CoordSystem: the data for von Staudt's construction
2. two_persp: the shared two-perspectivity composition pattern
3. coord_add: addition via perspectivities (bridge: m, zero: E)
4. Ring axioms: identity (commutativity split to FTPGAddComm.lean)

## two_persp

Both coord_add and coord_mul (FTPGMul.lean) factor through two_persp,
the composition of two perspectivity intersections projected onto l.
The bridge parameter is the only free variable:

  coord_add a b = two_persp Γ (a⊔C) m (b⊔E) q       -- bridge: m
  coord_mul a b = two_persp Γ (O⊔C) (b⊔E_I) (a⊔C) m -- bridge: O⊔C

Both equalities hold by rfl (definitional). This is the concrete
instantiation of composed analogy (derivations/analogy.md).
-/

import Foam.FTPGExplore

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

-- § Coordinate system

/-- A coordinate system for the von Staudt construction.

    Fixed data:
    - Line l = O ⊔ U (the "coordinate line")
    - Atom I on l (the "unit"), distinct from O and U
    - Atom V off l (determines auxiliary line m = U ⊔ V)
    - Atom C off both l and m, in the plane (the "standard center")

    From this we derive:
    - E = (O ⊔ C) ⊓ m (the "zero" on m, projection of O via C)
    - Addition: a + b uses C for l→m and a third point on b ⊔ E for m→l
    - Multiplication: uses perspectivities fixing O and U -/
structure CoordSystem (L : Type u) [Lattice L] [BoundedOrder L]
    [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] where
  O : L
  U : L
  I : L
  V : L
  C : L
  hO : IsAtom O
  hU : IsAtom U
  hI : IsAtom I
  hV : IsAtom V
  hC : IsAtom C
  hOU : O ≠ U
  hOI : O ≠ I
  hUI : U ≠ I
  hI_on : I ≤ O ⊔ U          -- I is on the coordinate line
  hV_off : ¬ V ≤ O ⊔ U       -- V is not on l
  hC_not_l : ¬ C ≤ O ⊔ U     -- C is not on l
  hC_not_m : ¬ C ≤ U ⊔ V     -- C is not on m
  hC_plane : C ≤ O ⊔ U ⊔ V   -- C is in the plane

variable (Γ : CoordSystem L)

/-- The coordinate line. -/
def CoordSystem.l : L := Γ.O ⊔ Γ.U

/-- The auxiliary line through U. -/
def CoordSystem.m : L := Γ.U ⊔ Γ.V

/-- The plane of the coordinate system. -/
def CoordSystem.π : L := Γ.O ⊔ Γ.U ⊔ Γ.V

/-- U is on both lines (the intersection point). -/
theorem CoordSystem.hU_on_l : Γ.U ≤ Γ.l :=
  le_sup_right

theorem CoordSystem.hU_on_m : Γ.U ≤ Γ.m :=
  le_sup_left

/-- E: the projection of O onto m via center C. This is the "zero" on m. -/
noncomputable def CoordSystem.E : L := (Γ.O ⊔ Γ.C) ⊓ Γ.m

/-- O is not on m (= U ⊔ V). -/
theorem CoordSystem.hO_not_m : ¬ Γ.O ≤ Γ.U ⊔ Γ.V := by
  intro hle
  apply Γ.hV_off
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have h_cov := line_covers_its_atoms Γ.hU Γ.hV hUV Γ.hO hle
  have h_cov_l := atom_covBy_join Γ.hO Γ.hU Γ.hOU
  exact (h_cov.eq_or_eq h_cov_l.lt.le (sup_le hle le_sup_left)).resolve_left
    (ne_of_gt h_cov_l.lt) ▸ le_sup_right

/-- m ⋖ π: the auxiliary line is covered by the plane. -/
theorem CoordSystem.m_covBy_π : (Γ.U ⊔ Γ.V) ⋖ (Γ.O ⊔ Γ.U ⊔ Γ.V) := by
  have h_meet : Γ.O ⊓ (Γ.U ⊔ Γ.V) = ⊥ := by
    rcases Γ.hO.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) Γ.hO_not_m
  have := covBy_sup_of_inf_covBy_left (h_meet ▸ Γ.hO.bot_covBy)
  rwa [show Γ.O ⊔ (Γ.U ⊔ Γ.V) = Γ.O ⊔ Γ.U ⊔ Γ.V from (sup_assoc _ _ _).symm] at this

/-- m ⊔ C = π: C is off m, in the plane, so generates the whole plane with m. -/
theorem CoordSystem.m_sup_C_eq_π : (Γ.U ⊔ Γ.V) ⊔ Γ.C = Γ.O ⊔ Γ.U ⊔ Γ.V := by
  have h_lt : Γ.U ⊔ Γ.V < (Γ.U ⊔ Γ.V) ⊔ Γ.C := lt_of_le_of_ne le_sup_left
    (fun h => Γ.hC_not_m (h ▸ le_sup_right))
  have h_le : (Γ.U ⊔ Γ.V) ⊔ Γ.C ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right) Γ.hC_plane
  exact (Γ.m_covBy_π.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)

/-- E is an atom on m. -/
theorem CoordSystem.hE_atom : IsAtom Γ.E := by
  unfold CoordSystem.E CoordSystem.m
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have h_in_plane : Γ.O ⊔ Γ.C ≤ (Γ.U ⊔ Γ.V) ⊔ Γ.C := by
    have h := Γ.m_sup_C_eq_π
    rw [h]
    exact sup_le (le_sup_of_le_left le_sup_left) Γ.hC_plane
  exact perspect_atom Γ.hC Γ.hO hOC Γ.hU Γ.hV hUV Γ.hC_not_m h_in_plane

variable {Γ}

-- § Addition via perspectivities

/-- E is not equal to U (since E ≤ O ⊔ C line and U is not, unless U = E
    which would force C on m). -/
theorem CoordSystem.hEU : Γ.E ≠ Γ.U := by
  unfold CoordSystem.E CoordSystem.m
  intro h
  -- E = U means (O ⊔ C) ⊓ (U ⊔ V) = U
  -- So U ≤ O ⊔ C. Then O ⊔ C ≥ O and O ⊔ C ≥ U, so O ⊔ C ≥ O ⊔ U = l.
  -- But C ≤ O ⊔ C and O ⊔ C is a line (join of two atoms O ≠ C).
  -- If O ⊔ U ≤ O ⊔ C, then by covering (O ⋖ O ⊔ U and O ⋖ O ⊔ C):
  -- O ⊔ U = O ⊔ C. Then C ≤ O ⊔ U = l, contradicting hC_not_l.
  have hU_le : Γ.U ≤ Γ.O ⊔ Γ.C := h ▸ inf_le_left
  have hOC : Γ.O ≠ Γ.C := fun heq => Γ.hC_not_l (heq ▸ le_sup_left)
  have h_cov_OC := atom_covBy_join Γ.hO Γ.hC hOC
  have h_cov_OU := atom_covBy_join Γ.hO Γ.hU Γ.hOU
  have h_le : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left hU_le
  exact Γ.hC_not_l ((h_cov_OC.eq_or_eq h_cov_OU.lt.le h_le).resolve_left
    (ne_of_gt h_cov_OU.lt) ▸ le_sup_right)

/-- l ⊓ m = U: the coordinate line meets the auxiliary line at U. -/
theorem CoordSystem.l_inf_m_eq_U : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
  rw [sup_comm Γ.O Γ.U]
  -- modular_intersection with a=U, b=O, c=V gives (U⊔O) ⊓ (U⊔V) = U
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hOV : Γ.O ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_left)
  have hV_not : ¬ Γ.V ≤ Γ.U ⊔ Γ.O := by
    intro h; exact Γ.hV_off (le_trans h (by rw [sup_comm]))
  exact modular_intersection Γ.hU Γ.hO Γ.hV Γ.hOU.symm hUV hOV hV_not

/-- An atom on l that's also on m must be U. -/
theorem CoordSystem.atom_on_both_eq_U {p : L} (hp : IsAtom p)
    (hp_l : p ≤ Γ.O ⊔ Γ.U) (hp_m : p ≤ Γ.U ⊔ Γ.V) : p = Γ.U := by
  have hp_le : p ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) := le_inf hp_l hp_m
  rw [Γ.l_inf_m_eq_U] at hp_le
  exact (Γ.hU.le_iff.mp hp_le).resolve_left hp.1

/-- E is on m. -/
theorem CoordSystem.hE_on_m : Γ.E ≤ Γ.U ⊔ Γ.V := by
  unfold CoordSystem.E CoordSystem.m; exact inf_le_right

/-- E is not on the coordinate line l. -/
theorem CoordSystem.hE_not_l : ¬ Γ.E ≤ Γ.O ⊔ Γ.U :=
  fun hE_l => absurd (Γ.atom_on_both_eq_U Γ.hE_atom hE_l CoordSystem.hE_on_m)
    CoordSystem.hEU

/-- O ≠ E (O is not on m, but E is). -/
theorem CoordSystem.hOE : Γ.O ≠ Γ.E :=
  fun h => Γ.hO_not_m (h ▸ CoordSystem.hE_on_m)

/-- E ≤ O ⊔ C (E is on the line through O and C). -/
theorem CoordSystem.hE_le_OC : Γ.E ≤ Γ.O ⊔ Γ.C := by
  unfold CoordSystem.E CoordSystem.m; exact inf_le_left

/-- O ⊔ E = O ⊔ C: E is on line O ⊔ C and E ≠ O, so they span the same line. -/
theorem CoordSystem.OE_eq_OC : Γ.O ⊔ Γ.E = Γ.O ⊔ Γ.C := by
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have h_le : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left CoordSystem.hE_le_OC
  exact ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
    (atom_covBy_join Γ.hO Γ.hE_atom CoordSystem.hOE).lt.le h_le).resolve_left
    (ne_of_gt (atom_covBy_join Γ.hO Γ.hE_atom CoordSystem.hOE).lt)

/-- E ⊔ U = m: E and U are distinct atoms on m, generating it. -/
theorem CoordSystem.EU_eq_m : Γ.E ⊔ Γ.U = Γ.U ⊔ Γ.V := by
  rw [sup_comm Γ.E Γ.U]
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have h_le : Γ.U ⊔ Γ.E ≤ Γ.U ⊔ Γ.V := sup_le le_sup_left CoordSystem.hE_on_m
  have h_lt : Γ.U < Γ.U ⊔ Γ.E := by
    apply lt_of_le_of_ne le_sup_left; intro h
    have : Γ.E ≤ Γ.U := h ▸ le_sup_right
    exact absurd ((Γ.hU.le_iff.mp this).resolve_left Γ.hE_atom.1) CoordSystem.hEU
  exact ((atom_covBy_join Γ.hU Γ.hV hUV).eq_or_eq h_lt.le h_le).resolve_left
    (ne_of_gt h_lt)

/-- O is not on line U ⊔ C. -/
theorem CoordSystem.hO_not_UC : ¬ Γ.O ≤ Γ.U ⊔ Γ.C := by
  intro h
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have h_le : Γ.U ⊔ Γ.O ≤ Γ.U ⊔ Γ.C := sup_le le_sup_left h
  have h_eq := ((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
    (atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).lt.le h_le).resolve_left
    (ne_of_gt (atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).lt)
  -- U ⊔ O = U ⊔ C, so C ≤ U ⊔ C = U ⊔ O.
  -- U ⊔ O = O ⊔ U = l, so C ≤ l. Contradiction.
  have : Γ.C ≤ Γ.U ⊔ Γ.O := h_eq ▸ le_sup_right
  exact Γ.hC_not_l (this.trans (by rw [sup_comm]))

/-- (O ⊔ C) ⊓ (U ⊔ C) = C: two distinct lines through C meet at C. -/
theorem CoordSystem.OC_inf_UC : (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C) = Γ.C := by
  rw [sup_comm Γ.O Γ.C, sup_comm Γ.U Γ.C]
  have hCO : Γ.C ≠ Γ.O := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hCU : Γ.C ≠ Γ.U := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hU_not_CO : ¬ Γ.U ≤ Γ.C ⊔ Γ.O := by
    intro h
    have hU_le_OC : Γ.U ≤ Γ.O ⊔ Γ.C := le_trans h (by rw [sup_comm Γ.C Γ.O])
    have h_le : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left hU_le_OC
    have h_eq := ((atom_covBy_join Γ.hO Γ.hC hCO.symm).eq_or_eq
      (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le h_le).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)
    exact Γ.hC_not_l (h_eq ▸ le_sup_right)
  exact modular_intersection Γ.hC Γ.hO Γ.hU hCO hCU Γ.hOU hU_not_CO

/-- Two-perspectivity composition on the coordinate line.

    Given line pairs (r₁, s₁) and (r₂, s₂), form two perspectivity
    intersection points p₁ = r₁ ⊓ s₁ and p₂ = r₂ ⊓ s₂, then project
    their join back onto l:

      two_persp r₁ s₁ r₂ s₂ = (r₁ ⊓ s₁ ⊔ r₂ ⊓ s₂) ⊓ l

    Both coord_add and coord_mul are instances of this pattern
    (see coord_add_eq_two_persp, coord_mul_eq_two_persp). -/
noncomputable def two_persp (Γ : CoordSystem L) (r₁ s₁ r₂ s₂ : L) : L :=
  (r₁ ⊓ s₁ ⊔ r₂ ⊓ s₂) ⊓ (Γ.O ⊔ Γ.U)

/-- Addition on the coordinate line.

    a + b = ((a ⊔ C) ⊓ m ⊔ D) ⊓ l

    where D = (b ⊔ E) ⊓ (U ⊔ C) is the canonical center for the
    return perspectivity, determined by b. The forward perspectivity
    projects a from l to m via center C; the return projects from m
    back to l via D. Since D lies on b ⊔ E, the return perspectivity
    sends E ↦ b. -/
noncomputable def coord_add (Γ : CoordSystem L) (a b : L) : L :=
  ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U)

/-- Addition factors through the two-perspectivity pattern.
    Bridge: m (via center C, return via E on q). -/
theorem coord_add_eq_two_persp (Γ : CoordSystem L) (a b : L) :
    coord_add Γ a b = two_persp Γ (a ⊔ Γ.C) (Γ.U ⊔ Γ.V) (b ⊔ Γ.E) (Γ.U ⊔ Γ.C) := rfl

/-- O is a left additive identity: O + b = b.

    With a = O, the forward perspectivity gives a' = E.
    By the modular law, E ⊔ D = (E ⊔ U ⊔ C) ⊓ (b ⊔ E) = π ⊓ (b ⊔ E) = b ⊔ E.
    Then (b ⊔ E) ⊓ l = b since b ≤ l and E ≰ l. -/
theorem coord_add_left_zero (Γ : CoordSystem L)
    (b : L) (hb : IsAtom b) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hb_ne_U : b ≠ Γ.U) :
    coord_add Γ Γ.O b = b := by
  -- After unfolding, (O⊔C)⊓(U⊔V) = E definitionally. Fold it.
  unfold coord_add
  change (Γ.E ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U) = b
  -- E ⊔ D = b ⊔ E by the modular law.
  have hbE_le_π : b ⊔ Γ.E ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (hb_on.trans le_sup_left)
      (CoordSystem.hE_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  have hED : Γ.E ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) = b ⊔ Γ.E :=
    calc Γ.E ⊔ (b ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)
        = Γ.E ⊔ (Γ.U ⊔ Γ.C) ⊓ (b ⊔ Γ.E) := by
            rw [@inf_comm L _ (b ⊔ Γ.E) (Γ.U ⊔ Γ.C)]
      _ = (Γ.E ⊔ (Γ.U ⊔ Γ.C)) ⊓ (b ⊔ Γ.E) :=
            (sup_inf_assoc_of_le (Γ.U ⊔ Γ.C) le_sup_right).symm
      _ = (Γ.E ⊔ Γ.U ⊔ Γ.C) ⊓ (b ⊔ Γ.E) := by rw [sup_assoc]
      _ = (Γ.U ⊔ Γ.V ⊔ Γ.C) ⊓ (b ⊔ Γ.E) := by rw [CoordSystem.EU_eq_m]
      _ = (Γ.O ⊔ Γ.U ⊔ Γ.V) ⊓ (b ⊔ Γ.E) := by rw [Γ.m_sup_C_eq_π]
      _ = b ⊔ Γ.E := inf_eq_right.mpr hbE_le_π
  rw [hED]
  -- (b ⊔ E) ⊓ l = b: b ≤ both sides, E ≰ l, so the meet is an atom = b.
  have hb_le : b ≤ (b ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left hb_on
  have hbE : b ≠ Γ.E := fun he => hb_ne_U
    (Γ.atom_on_both_eq_U hb hb_on (he ▸ CoordSystem.hE_on_m))
  have h_lt : (b ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro h
    -- h: (b⊔E) ⊓ l = l, so l ≤ b⊔E.
    -- b ⋖ b⊔E and b < l ≤ b⊔E, so l = b⊔E.
    -- Then E ≤ l, contradicting hE_not_l.
    have hl_le : Γ.O ⊔ Γ.U ≤ b ⊔ Γ.E := inf_eq_right.mp h
    have h_eq := ((atom_covBy_join hb Γ.hE_atom hbE).eq_or_eq
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hb hb_on).lt.le hl_le).resolve_left
      (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hb hb_on).lt)
    exact CoordSystem.hE_not_l (le_sup_right.trans (le_of_eq h_eq.symm))
  exact ((line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le hb.bot_lt hb_le) h_lt
    |>.le_iff.mp hb_le).resolve_left hb.1).symm

/-- O is a right additive identity: a + O = a.

    With b = O, D = (O ⊔ E) ⊓ (U ⊔ C) = (O ⊔ C) ⊓ (U ⊔ C) = C.
    Then a' ⊔ C = a ⊔ C (covering), and (a ⊔ C) ⊓ l = a. -/
theorem coord_add_right_zero (Γ : CoordSystem L)
    (a : L) (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) :
    coord_add Γ a Γ.O = a := by
  unfold coord_add
  -- D = (O ⊔ E) ⊓ (U ⊔ C). Rewrite: O ⊔ E = O ⊔ C, (O⊔C) ⊓ (U⊔C) = C.
  rw [CoordSystem.OE_eq_OC, CoordSystem.OC_inf_UC]
  -- Goal: ((a ⊔ C) ⊓ m ⊔ C) ⊓ l = a.
  -- a' ⊔ C = a ⊔ C: a' ≤ a ⊔ C (inf_le_left), C ≤ a ⊔ C (le_sup_right),
  -- so a' ⊔ C ≤ a ⊔ C. And C < a' ⊔ C (since a' ≰ C: a' ≤ m, C ≰ m).
  -- By covering C ⋖ a ⊔ C, we get a' ⊔ C = a ⊔ C.
  have hAC : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have ha'C_le : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ Γ.C ≤ a ⊔ Γ.C :=
    sup_le inf_le_left le_sup_right
  -- a' ≠ ⊥: lines a ⊔ C and m are coplanar and distinct, so they meet.
  have ha_lt_aC : a < a ⊔ Γ.C := by
    apply lt_of_le_of_ne le_sup_left; intro h
    have hC_le_a : Γ.C ≤ a := by rw [h]; exact le_sup_right
    exact Γ.hC_not_l ((ha.le_iff.mp hC_le_a).resolve_left Γ.hC.1 ▸ ha_on)
  have ha'_ne_bot : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≠ ⊥ := by
    have h_meet := lines_meet_if_coplanar Γ.m_covBy_π
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane)
      (fun h => Γ.hC_not_m (le_trans le_sup_right h))
      ha ha_lt_aC
    rwa [@inf_comm L _] at h_meet
  have hC_lt : Γ.C < (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ Γ.C := by
    apply lt_of_le_of_ne le_sup_right; intro h
    -- a' ⊔ C = C means a' ≤ C. Then a' ≤ C ⊓ m = ⊥. So a' = ⊥.
    have ha'_le_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.C := le_sup_left.trans h.symm.le
    have ha'_le_m : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V := inf_le_right
    have hCm : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ := by
      rcases Γ.hC.le_iff.mp inf_le_left with h | h
      · exact h
      · exact absurd (h ▸ inf_le_right) Γ.hC_not_m
    have : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ ⊥ := hCm ▸ le_inf ha'_le_C ha'_le_m
    exact ha'_ne_bot (le_antisymm this bot_le)
  have h_cov_Ca : Γ.C ⋖ a ⊔ Γ.C := by
    have := atom_covBy_join Γ.hC ha hAC.symm; rwa [sup_comm] at this
  have ha'C_eq : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ Γ.C = a ⊔ Γ.C :=
    (h_cov_Ca.eq_or_eq hC_lt.le ha'C_le).resolve_left (ne_of_gt hC_lt)
  rw [ha'C_eq]
  -- (a ⊔ C) ⊓ l = a.
  have ha_le : a ≤ (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left ha_on
  have h_lt : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro h
    have hl_le := inf_eq_right.mp h  -- l ≤ a ⊔ C
    -- a ⋖ a ⊔ C, a < l ≤ a ⊔ C ⟹ l = a ⊔ C ⟹ C ≤ l.
    have h_eq := ((atom_covBy_join ha Γ.hC hAC).eq_or_eq
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le hl_le).resolve_left
      (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)
    exact Γ.hC_not_l (le_sup_right.trans (le_of_eq h_eq.symm))
  exact ((line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le ha.bot_lt ha_le) h_lt
    |>.le_iff.mp ha_le).resolve_left ha.1).symm

omit [ComplementedLattice L] [IsAtomistic L] in
/-- If R is an atom not in π and s ≤ π, then π ⊓ (R ⊔ s) = s.
    The modular law gives (s ⊔ R) ⊓ π = s ⊔ (R ⊓ π) = s ⊔ ⊥ = s,
    using the fact that an atom outside π meets π trivially. -/
theorem inf_sup_of_atom_not_le {s π R : L}
    (hR : IsAtom R) (hR_not : ¬ R ≤ π) (hs_le : s ≤ π) :
    π ⊓ (R ⊔ s) = s := by
  have hR_inf : R ⊓ π = ⊥ :=
    (hR.le_iff.mp inf_le_left).resolve_right (fun h => hR_not (h ▸ inf_le_right))
  have key : (s ⊔ R) ⊓ π = s ⊔ R ⊓ π := sup_inf_assoc_of_le R hs_le
  rw [hR_inf, sup_bot_eq] at key  -- key : (s ⊔ R) ⊓ π = s
  rw [sup_comm, inf_comm] at key   -- key : π ⊓ (R ⊔ s) = s
  exact key


omit [ComplementedLattice L] in
/-- **Lifting preserves side intersections.**

    When a triangle side b₁ ⊔ b₂ is "lifted" to b₁' ⊔ b₂' (with
    b_i' on both o' ⊔ a_i and R ⊔ b_i), the lifted side meets
    a₁ ⊔ a₂ at the same point as the original side.

    Proof: both lines are in o' ⊔ a₁ ⊔ a₂ (a plane), so they meet
    at an atom T. Then T ≤ π (from a₁ ⊔ a₂ ≤ π) and T ≤ R ⊔ b₁ ⊔ b₂
    (from lifting). The modular law gives π ⊓ (R ⊔ b₁ ⊔ b₂) = b₁ ⊔ b₂.
    So T ≤ (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) = S, and since both are atoms, T = S. -/
theorem lift_side_intersection
    {a₁ a₂ b₁ b₂ R o' b₁' b₂' π : L}
    (ha₁ : IsAtom a₁) (ha₂ : IsAtom a₂) (ha₁₂ : a₁ ≠ a₂)
    (hb₁ : IsAtom b₁) (hb₂ : IsAtom b₂) (hb₁₂ : b₁ ≠ b₂)
    (hb₁' : IsAtom b₁') (hb₂' : IsAtom b₂') (hb₁₂' : b₁' ≠ b₂')
    (hR : IsAtom R) (ho' : IsAtom o')
    (ha_le : a₁ ⊔ a₂ ≤ π) (hb_le : b₁ ⊔ b₂ ≤ π)
    (h_sides : a₁ ⊔ a₂ ≠ b₁ ⊔ b₂)
    (hR_not : ¬ R ≤ π) (ho'_not : ¬ o' ≤ π)
    (hb₁'_oa : b₁' ≤ o' ⊔ a₁) (hb₂'_oa : b₂' ≤ o' ⊔ a₂)
    (hb₁'_Rb : b₁' ≤ R ⊔ b₁) (hb₂'_Rb : b₂' ≤ R ⊔ b₂)
    (hb₁'_not : ¬ b₁' ≤ π) :
    (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') = (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) := by
  -- Both lines are in τ = o' ⊔ a₁ ⊔ a₂.
  have hb'_le_τ : b₁' ⊔ b₂' ≤ o' ⊔ a₁ ⊔ a₂ :=
    sup_le (hb₁'_oa.trans (sup_le (le_sup_left.trans le_sup_left)
      (le_sup_right.trans le_sup_left)))
    (hb₂'_oa.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  -- a₁ ⊔ a₂ ⋖ τ
  have ho'_disj : o' ⊓ (a₁ ⊔ a₂) = ⊥ :=
    (ho'.le_iff.mp inf_le_left).resolve_right
      (fun h => ho'_not (le_trans (h ▸ inf_le_right) ha_le))
  have h_cov_τ : a₁ ⊔ a₂ ⋖ o' ⊔ a₁ ⊔ a₂ := by
    have h := covBy_sup_of_inf_covBy_left (ho'_disj ▸ ho'.bot_covBy)
    rw [← sup_assoc] at h; exact h
  -- b₁' ⊔ b₂' ≰ a₁ ⊔ a₂
  have hb'_not : ¬ b₁' ⊔ b₂' ≤ a₁ ⊔ a₂ :=
    fun h => hb₁'_not (le_trans le_sup_left (le_trans h ha_le))
  -- T ≠ ⊥: two lines in a plane meet.
  have hT_ne : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') ≠ ⊥ :=
    lines_meet_if_coplanar h_cov_τ hb'_le_τ hb'_not hb₁'
      (atom_covBy_join hb₁' hb₂' hb₁₂').lt
  -- T < a₁ ⊔ a₂
  have hT_lt : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') < a₁ ⊔ a₂ := by
    apply lt_of_le_of_ne inf_le_left; intro h
    have h_le : a₁ ⊔ a₂ ≤ b₁' ⊔ b₂' := inf_eq_left.mp h
    rcases h_cov_τ.eq_or_eq h_le hb'_le_τ with heq | heq
    · -- b₁' ⊔ b₂' = a₁ ⊔ a₂: then b₁' ≤ π, contradiction
      exact hb₁'_not (le_trans le_sup_left (heq ▸ ha_le))
    · -- b₁' ⊔ b₂' = τ (plane): impossible, a₁ ⊔ a₂ is between ⊥ and b₁'⊔b₂'
      -- but not an atom (a₁ is strictly between)
      have h_aa_lt : a₁ ⊔ a₂ < b₁' ⊔ b₂' :=
        lt_of_lt_of_le h_cov_τ.lt (le_of_eq heq.symm)
      have h_aa_atom := line_height_two hb₁' hb₂' hb₁₂'
        (lt_of_lt_of_le ha₁.bot_lt le_sup_left) h_aa_lt
      -- a₁ ⊔ a₂ is an atom but ⊥ < a₁ < a₁ ⊔ a₂ — violates covering
      exact h_aa_atom.bot_covBy.2 ha₁.bot_lt (atom_covBy_join ha₁ ha₂ ha₁₂).lt
  -- T is an atom.
  have hT_atom : IsAtom ((a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂')) :=
    line_height_two ha₁ ha₂ ha₁₂ (bot_lt_iff_ne_bot.mpr hT_ne) hT_lt
  -- T ≤ b₁ ⊔ b₂ via modular law.
  have hT_le_bb : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') ≤ b₁ ⊔ b₂ := by
    have hT_le_π : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') ≤ π := le_trans inf_le_left ha_le
    have hT_le_Rbb : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') ≤ R ⊔ (b₁ ⊔ b₂) :=
      le_trans inf_le_right (sup_le
        (hb₁'_Rb.trans (sup_le le_sup_left (le_sup_left.trans le_sup_right)))
        (hb₂'_Rb.trans (sup_le le_sup_left (le_sup_right.trans le_sup_right))))
    calc (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂')
        ≤ π ⊓ (R ⊔ (b₁ ⊔ b₂)) := le_inf hT_le_π hT_le_Rbb
      _ = b₁ ⊔ b₂ := inf_sup_of_atom_not_le hR hR_not hb_le
  -- T ≤ S.
  have hT_le_S : (a₁ ⊔ a₂) ⊓ (b₁' ⊔ b₂') ≤ (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) :=
    le_inf inf_le_left hT_le_bb
  -- S is an atom.
  have hS_lt : (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) < a₁ ⊔ a₂ := by
    apply lt_of_le_of_ne inf_le_left; intro h
    have h_le : a₁ ⊔ a₂ ≤ b₁ ⊔ b₂ := inf_eq_left.mp h
    have ha₁_cov := line_covers_its_atoms hb₁ hb₂ hb₁₂ ha₁ (le_sup_left.trans h_le)
    exact h_sides ((ha₁_cov.eq_or_eq (atom_covBy_join ha₁ ha₂ ha₁₂).lt.le h_le).resolve_left
      (ne_of_gt (atom_covBy_join ha₁ ha₂ ha₁₂).lt))
  have hS_atom : IsAtom ((a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂)) :=
    line_height_two ha₁ ha₂ ha₁₂ (lt_of_lt_of_le hT_atom.bot_lt hT_le_S) hS_lt
  exact (hS_atom.le_iff.mp hT_le_S).resolve_left hT_atom.1

omit [ComplementedLattice L] in
/-- **Desargues' theorem (planar case).**

    Two triangles in a plane π, perspective from a point o, have
    their three pairs of corresponding sides meeting on a common
    line — provided the lattice has height ≥ 4 (an atom outside π
    exists) and irreducibility (lines have ≥ 3 points).

    The proof lifts one triangle out of the plane using an external
    point R, applies the non-planar Desargues theorem, and uses
    lift_side_intersection to transfer collinearity back.

    This is the theorem that makes dimension matter: the algebra of
    the plane inherits its structure from the space it sits in. -/
theorem desargues_planar
    {o a₁ a₂ a₃ b₁ b₂ b₃ π : L}
    -- All atoms in the plane
    (ho : IsAtom o) (ha₁ : IsAtom a₁) (ha₂ : IsAtom a₂) (ha₃ : IsAtom a₃)
    (hb₁ : IsAtom b₁) (hb₂ : IsAtom b₂) (hb₃ : IsAtom b₃)
    -- All in π
    (ho_le : o ≤ π) (ha₁_le : a₁ ≤ π) (ha₂_le : a₂ ≤ π) (ha₃_le : a₃ ≤ π)
    (hb₁_le : b₁ ≤ π) (hb₂_le : b₂ ≤ π) (hb₃_le : b₃ ≤ π)
    -- Perspective from o: b_i on line o ⊔ a_i
    (hb₁_on : b₁ ≤ o ⊔ a₁) (hb₂_on : b₂ ≤ o ⊔ a₂) (hb₃_on : b₃ ≤ o ⊔ a₃)
    -- Distinct triangle vertices
    (ha₁₂ : a₁ ≠ a₂) (ha₁₃ : a₁ ≠ a₃) (ha₂₃ : a₂ ≠ a₃)
    (hb₁₂ : b₁ ≠ b₂) (hb₁₃ : b₁ ≠ b₃) (hb₂₃ : b₂ ≠ b₃)
    -- Distinct corresponding sides
    (h_sides₁₂ : a₁ ⊔ a₂ ≠ b₁ ⊔ b₂)
    (h_sides₁₃ : a₁ ⊔ a₃ ≠ b₁ ⊔ b₃)
    (h_sides₂₃ : a₂ ⊔ a₃ ≠ b₂ ⊔ b₃)
    -- Triangle planes (both in π)
    (hπA : a₁ ⊔ a₂ ⊔ a₃ = π) (_hπB : b₁ ⊔ b₂ ⊔ b₃ = π)
    -- o ≠ a_i (center is off the triangle)
    (hoa₁ : o ≠ a₁) (hoa₂ : o ≠ a₂) (hoa₃ : o ≠ a₃)
    -- o ≠ b_i (center is off both triangles)
    (hob₁ : o ≠ b₁) (hob₂ : o ≠ b₂) (hob₃ : o ≠ b₃)
    -- Corresponding vertices are distinct
    (ha₁b₁ : a₁ ≠ b₁) (ha₂b₂ : a₂ ≠ b₂) (_ha₃b₃ : a₃ ≠ b₃)
    -- Height ≥ 4: an atom outside π
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ π)
    -- Irreducibility: third atom on each line
    (h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    -- Sides are lines covered by π
    (h_cov₁₂ : a₁ ⊔ a₂ ⋖ π) (_h_cov₁₃ : a₁ ⊔ a₃ ⋖ π) (_h_cov₂₃ : a₂ ⊔ a₃ ⋖ π) :
    -- All three intersection points lie on a common line (strictly below π)
    ∃ (axis : L), axis ≤ π ∧ axis ≠ π ∧
      (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) ≤ axis ∧
      (a₁ ⊔ a₃) ⊓ (b₁ ⊔ b₃) ≤ axis ∧
      (a₂ ⊔ a₃) ⊓ (b₂ ⊔ b₃) ≤ axis := by
  -- Step 1: Pick o' on line R ⊔ o, distinct from R and o.
  have hRo : R ≠ o := fun h => hR_not (h ▸ ho_le)
  obtain ⟨o', ho'_atom, ho'_le, ho'_ne_R, ho'_ne_o⟩ := h_irred R o hR ho hRo
  have ho'_not : ¬ o' ≤ π := by
    intro h
    -- o' ≤ π and o' ≤ R ⊔ o. So o' ≤ π ⊓ (R ⊔ o) = o (modular law).
    have := inf_sup_of_atom_not_le hR hR_not ho_le
    have ho'_le_o : o' ≤ o := this ▸ le_inf h ho'_le
    exact ho'_ne_o ((ho.le_iff.mp ho'_le_o).resolve_left ho'_atom.1)
  -- Step 2: Define lifted vertices b_i' = (o' ⊔ a_i) ⊓ (R ⊔ b_i).
  set b₁' := (o' ⊔ a₁) ⊓ (R ⊔ b₁) with hb₁'_def
  set b₂' := (o' ⊔ a₂) ⊓ (R ⊔ b₂) with hb₂'_def
  set b₃' := (o' ⊔ a₃) ⊓ (R ⊔ b₃) with hb₃'_def

  -- Step 3: Mechanical properties of lifted vertices.

  -- Helpers: R ⊔ o' = R ⊔ o (o' is a third point on line R ⊔ o).
  have ho'_not_R : ¬ o' ≤ R := fun h =>
    ho'_ne_R ((hR.le_iff.mp h).resolve_left ho'_atom.1)
  have hRo'_eq : R ⊔ o' = R ⊔ o := by
    have h_cov := atom_covBy_join hR ho hRo
    have h_lt : R < R ⊔ o' := lt_of_le_of_ne le_sup_left
      (fun h => ho'_not_R (h ▸ le_sup_right))
    exact (h_cov.eq_or_eq h_lt.le (sup_le le_sup_left ho'_le)).resolve_left (ne_of_gt h_lt)
  -- o ≤ R ⊔ o' (since R ⊔ o' = R ⊔ o)
  have ho_le_Ro' : o ≤ R ⊔ o' := hRo'_eq ▸ (le_sup_right : o ≤ R ⊔ o)
  -- b_i ≱ R ⊔ o (if so, modular law gives b_i ≤ o, so b_i = o)
  have hb₁_not_Ro : ¬ b₁ ≤ R ⊔ o := fun h =>
    hob₁ ((ho.le_iff.mp (inf_sup_of_atom_not_le hR hR_not ho_le ▸
      le_inf hb₁_le h)).resolve_left hb₁.1).symm
  have hb₂_not_Ro : ¬ b₂ ≤ R ⊔ o := fun h =>
    hob₂ ((ho.le_iff.mp (inf_sup_of_atom_not_le hR hR_not ho_le ▸
      le_inf hb₂_le h)).resolve_left hb₂.1).symm
  have hb₃_not_Ro : ¬ b₃ ≤ R ⊔ o := fun h =>
    hob₃ ((ho.le_iff.mp (inf_sup_of_atom_not_le hR hR_not ho_le ▸
      le_inf hb₃_le h)).resolve_left hb₃.1).symm
  -- R ≠ b_i (since b_i ≤ π and R ≱ π)
  have hR_ne_b₁ : R ≠ b₁ := fun h => hR_not (h ▸ hb₁_le)
  have hR_ne_b₂ : R ≠ b₂ := fun h => hR_not (h ▸ hb₂_le)
  have hR_ne_b₃ : R ≠ b₃ := fun h => hR_not (h ▸ hb₃_le)
  -- o ⊔ b_i = o ⊔ a_i (since b_i ≤ o ⊔ a_i and o ≠ b_i, covering gives equality)
  have hob₁_eq : o ⊔ b₁ = o ⊔ a₁ :=
    ((atom_covBy_join ho ha₁ hoa₁).eq_or_eq le_sup_left
      (sup_le le_sup_left hb₁_on)).resolve_left
      (ne_of_gt (atom_covBy_join ho hb₁ hob₁).lt)
  have hob₂_eq : o ⊔ b₂ = o ⊔ a₂ :=
    ((atom_covBy_join ho ha₂ hoa₂).eq_or_eq le_sup_left
      (sup_le le_sup_left hb₂_on)).resolve_left
      (ne_of_gt (atom_covBy_join ho hb₂ hob₂).lt)
  have hob₃_eq : o ⊔ b₃ = o ⊔ a₃ :=
    ((atom_covBy_join ho ha₃ hoa₃).eq_or_eq le_sup_left
      (sup_le le_sup_left hb₃_on)).resolve_left
      (ne_of_gt (atom_covBy_join ho hb₃ hob₃).lt)
  -- a_i ≤ (R ⊔ b_i) ⊔ o': the plane through R, b_i, o' also contains a_i.
  -- Proof: o ⊔ b_i = o ⊔ a_i (since b_i ≤ o ⊔ a_i, covering).
  -- o ⊔ b_i ≤ (R ⊔ b_i) ⊔ o' (since o ≤ R ⊔ o' and b_i ≤ R ⊔ b_i).
  -- So a_i ≤ o ⊔ a_i = o ⊔ b_i ≤ (R ⊔ b_i) ⊔ o'.
  have hob_le₁ : o ⊔ b₁ ≤ (R ⊔ b₁) ⊔ o' :=
    sup_le (ho_le_Ro'.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      (le_sup_right.trans le_sup_left)
  have hob_le₂ : o ⊔ b₂ ≤ (R ⊔ b₂) ⊔ o' :=
    sup_le (ho_le_Ro'.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      (le_sup_right.trans le_sup_left)
  have hob_le₃ : o ⊔ b₃ ≤ (R ⊔ b₃) ⊔ o' :=
    sup_le (ho_le_Ro'.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      (le_sup_right.trans le_sup_left)
  have ha₁_in : a₁ ≤ (R ⊔ b₁) ⊔ o' := by
    calc a₁ ≤ o ⊔ a₁ := le_sup_right
      _ = o ⊔ b₁ := hob₁_eq.symm
      _ ≤ (R ⊔ b₁) ⊔ o' := hob_le₁
  have ha₂_in : a₂ ≤ (R ⊔ b₂) ⊔ o' := by
    calc a₂ ≤ o ⊔ a₂ := le_sup_right
      _ = o ⊔ b₂ := hob₂_eq.symm
      _ ≤ (R ⊔ b₂) ⊔ o' := hob_le₂
  have ha₃_in : a₃ ≤ (R ⊔ b₃) ⊔ o' := by
    calc a₃ ≤ o ⊔ a₃ := le_sup_right
      _ = o ⊔ b₃ := hob₃_eq.symm
      _ ≤ (R ⊔ b₃) ⊔ o' := hob_le₃
  -- o' ≱ R ⊔ b_i: if o' ≤ R ⊔ b_i, then o' ≤ (R ⊔ o) ⊓ (R ⊔ b_i).
  -- Since b_i ≱ R ⊔ o, lines R ⊔ o and R ⊔ b_i are distinct through R.
  -- Modular intersection: (R ⊔ o) ⊓ (R ⊔ b_i) = R. So o' ≤ R, o' = R. Contradiction.
  have ho'_not_Rb₁ : ¬ o' ≤ R ⊔ b₁ := by
    intro h
    have h_meet := modular_intersection hR ho hb₁ hRo hR_ne_b₁ hob₁ hb₁_not_Ro
    exact ho'_ne_R ((hR.le_iff.mp (h_meet ▸ le_inf ho'_le h)).resolve_left ho'_atom.1)
  have ho'_not_Rb₂ : ¬ o' ≤ R ⊔ b₂ := by
    intro h
    have h_meet := modular_intersection hR ho hb₂ hRo hR_ne_b₂ hob₂ hb₂_not_Ro
    exact ho'_ne_R ((hR.le_iff.mp (h_meet ▸ le_inf ho'_le h)).resolve_left ho'_atom.1)
  have ho'_not_Rb₃ : ¬ o' ≤ R ⊔ b₃ := by
    intro h
    have h_meet := modular_intersection hR ho hb₃ hRo hR_ne_b₃ hob₃ hb₃_not_Ro
    exact ho'_ne_R ((hR.le_iff.mp (h_meet ▸ le_inf ho'_le h)).resolve_left ho'_atom.1)
  -- a_i ≠ o' (since a_i ≤ π and o' ≱ π)
  have ha₁_ne_o' : a₁ ≠ o' := fun h => ho'_not (h ▸ ha₁_le)
  have ha₂_ne_o' : a₂ ≠ o' := fun h => ho'_not (h ▸ ha₂_le)
  have ha₃_ne_o' : a₃ ≠ o' := fun h => ho'_not (h ▸ ha₃_le)

  -- 3a: Each b_i' is an atom (perspect_atom with p=a_i, c=o', line=R ⊔ b_i).
  have hb₁'_atom : IsAtom b₁' := by
    rw [hb₁'_def, show o' ⊔ a₁ = a₁ ⊔ o' from sup_comm _ _]
    exact perspect_atom ho'_atom ha₁ ha₁_ne_o' hR hb₁ hR_ne_b₁
      ho'_not_Rb₁ (sup_le ha₁_in le_sup_right)
  have hb₂'_atom : IsAtom b₂' := by
    rw [hb₂'_def, show o' ⊔ a₂ = a₂ ⊔ o' from sup_comm _ _]
    exact perspect_atom ho'_atom ha₂ ha₂_ne_o' hR hb₂ hR_ne_b₂
      ho'_not_Rb₂ (sup_le ha₂_in le_sup_right)
  have hb₃'_atom : IsAtom b₃' := by
    rw [hb₃'_def, show o' ⊔ a₃ = a₃ ⊔ o' from sup_comm _ _]
    exact perspect_atom ho'_atom ha₃ ha₃_ne_o' hR hb₃ hR_ne_b₃
      ho'_not_Rb₃ (sup_le ha₃_in le_sup_right)

  -- 3b: b_i' ≱ π. If b_i' ≤ π, then b_i' ≤ π ⊓ (R ⊔ b_i) = b_i,
  -- so b_i' = b_i. Then b_i ≤ o' ⊔ a_i, so b_i ≤ π ⊓ (o' ⊔ a_i) = a_i,
  -- hence b_i = a_i. Contradiction with a_i ≠ b_i.
  have hb₁'_not : ¬ b₁' ≤ π := by
    intro h
    -- b₁' ≤ π ⊓ (R ⊔ b₁) = b₁
    have hb₁'_le_b₁ : b₁' ≤ b₁ := by
      have := inf_sup_of_atom_not_le hR hR_not hb₁_le
      exact this ▸ le_inf h inf_le_right
    have hb₁'_eq_b₁ : b₁' = b₁ :=
      (hb₁.le_iff.mp hb₁'_le_b₁).resolve_left hb₁'_atom.1
    -- Then b₁ ≤ o' ⊔ a₁, so b₁ ≤ π ⊓ (o' ⊔ a₁) = a₁
    have hb₁_le_o'a₁ : b₁ ≤ o' ⊔ a₁ := hb₁'_eq_b₁ ▸ (inf_le_left : b₁' ≤ o' ⊔ a₁)
    have hb₁_le_a₁ : b₁ ≤ a₁ := by
      have := inf_sup_of_atom_not_le ho'_atom ho'_not ha₁_le
      exact this ▸ le_inf hb₁_le hb₁_le_o'a₁
    exact ha₁b₁ ((ha₁.le_iff.mp hb₁_le_a₁).resolve_left hb₁.1).symm
  have hb₂'_not : ¬ b₂' ≤ π := by
    intro h
    have hb₂'_le_b₂ : b₂' ≤ b₂ := by
      have := inf_sup_of_atom_not_le hR hR_not hb₂_le
      exact this ▸ le_inf h inf_le_right
    have hb₂'_eq_b₂ : b₂' = b₂ :=
      (hb₂.le_iff.mp hb₂'_le_b₂).resolve_left hb₂'_atom.1
    have hb₂_le_o'a₂ : b₂ ≤ o' ⊔ a₂ := hb₂'_eq_b₂ ▸ (inf_le_left : b₂' ≤ o' ⊔ a₂)
    have hb₂_le_a₂ : b₂ ≤ a₂ := by
      have := inf_sup_of_atom_not_le ho'_atom ho'_not ha₂_le
      exact this ▸ le_inf hb₂_le hb₂_le_o'a₂
    exact ha₂b₂ ((ha₂.le_iff.mp hb₂_le_a₂).resolve_left hb₂.1).symm

  -- 3c: Lifted vertices are distinct.
  -- If b₁' = b₂', then b₁' ≤ (o' ⊔ a₁) ⊓ (o' ⊔ a₂) = o' (modular intersection,
  -- since a₂ ≱ o' ⊔ a₁ — otherwise o' ≤ a₁ ⊔ a₂ ≤ π, contradiction).
  -- Then o' ≤ R ⊔ b₁ (since b₁' ≤ R ⊔ b₁). But o' ≱ R ⊔ b₁. Contradiction.
  -- (o' ⊔ a_i) ⊓ (o' ⊔ a_j) = o' for distinct i,j.
  -- Non-collinearity: if a_j ≤ o' ⊔ a_i, then a_i ⊔ a_j ≤ o' ⊔ a_i.
  -- Covering a_i ⋖ o' ⊔ a_i (rewritten from a_i ⋖ a_i ⊔ o') gives
  -- o' ⊔ a_i = a_i ⊔ a_j, so o' ≤ a_i ⊔ a_j ≤ π, contradiction.
  have h_not_coll₁₂ : ¬ a₂ ≤ o' ⊔ a₁ := by
    intro h
    have h_le : a₁ ⊔ a₂ ≤ o' ⊔ a₁ := sup_le le_sup_right h
    have h_cov : a₁ ⋖ o' ⊔ a₁ := by
      rw [show o' ⊔ a₁ = a₁ ⊔ o' from sup_comm _ _]
      exact atom_covBy_join ha₁ ho'_atom ha₁_ne_o'
    have h_eq : a₁ ⊔ a₂ = o' ⊔ a₁ :=
      (h_cov.eq_or_eq (atom_covBy_join ha₁ ha₂ ha₁₂).lt.le h_le).resolve_left
        (ne_of_gt (atom_covBy_join ha₁ ha₂ ha₁₂).lt)
    exact ho'_not (calc o' ≤ o' ⊔ a₁ := le_sup_left
      _ = a₁ ⊔ a₂ := h_eq.symm
      _ ≤ π := sup_le ha₁_le ha₂_le)
  have h_not_coll₁₃ : ¬ a₃ ≤ o' ⊔ a₁ := by
    intro h
    have h_le : a₁ ⊔ a₃ ≤ o' ⊔ a₁ := sup_le le_sup_right h
    have h_cov : a₁ ⋖ o' ⊔ a₁ := by
      rw [show o' ⊔ a₁ = a₁ ⊔ o' from sup_comm _ _]
      exact atom_covBy_join ha₁ ho'_atom ha₁_ne_o'
    have h_eq : a₁ ⊔ a₃ = o' ⊔ a₁ :=
      (h_cov.eq_or_eq (atom_covBy_join ha₁ ha₃ ha₁₃).lt.le h_le).resolve_left
        (ne_of_gt (atom_covBy_join ha₁ ha₃ ha₁₃).lt)
    exact ho'_not (calc o' ≤ o' ⊔ a₁ := le_sup_left
      _ = a₁ ⊔ a₃ := h_eq.symm
      _ ≤ π := sup_le ha₁_le ha₃_le)
  have h_not_coll₂₃ : ¬ a₃ ≤ o' ⊔ a₂ := by
    intro h
    have h_le : a₂ ⊔ a₃ ≤ o' ⊔ a₂ := sup_le le_sup_right h
    have h_cov : a₂ ⋖ o' ⊔ a₂ := by
      rw [show o' ⊔ a₂ = a₂ ⊔ o' from sup_comm _ _]
      exact atom_covBy_join ha₂ ho'_atom ha₂_ne_o'
    have h_eq : a₂ ⊔ a₃ = o' ⊔ a₂ :=
      (h_cov.eq_or_eq (atom_covBy_join ha₂ ha₃ ha₂₃).lt.le h_le).resolve_left
        (ne_of_gt (atom_covBy_join ha₂ ha₃ ha₂₃).lt)
    exact ho'_not (calc o' ≤ o' ⊔ a₂ := le_sup_left
      _ = a₂ ⊔ a₃ := h_eq.symm
      _ ≤ π := sup_le ha₂_le ha₃_le)
  have h_meet_o'₁₂ : (o' ⊔ a₁) ⊓ (o' ⊔ a₂) = o' :=
    modular_intersection ho'_atom ha₁ ha₂ ha₁_ne_o'.symm ha₂_ne_o'.symm ha₁₂ h_not_coll₁₂
  have h_meet_o'₁₃ : (o' ⊔ a₁) ⊓ (o' ⊔ a₃) = o' :=
    modular_intersection ho'_atom ha₁ ha₃ ha₁_ne_o'.symm ha₃_ne_o'.symm ha₁₃ h_not_coll₁₃
  have h_meet_o'₂₃ : (o' ⊔ a₂) ⊓ (o' ⊔ a₃) = o' :=
    modular_intersection ho'_atom ha₂ ha₃ ha₂_ne_o'.symm ha₃_ne_o'.symm ha₂₃ h_not_coll₂₃
  have hb₁₂' : b₁' ≠ b₂' := by
    intro h
    -- b₁' = b₂' ≤ (o' ⊔ a₁) ⊓ (o' ⊔ a₂) = o'
    have hb₁'_le_o' : b₁' ≤ o' :=
      h_meet_o'₁₂ ▸ le_inf inf_le_left (h ▸ inf_le_left)
    -- So b₁' = o' (both atoms).
    have hb₁'_eq : b₁' = o' :=
      (ho'_atom.le_iff.mp hb₁'_le_o').resolve_left hb₁'_atom.1
    -- But b₁' ≤ R ⊔ b₁, so o' ≤ R ⊔ b₁. Contradiction.
    exact ho'_not_Rb₁ (hb₁'_eq ▸ inf_le_right)
  have hb₁₃' : b₁' ≠ b₃' := by
    intro h
    have hb₁'_le_o' : b₁' ≤ o' :=
      h_meet_o'₁₃ ▸ le_inf inf_le_left (h ▸ inf_le_left)
    have hb₁'_eq : b₁' = o' :=
      (ho'_atom.le_iff.mp hb₁'_le_o').resolve_left hb₁'_atom.1
    exact ho'_not_Rb₁ (hb₁'_eq ▸ inf_le_right)
  have hb₂₃' : b₂' ≠ b₃' := by
    intro h
    have hb₂'_le_o' : b₂' ≤ o' :=
      h_meet_o'₂₃ ▸ le_inf inf_le_left (h ▸ inf_le_left)
    have hb₂'_eq : b₂' = o' :=
      (ho'_atom.le_iff.mp hb₂'_le_o').resolve_left hb₂'_atom.1
    exact ho'_not_Rb₂ (hb₂'_eq ▸ inf_le_right)

  -- Step 4: Apply non-planar Desargues to a₁a₂a₃ and b₁'b₂'b₃'.
  -- (Perspective from o': b_i' ≤ o' ⊔ a_i by definition.)
  have h_des := desargues_nonplanar ho'_atom ha₁ ha₂ ha₃
    hb₁'_atom hb₂'_atom hb₃'_atom
    (inf_le_left : b₁' ≤ o' ⊔ a₁)
    (inf_le_left : b₂' ≤ o' ⊔ a₂)
    (inf_le_left : b₃' ≤ o' ⊔ a₃)
    π hπA.symm (b₁' ⊔ b₂' ⊔ b₃') rfl

  -- Step 5: Apply lift_side_intersection three times.
  have h_lift₁₂ := lift_side_intersection ha₁ ha₂ ha₁₂ hb₁ hb₂ hb₁₂
    hb₁'_atom hb₂'_atom hb₁₂' hR ho'_atom
    (sup_le ha₁_le ha₂_le) (sup_le hb₁_le hb₂_le) h_sides₁₂ hR_not ho'_not
    inf_le_left inf_le_left inf_le_right inf_le_right hb₁'_not
  have h_lift₁₃ := lift_side_intersection ha₁ ha₃ ha₁₃ hb₁ hb₃ hb₁₃
    hb₁'_atom hb₃'_atom hb₁₃' hR ho'_atom
    (sup_le ha₁_le ha₃_le) (sup_le hb₁_le hb₃_le) h_sides₁₃ hR_not ho'_not
    inf_le_left inf_le_left inf_le_right inf_le_right hb₁'_not
  have h_lift₂₃ := lift_side_intersection ha₂ ha₃ ha₂₃ hb₂ hb₃ hb₂₃
    hb₂'_atom hb₃'_atom hb₂₃' hR ho'_atom
    (sup_le ha₂_le ha₃_le) (sup_le hb₂_le hb₃_le) h_sides₂₃ hR_not ho'_not
    inf_le_left inf_le_left inf_le_right inf_le_right hb₂'_not


  -- Step 6: The axis is π ⊓ (b₁' ⊔ b₂' ⊔ b₃'), strictly below π.
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := h_des
  have haxis_ne : π ⊓ (b₁' ⊔ b₂' ⊔ b₃') ≠ π := by
    intro h_eq
    have hπ_le : π ≤ b₁' ⊔ b₂' ⊔ b₃' := inf_eq_left.mp h_eq
    have hπB_le : b₁' ⊔ b₂' ⊔ b₃' ≤ o' ⊔ π :=
      sup_le (sup_le
        ((inf_le_left : b₁' ≤ o' ⊔ a₁).trans (sup_le le_sup_left (ha₁_le.trans le_sup_right)))
        ((inf_le_left : b₂' ≤ o' ⊔ a₂).trans (sup_le le_sup_left (ha₂_le.trans le_sup_right))))
        ((inf_le_left : b₃' ≤ o' ⊔ a₃).trans (sup_le le_sup_left (ha₃_le.trans le_sup_right)))
    have ho'_disj : π ⊓ o' = ⊥ := by
      rcases ho'_atom.le_iff.mp inf_le_right with h | h
      · exact h
      · exfalso; exact ho'_not (le_of_eq h.symm |>.trans inf_le_left)
    have hπ_cov_s : π ⋖ o' ⊔ π := by
      have h := covBy_sup_of_inf_covBy_right (ho'_disj ▸ ho'_atom.bot_covBy)
      rwa [sup_comm] at h
    rcases hπ_cov_s.eq_or_eq hπ_le hπB_le with hcase | hcase
    · exact hb₁'_not (le_sup_left.trans (le_sup_left.trans (le_of_eq hcase)))
    · rw [← hcase] at hπ_cov_s
      have hb_cov : b₁' ⋖ b₁' ⊔ b₂' := atom_covBy_join hb₁'_atom hb₂'_atom hb₁₂'
      by_cases hb₃'_col : b₃' ≤ b₁' ⊔ b₂'
      · -- Collinear case: πB = b₁'⊔b₂'. a₁ ⋖ line, so a₁⊔a₂ = line, π ≤ a₁⊔a₂ < π.
        rw [show b₁' ⊔ b₂' ⊔ b₃' = b₁' ⊔ b₂' from
          le_antisymm (sup_le le_rfl hb₃'_col) le_sup_left] at hπ_le
        have ha₁_cov_line : a₁ ⋖ b₁' ⊔ b₂' :=
          line_covers_its_atoms hb₁'_atom hb₂'_atom hb₁₂' ha₁ (ha₁_le.trans hπ_le)
        have h12_eq : a₁ ⊔ a₂ = b₁' ⊔ b₂' :=
          (ha₁_cov_line.eq_or_eq le_sup_left (h_cov₁₂.le.trans hπ_le)).resolve_left
            (ne_of_gt (atom_covBy_join ha₁ ha₂ ha₁₂).lt)
        exact lt_irrefl _ (lt_of_lt_of_le h_cov₁₂.lt (h12_eq ▸ hπ_le))
      · -- Non-collinear: b₁'⊔b₂' and π both ⋖ πB. Meet ⋖ π is impossible.
        have hb₃'_disj : b₃' ⊓ (b₁' ⊔ b₂') = ⊥ :=
          (hb₃'_atom.le_iff.mp inf_le_left).resolve_right
            (fun h => hb₃'_col (h ▸ inf_le_right))
        have hline_cov : b₁' ⊔ b₂' ⋖ b₁' ⊔ b₂' ⊔ b₃' := by
          rw [show b₁' ⊔ b₂' ⊔ b₃' = b₃' ⊔ (b₁' ⊔ b₂') from sup_comm _ _]
          exact covBy_sup_of_inf_covBy_left (hb₃'_disj ▸ hb₃'_atom.bot_covBy)
        have hline_ne : b₁' ⊔ b₂' ≠ π :=
          fun h => hb₁'_not (le_sup_left.trans (le_of_eq h))
        obtain ⟨hmeet_cov_line, hmeet_cov_π⟩ :=
          planes_meet_covBy hline_cov hπ_cov_s hline_ne
        -- p := (b₁'⊔b₂') ⊓ π is an atom (via diamond with b₁')
        have hp_ne_b₁ : (b₁' ⊔ b₂') ⊓ π ≠ b₁' :=
          fun h => hb₁'_not (h ▸ inf_le_right)
        obtain ⟨hpb_cov_p, hpb_cov_b₁⟩ :=
          planes_meet_covBy hmeet_cov_line hb_cov hp_ne_b₁
        have : (b₁' ⊔ b₂') ⊓ π ⊓ b₁' = ⊥ := by
          rcases hb₁'_atom.le_iff.mp hpb_cov_b₁.le with h | h
          · exact h
          · exfalso; exact hb₁'_not
              ((le_of_eq h.symm).trans (inf_le_left.trans inf_le_right))
        rw [this] at hpb_cov_p  -- ⊥ ⋖ p
        have hp_atom := line_height_two hb₁'_atom hb₂'_atom hb₁₂'
          hpb_cov_p.lt hmeet_cov_line.lt
        -- p ⋖ π, but a₁ < a₁⊔a₂ < π: CovBy contradiction
        by_cases ha₁p : a₁ = (b₁' ⊔ b₂') ⊓ π
        · exact (ha₁p ▸ hmeet_cov_π).2
            (atom_covBy_join ha₁ ha₂ ha₁₂).lt h_cov₁₂.lt
        · have hp_lt : (b₁' ⊔ b₂') ⊓ π < (b₁' ⊔ b₂') ⊓ π ⊔ a₁ :=
            lt_of_le_of_ne le_sup_left (fun h => ha₁p
              ((hp_atom.le_iff.mp (h ▸ le_sup_right)).resolve_left ha₁.1))
          have hp_eq : (b₁' ⊔ b₂') ⊓ π ⊔ a₁ = π :=
            (hmeet_cov_π.eq_or_eq hp_lt.le
              (sup_le hmeet_cov_π.le ha₁_le)).resolve_left (ne_of_gt hp_lt)
          have ha₁_cov_π : a₁ ⋖ π := by
            rw [← hp_eq, sup_comm]
            exact atom_covBy_join ha₁ hp_atom ha₁p
          exact ha₁_cov_π.2
            (atom_covBy_join ha₁ ha₂ ha₁₂).lt h_cov₁₂.lt
  exact ⟨π ⊓ (b₁' ⊔ b₂' ⊔ b₃'), inf_le_left, haxis_ne,
    h_lift₁₂ ▸ h₁₂, h_lift₁₃ ▸ h₁₃, h_lift₂₃ ▸ h₂₃⟩

omit [BoundedOrder L] [IsModularLattice L] [IsAtomistic L] in
/-- **Collinearity from Desargues.** If three points lie on a common
    element strictly below π, and two of them span a line covered by π,
    the third lies on that line.

    This is the extraction step: desargues_planar gives ∃ axis with
    axis ≤ π ∧ axis ≠ π, and two known side-intersections S₁₂, S₁₃
    span a line ℓ ⋖ π. Then ℓ ≤ axis < π, and ℓ ⋖ π forces axis = ℓ.
    The third point S₂₃ ≤ axis = ℓ. -/
theorem collinear_of_common_bound {s₁ s₂ s₃ axis π : L}
    (h_cov : s₁ ⊔ s₂ ⋖ π)
    (h_axis_le : axis ≤ π) (h_axis_ne : axis ≠ π)
    (h₁ : s₁ ≤ axis) (h₂ : s₂ ≤ axis) (h₃ : s₃ ≤ axis) :
    s₃ ≤ s₁ ⊔ s₂ := by
  have h12_le : s₁ ⊔ s₂ ≤ axis := sup_le h₁ h₂
  have h_axis_lt : axis < π := lt_of_le_of_ne h_axis_le h_axis_ne
  -- s₁ ⊔ s₂ ≤ axis < π, with s₁ ⊔ s₂ ⋖ π: axis = s₁ ⊔ s₂
  have h_eq : axis = s₁ ⊔ s₂ :=
    (h_cov.eq_or_eq h12_le h_axis_lt.le).resolve_right (ne_of_lt h_axis_lt)
  exact h_eq ▸ h₃


-- § Small Desargues (A5a)

omit [ComplementedLattice L] in
/-- **Small Desargues (A5a).** Three lines through a common point U in a plane π,
    with six atoms satisfying two "parallelism" conditions. Desargues gives the third.

    "Parallel" means: the two lines meet the base line m at the same point.

    Concretely: three lines l₁ = A⊔U, l₂ = B⊔U, l₃ = C⊔U through U,
    with A' on l₁, B' on l₂, C' on l₃.
    If (A⊔B)⊓m = (A'⊔B')⊓m and (A⊔C)⊓m = (A'⊔C')⊓m,
    then (B⊔C)⊓m = (B'⊔C')⊓m.

    This is desargues_planar with center U, extracting the third axis point on m. -/
theorem small_desargues'
    {U A B C A' B' C' m π : L}
    -- Atoms
    (hU : IsAtom U) (hA : IsAtom A) (hB : IsAtom B) (hC : IsAtom C)
    (hA' : IsAtom A') (hB' : IsAtom B') (hC' : IsAtom C')
    -- All in π
    (hU_le : U ≤ π) (hA_le : A ≤ π) (hB_le : B ≤ π) (hC_le : C ≤ π)
    (hA'_le : A' ≤ π) (hB'_le : B' ≤ π) (hC'_le : C' ≤ π)
    -- m is a line in π through U
    (hm_le : m ≤ π) (hm_ne : m ≠ π) (hU_on_m : U ≤ m)
    -- Lines through U: A' on U⊔A, B' on U⊔B, C' on U⊔C
    (hA'_on : A' ≤ U ⊔ A) (hB'_on : B' ≤ U ⊔ B) (hC'_on : C' ≤ U ⊔ C)
    -- Distinct vertices (A ≠ B etc.)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hA'B' : A' ≠ B') (hA'C' : A' ≠ C') (hB'C' : B' ≠ C')
    -- Distinct sides
    (h_sides_AB : A ⊔ B ≠ A' ⊔ B')
    (h_sides_AC : A ⊔ C ≠ A' ⊔ C')
    (h_sides_BC : B ⊔ C ≠ B' ⊔ C')
    -- Triangles span π
    (hπA : A ⊔ B ⊔ C = π) (hπB : A' ⊔ B' ⊔ C' = π)
    -- Center off both triangles
    (hUA : U ≠ A) (hUB : U ≠ B) (hUC : U ≠ C)
    (hUA' : U ≠ A') (hUB' : U ≠ B') (hUC' : U ≠ C')
    -- Corresponding vertices distinct
    (hAA' : A ≠ A') (hBB' : B ≠ B') (hCC' : C ≠ C')
    -- Height ≥ 4
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ π)
    -- Irreducibility
    (h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    -- Sides covered by π
    (h_cov_AB : A ⊔ B ⋖ π) (h_cov_AC : A ⊔ C ⋖ π) (h_cov_BC : B ⊔ C ⋖ π)
    -- m covered by π (m is a line)
    (hm_cov : m ⋖ π)
    -- ══ Parallelism hypotheses ══
    (h_par_AB : (A ⊔ B) ⊓ m = (A' ⊔ B') ⊓ m)
    (h_par_AC : (A ⊔ C) ⊓ m = (A' ⊔ C') ⊓ m) :
    -- ══ Conclusion: third parallelism ══
    (B ⊔ C) ⊓ m = (B' ⊔ C') ⊓ m := by
  -- Step 1: Apply desargues_planar with center U.
  obtain ⟨axis, h_axis_le, h_axis_ne, h₁₂, h₁₃, h₂₃⟩ :=
    desargues_planar hU hA hB hC hA' hB' hC'
      hU_le hA_le hB_le hC_le hA'_le hB'_le hC'_le
      hA'_on hB'_on hC'_on
      hAB hAC hBC hA'B' hA'C' hB'C'
      h_sides_AB h_sides_AC h_sides_BC
      hπA hπB
      hUA hUB hUC hUA' hUB' hUC'
      hAA' hBB' hCC'
      R hR hR_not h_irred
      h_cov_AB h_cov_AC h_cov_BC
  -- ── Helpers: unprimed sides ≠ m ──
  -- If X⊔Y = m, then U ≤ X⊔Y, so X'⊔Y' ≤ X⊔Y. Line inside line → equal. ✗
  have side_ne_m : ∀ {X Y X' Y' : L}, IsAtom X → IsAtom Y → X ≠ Y →
      IsAtom X' → IsAtom Y' → X' ≠ Y' →
      X' ≤ U ⊔ X → Y' ≤ U ⊔ Y → X ⊔ Y ≠ X' ⊔ Y' → X ⊔ Y ⋖ π →
      X ⊔ Y ≠ m := by
    intro X Y X' Y' hX hY hXY hX' hY' hX'Y' hX'_on hY'_on h_sides h_cov h_eq
    have hU_le : U ≤ X ⊔ Y := h_eq ▸ hU_on_m
    have hX'Y'_le : X' ⊔ Y' ≤ X ⊔ Y :=
      sup_le (le_trans hX'_on (sup_le hU_le le_sup_left))
             (le_trans hY'_on (sup_le hU_le le_sup_right))
    -- X'⊔Y' < X⊔Y is impossible: line_height_two says X'⊔Y' is an atom,
    -- but X' ≤ X'⊔Y' with X' an atom gives X' = X'⊔Y', so Y' ≤ X' = Y'. ✗
    have h_eq' : X' ⊔ Y' = X ⊔ Y := by
      by_contra h_ne
      have h_lt : X' ⊔ Y' < X ⊔ Y := lt_of_le_of_ne hX'Y'_le h_ne
      have h_pos : ⊥ < X' ⊔ Y' := lt_of_lt_of_le hX'.bot_lt le_sup_left
      have h_atom := line_height_two hX hY hXY h_pos h_lt
      -- X' ≤ X'⊔Y' and X'⊔Y' is an atom: X' = ⊥ or X' = X'⊔Y'.
      have := (h_atom.le_iff.mp le_sup_left).resolve_left hX'.1
      -- X' = X'⊔Y', so Y' ≤ X'. Y' atom ≤ X' atom → Y' = X'. ✗
      exact hX'Y' ((hX'.le_iff.mp (this ▸ le_sup_right)).resolve_left hY'.1).symm
    exact h_sides h_eq'.symm
  have hAB_ne_m : A ⊔ B ≠ m := side_ne_m hA hB hAB hA' hB' hA'B' hA'_on hB'_on h_sides_AB h_cov_AB
  have hAC_ne_m : A ⊔ C ≠ m := side_ne_m hA hC hAC hA' hC' hA'C' hA'_on hC'_on h_sides_AC h_cov_AC
  have hBC_ne_m : B ⊔ C ≠ m := side_ne_m hB hC hBC hB' hC' hB'C' hB'_on hC'_on h_sides_BC h_cov_BC
  -- ── Helper: primed side ≠ m ──
  -- If B'⊔C' = m: from B' ≤ U⊔B and B' ≤ m, modular law gives B' ≤ U⊔(B⊓m).
  -- If B ≱ m, B⊓m = ⊥, so B' ≤ U, hence B' = U. ✗ So B ≤ m. Similarly C ≤ m.
  -- Then B⊔C ≤ m, so B⊔C = m. ✗
  have hB'C'_ne_m : B' ⊔ C' ≠ m := by
    intro h_eq
    have hB'_le_m : B' ≤ m := h_eq ▸ le_sup_left
    have hC'_le_m : C' ≤ m := h_eq ▸ le_sup_right
    have hB_le_m : B ≤ m := by
      by_contra hB_not
      have : B ⊓ m = ⊥ := (hB.le_iff.mp inf_le_left).resolve_right
        (fun h => hB_not (h ▸ inf_le_right))
      have hB'_le : B' ≤ U ⊔ B ⊓ m := by
        rw [← sup_inf_assoc_of_le B hU_on_m]; exact le_inf hB'_on hB'_le_m
      rw [this, sup_bot_eq] at hB'_le
      exact hUB' ((hU.le_iff.mp hB'_le).resolve_left hB'.1).symm
    have hC_le_m : C ≤ m := by
      by_contra hC_not
      have : C ⊓ m = ⊥ := (hC.le_iff.mp inf_le_left).resolve_right
        (fun h => hC_not (h ▸ inf_le_right))
      have hC'_le : C' ≤ U ⊔ C ⊓ m := by
        rw [← sup_inf_assoc_of_le C hU_on_m]; exact le_inf hC'_on hC'_le_m
      rw [this, sup_bot_eq] at hC'_le
      exact hUC' ((hU.le_iff.mp hC'_le).resolve_left hC'.1).symm
    exact hBC_ne_m ((h_cov_BC.eq_or_eq (sup_le hB_le_m hC_le_m) hm_le).resolve_right
      hm_ne).symm
  -- ── Helpers: primed sides ⋖ π ──
  -- If Z' ≤ X'⊔Y', then X'⊔Y' = π. Then (X'⊔Y')⊓m = m, so (X⊔Y)⊓m = m,
  -- so m ≤ X⊔Y, so X⊔Y = m. ✗
  have primed_cov : ∀ {X' Y' Z' : L},
      IsAtom X' → IsAtom Y' → IsAtom Z' →
      X' ≠ Y' → X' ≠ Z' → Y' ≠ Z' →
      ∀ {X Y : L}, X ⊔ Y ⋖ π → X ⊔ Y ≠ m →
      X' ⊔ Y' ⊔ Z' = π → (X ⊔ Y) ⊓ m = (X' ⊔ Y') ⊓ m →
      X' ⊔ Y' ⋖ π := by
    intro X' Y' Z' hX' hY' hZ' hX'Y' hX'Z' hY'Z' X Y h_cov h_ne_m h_span h_par
    have hZ'_not : ¬ Z' ≤ X' ⊔ Y' := by
      intro hle
      have hXY'_eq : X' ⊔ Y' = π :=
        (sup_eq_left.mpr hle).symm.trans h_span
      have hm_le_XY : m ≤ X ⊔ Y := by
        have h1 : (X' ⊔ Y') ⊓ m = m := by rw [hXY'_eq]; exact inf_eq_right.mpr hm_le
        have h2 : (X ⊔ Y) ⊓ m = m := h_par.trans h1
        exact le_of_eq h2.symm |>.trans inf_le_left
      exact h_ne_m ((hm_cov.eq_or_eq hm_le_XY h_cov.le).resolve_right (ne_of_lt h_cov.lt))
    rw [← h_span]
    exact line_covBy_plane hX' hY' hZ' hX'Y' hX'Z' hY'Z' hZ'_not
  have h_cov_A'B' : A' ⊔ B' ⋖ π :=
    primed_cov hA' hB' hC' hA'B' hA'C' hB'C' h_cov_AB hAB_ne_m hπB h_par_AB
  have h_cov_A'C' : A' ⊔ C' ⋖ π := by
    have : A' ⊔ C' ⊔ B' = π := by
      rw [show A' ⊔ C' ⊔ B' = A' ⊔ B' ⊔ C' from by ac_rfl]; exact hπB
    exact primed_cov hA' hC' hB' hA'C' hA'B' hB'C'.symm h_cov_AC hAC_ne_m this h_par_AC
  -- ── Step 2: Side intersections lie on m ──
  have h_meet_cov_AB : (A ⊔ B) ⊓ (A' ⊔ B') ⋖ (A ⊔ B) :=
    (planes_meet_covBy h_cov_AB h_cov_A'B' h_sides_AB).1
  have h_meet_cov_AC : (A ⊔ C) ⊓ (A' ⊔ C') ⋖ (A ⊔ C) :=
    (planes_meet_covBy h_cov_AC h_cov_A'C' h_sides_AC).1
  have h_mAB_cov : (A ⊔ B) ⊓ m ⋖ (A ⊔ B) :=
    (planes_meet_covBy h_cov_AB hm_cov hAB_ne_m).1
  have h_mAC_cov : (A ⊔ C) ⊓ m ⋖ (A ⊔ C) :=
    (planes_meet_covBy h_cov_AC hm_cov hAC_ne_m).1
  have hP_AB_le : (A ⊔ B) ⊓ m ≤ (A ⊔ B) ⊓ (A' ⊔ B') :=
    le_inf inf_le_left (h_par_AB ▸ inf_le_left)
  have h₁₂_on_m : (A ⊔ B) ⊓ (A' ⊔ B') ≤ m :=
    (h_mAB_cov.eq_or_eq hP_AB_le h_meet_cov_AB.lt.le).elim
      (fun h => h ▸ inf_le_right) (fun h => absurd h (ne_of_lt h_meet_cov_AB.lt))
  have hP_AC_le : (A ⊔ C) ⊓ m ≤ (A ⊔ C) ⊓ (A' ⊔ C') :=
    le_inf inf_le_left (h_par_AC ▸ inf_le_left)
  have h₁₃_on_m : (A ⊔ C) ⊓ (A' ⊔ C') ≤ m :=
    (h_mAC_cov.eq_or_eq hP_AC_le h_meet_cov_AC.lt.le).elim
      (fun h => h ▸ inf_le_right) (fun h => absurd h (ne_of_lt h_meet_cov_AC.lt))
  -- ── Step 3: axis = m, hence h₂₃ ≤ m ──
  have h₁₂_ne_bot : (A ⊔ B) ⊓ (A' ⊔ B') ≠ ⊥ := by
    intro h; rw [h] at h_meet_cov_AB
    exact h_meet_cov_AB.2 hA.bot_lt (atom_covBy_join hA hB hAB).lt
  have h₁₃_ne_bot : (A ⊔ C) ⊓ (A' ⊔ C') ≠ ⊥ := by
    intro h; rw [h] at h_meet_cov_AC
    exact h_meet_cov_AC.2 hA.bot_lt (atom_covBy_join hA hC hAC).lt
  have h₁₂_atom : IsAtom ((A ⊔ B) ⊓ (A' ⊔ B')) :=
    line_height_two hA hB hAB (bot_lt_iff_ne_bot.mpr h₁₂_ne_bot) h_meet_cov_AB.lt
  have h₁₃_atom : IsAtom ((A ⊔ C) ⊓ (A' ⊔ C')) :=
    line_height_two hA hC hAC (bot_lt_iff_ne_bot.mpr h₁₃_ne_bot) h_meet_cov_AC.lt
  -- Distinct: if equal, P ≤ (A⊔B)⊓(A⊔C) = A and P ≤ (A'⊔B')⊓(A'⊔C') = A', so A = A'. ✗
  have hC_not_AB : ¬ C ≤ A ⊔ B := by
    intro hle; exact ne_of_lt h_cov_AB.lt (sup_eq_left.mpr hle ▸ hπA)
  have h₁₂_ne_h₁₃ : (A ⊔ B) ⊓ (A' ⊔ B') ≠ (A ⊔ C) ⊓ (A' ⊔ C') := by
    intro h_eq
    have hC'_not_A'B' : ¬ C' ≤ A' ⊔ B' := by
      intro hle; exact ne_of_lt h_cov_A'B'.lt (sup_eq_left.mpr hle ▸ hπB)
    have hP_le_A : (A ⊔ B) ⊓ (A' ⊔ B') ≤ A := le_trans
      (le_inf inf_le_left (le_trans (le_of_eq h_eq) inf_le_left))
      (le_of_eq (modular_intersection hA hB hC hAB hAC hBC hC_not_AB))
    have hP_le_A' : (A ⊔ B) ⊓ (A' ⊔ B') ≤ A' := le_trans
      (le_inf inf_le_right (le_trans (le_of_eq h_eq) inf_le_right))
      (le_of_eq (modular_intersection hA' hB' hC' hA'B' hA'C' hB'C' hC'_not_A'B'))
    exact hAA' ((hA.le_iff.mp hP_le_A).resolve_left h₁₂_atom.1 |>.symm |>.trans
      ((hA'.le_iff.mp hP_le_A').resolve_left h₁₂_atom.1))
  -- h₁₂ = (A⊔B)⊓m and h₁₂ ⋖ m.
  have h₁₂_cov_m : (A ⊔ B) ⊓ (A' ⊔ B') ⋖ m := by
    have h₁₂_eq : (A ⊔ B) ⊓ (A' ⊔ B') = (A ⊔ B) ⊓ m :=
      (h_mAB_cov.eq_or_eq hP_AB_le h_meet_cov_AB.lt.le).elim
        id (fun h => absurd h (ne_of_lt h_meet_cov_AB.lt))
    exact h₁₂_eq ▸ (planes_meet_covBy h_cov_AB hm_cov hAB_ne_m).2
  -- Two distinct atoms on m span m. h₁₂ ⋖ join ≤ m and h₁₂ ⋖ m → join = m.
  have h_lt_join : (A ⊔ B) ⊓ (A' ⊔ B') < (A ⊔ B) ⊓ (A' ⊔ B') ⊔ (A ⊔ C) ⊓ (A' ⊔ C') := by
    apply lt_of_le_of_ne le_sup_left
    intro h; exact h₁₂_ne_h₁₃ ((h₁₂_atom.le_iff.mp (h ▸ le_sup_right)).resolve_left h₁₃_atom.1).symm
  have h_join_eq_m : (A ⊔ B) ⊓ (A' ⊔ B') ⊔ (A ⊔ C) ⊓ (A' ⊔ C') = m :=
    (h₁₂_cov_m.eq_or_eq h_lt_join.le (sup_le h₁₂_on_m h₁₃_on_m)).resolve_left
      (ne_of_gt h_lt_join)
  have h_axis_eq_m : axis = m :=
    (hm_cov.eq_or_eq (h_join_eq_m ▸ sup_le h₁₂ h₁₃) h_axis_le).resolve_right h_axis_ne
  have h₂₃_on_m : (B ⊔ C) ⊓ (B' ⊔ C') ≤ m := h_axis_eq_m ▸ h₂₃
  -- ── Step 4: (B⊔C)⊓m = (B'⊔C')⊓m ──
  -- First derive B'⊔C' ⋖ π: if B'⊔C' = π, then (B⊔C)⊓(B'⊔C') = B⊔C ≤ m, so B⊔C = m. ✗
  have h_cov_B'C' : B' ⊔ C' ⋖ π := by
    have hA'_not : ¬ A' ≤ B' ⊔ C' := by
      intro hle
      have hB'C'_eq_π : B' ⊔ C' = π := by
        have : A' ⊔ B' ⊔ C' = B' ⊔ C' := by
          rw [show A' ⊔ B' ⊔ C' = B' ⊔ C' ⊔ A' from by ac_rfl]; exact sup_eq_left.mpr hle
        rw [this] at hπB; exact hπB
      -- (B⊔C)⊓(B'⊔C') = (B⊔C)⊓π = B⊔C (since B⊔C ≤ π)
      have : (B ⊔ C) ⊓ (B' ⊔ C') = B ⊔ C := by
        rw [hB'C'_eq_π]; exact inf_eq_left.mpr h_cov_BC.le
      -- B⊔C ≤ m from h₂₃_on_m, so B⊔C = m. ✗
      have hBC_le_m : B ⊔ C ≤ m := this ▸ h₂₃_on_m
      exact hBC_ne_m ((h_cov_BC.eq_or_eq hBC_le_m hm_le).resolve_right hm_ne).symm
    rw [← hπB, show A' ⊔ B' ⊔ C' = B' ⊔ C' ⊔ A' from by ac_rfl]
    exact line_covBy_plane hB' hC' hA' hB'C' hA'B'.symm hA'C'.symm hA'_not
  -- Now the covering argument works.
  have h_meet_cov_BC : (B ⊔ C) ⊓ (B' ⊔ C') ⋖ (B ⊔ C) :=
    (planes_meet_covBy h_cov_BC h_cov_B'C' h_sides_BC).1
  have h_meet_cov_BC' : (B ⊔ C) ⊓ (B' ⊔ C') ⋖ (B' ⊔ C') :=
    (planes_meet_covBy h_cov_BC h_cov_B'C' h_sides_BC).2
  have h_mBC_cov : (B ⊔ C) ⊓ m ⋖ (B ⊔ C) :=
    (planes_meet_covBy h_cov_BC hm_cov hBC_ne_m).1
  have h_mB'C'_cov : (B' ⊔ C') ⊓ m ⋖ (B' ⊔ C') :=
    (planes_meet_covBy h_cov_B'C' hm_cov hB'C'_ne_m).1
  have hBC_eq : (B ⊔ C) ⊓ m = (B ⊔ C) ⊓ (B' ⊔ C') :=
    (h_meet_cov_BC.eq_or_eq (le_inf inf_le_left h₂₃_on_m) h_mBC_cov.lt.le).elim id
      (fun h => absurd h (ne_of_lt h_mBC_cov.lt))
  have hB'C'_eq : (B' ⊔ C') ⊓ m = (B ⊔ C) ⊓ (B' ⊔ C') :=
    (h_meet_cov_BC'.eq_or_eq (le_inf inf_le_right h₂₃_on_m) h_mB'C'_cov.lt.le).elim id
      (fun h => absurd h (ne_of_lt h_mB'C'_cov.lt))
  rw [hBC_eq, hB'C'_eq]



end Foam.FTPGExplore
