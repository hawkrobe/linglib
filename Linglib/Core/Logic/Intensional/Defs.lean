import Mathlib.Logic.Basic

/-!
# Polymorphic Kripke Foundation

@cite{kripke-1963}

The bare foundation for accessibility-restricted modal logic, parameterised
by `{W : Type*}` — no Frame, no Entity, no type system. This file holds the
definitions and very simple lemmas that the rest of `Core.IntensionalLogic`
(including Montague's S5 `box`/`diamond` in `Quantification.lean` and the
modal-axiom theorems in `RestrictedModality.lean`) builds on.

`Defs.lean` is the foundation file in mathlib's sense: just the data and the
relationships among frame conditions. Modal axiom correspondence theorems
(K/T/D/4/B/5), monotonicity, distribution, restriction, the Logic lattice,
and the Gallin hierarchy live in `RestrictedModality.lean`.
-/

namespace Core.IntensionalLogic

-- ────────────────────────────────────────────────────────────────
-- §1 Accessibility Relations
-- ────────────────────────────────────────────────────────────────

/-- An accessibility relation on worlds. `R w v` means world `v` is
    accessible from world `w`. -/
abbrev AccessRel (W : Type*) := W → W → Prop

/-- Agent-indexed accessibility relation: each agent has their own
    accessibility relation over worlds. -/
abbrev AgentAccessRel (W E : Type*) := E → AccessRel W

/-- Universal accessibility: every world is accessible from every world. -/
def universalR {W : Type*} : AccessRel W := fun _ _ => True

/-- Empty accessibility: no world is accessible from any world. -/
def emptyR {W : Type*} : AccessRel W := fun _ _ => False

/-- Reflexive (identity) accessibility: each world accesses only itself. -/
def identityR {W : Type*} : AccessRel W := fun w v => w = v

-- ────────────────────────────────────────────────────────────────
-- §2 Frame Conditions
-- ────────────────────────────────────────────────────────────────

/-- Reflexivity: every world accesses itself. -/
def IsReflexive {W : Type*} (R : AccessRel W) : Prop := ∀ w, R w w

/-- Seriality: every world accesses at least one world. -/
def IsSerial {W : Type*} (R : AccessRel W) : Prop := ∀ w, ∃ v, R w v

/-- Transitivity. -/
def IsTransitive {W : Type*} (R : AccessRel W) : Prop := ∀ w v u, R w v → R v u → R w u

/-- Symmetry. -/
def IsSymmetric {W : Type*} (R : AccessRel W) : Prop := ∀ w v, R w v → R v w

/-- Euclideanness. -/
def IsEuclidean {W : Type*} (R : AccessRel W) : Prop := ∀ w v u, R w v → R w u → R v u

-- ────────────────────────────────────────────────────────────────
-- §3 Frame Condition Relationships
-- ────────────────────────────────────────────────────────────────

variable {W : Type*}

theorem universalR_refl : IsReflexive (universalR (W := W)) := fun _ => trivial
theorem universalR_serial : IsSerial (universalR (W := W)) := fun w => ⟨w, trivial⟩
theorem universalR_trans : IsTransitive (universalR (W := W)) := fun _ _ _ _ _ => trivial
theorem universalR_symm : IsSymmetric (universalR (W := W)) := fun _ _ _ => trivial
theorem universalR_eucl : IsEuclidean (universalR (W := W)) := fun _ _ _ _ _ => trivial

theorem refl_serial {R : AccessRel W} (h : IsReflexive R) : IsSerial R :=
  fun w => ⟨w, h w⟩

theorem refl_eucl_symm {R : AccessRel W} (hR : IsReflexive R) (hE : IsEuclidean R) : IsSymmetric R :=
  fun w v hwv => hE w v w hwv (hR w)

theorem refl_eucl_trans {R : AccessRel W} (hR : IsReflexive R) (hE : IsEuclidean R) : IsTransitive R :=
  fun w v u hwv hvu => hE v w u (refl_eucl_symm hR hE w v hwv) hvu

theorem symm_trans_eucl {R : AccessRel W} (hS : IsSymmetric R) (hT : IsTransitive R) : IsEuclidean R :=
  fun w v u hwv hwu => hT v w u (hS w v hwv) hwu

/-- S5 frames are equivalence relations. -/
theorem S5_equiv {R : AccessRel W} (hR : IsReflexive R) (hE : IsEuclidean R) :
    IsReflexive R ∧ IsSymmetric R ∧ IsTransitive R :=
  ⟨hR, refl_eucl_symm hR hE, refl_eucl_trans hR hE⟩

/-- S4 frames are preorders. -/
theorem S4_preorder {R : AccessRel W} (hR : IsReflexive R) (hT : IsTransitive R) :
    IsReflexive R ∧ IsTransitive R := ⟨hR, hT⟩

/-- M implies D (reflexive implies serial). -/
theorem M_implies_D {R : AccessRel W} (hM : IsReflexive R) : IsSerial R :=
  refl_serial hM

/-- M + 5 implies B. -/
theorem M5_implies_B {R : AccessRel W} (hM : IsReflexive R) (h5 : IsEuclidean R) : IsSymmetric R :=
  refl_eucl_symm hM h5

/-- M + 5 implies 4. -/
theorem M5_implies_4 {R : AccessRel W} (hM : IsReflexive R) (h5 : IsEuclidean R) : IsTransitive R :=
  refl_eucl_trans hM h5

-- ────────────────────────────────────────────────────────────────
-- §4 Restricted Box and Diamond
-- ────────────────────────────────────────────────────────────────

/-- Restricted necessity: `□_R p` at world `w` holds iff `p v` for all
    `v` accessible from `w`.

    `⟦□_R φ⟧^w = 1` iff `⟦φ⟧^v = 1` for all `v` with `R(w,v)`.

    This is the Kripke generalization of DWP's Rule B.13 (`box`); the
    `Core.IntensionalLogic.box` operator in `Quantification.lean` is the
    universal-accessibility special case. -/
def boxR (R : AccessRel W) (p : W → Prop) (w : W) : Prop :=
  ∀ v, R w v → p v

/-- Restricted possibility: `◇_R p` at world `w` holds iff `p v` for some
    `v` accessible from `w`. Dual of `boxR`. -/
def diamondR (R : AccessRel W) (p : W → Prop) (w : W) : Prop :=
  ∃ v, R w v ∧ p v

-- ────────────────────────────────────────────────────────────────
-- §5 Duality
-- ────────────────────────────────────────────────────────────────

/-- `□_R p ↔ ¬◇_R ¬p` — restricted modal duality. -/
theorem boxR_neg_diamondR (R : AccessRel W) (p : W → Prop) (w : W) :
    boxR R p w = ¬(diamondR R (fun v => ¬(p v)) w) := by
  simp only [boxR, diamondR, not_exists, not_and, not_not]

/-- `◇_R p ↔ ¬□_R ¬p` — dual form. -/
theorem diamondR_neg_boxR (R : AccessRel W) (p : W → Prop) (w : W) :
    diamondR R p w = ¬(boxR R (fun v => ¬(p v)) w) := by
  simp only [diamondR, boxR]
  exact propext ⟨
    fun ⟨v, hwv, hpv⟩ h => h v hwv hpv,
    fun h => Classical.byContradiction fun hne => by
      simp only [not_exists, not_and] at hne
      exact h (fun v hwv => hne v hwv)⟩

end Core.IntensionalLogic
