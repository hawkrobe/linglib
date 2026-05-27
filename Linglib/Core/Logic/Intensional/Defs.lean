import Mathlib.Logic.Basic
import Mathlib.Order.Defs.Unbundled

/-!
# Polymorphic Kripke Foundation

@cite{kripke-1963}

The bare foundation for accessibility-restricted modal logic, parameterised
by `{W : Type*}` — no Frame, no Entity, no type system. This file holds the
definitions and very simple lemmas that the rest of `Core.Logic.Intensional`
(including Montague's S5 `box`/`diamond` in `Quantification.lean` and the
modal-axiom theorems in `RestrictedModality.lean`) builds on.

`Defs.lean` is the foundation file in mathlib's sense: just the data and the
relationships among frame conditions. Modal axiom correspondence theorems
(K/T/D/4/B/5), monotonicity, distribution, restriction, the Logic lattice,
and the Gallin hierarchy live in `RestrictedModality.lean`.
-/

namespace Core.Logic.Intensional

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
-- §2 Modal-Specific Frame Conditions
-- ────────────────────────────────────────────────────────────────

/-! Reflexivity, symmetry, and transitivity are `Std.Refl R`,
    `Std.Symm R`, `IsTrans W R` from Lean core + mathlib. Seriality
    and Euclideanness are modal-logic-specific and defined here. -/

/-- Seriality: every world accesses at least one world.

    Identical as a `Prop` to `Mathlib.Logic.Relator.LeftTotal R`, but
    packaged as a class with the modal-logic-canonical name. -/
class IsSerial {W : Type*} (R : AccessRel W) : Prop where
  serial : ∀ w, ∃ v, R w v

/-- Euclideanness: from any pair of `R`-successors of `w`, each is an
    `R`-successor of the other. No mathlib analogue (modal-specific). -/
class IsEuclidean {W : Type*} (R : AccessRel W) : Prop where
  eucl : ∀ w v u, R w v → R w u → R v u

-- ────────────────────────────────────────────────────────────────
-- §3 Bundled Frame Classes
-- ────────────────────────────────────────────────────────────────

/-- S4 frame: reflexive + transitive. -/
class IsS4Frame {W : Type*} (R : AccessRel W) : Prop extends Std.Refl R, IsTrans W R

/-- S5 frame: reflexive + euclidean (implies symmetric + transitive). -/
class IsS5Frame {W : Type*} (R : AccessRel W) : Prop extends Std.Refl R, IsEuclidean R

/-- KD45 frame for textbook belief: serial + transitive + euclidean. -/
class IsKD45Frame {W : Type*} (R : AccessRel W) : Prop
  extends IsSerial R, IsTrans W R, IsEuclidean R

/-- K4-Eucl frame: transitive + euclidean, NOT serial. The frame condition
    for commitment in @cite{stalnaker-1984}-style discourse models, where
    commitment violations (no accessible compliance world) must be
    expressible. -/
class IsK4EuclFrame {W : Type*} (R : AccessRel W) : Prop
  extends IsTrans W R, IsEuclidean R

/-- KT frame: reflexive. (T axiom alone.) -/
class IsKTFrame {W : Type*} (R : AccessRel W) : Prop extends Std.Refl R

/-- KTB frame: reflexive + symmetric. The natural setting for tolerance
    semantics (@cite{cobreros-etal-2012}) where each predicate's
    similarity relation is reflexive and symmetric but possibly
    non-transitive. -/
class IsKTBFrame {W : Type*} (R : AccessRel W) : Prop
  extends Std.Refl R, Std.Symm R

/-- `Rb` is a *belief refinement* of `Rk`: every belief-accessible world is
    knowledge-accessible. The pure subset condition; whether `Rk` is S5
    and `Rb` is KD45 is asserted by separate instance declarations. -/
class IsBeliefRefinementOf {W : Type*} (Rk Rb : AccessRel W) : Prop where
  sub : ∀ w v, Rb w v → Rk w v

-- ────────────────────────────────────────────────────────────────
-- §4 Frame Condition Relationships and Instances
-- ────────────────────────────────────────────────────────────────

variable {W : Type*}

instance universalR_isRefl : Std.Refl (universalR (W := W)) := ⟨fun _ => trivial⟩
instance universalR_isSerial : IsSerial (universalR (W := W)) := ⟨fun w => ⟨w, trivial⟩⟩
instance universalR_isTrans : IsTrans W (universalR (W := W)) :=
  ⟨fun _ _ _ _ _ => trivial⟩
instance universalR_isSymm : Std.Symm (universalR (W := W)) := ⟨fun _ _ _ => trivial⟩
instance universalR_isEuclidean : IsEuclidean (universalR (W := W)) :=
  ⟨fun _ _ _ _ _ => trivial⟩

/-- Reflexive relations are serial. -/
instance (priority := 100) Std.Refl.toIsSerial {R : AccessRel W} [h : Std.Refl R] :
    IsSerial R := ⟨fun w => ⟨w, h.refl w⟩⟩

/-- Reflexive + Euclidean implies symmetric. -/
instance (priority := 100) {R : AccessRel W} [hR : Std.Refl R] [hE : IsEuclidean R] :
    Std.Symm R :=
  ⟨fun w v hwv => hE.eucl w v w hwv (hR.refl w)⟩

/-- Reflexive + Euclidean implies transitive. -/
instance (priority := 100) {R : AccessRel W} [hR : Std.Refl R] [hE : IsEuclidean R] :
    IsTrans W R :=
  ⟨fun w v u hwv hvu => hE.eucl v w u (Std.Symm.symm w v hwv) hvu⟩

/-- Symmetric + transitive implies euclidean. -/
instance (priority := 100) {R : AccessRel W} [hS : Std.Symm R] [hT : IsTrans W R] :
    IsEuclidean R :=
  ⟨fun w v u hwv hwu => hT.trans v w u (hS.symm w v hwv) hwu⟩

-- ────────────────────────────────────────────────────────────────
-- §4 Restricted Box and Diamond
-- ────────────────────────────────────────────────────────────────

/-- Restricted necessity: `□_R p` at world `w` holds iff `p v` for all
    `v` accessible from `w`.

    `⟦□_R φ⟧^w = 1` iff `⟦φ⟧^v = 1` for all `v` with `R(w,v)`.

    This is the Kripke generalization of DWP's Rule B.13 (`box`); the
    `Core.Logic.Intensional.box` operator in `Quantification.lean` is the
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

end Core.Logic.Intensional
