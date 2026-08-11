import Mathlib.Logic.Basic
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.PropInstances

/-!
# Frame conditions and modal operators

This file defines the frame conditions of modal correspondence theory for
accessibility relations `W → W → Prop`, and the relational `box`/`diamond`
of Kripke semantics ([kripke-1963]).
-/

namespace ModalLogic

/-! ### Frame conditions -/

/-! Reflexivity, symmetry, and transitivity are `Std.Refl R`,
    `Std.Symm R`, `IsTrans W R` from Lean core + mathlib. Seriality
    and Euclideanness are modal-logic-specific and defined here. -/

/-- Seriality: every world accesses at least one world.

    Identical as a `Prop` to `Mathlib.Logic.Relator.LeftTotal R`, but
    packaged as a class with the modal-logic-canonical name. -/
class IsSerial {W : Type*} (R : W → W → Prop) : Prop where
  serial : ∀ w, ∃ v, R w v

/-- Euclideanness: from any pair of `R`-successors of `w`, each is an
    `R`-successor of the other. No mathlib analogue (modal-specific). -/
class IsEuclidean {W : Type*} (R : W → W → Prop) : Prop where
  eucl : ∀ w v u, R w v → R w u → R v u

/-- `Rb` is a *belief refinement* of `Rk`: every belief-accessible world is
    knowledge-accessible. The pure subset condition; whether `Rk` is S5
    and `Rb` is KD45 is asserted by separate instance declarations. -/
class IsBeliefRefinementOf {W : Type*} (Rk Rb : W → W → Prop) : Prop where
  sub : ∀ w v, Rb w v → Rk w v

/-! ### Frame implications and instances

The universal relation is `⊤ : W → W → Prop` and the empty relation `⊥`,
via the pointwise lattice on relations. -/

variable {W : Type*}

instance : Std.Refl (⊤ : W → W → Prop) := ⟨fun _ => trivial⟩
instance : IsSerial (⊤ : W → W → Prop) := ⟨fun w => ⟨w, trivial⟩⟩
instance : IsTrans W (⊤ : W → W → Prop) := ⟨fun _ _ _ _ _ => trivial⟩
instance : Std.Symm (⊤ : W → W → Prop) := ⟨fun _ _ _ => trivial⟩
instance : IsEuclidean (⊤ : W → W → Prop) := ⟨fun _ _ _ _ _ => trivial⟩

/-- Reflexive relations are serial. -/
instance (priority := 100) Std.Refl.toIsSerial {R : W → W → Prop} [h : Std.Refl R] :
    IsSerial R := ⟨fun w => ⟨w, h.refl w⟩⟩

/-- Reflexive + Euclidean implies symmetric. -/
instance (priority := 100) {R : W → W → Prop} [hR : Std.Refl R] [hE : IsEuclidean R] :
    Std.Symm R :=
  ⟨fun w v hwv => hE.eucl w v w hwv (hR.refl w)⟩

/-- Reflexive + Euclidean implies transitive. -/
instance (priority := 100) {R : W → W → Prop} [hR : Std.Refl R] [hE : IsEuclidean R] :
    IsTrans W R :=
  ⟨fun w v u hwv hvu => hE.eucl v w u (Std.Symm.symm w v hwv) hvu⟩

/-- Symmetric + transitive implies euclidean. -/
instance (priority := 100) {R : W → W → Prop} [hS : Std.Symm R] [hT : IsTrans W R] :
    IsEuclidean R :=
  ⟨fun w v u hwv hwu => hT.trans v w u (hS.symm w v hwv) hwu⟩

/-! ### Box and diamond -/

/-- Restricted necessity: `□_R p` at world `w` holds iff `p v` for all
    `v` accessible from `w`.

    `⟦□_R φ⟧^w = 1` iff `⟦φ⟧^v = 1` for all `v` with `R(w,v)` — the Kripke
    generalization of the S5 necessity of [dowty-wall-peters-1981]'s IL,
    whose `Intensional.box` is the universal-accessibility special case. -/
def box (R : W → W → Prop) (p : W → Prop) (w : W) : Prop :=
  ∀ v, R w v → p v

/-- Restricted possibility: `◇_R p` at world `w` holds iff `p v` for some
    `v` accessible from `w`. Dual of `box`. -/
def diamond (R : W → W → Prop) (p : W → Prop) (w : W) : Prop :=
  ∃ v, R w v ∧ p v

/-! ### Duality -/

/-- Restricted modal duality: `□_R p ↔ ¬◇_R ¬p`. -/
theorem box_neg_diamond (R : W → W → Prop) (p : W → Prop) (w : W) :
    box R p w ↔ ¬ diamond R (fun v => ¬ p v) w :=
  ⟨fun hb ⟨v, hwv, hnp⟩ => hnp (hb v hwv),
   fun h v hwv => Classical.byContradiction fun hnp => h ⟨v, hwv, hnp⟩⟩

/-- Dual form: `◇_R p ↔ ¬□_R ¬p`. -/
theorem diamond_neg_box (R : W → W → Prop) (p : W → Prop) (w : W) :
    diamond R p w ↔ ¬ box R (fun v => ¬ p v) w :=
  ⟨fun ⟨v, hwv, hpv⟩ h => h v hwv hpv,
   fun h => Classical.byContradiction fun hne =>
     h fun v hwv hpv => hne ⟨v, hwv, hpv⟩⟩

end ModalLogic
