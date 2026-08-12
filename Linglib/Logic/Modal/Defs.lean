import Mathlib.Logic.Basic
import Mathlib.Logic.Relator
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.PropInstances

/-!
# Modal operators and frame conditions

This file defines the relational `box`/`diamond` of Kripke semantics
([kripke-1963]) and the frame conditions of modal correspondence theory
for accessibility relations `W → W → Prop`; the `Set`-valued mathlib
counterparts of the operators are `Rel.core` and `Rel.preimage`.
-/

namespace ModalLogic

variable {W : Type*} (R : W → W → Prop)

/-! ### Box and diamond -/

/-- Restricted necessity: `box R p w` holds iff `p v` for all `v`
    accessible from `w`. -/
def box (p : W → Prop) (w : W) : Prop :=
  ∀ v, R w v → p v

/-- Restricted possibility: `diamond R p w` holds iff `p v` for some `v`
    accessible from `w`. Dual of `box`. -/
def diamond (p : W → Prop) (w : W) : Prop :=
  ∃ v, R w v ∧ p v

@[inherit_doc] scoped notation:max "□[" R "]" => box R
@[inherit_doc] scoped notation:max "◇[" R "]" => diamond R

/-! ### Duality -/

/-- Push negation through `box`: `¬□p ↔ ◇¬p`. -/
@[simp] theorem not_box (p : W → Prop) (w : W) :
    ¬ □[R] p w ↔ ◇[R] (fun v => ¬ p v) w := by
  simp [box, diamond, not_forall]

/-- Push negation through `diamond`: `¬◇p ↔ □¬p`. -/
@[simp] theorem not_diamond (p : W → Prop) (w : W) :
    ¬ ◇[R] p w ↔ □[R] (fun v => ¬ p v) w := by
  simp [box, diamond, not_and]

/-! ### Frame conditions -/

/-- `R` is **serial** if every world accesses at least one world. -/
class IsSerial : Prop where
  serial : Relator.LeftTotal R

/-- `R` is **Euclidean** if from any pair of `R`-successors of `w`, each is
    an `R`-successor of the other. -/
class IsEuclidean : Prop where
  eucl : ∀ w v u, R w v → R w u → R v u

/-! ### Frame implications and instances -/

variable {R}

-- Seriality, symmetry, and transitivity of `⊤` follow from the two
-- instances below via the derivations that follow.
instance : Std.Refl (⊤ : W → W → Prop) := ⟨fun _ => trivial⟩
instance : IsEuclidean (⊤ : W → W → Prop) := ⟨fun _ _ _ _ _ => trivial⟩

/-- Reflexive relations are serial. -/
instance [hR : Std.Refl R] : IsSerial R where serial w := ⟨w, hR.refl w⟩

/-- Reflexive + Euclidean implies symmetric. -/
instance [hR : Std.Refl R] [hE : IsEuclidean R] : Std.Symm R where
  symm w v hwv := hE.eucl w v w hwv (hR.refl w)

/-- Reflexive + Euclidean implies transitive. -/
instance [hR : Std.Refl R] [hE : IsEuclidean R] : IsTrans W R where
  trans w v u hwv hvu := hE.eucl v w u (hE.eucl w v w hwv (hR.refl w)) hvu

/-- Symmetric + transitive implies euclidean. -/
instance [hS : Std.Symm R] [hT : IsTrans W R] : IsEuclidean R where
  eucl w v u hwv hwu := hT.trans v w u (hS.symm w v hwv) hwu

end ModalLogic
