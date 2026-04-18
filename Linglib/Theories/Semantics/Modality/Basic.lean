/-
Modal Theory Infrastructure.

Defines `ModalTheory` for comparing derived-accessibility
semantics with Simple/primitive-accessibility semantics.

- @cite{kratzer-1991}
- @cite{kripke-1963}
-/

import Linglib.Theories.Semantics.Attitudes.Intensional

namespace Semantics.Modality

open Semantics.Attitudes.Intensional

/-- Modal force: necessity (□) or possibility (◇). Reuses `Core.Modality.ModalForce`. -/
abbrev ModalForce := Core.Modality.ModalForce

/-- A semantic theory for modal auxiliaries. `eval` is `Prop`-valued at the
generic `World → Prop` proposition type; `decEval` bundles a `Decidable`
instance parameterized by `[DecidablePred p]` so concrete instantiations
remain computable via `decide` whenever the proposition is decidable. -/
structure ModalTheory where
  /-- Name of the theory. -/
  name : String
  /-- Academic citation. -/
  citation : String
  /-- Core evaluation: does modal force applied to proposition `p` hold at world `w`? -/
  eval : ModalForce → (World → Prop) → World → Prop
  /-- Decidability of `eval` whenever the proposition itself is decidable. -/
  decEval : ∀ (f : ModalForce) (p : World → Prop) [DecidablePred p] (w : World),
    Decidable (eval f p w)

instance (T : ModalTheory) (f : ModalForce) (p : World → Prop) [DecidablePred p] (w : World) :
    Decidable (T.eval f p w) := T.decEval f p w

section DerivedNotions

/-- Necessity operator: □p is true at w. -/
def ModalTheory.necessity (T : ModalTheory) (p : World → Prop) (w : World) : Prop :=
  T.eval .necessity p w

instance (T : ModalTheory) (p : World → Prop) [DecidablePred p] (w : World) :
    Decidable (T.necessity p w) := by unfold ModalTheory.necessity; infer_instance

/-- Possibility operator: ◇p is true at w. -/
def ModalTheory.possibility (T : ModalTheory) (p : World → Prop) (w : World) : Prop :=
  T.eval .possibility p w

instance (T : ModalTheory) (p : World → Prop) [DecidablePred p] (w : World) :
    Decidable (T.possibility p w) := by unfold ModalTheory.possibility; infer_instance

/-- Weak necessity operator: □wφ is true at w.
    **Note**: For Kratzer semantics, weak necessity differs from strong necessity
    in the *ordering source*, not the quantifier. Use `Directive.weakNecessity`
    (which takes a secondary ordering source) for the proper @cite{vonfintel-iatridou-2008}
    semantics. Calling `T.eval .weakNecessity` on a `KratzerTheory` returns
    the same result as `T.eval .necessity` — the distinction lives in which
    `KratzerParams` you pass, not in the force enum. -/
def ModalTheory.weakNecessity (T : ModalTheory) (p : World → Prop) (w : World) : Prop :=
  T.eval .weakNecessity p w

instance (T : ModalTheory) (p : World → Prop) [DecidablePred p] (w : World) :
    Decidable (T.weakNecessity p w) := by unfold ModalTheory.weakNecessity; infer_instance

/-- Consistency check: □p → ◇p. -/
def ModalTheory.necessityEntailsPossibility (T : ModalTheory) (p : World → Prop) (w : World) : Prop :=
  T.necessity p w → T.possibility p w

instance (T : ModalTheory) (p : World → Prop) [DecidablePred p] (w : World) :
    Decidable (T.necessityEntailsPossibility p w) := by
  unfold ModalTheory.necessityEntailsPossibility; infer_instance

/-- Duality check: □p ↔ ¬◇¬p at world w. -/
def ModalTheory.dualityHolds (T : ModalTheory) (p : World → Prop) (w : World) : Prop :=
  T.necessity p w ↔ ¬ T.possibility (fun w' => ¬ p w') w

instance (T : ModalTheory) (p : World → Prop) [DecidablePred p] (w : World) :
    Decidable (T.dualityHolds p w) := by
  unfold ModalTheory.dualityHolds; infer_instance

/-- Check duality across all worlds for a proposition. -/
def ModalTheory.checkDuality (T : ModalTheory) (p : World → Prop) : Prop :=
  ∀ w : World, T.dualityHolds p w

instance (T : ModalTheory) (p : World → Prop) [DecidablePred p] :
    Decidable (T.checkDuality p) := by
  unfold ModalTheory.checkDuality; infer_instance

/-- Check consistency across all worlds for a proposition. -/
def ModalTheory.checkConsistency (T : ModalTheory) (p : World → Prop) : Prop :=
  ∀ w : World, T.necessityEntailsPossibility p w

instance (T : ModalTheory) (p : World → Prop) [DecidablePred p] :
    Decidable (T.checkConsistency p) := by
  unfold ModalTheory.checkConsistency; infer_instance

end DerivedNotions

section Properties

/-- A theory is normal iff duality holds universally: ∀ p w, □p ↔ ¬◇¬p. -/
def ModalTheory.isNormal (T : ModalTheory) : Prop :=
  ∀ (p : World → Prop) (w : World), T.dualityHolds p w

/-- A theory is consistent iff □p → ◇p universally (D axiom / seriality). -/
def ModalTheory.isConsistent (T : ModalTheory) : Prop :=
  ∀ (p : World → Prop) (w : World), T.necessityEntailsPossibility p w

end Properties

end Semantics.Modality
