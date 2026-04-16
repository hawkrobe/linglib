/-
Modal Theory Infrastructure.

Defines `ModalTheory` for comparing derived-accessibility
semantics with Simple/primitive-accessibility semantics.

- Kratzer, A. (1991). Modality. In Semantics: An International Handbook.
- Kripke, S. (1963). Semantical Considerations on Modal Logic.
-/

import Linglib.Theories.Semantics.Attitudes.Intensional

namespace Semantics.Modality

open Semantics.Attitudes.Intensional

section CoreTypes

/-- Modal force: necessity (□) or possibility (◇). Reuses `Core.Modality.ModalForce`. -/
abbrev ModalForce := Core.Modality.ModalForce

/-- A proposition is a function from worlds to truth values. -/
abbrev Proposition := BProp World

/-- The set of all worlds (from Attitudes.lean). -/
def allWorlds' : List World := allWorlds

/-- Modal.Proposition equals Core.Proposition.BProp World. -/
theorem proposition_eq_bprop : Proposition = Core.Proposition.BProp World := rfl

end CoreTypes

/-- A semantic theory for modal auxiliaries, with eval : ModalForce -> Proposition -> World -> Bool. -/
structure ModalTheory where
  /-- Name of the theory. -/
  name : String
  /-- Academic citation. -/
  citation : String
  /-- Core evaluation function: is modal force applied to proposition p true at world w? -/
  eval : ModalForce → Proposition → World → Bool

section DerivedNotions

/-- Necessity operator: □p is true at w. -/
def ModalTheory.necessity (T : ModalTheory) (p : Proposition) (w : World) : Bool :=
  T.eval .necessity p w

/-- Possibility operator: ◇p is true at w. -/
def ModalTheory.possibility (T : ModalTheory) (p : Proposition) (w : World) : Bool :=
  T.eval .possibility p w

/-- Weak necessity operator: □wφ is true at w.
    **Note**: For Kratzer semantics, weak necessity differs from strong necessity
    in the *ordering source*, not the quantifier. Use `Directive.weakNecessity`
    (which takes a secondary ordering source) for the proper von Fintel & Iatridou
    (2008) semantics. Calling `T.eval .weakNecessity` on a `KratzerTheory` returns
    the same result as `T.eval .necessity` — the distinction lives in which
    `KratzerParams` you pass, not in the force enum. -/
def ModalTheory.weakNecessity (T : ModalTheory) (p : Proposition) (w : World) : Bool :=
  T.eval .weakNecessity p w

/-- Consistency check: □p -> ◇p. -/
def ModalTheory.necessityEntailsPossibility (T : ModalTheory) (p : Proposition) (w : World) : Bool :=
  !T.necessity p w || T.possibility p w

/-- Duality check: □p ↔ ¬◇¬p at world w. -/
def ModalTheory.dualityHolds (T : ModalTheory) (p : Proposition) (w : World) : Bool :=
  let notP : Proposition := λ w' => !p w'
  let lhs := T.necessity p w
  let rhs := !T.possibility notP w
  lhs == rhs

/-- Check duality across all worlds for a proposition. -/
def ModalTheory.checkDuality (T : ModalTheory) (p : Proposition) : Bool :=
  allWorlds'.all λ w => T.dualityHolds p w

/-- Check consistency across all worlds for a proposition. -/
def ModalTheory.checkConsistency (T : ModalTheory) (p : Proposition) : Bool :=
  allWorlds'.all λ w => T.necessityEntailsPossibility p w

end DerivedNotions

section Properties

/-- A theory is normal iff duality holds universally: ∀ p w, □p ↔ ¬◇¬p. -/
def ModalTheory.isNormal (T : ModalTheory) : Prop :=
  ∀ (p : Proposition) (w : World), T.dualityHolds p w = true

/-- A theory is consistent iff □p -> ◇p universally (D axiom / seriality). -/
def ModalTheory.isConsistent (T : ModalTheory) : Prop :=
  ∀ (p : Proposition) (w : World), T.necessityEntailsPossibility p w = true

end Properties

end Semantics.Modality
