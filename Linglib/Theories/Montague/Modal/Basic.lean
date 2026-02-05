/-
Modal Theory Infrastructure.

Defines `ModalTheory` for comparing Kratzer (1977, 1981, 1991) derived-accessibility
semantics with Simple/Kripke (1963) primitive-accessibility semantics.

- Kratzer, A. (1991). Modality. In Semantics: An International Handbook.
- Kripke, S. (1963). Semantical Considerations on Modal Logic.
-/

import Linglib.Theories.Montague.Verb.Attitude.Examples

namespace Montague.Modal

open Montague.Verb.Attitude.Examples

section CoreTypes

/-- Modal force: necessity (□) or possibility (◇). -/
inductive ModalForce where
  | necessity   -- must, have to, necessarily
  | possibility -- can, may, might, possibly
  deriving DecidableEq, BEq, Repr, Inhabited

instance : ToString ModalForce where
  toString
    | .necessity => "□"
    | .possibility => "◇"

/-- A proposition is a function from worlds to truth values. -/
abbrev Proposition := World → Bool

/-- The set of all worlds (from Attitudes.lean). -/
def allWorlds' : List World := allWorlds

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

section TestPropositions

/-- Proposition: it is raining. -/
def raining : Proposition := λ w =>
  match w with
  | .w0 => true
  | .w1 => true
  | .w2 => false
  | .w3 => false

/-- Proposition: the ground is wet. -/
def groundWet : Proposition := λ w =>
  match w with
  | .w0 => true
  | .w1 => true
  | .w2 => false
  | .w3 => true

/-- Proposition: John is home. -/
def johnHome : Proposition := λ w =>
  match w with
  | .w0 => true
  | .w1 => false
  | .w2 => true
  | .w3 => false

/-- A trivially true proposition (true at all worlds). -/
def triviallyTrue : Proposition := λ _ => true

/-- A trivially false proposition (false at all worlds). -/
def triviallyFalse : Proposition := λ _ => false

end TestPropositions

end Montague.Modal
