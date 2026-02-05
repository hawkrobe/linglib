/-
# Intensional Semantics Examples

Toy examples demonstrating intensional semantics phenomena:
- Hesperus/Phosphorus puzzle (co-reference vs co-intension)
- Belief contexts and substitution failure
- De dicto vs de re readings

These examples use the infrastructure from `Theories/Montague/Verb/Attitude/Examples.lean`.

Reference: Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English.
-/

import Linglib.Theories.Montague.Verb.Attitude.Examples

namespace Phenomena.Attitudes.IntensionalExamples

open Montague
open Montague.Verb.Attitude.Examples

/-- A small domain for examples -/
inductive ToyIEntity where
  | john
  | mary
  | hesperus  -- the morning star
  | phosphorus -- the evening star (= Venus, but potentially different in other worlds)
  deriving Repr, DecidableEq

def toyIModel : IModel := {
  Entity := ToyIEntity
  decEq := inferInstance
}

/-- "sleeps" as a world-dependent property. -/
def sleeps : toyIModel.interpTy (Ty.intens (.e ⇒ .t)) :=
  λ w x => match w, x with
    | .w0, .john => true
    | .w0, .mary => false
    | .w1, .john => false
    | .w1, .mary => true
    | .w2, .john => true
    | .w2, .mary => true
    | .w3, .john => false
    | .w3, .mary => false
    | _, _ => false

/-- "is happy" as a world-dependent property. -/
def happy : toyIModel.interpTy (Ty.intens (.e ⇒ .t)) :=
  λ w x => match w, x with
    | .w0, .john => true
    | .w0, .mary => true
    | .w1, .john => false
    | .w1, .mary => true
    | .w2, .john => true
    | .w2, .mary => false
    | .w3, .john => false
    | .w3, .mary => false
    | _, _ => false

/-- "the morning star" - an individual concept that picks out potentially
different individuals in different worlds. -/
def morningStar : toyIModel.interpTy Ty.indConcept :=
  λ w => match w with
    | .w0 => .hesperus
    | .w1 => .hesperus
    | .w2 => .phosphorus  -- different in w2!
    | .w3 => .hesperus

/-- "the evening star" - another individual concept -/
def eveningStar : toyIModel.interpTy Ty.indConcept :=
  λ w => match w with
    | .w0 => .hesperus
    | .w1 => .phosphorus  -- different in w1!
    | .w2 => .hesperus
    | .w3 => .hesperus

/-- In the actual world (w0), morning star = evening star.
But their INTENSIONS differ (they pick out different things in other worlds). -/
theorem extensions_equal_at_w0 :
    down morningStar .w0 = down eveningStar .w0 := rfl

theorem intensions_differ :
    morningStar ≠ eveningStar := by
  intro h
  have : morningStar .w1 = eveningStar .w1 := congrFun h .w1
  simp only [morningStar, eveningStar] at this
  cases this

/-- Doxastic accessibility relation: which worlds are compatible with
what an agent believes. R(a, w, w') means w' is compatible with what a believes in w. -/
def believes_access : ToyIEntity → World → World → Bool
  | .john, .w0, .w0 => true
  | .john, .w0, .w2 => true
  | .mary, .w0, .w1 => true
  | .mary, .w0, .w2 => true
  | _, w, w' => w == w'

/-- "believe" as an attitude verb.
⟦believe⟧(a)(p)(w) = ∀w'. R(a,w,w') → p(w') -/
def believe : toyIModel.interpTy (.e ⇒ Ty.prop ⇒ .t) :=
  λ agent prop =>
    allWorlds.all λ w' =>
      !believes_access agent .w0 w' || prop w'

/-- Extended believe that's world-dependent. -/
def believeAt : World → toyIModel.interpTy (.e ⇒ Ty.prop ⇒ .t) :=
  λ evalWorld agent prop =>
    allWorlds.all λ w' =>
      !believes_access agent evalWorld w' || prop w'

/-- "John believes Mary sleeps" (de dicto) -/
def johnBelievesMary_deDicto : toyIModel.interpTy .t :=
  let marySleeps : toyIModel.interpTy Ty.prop := λ w => sleeps w .mary
  believe .john marySleeps

#eval johnBelievesMary_deDicto  -- false

/-- "John believes John sleeps" (de dicto) -/
def johnBelievesJohnSleeps : toyIModel.interpTy .t :=
  let johnSleeps : toyIModel.interpTy Ty.prop := λ w => sleeps w .john
  believe .john johnSleeps

#eval johnBelievesJohnSleeps  -- true

/-- Proposition: "John ate some cookies" (simplified) -/
def someCookies : toyIModel.interpTy Ty.prop := λ _ => true

/-- Proposition: "John ate all cookies" (simplified) -/
def allCookies : toyIModel.interpTy Ty.prop :=
  λ w => match w with
    | .w0 | .w1 => true
    | .w2 | .w3 => false

/-- "Mary believes John ate some cookies" -/
def maryBelievesSome : toyIModel.interpTy .t := believe .mary someCookies

/-- "Mary believes John ate all cookies" -/
def maryBelievesAll : toyIModel.interpTy .t := believe .mary allCookies

#eval maryBelievesSome  -- true
#eval maryBelievesAll   -- depends on Mary's accessible worlds

/-- Belief is intensional: co-extensional expressions can differ under belief. -/
theorem belief_intensional :
    (down morningStar .w0 = down eveningStar .w0)
    ∧ (morningStar ≠ eveningStar) := by
  constructor
  · rfl
  · intro h
    have : morningStar .w1 = eveningStar .w1 := congrFun h .w1
    simp only [morningStar, eveningStar] at this
    cases this

/-- Up-down identity: applying down after up returns the original value. -/
theorem up_down_identity {m : IModel} {τ : Ty} (x : m.interpTy τ) (w : World) :
    down (up x) w = x := rfl

end Phenomena.Attitudes.IntensionalExamples
