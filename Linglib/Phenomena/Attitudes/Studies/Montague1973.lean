import Linglib.Core.IntensionalLogic.Frame
import Linglib.Core.IntensionalLogic.Rigidity
import Mathlib.Data.Fin.Basic

/-! # Montague (1973) intensional examples @cite{montague-1973}

Toy examples in Montague's PTQ-style intensional logic:
- Hesperus/Phosphorus puzzle (co-reference vs co-intension)
- Belief contexts and substitution failure
- De dicto vs de re readings

Uses the infrastructure from
`Core/IntensionalLogic/Examples.lean`. -/

namespace Phenomena.Attitudes.Studies.Montague1973

abbrev World := Fin 4

open Core.IntensionalLogic

/-- A small domain for examples -/
inductive ToyIEntity where
  | john
  | mary
  | hesperus  -- the morning star
  | phosphorus -- the evening star (= Venus, but potentially different in other worlds)
  deriving Repr, DecidableEq

def toyIFrame : Frame := {
  Entity := ToyIEntity
  Index := World
}

/-- "sleeps" as a world-dependent property. -/
def sleeps : toyIFrame.Denot (Ty.intens (.e ⇒ .t)) :=
  λ (w : World) x => match w, x with
    | 0, .john => True
    | 1, .mary => True
    | 2, .john => True
    | 2, .mary => True
    | _, _ => False

/-- "is happy" as a world-dependent property. -/
def happy : toyIFrame.Denot (Ty.intens (.e ⇒ .t)) :=
  λ (w : World) x => match w, x with
    | 0, .john => True
    | 0, .mary => True
    | 1, .mary => True
    | 2, .john => True
    | _, _ => False

/-- "the morning star" - an individual concept that picks out potentially
different individuals in different worlds. -/
def morningStar : toyIFrame.Denot Ty.indConcept :=
  λ (w : World) => match w with
    | 0 => .hesperus
    | 1 => .hesperus
    | 2 => .phosphorus  -- different in w2!
    | 3 => .hesperus

/-- "the evening star" - another individual concept -/
def eveningStar : toyIFrame.Denot Ty.indConcept :=
  λ (w : World) => match w with
    | 0 => .hesperus
    | 1 => .phosphorus  -- different in w1!
    | 2 => .hesperus
    | 3 => .hesperus

/-- In the actual world (w0), morning star = evening star.
But their INTENSIONS differ (they pick out different things in other worlds). -/
theorem extensions_equal_at_w0 :
    down morningStar (0 : World) = down eveningStar (0 : World) := rfl

theorem intensions_differ :
    morningStar ≠ eveningStar := by
  intro h
  have : morningStar (1 : World) = eveningStar (1 : World) := congrFun h (1 : World)
  simp only [morningStar, eveningStar] at this
  cases this

/-- Doxastic accessibility relation: which worlds are compatible with
what an agent believes. R(a, w, w') means w' is compatible with what a believes in w. -/
def believes_access : ToyIEntity → World → World → Bool
  | .john, 0, 0 => true
  | .john, 0, 2 => true
  | .mary, 0, 1 => true
  | .mary, 0, 2 => true
  | _, w, w' => w == w'

/-- "believe" as an attitude verb.
⟦believe⟧(a)(p)(w) = ∀w'. R(a,w,w') → p(w') -/
def believe : toyIFrame.Denot (.e ⇒ Ty.prop ⇒ .t) :=
  λ agent prop =>
    ∀ w' : World, believes_access agent (0 : World) w' = true → prop w'

/-- Extended believe that's world-dependent. -/
def believeAt : World → toyIFrame.Denot (.e ⇒ Ty.prop ⇒ .t) :=
  λ evalWorld agent prop =>
    ∀ w' : World, believes_access agent evalWorld w' = true → prop w'

/-- "John believes Mary sleeps" (de dicto) -/
def johnBelievesMary_deDicto : toyIFrame.Denot .t :=
  let marySleeps : toyIFrame.Denot Ty.prop := λ w => sleeps w .mary
  believe .john marySleeps

/-- John does NOT believe Mary sleeps: Mary doesn't sleep in w0 (John's accessible world). -/
theorem johnDoesNotBelieveMarySleeps : ¬johnBelievesMary_deDicto := by
  intro h
  have := h (0 : World) rfl
  simp [sleeps] at this

/-- "John believes John sleeps" (de dicto) -/
def johnBelievesJohnSleeps : toyIFrame.Denot .t :=
  let johnSleeps : toyIFrame.Denot Ty.prop := λ w => sleeps w .john
  believe .john johnSleeps

/-- John believes he sleeps: he sleeps in both w0 and w2. -/
theorem johnBelievesJohnSleeps_true : johnBelievesJohnSleeps := by
  intro w' h
  match w', h with
  | 0, _ => simp [sleeps]
  | 1, h => simp [believes_access] at h
  | 2, _ => simp [sleeps]
  | 3, h => simp [believes_access] at h

/-- Proposition: "John ate some cookies" (simplified) -/
def someCookies : toyIFrame.Denot Ty.prop := λ _ => True

/-- Proposition: "John ate all cookies" (simplified) -/
def allCookies : toyIFrame.Denot Ty.prop :=
  λ (w : World) => match w with
    | 0 | 1 => True
    | 2 | 3 => False

/-- "Mary believes John ate some cookies" -/
def maryBelievesSome : toyIFrame.Denot .t := believe .mary someCookies

/-- "Mary believes John ate all cookies" -/
def maryBelievesAll : toyIFrame.Denot .t := believe .mary allCookies

/-- Mary believes John ate some cookies (trivially true proposition). -/
theorem maryBelievesSome_true : maryBelievesSome := by
  intro _ _; trivial

/-- Belief is intensional: co-extensional expressions can differ under belief. -/
theorem belief_intensional :
    (down morningStar (0 : World) = down eveningStar (0 : World))
    ∧ (morningStar ≠ eveningStar) := by
  constructor
  · rfl
  · intro h
    have : morningStar (1 : World) = eveningStar (1 : World) := congrFun h (1 : World)
    simp only [morningStar, eveningStar] at this
    cases this

/-- Up-down identity: applying down after up returns the original value. -/
theorem up_down_identity {F : Frame} {τ : Ty} (x : F.Denot τ) (w : F.Index) :
    down (up x) w = x := rfl

/-! ## Bridge to Direct Reference Theory

The `morningStar`/`eveningStar` individual concepts defined above are
*Fregean concepts* (world-dependent). In contrast, proper names in
`Semantics.Reference.Basic` are *Kripkean rigid designators*.

This section makes the distinction explicit, connecting the existing
Hesperus/Phosphorus examples to the direct reference framework. -/

/-- "Hesperus" as a Kripkean proper name: rigid designator.

Contrast with `morningStar` above, which is a Fregean individual concept
that varies across worlds. The proper name always returns `.hesperus`. -/
def hesperus_rigid : Core.Intension World ToyIEntity :=
  Core.Intension.rigid .hesperus

/-- `morningStar` is NOT rigid: it picks out different entities at
different worlds. This contrasts with `hesperus_rigid` which IS rigid. -/
theorem morningStar_not_rigid : ¬ Core.Intension.IsRigid morningStar := by
  intro h
  have h12 := h (1 : World) (2 : World)
  simp only [morningStar] at h12
  cases h12

/-- `hesperus_rigid` IS rigid (a proper name in the Kripkean sense). -/
theorem hesperus_rigid_isRigid : Core.Intension.IsRigid hesperus_rigid :=
  Core.Intension.rigid_isRigid _

/-- Independence of names vs concepts: a Fregean individual concept
(`morningStar`) can agree with a Kripkean name (`hesperus_rigid`) at
one world while diverging at others. -/
theorem name_vs_concept_independence :
    -- They agree at w0 (both pick out .hesperus)
    Core.Intension.CoRefer hesperus_rigid morningStar (0 : World) ∧
    -- But they are NOT co-extensional
    ¬ Core.Intension.CoExtensional hesperus_rigid morningStar := by
  constructor
  · -- CoRefer at w0: hesperus_rigid (0 : World) = morningStar (0 : World)
    rfl
  · -- Not co-extensional: they disagree at w2
    intro h
    have := h (2 : World)
    simp only [hesperus_rigid, Core.Intension.rigid, morningStar] at this
    cases this

end Phenomena.Attitudes.Studies.Montague1973
