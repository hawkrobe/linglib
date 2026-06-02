import Linglib.Semantics.Conditionals.Counterfactual

/-!
# McKay & Van Inwagen 1977 [mckay-vaninwagen-1977]

Counterfactuals with Disjunctive Antecedents.
*Philosophical Studies* 31: 353–356.

## Core Contribution

Defends [lewis-1973]'s variably strict conditional semantics against
the claim that **Simplification of Disjunctive Antecedents (SDA)** should
be valid:

    SDA: [(A ∨ B) > C] ⊃ (B > C)

Critics (Nute 1975, Fine 1975, Creary & Hill 1975) proposed SDA as a
validity constraint on counterfactual logic. McKay & Van Inwagen refute
this with two arguments:

1. **The bumper crop argument**: The English sentence "if good weather or
   sun cold, bumper crop" is false, but [lewis-1973]'s
   disjunctive-closure reading `(goodWeather ∨ sunCold) > bumperCrop` is
   true. So the English sentence is NOT equivalent to the
   disjunctive-closure reading. The correct regimentation is the
   conjunction `(goodWeather > bumperCrop) ∧ (sunCold > bumperCrop)`,
   which IS false — matching the English judgment.

2. **The Spain counterexample**: "If Spain had fought on the Axis side or
   the Allied side, Spain would have fought on the Axis side" is
   acceptable, but SDA gives the absurd "If Spain had fought on the
   Allied side, Spain would have fought on the Axis side."

## Substrate consumption

Both readings reduce to the canonical Lewis universal counterfactual
operator `Conditionals.Counterfactual.universalCounterfactual`. The
disjunctive-closure reading evaluates the operator on `A ∨ B`; the
conjunction regimentation conjoins per-disjunct evaluations.
Worlds and predicates are typed `Prop` (not `Bool`) — DecidablePred
instances are auto-derived from `DecidableEq` on the world enums.
-/

namespace McKayVanInwagen1977

open Core.Order (SimilarityOrdering)
open Semantics.Conditionals.Counterfactual (universalCounterfactual)


-- ════════════════════════════════════════════════════
-- The Bumper Crop Argument: S ≠ S*
-- ════════════════════════════════════════════════════

/-!
## The Bumper Crop Argument

The critics argue that Lewis's semantics is wrong using the sentence:

  S: "If we were to have good weather this summer or if the sun were to
      grow cold, we would have a bumper crop."

They claim S is equivalent to the regimented counterfactual
S* = (goodWeather ∨ sunCold) > bumperCrop. Since Lewis's semantics
makes S* true (the closest (goodWeather ∨ sunCold)-world has good
weather, hence bumper crop) but S is clearly false, Lewis must be wrong.

McKay & Van Inwagen's rebuttal: premise (2) is false — S is NOT
equivalent to S*. The correct regimentation of S is the conjunction
(goodWeather > bumperCrop) ∧ (sunCold > bumperCrop), which IS false on
Lewis's semantics, matching the English judgment.
-/

section BumperCrop

inductive CropWorld where | actual | goodWeather | sunCold
  deriving Repr, DecidableEq

instance : Fintype CropWorld where
  elems := {.actual, .goodWeather, .sunCold}
  complete x := by cases x <;> simp

/-- Good weather is much more similar to the actual world than the sun
    growing cold. -/
def cropSim : SimilarityOrdering CropWorld := .ofBool
  (fun _ w₁ w₂ => w₁ == w₂ || (w₁ == .goodWeather && w₂ == .sunCold))
  (by decide) (by decide)

/-- "Good weather" world predicate. -/
def goodWeather (w : CropWorld) : Prop := w = .goodWeather
/-- "Sun cold" world predicate. -/
def sunCold (w : CropWorld) : Prop := w = .sunCold
/-- "Bumper crop" world predicate. True at the good-weather world. -/
def bumperCrop (w : CropWorld) : Prop := w = .goodWeather

instance : DecidablePred goodWeather := fun w => decEq w .goodWeather
instance : DecidablePred sunCold := fun w => decEq w .sunCold
instance : DecidablePred bumperCrop := fun w => decEq w .goodWeather

/-- S* (Lewis disjunctive closure) is TRUE: the closest
    (goodWeather ∨ sunCold)-world is a good-weather world. This is
    premise (3) of the critics' argument. -/
theorem bumperCrop_lewis_true :
    universalCounterfactual cropSim
      (fun w => goodWeather w ∨ sunCold w) bumperCrop .actual := by decide

/-- The conjunction regimentation is FALSE:
    "if the sun grew cold, we'd have a bumper crop" is false.
    This matches the English judgment that S is false. -/
theorem bumperCrop_conjunction_false :
    ¬ (universalCounterfactual cropSim goodWeather bumperCrop .actual ∧
       universalCounterfactual cropSim sunCold bumperCrop .actual) := by
  decide

/-- Lewis's disjunctive closure is true while the conjunction
    regimentation is false. Since the English sentence S is false
    (matching the conjunction) while S* is true (matching Lewis),
    S ≠ S*: premise (2) is false. -/
theorem lewis_ne_conjunction :
    universalCounterfactual cropSim
      (fun w => goodWeather w ∨ sunCold w) bumperCrop .actual ∧
    ¬ (universalCounterfactual cropSim goodWeather bumperCrop .actual ∧
       universalCounterfactual cropSim sunCold bumperCrop .actual) :=
  ⟨bumperCrop_lewis_true, bumperCrop_conjunction_false⟩

end BumperCrop

-- ════════════════════════════════════════════════════
-- The Spain Counterexample to SDA
-- ════════════════════════════════════════════════════

/-!
## The Spain Example

"Neither. Spain did not enter the war. But if she had fought on one side
or the other, it would have been the Axis."

That is, we assert: (Axis ∨ Allies) > Axis. This is true on Lewis's
semantics (Spain was ideologically closer to the Axis).

But if SDA were valid, it would follow that: Allies > Axis — "If Spain
had fought on the Allied side, Spain would have fought on the Axis side."
This is absurd.
-/

section Spain

inductive SpainWorld where | actual | axis | allies
  deriving Repr, DecidableEq

instance : Fintype SpainWorld where
  elems := {.actual, .axis, .allies}
  complete x := by cases x <;> simp

/-- Axis is closer to actual than Allies (Spain's ideological alignment). -/
def spainSim : SimilarityOrdering SpainWorld := .ofBool
  (fun _ w₁ w₂ => w₁ == w₂ || (w₁ == .axis && w₂ == .allies))
  (by decide) (by decide)

/-- "Spain fought with the Axis" world predicate. -/
def foughtAxis (w : SpainWorld) : Prop := w = .axis
/-- "Spain fought with the Allies" world predicate. -/
def foughtAllies (w : SpainWorld) : Prop := w = .allies

instance : DecidablePred foughtAxis := fun w => decEq w .axis
instance : DecidablePred foughtAllies := fun w => decEq w .allies

/-- Lewis's disjunctive-closure reading is TRUE: the closest
    (Axis ∨ Allies)-world is the Axis-world, which satisfies C.
    The English sentence "if she had fought on one side or the other,
    it would have been the Axis" is acceptable. -/
theorem spain_lewis_true :
    universalCounterfactual spainSim
      (fun w => foughtAxis w ∨ foughtAllies w) foughtAxis .actual := by
  decide

/-- The absurd SDA simplification: "If Spain had fought on the Allied
    side, Spain would have fought on the Axis side" is false. This is
    what the SDA schema would derive from `spain_lewis_true`. -/
theorem allies_implies_axis_false :
    ¬ universalCounterfactual spainSim foughtAllies foughtAxis .actual := by
  decide

/-- The conjunction reading (both simplifications must hold) is FALSE,
    because the Allies simplification fails. -/
theorem spain_conjunction_false :
    ¬ (universalCounterfactual spainSim foughtAxis foughtAxis .actual ∧
       universalCounterfactual spainSim foughtAllies foughtAxis .actual) := by
  decide

/-- **SDA is not a valid schema for counterfactuals.** There exist
    propositions A, B, C and a world w such that (A ∨ B) > C is true
    but B > C is false. The Spain example: (Axis ∨ Allies) > Axis is
    true, but Allies > Axis is false. -/
theorem sda_invalid :
    ∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
      (sim : SimilarityOrdering W) (A B C : W → Prop)
      (_ : DecidablePred A) (_ : DecidablePred B) (_ : DecidablePred C)
      (w : W),
      universalCounterfactual sim (fun v => A v ∨ B v) C w ∧
      ¬ universalCounterfactual sim B C w :=
  ⟨SpainWorld, inferInstance, inferInstance, spainSim,
   foughtAxis, foughtAllies, foughtAxis,
   inferInstance, inferInstance, inferInstance, .actual,
   spain_lewis_true, allies_implies_axis_false⟩

end Spain

end McKayVanInwagen1977
