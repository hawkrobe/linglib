import Linglib.Theories.Semantics.Conditionals.AlternativeSensitive

/-!
# McKay & Van Inwagen 1977 @cite{mckay-vaninwagen-1977}

Counterfactuals with Disjunctive Antecedents.
*Philosophical Studies* 31: 353–356.

## Core Contribution

Defends Lewis's variably strict conditional semantics against the claim
that **Simplification of Disjunctive Antecedents (SDA)** should be valid:

    SDA: [(A ∨ B) > C] ⊃ (B > C)

Critics (Nute 1975, Fine 1975, Creary & Hill 1975) proposed SDA as a
validity constraint on counterfactual logic. McKay & Van Inwagen refute
this with two arguments:

1. **The bumper crop argument**: The English sentence "if good weather or
   sun cold, bumper crop" is false, but Lewis's disjunctive-closure
   reading (goodWeather ∨ sunCold) > bumperCrop is true. So the English
   sentence is NOT equivalent to the disjunctive-closure reading. The
   correct regimentation is the conjunction (goodWeather > bumperCrop) ∧
   (sunCold > bumperCrop), which IS false — matching the English judgment.

2. **The Spain counterexample**: "If Spain had fought on the Axis side or
   the Allied side, Spain would have fought on the Axis side" is
   acceptable, but SDA gives the absurd "If Spain had fought on the
   Allied side, Spain would have fought on the Axis side."

## Integration

- The conjunction regimentation corresponds to `sdaEval` in
  `AlternativeSensitive.lean`
- Lewis's disjunctive-closure semantics corresponds to `lewisDAC`
-/

namespace Phenomena.Conditionals.Studies.McKayVanInwagen1977

open Semantics.Conditionals.Counterfactual (closestWorldsB)
open Semantics.Conditionals.AlternativeSensitive (lewisDAC sdaEval)

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

/-- Good weather is much more similar to the actual world than the sun
    growing cold. -/
def cropCloser : CropWorld → CropWorld → CropWorld → Bool
  | _, w₁, w₂ => w₁ == w₂ || (w₁ == .goodWeather && w₂ == .sunCold)

def cropDomain : List CropWorld := [.actual, .goodWeather, .sunCold]
def goodWeather : CropWorld → Bool | .goodWeather => true | _ => false
def sunCold : CropWorld → Bool | .sunCold => true | _ => false
def bumperCrop : CropWorld → Bool | .goodWeather => true | _ => false

/-- S* (Lewis disjunctive closure) is TRUE: the closest
    (goodWeather ∨ sunCold)-world is a good-weather world. This is
    premise (3) of the critics' argument. -/
theorem bumperCrop_lewis_true :
    lewisDAC cropCloser cropDomain goodWeather sunCold
      bumperCrop .actual = true := by native_decide

/-- The conjunction regimentation is FALSE:
    "if the sun grew cold, we'd have a bumper crop" is false.
    This matches the English judgment that S is false. -/
theorem bumperCrop_conjunction_false :
    sdaEval cropCloser cropDomain [goodWeather, sunCold]
      bumperCrop .actual = false := by native_decide

/-- Lewis's disjunctive closure and the conjunction regimentation diverge.
    Since the English sentence S is false (matching the conjunction) while
    S* is true (matching Lewis), S ≠ S*: premise (2) is false. -/
theorem lewis_ne_conjunction :
    lewisDAC cropCloser cropDomain goodWeather sunCold bumperCrop .actual ≠
    sdaEval cropCloser cropDomain [goodWeather, sunCold] bumperCrop .actual := by
  native_decide

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

/-- Axis is closer to actual than Allies (Spain's ideological alignment). -/
def spainCloser : SpainWorld → SpainWorld → SpainWorld → Bool
  | _, w₁, w₂ => w₁ == w₂ || (w₁ == .axis && w₂ == .allies)

def spainDomain : List SpainWorld := [.actual, .axis, .allies]
def foughtAxis : SpainWorld → Bool | .axis => true | _ => false
def foughtAllies : SpainWorld → Bool | .allies => true | _ => false

/-- Lewis's disjunctive-closure reading is TRUE: the closest
    (Axis ∨ Allies)-world is the Axis-world, which satisfies C.
    The English sentence "if she had fought on one side or the other,
    it would have been the Axis" is acceptable. -/
theorem spain_lewis_true :
    lewisDAC spainCloser spainDomain foughtAxis foughtAllies
      foughtAxis .actual = true := by native_decide

/-- The absurd SDA simplification: "If Spain had fought on the Allied
    side, Spain would have fought on the Axis side" is false. This is
    what the SDA schema would derive from `spain_lewis_true`. -/
theorem allies_implies_axis_false :
    sdaEval spainCloser spainDomain [foughtAllies]
      foughtAxis .actual = false := by native_decide

/-- The conjunction reading (both simplifications must hold) is FALSE,
    because the Allies simplification fails. -/
theorem spain_conjunction_false :
    sdaEval spainCloser spainDomain [foughtAxis, foughtAllies]
      foughtAxis .actual = false := by native_decide

/-- **SDA is not a valid schema for counterfactuals.** There exist
    propositions A, B, C and a world w such that (A ∨ B) > C is true
    but B > C is false. The Spain example: (Axis ∨ Allies) > Axis is
    true, but Allies > Axis is false. -/
theorem sda_invalid :
    ∃ (W : Type) (_ : DecidableEq W) (closer : W → W → W → Bool)
      (domain : List W) (A B C : W → Bool) (w : W),
      lewisDAC closer domain A B C w = true ∧
      sdaEval closer domain [B] C w = false :=
  ⟨SpainWorld, inferInstance, spainCloser, spainDomain,
   foughtAxis, foughtAllies, foughtAxis, .actual,
   ⟨by native_decide, by native_decide⟩⟩

end Spain

-- ════════════════════════════════════════════════════
-- Summary: The Two Readings Diverge
-- ════════════════════════════════════════════════════

/-!
## Divergence of Readings

In both examples, Lewis's disjunctive closure (`lewisDAC`) returns true
while the conjunction regimentation (`sdaEval`) returns false. But the
English judgments differ:
- Spain: the English sentence is **acceptable** (matches Lewis)
- Bumper crop: the English sentence is **unacceptable** (matches conjunction)

This shows that natural-language "or" in counterfactual antecedents does
not uniformly correspond to either formal reading. The ambiguity is
between conjunction/SDA (each disjunct evaluated separately) and Lewis's
disjunctive closure (disjuncts combined before evaluation).
-/

/-- Both examples show the two formal readings diverge: Lewis gives true,
    conjunction gives false. The English judgments select different
    readings in each case — confirming that natural-language "or" in
    counterfactual antecedents is ambiguous between the two. -/
theorem readings_diverge :
    (lewisDAC spainCloser spainDomain foughtAxis foughtAllies
       foughtAxis .actual = true ∧
     sdaEval spainCloser spainDomain [foughtAxis, foughtAllies]
       foughtAxis .actual = false) ∧
    (lewisDAC cropCloser cropDomain goodWeather sunCold
       bumperCrop .actual = true ∧
     sdaEval cropCloser cropDomain [goodWeather, sunCold]
       bumperCrop .actual = false) :=
  ⟨⟨spain_lewis_true, spain_conjunction_false⟩,
   ⟨bumperCrop_lewis_true, bumperCrop_conjunction_false⟩⟩

end Phenomena.Conditionals.Studies.McKayVanInwagen1977
