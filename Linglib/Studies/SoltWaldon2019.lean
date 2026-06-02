/-!
# [solt-waldon-2019]: Numerals under negation

Empirical data from Stephanie Solt and Brandon Waldon (2019), "Numerals under
negation," *Glossa* 4(1).

## Empirical contribution

A negative-numeral sentence ("She doesn't have 40 sheep") is degraded as an
answer to a "how many" question but acceptable as an answer to a polar
question. Solt & Waldon argue this licensing pattern reflects the QUD-relative
function of negated numerals as polar denials rather than quantitative answers.

## Provenance

This datum was previously bundled inside `Phenomena/Imprecision/Numerals.lean`
(then `Studies/Haslinger2025.lean`). Moved here at 0.230.521 — the empirical
anchor is Solt & Waldon 2019; Haslinger 2025 cites this work as background
substrate, not as her own observation.

-/

namespace SoltWaldon2019

/--
A negation-licensing datum for bare numerals.

Source: [solt-waldon-2019].
-/
structure NegationConstraintDatum where
  /-- Positive sentence -/
  positiveSentence : String
  /-- Negative sentence -/
  negativeSentence : String
  /-- "How many" question context -/
  howManyContext : String
  /-- Polar question context -/
  polarContext : String
  /-- Negative OK in how-many context? -/
  negativeOkHowMany : Bool
  /-- Negative OK in polar context? -/
  negativeOkPolar : Bool
  deriving Repr

def sheepNegation : NegationConstraintDatum :=
  { positiveSentence := "She has 40 sheep."
  , negativeSentence := "She doesn't have 40 sheep."
  , howManyContext := "A: How many sheep does Lisa have?"
  , polarContext := "A: Does Lisa really have 40 sheep?"
  , negativeOkHowMany := false  -- degraded as answer to how-many
  , negativeOkPolar := true     -- fine as answer to polar question
  }

def negationConstraintData : List NegationConstraintDatum :=
  [sheepNegation]

end SoltWaldon2019
