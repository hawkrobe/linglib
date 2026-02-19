/-
# Tessler & Franke (2020) "Not unreasonable"

RSA model for flexible negation: why two negatives don't make a positive.

## Innovation

The paper models why "not unhappy" != "happy" by treating the
contradictory/contrary distinction as lexical ambiguity:

1. **Contradictory negation**: not(x > theta) = x <= theta (complement)
2. **Contrary negation**: x < theta_neg where theta_neg < theta_pos (polar opposite with gap)

## Shared Infrastructure

This model uses the negation infrastructure from `Fragments.Degrees`:
- `NegationType`: contradictory vs. contrary
- `contraryNeg`, `contradictoryNeg`: semantic functions
- `inGapRegion`: check if degree is in the gap

## Simplified Model

We use 5 degrees with fixed thresholds:
- theta_neg = 2 (threshold for "unhappy")
- theta_pos = 3 (threshold for "happy")
- Gap region: degrees 2-3

## References

- Tessler & Franke (2020). Not unreasonable: Why two negatives don't make a positive.
- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.
-/

import Linglib.Theories.Pragmatics.RSA.Domains.Degrees
import Mathlib.Tactic.DeriveFintype

namespace RSA.TesslerFranke2020

open RSA.Domains.Degrees
open Core.Scale (Degree Degree.toNat Threshold.toNat deg thr allDegrees)
open Semantics.Lexical.Adjective (NegationType ThresholdPair
  positiveMeaning' contradictoryNeg contraryNegMeaning notContraryNegMeaning inGapRegion)

-- Domain: 5-point Happiness Scale

/--
Simplified happiness scale: 0 (miserable) to 4 (ecstatic).

Regions (using shared infrastructure):
- 0-1: Unhappy (below theta_neg = 2, `contraryNeg` is true)
- 2-3: Gap (`inGapRegion` is true)
- 4: Happy (above theta_pos = 3, `positiveMeaning` is true)
-/
abbrev HappinessDegree := Degree 4

def allHappinessDegrees : List HappinessDegree := allDegrees 4

-- Fixed thresholds using ThresholdPair from Fragments.Degrees
def happinessThresholds : ThresholdPair 4 :=
  { pos := ⟨⟨3, by omega⟩⟩  -- "happy" = degree > 3
  , neg := ⟨⟨2, by omega⟩⟩  -- "unhappy" (contrary) = degree < 2
  , gap_exists := by decide
  }

-- Utterances

inductive Utterance where
  | happy       -- "is happy"
  | notHappy    -- "is not happy"
  | unhappy     -- "is unhappy"
  | notUnhappy  -- "is not unhappy"
  | silent      -- say nothing
  deriving Repr, DecidableEq, BEq, Fintype

def allUtterances : List Utterance :=
  [.happy, .notHappy, .unhappy, .notUnhappy, .silent]

-- Lexica: How is "un-" interpreted?

/--
Two interpretations of morphological negation ("un-"):
- Contrary: polar opposite with gap (default for morphological antonyms)
- Contradictory: logical complement (marked, same as "not")

"not" is always contradictory in this model.

Uses `NegationType` from Fragments.Degrees.
-/
abbrev UnLexicon := NegationType

def allLexica : List UnLexicon := [.contrary, .contradictory]

/-- Prior: contrary is default for morphological negation -/
def lexiconPrior : UnLexicon → ℚ
  | .contrary => 3       -- Default for "un-"
  | .contradictory => 1  -- Marked interpretation

-- Semantics (using Fragments.Degrees infrastructure)

/-- Meaning given lexicon for "un-" interpretation -/
def meaning (L : UnLexicon) (u : Utterance) (d : HappinessDegree) : Bool :=
  let tp := happinessThresholds
  match u with
  | .happy => positiveMeaning' d tp
  | .silent => true
  | .notHappy => contradictoryNeg d tp.pos  -- "not" is always contradictory
  | .unhappy =>
    match L with
    | .contrary => contraryNegMeaning d tp
    | .contradictory => contradictoryNeg d tp.pos
  | .notUnhappy =>
    match L with
    | .contrary => notContraryNegMeaning d tp  -- includes gap!
    | .contradictory => positiveMeaning' d tp  -- collapses to "happy"

-- World Prior

def degreePrior : HappinessDegree → ℚ
  | ⟨⟨0, _⟩⟩ => 1
  | ⟨⟨1, _⟩⟩ => 2
  | ⟨⟨2, _⟩⟩ => 3
  | ⟨⟨3, _⟩⟩ => 2
  | ⟨⟨4, _⟩⟩ => 1
  | ⟨⟨n + 5, h⟩⟩ => absurd h (by omega)

-- Gap Analysis (using Fragments.Degrees infrastructure)

/-- Check whether a degree is in the gap region between the positive and
negative thresholds. This is the key semantic region that distinguishes
"not unhappy" from "happy". -/
def isInGap (d : HappinessDegree) : Bool :=
  inGapRegion d happinessThresholds

-- Theorems

/-- "happy" assigns zero probability to gap region (semantically).

With the positive threshold at 3, no degree in the gap region (2-3)
satisfies the positive meaning. -/
theorem happy_excludes_gap_semantically :
    ∀ d : HappinessDegree, isInGap d = true → meaning .contrary .happy d = false := by
  native_decide

/-- "not unhappy" with contrary lexicon includes the gap region.

With contrary negation, "unhappy" = degree < 2, so "not unhappy" = degree >= 2.
Degrees 2 and 3 are in the gap AND satisfy "not unhappy". -/
theorem not_unhappy_includes_gap_semantically :
    ∃ d : HappinessDegree, isInGap d = true ∧ meaning .contrary .notUnhappy d = true := by
  native_decide

/-- THE KEY INSIGHT: "not unhappy" != "happy" because "not unhappy" covers
the gap region while "happy" does not.

Under the contrary lexicon (the default for morphological negation),
"unhappy" = degree < theta_neg (polar opposite), so "not unhappy" includes
the gap region between theta_neg and theta_pos. "happy" = degree > theta_pos,
which excludes the gap.

This semantic difference drives the pragmatic distinction via RSA. -/
theorem not_unhappy_differs_from_happy_semantically :
    (∃ d : HappinessDegree, meaning .contrary .notUnhappy d = true ∧
                             meaning .contrary .happy d = false) := by
  native_decide

-- Summary

/-
## Tessler & Franke (2020): Not unreasonable

### The Puzzle
Why does "not unhappy" != "happy"?

### The Solution (using shared Fragments.Degrees infrastructure)
- `ThresholdPair`: theta_neg = 2 (for "unhappy"), theta_pos = 3 (for "happy")
- `inGapRegion`: degrees 2-3 are neither happy nor unhappy
- `contraryNegMeaning`: "unhappy" = degree < theta_neg
- `notContraryNegMeaning`: "not unhappy" = degree >= theta_neg (includes gap!)
- `positiveMeaning'`: "happy" = degree > theta_pos (excludes gap)

### Results
1. `happy_excludes_gap_semantically`: "happy" does not cover the gap
2. `not_unhappy_includes_gap_semantically`: "not unhappy" covers the gap
3. `not_unhappy_differs_from_happy_semantically`: Therefore they differ

### Architectural Note
This model imports `NegationType`, `contraryNeg`, `inGapRegion`, etc. from
`Fragments.Degrees`. Other models using gradable adjectives should also
engage with this infrastructure to handle the contrary/contradictory distinction.
-/

end RSA.TesslerFranke2020
