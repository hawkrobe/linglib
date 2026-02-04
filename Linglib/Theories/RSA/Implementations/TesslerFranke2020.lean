/-
# Tessler & Franke (2020) "Not unreasonable"

RSA model for flexible negation: why two negatives don't make a positive.

## Key Innovation

The paper models why "not unhappy" ≠ "happy" by treating the
contradictory/contrary distinction as lexical ambiguity:

1. **Contradictory negation**: ¬(x > θ) = x ≤ θ (complement)
2. **Contrary negation**: x < θ_neg where θ_neg < θ_pos (polar opposite with gap)

## Shared Infrastructure

This model uses the negation infrastructure from `Fragments.Degrees`:
- `NegationType`: contradictory vs. contrary
- `contraryNeg`, `contradictoryNeg`: semantic functions
- `inGapRegion`: check if degree is in the gap

## Simplified Model

We use 5 degrees with fixed thresholds:
- θ_neg = 2 (threshold for "unhappy")
- θ_pos = 3 (threshold for "happy")
- Gap region: degrees 2-3

## References

- Tessler & Franke (2020). Not unreasonable: Why two negatives don't make a positive.
- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.RSA.Domains.Degrees
import Mathlib.Data.Rat.Defs

namespace RSA.TesslerFranke2020

open RSA.Eval
open RSA.Domains.Degrees
open Montague.Domain.Degrees

-- Domain: 5-point Happiness Scale

/--
Simplified happiness scale: 0 (miserable) to 4 (ecstatic).

Regions (using shared infrastructure):
- 0-1: Unhappy (below θ_neg = 2, `contraryNeg` is true)
- 2-3: Gap (`inGapRegion` is true)
- 4: Happy (above θ_pos = 3, `positiveMeaning` is true)
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

-- RSA Computations with Lexical Uncertainty

/--
L1 marginal over worlds with lexical uncertainty.

This computes the pragmatic listener's posterior over degrees,
marginalizing over the two possible lexica for "un-".
-/
def l1_world_lexicalUncertainty (u : Utterance) : List (HappinessDegree × ℚ) :=
  RSA.Eval.L1_world allUtterances allHappinessDegrees [()] allLexica
    [()] [()]
    (fun _ l u' d => boolToRat (meaning l u' d))
    degreePrior
    (fun _ => 1)  -- interp prior
    lexiconPrior
    (fun _ => 1)  -- belief state prior
    (fun _ => 1)  -- goal prior
    (fun _ _ => 1)  -- speaker credence
    (fun _ d1 d2 => d1 == d2)  -- identity goal projection
    (fun _ => 0)  -- no cost
    1  -- α = 1
    u

/--
L1 marginal over lexica.

This computes the listener's posterior over lexica,
useful for seeing which interpretation is preferred.
-/
def l1_lexicon (u : Utterance) : List (UnLexicon × ℚ) :=
  let tuples := allHappinessDegrees.flatMap fun d =>
    allLexica.map fun l => (d, l)
  let scores := tuples.map fun (d, l) =>
    let priorScore := degreePrior d * lexiconPrior l
    let s1 := basicS1 allUtterances allHappinessDegrees
      (fun u' d' => boolToRat (meaning l u' d')) degreePrior 1 (fun _ => 0) d
    let s1Score := getScore s1 u
    ((d, l), priorScore * s1Score)
  let normalized := normalize scores
  -- Marginalize over degrees
  allLexica.map fun l =>
    let lScores := normalized.filter (fun ((_, l'), _) => l' == l) |>.map (·.2)
    (l, sumScores lScores)

-- Computations

def l1_happy : List (HappinessDegree × ℚ) := l1_world_lexicalUncertainty .happy
def l1_unhappy : List (HappinessDegree × ℚ) := l1_world_lexicalUncertainty .unhappy
def l1_notHappy : List (HappinessDegree × ℚ) := l1_world_lexicalUncertainty .notHappy
def l1_notUnhappy : List (HappinessDegree × ℚ) := l1_world_lexicalUncertainty .notUnhappy

def l1_lexicon_unhappy : List (UnLexicon × ℚ) := l1_lexicon .unhappy
def l1_lexicon_notUnhappy : List (UnLexicon × ℚ) := l1_lexicon .notUnhappy

-- Evaluate

#eval l1_happy       -- Should concentrate on degree 4
#eval l1_unhappy     -- Should concentrate on degrees 0, 1
#eval l1_notHappy    -- Should cover degrees 0-3
#eval l1_notUnhappy  -- Should cover degrees 2-4 (THE KEY: includes gap!)

#eval l1_lexicon_unhappy     -- Should prefer contrary
#eval l1_lexicon_notUnhappy  -- Lexicon inference for double negation

-- Gap Analysis (using Fragments.Degrees infrastructure)

def gapProb (dist : List (HappinessDegree × ℚ)) : ℚ :=
  dist.foldl (fun acc (d, p) =>
    if inGapRegion d happinessThresholds then acc + p else acc) 0

def gapProb_happy : ℚ := gapProb l1_happy
def gapProb_notUnhappy : ℚ := gapProb l1_notUnhappy

#eval gapProb_happy      -- Should be 0
#eval gapProb_notUnhappy -- Should be positive

-- Theorems

/-- "unhappy" prefers contrary lexicon (polar opposite) -/
theorem unhappy_prefers_contrary :
    getScore l1_lexicon_unhappy .contrary >
    getScore l1_lexicon_unhappy .contradictory := by
  native_decide

/-- "happy" assigns zero probability to gap region -/
theorem happy_excludes_gap : gapProb_happy = 0 := by native_decide

/-- "not unhappy" assigns positive probability to gap region -/
theorem not_unhappy_includes_gap : gapProb_notUnhappy > 0 := by native_decide

/-- THE KEY THEOREM: "not unhappy" ≠ "happy" -/
theorem not_unhappy_differs_from_happy :
    gapProb_notUnhappy > gapProb_happy := by native_decide

/-- "happy" → high degree, "unhappy" → low degree -/
theorem opposite_poles :
    getScore l1_happy ⟨⟨4, by omega⟩⟩ > getScore l1_happy ⟨⟨0, by omega⟩⟩ ∧
    getScore l1_unhappy ⟨⟨0, by omega⟩⟩ > getScore l1_unhappy ⟨⟨4, by omega⟩⟩ := by
  native_decide

-- Summary

/-
## Tessler & Franke (2020): Not unreasonable

### The Puzzle
Why does "not unhappy" ≠ "happy"?

### The Solution (using shared Fragments.Degrees infrastructure)
- `ThresholdPair`: θ_neg = 2 (for "unhappy"), θ_pos = 3 (for "happy")
- `inGapRegion`: degrees 2-3 are neither happy nor unhappy
- `contraryNegMeaning`: "unhappy" = degree < θ_neg
- `notContraryNegMeaning`: "not unhappy" = degree ≥ θ_neg (includes gap!)
- `positiveMeaning'`: "happy" = degree > θ_pos (excludes gap)

### Key Results
1. `unhappy_prefers_contrary`: Morphological negation → polar opposite
2. `happy_excludes_gap`: "happy" has zero probability in gap
3. `not_unhappy_includes_gap`: "not unhappy" has positive probability in gap
4. `not_unhappy_differs_from_happy`: Therefore they're not equivalent

### Architectural Note
This model imports `NegationType`, `contraryNeg`, `inGapRegion`, etc. from
`Fragments.Degrees`. Other models using gradable adjectives should also
engage with this infrastructure to handle the contrary/contradictory distinction.
-/

end RSA.TesslerFranke2020
