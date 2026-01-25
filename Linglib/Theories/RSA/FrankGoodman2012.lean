/-
# Frank & Goodman (2012)

"Predicting Pragmatic Reasoning in Language Games"
Science 336(6084): 998

This paper introduced the RSA (Rational Speech Acts) framework, showing that
pragmatic inferences in reference games can be predicted by modeling listeners
as reasoning about rational, informative speakers.

## The Reference Game

Context: {blue_square, blue_circle, green_square}
Utterances: {blue, green, square, circle}

## Key Result

L1("square") assigns higher probability to blue_square than green_square.

Why? A speaker wanting green_square would say "green" (uniquely identifying).
Saying "square" signals they probably mean blue_square.
-/

import Linglib.Core.RSA
import Linglib.Core.Frac

namespace RSA.FrankGoodman2012

open RSA Frac

-- ============================================================================
-- Domain: Objects and Utterances
-- ============================================================================

/-- Objects in the reference game context -/
inductive Object where
  | blue_square
  | blue_circle
  | green_square
  deriving Repr, DecidableEq, BEq

/-- Utterances (feature words) -/
inductive Utterance where
  | blue
  | green
  | square
  | circle
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Literal Semantics
-- ============================================================================

/-- Literal meaning: does utterance apply to object? -/
def meaning : Utterance → Object → Bool
  | .blue, .blue_square => true
  | .blue, .blue_circle => true
  | .blue, .green_square => false
  | .green, .blue_square => false
  | .green, .blue_circle => false
  | .green, .green_square => true
  | .square, .blue_square => true
  | .square, .blue_circle => false
  | .square, .green_square => true
  | .circle, .blue_square => false
  | .circle, .blue_circle => true
  | .circle, .green_square => false

-- ============================================================================
-- RSAScenario Instance (replaces FiniteSemanticBackend)
-- ============================================================================

/-- Reference game RSA scenario -/
def refGameScenario : ExactRSAScenario :=
  RSAScenario.ofBool
    [.blue, .green, .square, .circle]
    [.blue_square, .blue_circle, .green_square]
    (fun obj utt => meaning utt obj)

/-- Legacy alias -/
abbrev refGameBackend := refGameScenario

-- ============================================================================
-- Compute RSA Distributions
-- ============================================================================

/-- L0 for "blue" - uniform over blue objects -/
def l0_blue : List (Object × Frac) := RSA.L0 refGameScenario .blue

/-- L0 for "green" - only green_square -/
def l0_green : List (Object × Frac) := RSA.L0 refGameScenario .green

/-- L0 for "square" - uniform over squares -/
def l0_square : List (Object × Frac) := RSA.L0 refGameScenario .square

/-- S1 in blue_square world -/
def s1_blue_square : List (Utterance × Frac) := RSA.S1 refGameScenario .blue_square

/-- S1 in green_square world -/
def s1_green_square : List (Utterance × Frac) := RSA.S1 refGameScenario .green_square

/-- L1 for "square" - the key pragmatic inference -/
def l1_square : List (Object × Frac) := RSA.L1 refGameScenario .square

/-- L1 for "blue" -/
def l1_blue : List (Object × Frac) := RSA.L1 refGameScenario .blue

-- ============================================================================
-- Evaluate
-- ============================================================================

#eval l0_blue      -- L0("blue"): 1/2 each for blue_square, blue_circle
#eval l0_green     -- L0("green"): 1 for green_square
#eval l0_square    -- L0("square"): 1/2 each for blue_square, green_square

#eval s1_blue_square   -- S1(blue_square): blue and square both informative
#eval s1_green_square  -- S1(green_square): green preferred over square!

#eval l1_square    -- L1("square"): blue_square > green_square (the inference!)
#eval l1_blue      -- L1("blue"): should be roughly uniform over blue objects

-- ============================================================================
-- Main Theorems
-- ============================================================================

/--
**Reference Game Theorem**

L1("square") assigns higher probability to blue_square than green_square.

This captures the pragmatic inference: if speaker wanted green_square,
they would have said "green" (uniquely identifying). Saying "square"
signals they probably mean blue_square.
-/
theorem reference_game_inference :
    RSA.getScore l1_square .blue_square > RSA.getScore l1_square .green_square := by
  native_decide

/-- At literal level L0, squares are equally likely -/
theorem l0_squares_equal :
    Frac.eq (RSA.getScore l0_square .blue_square) (RSA.getScore l0_square .green_square) := by
  native_decide

/-- Speaker in green_square world prefers "green" over "square" -/
theorem s1_green_prefers_green :
    RSA.getScore s1_green_square .green > RSA.getScore s1_green_square .square := by
  native_decide

/-- Speaker in blue_square world: "blue" and "square" are equally informative -/
theorem s1_blue_square_equal :
    Frac.eq (RSA.getScore s1_blue_square .blue) (RSA.getScore s1_blue_square .square) := by
  native_decide

-- ============================================================================
-- Additional: Unique Reference
-- ============================================================================

/-- "green" uniquely identifies green_square at L0 -/
theorem green_unique :
    (RSA.getScore l0_green .green_square).num > 0 ∧
    (RSA.getScore l0_green .blue_square).num = 0 ∧
    (RSA.getScore l0_green .blue_circle).num = 0 := by
  native_decide

/-- "circle" uniquely identifies blue_circle at L0 -/
theorem circle_unique :
    (RSA.getScore (RSA.L0 refGameScenario .circle) .blue_circle).num > 0 ∧
    (RSA.getScore (RSA.L0 refGameScenario .circle) .blue_square).num = 0 := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## How RSA Derives the Reference Game Inference

1. **L0**: Literal listener
   - "square" → uniform over {blue_square, green_square}
   - "green" → only green_square

2. **S1**: Pragmatic speaker
   - In green_square world: "green" is maximally informative (1 referent)
     while "square" is less informative (2 referents). Prefers "green"!
   - In blue_square world: "blue" and "square" equally informative (2 each)

3. **L1**: Pragmatic listener hearing "square"
   - Reasons: "If speaker meant green_square, they'd say 'green'"
   - Speaker said "square" → probably NOT green_square
   - Therefore: blue_square more likely than green_square

This is the core RSA insight: pragmatic listeners infer meaning by
reasoning about rational speaker behavior.
-/

end RSA.FrankGoodman2012
