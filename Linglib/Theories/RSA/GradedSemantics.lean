/-
# Graded Semantics Example: Vague Adjectives

Demonstrates RSA with graded φ ∈ [0,1] rather than Boolean.

## The Scenario

Context: Describing a person's height (in cm)
- Heights: 150, 160, 170, 180, 190
- Utterances: "tall", "short", "silence"

## Graded Meaning

Unlike Boolean semantics where φ ∈ {0, 1}, here φ captures
degrees of applicability:
- tallDegree(190) = 0.9  (very tall)
- tallDegree(170) = 0.5  (borderline)
- tallDegree(150) = 0.1  (not very tall)

## RSA with Graded Semantics

L0(w | "tall") ∝ tallDegree(w)

This naturally captures vagueness without a hard threshold.

Reference: Lassiter & Goodman (2017), "Adjectival vagueness in a Bayesian model"
-/

import Linglib.Core.RSA
import Mathlib.Data.Rat.Defs

namespace RSA.GradedSemantics

-- ============================================================================
-- Domain: Heights
-- ============================================================================

/-- Heights in centimeters (simplified to 5 values) -/
inductive Height where
  | h150 | h160 | h170 | h180 | h190
  deriving DecidableEq, BEq, Repr

/-- Utterances about height -/
inductive Utterance where
  | tall
  | short
  | silence  -- Null utterance (always "true")
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Graded Meanings
-- ============================================================================

/--
Graded meaning: degree to which height satisfies "tall".

These are scaled as fractions out of 10:
- 150cm → 1/10 (barely tall)
- 160cm → 3/10
- 170cm → 5/10 (borderline)
- 180cm → 7/10
- 190cm → 9/10 (very tall)
-/
def tallDegree : Height → ℚ
  | .h150 => 1 / 10
  | .h160 => 3 / 10
  | .h170 => 5 / 10
  | .h180 => 7 / 10
  | .h190 => 9 / 10

/--
Short degree: inverse of tall degree.
Computed as (10 - tallNum) / 10.
-/
def shortDegree : Height → ℚ
  | .h150 => 9 / 10   -- 1 - 1/10 = 9/10
  | .h160 => 7 / 10   -- 1 - 3/10 = 7/10
  | .h170 => 5 / 10   -- 1 - 5/10 = 5/10
  | .h180 => 3 / 10   -- 1 - 7/10 = 3/10
  | .h190 => 1 / 10   -- 1 - 9/10 = 1/10

/--
The graded φ function for height utterances.

Unlike Boolean semantics, this returns degrees in [0,1]:
- "tall" at 190cm → 0.9 (very applicable)
- "tall" at 150cm → 0.1 (barely applicable)
- "silence" → 1 (always applicable, uninformative)
-/
def φ : Utterance → Height → ℚ
  | .tall, h => tallDegree h
  | .short, h => shortDegree h
  | .silence, _ => 1  -- Null utterance always "true"

-- ============================================================================
-- RSAScenario with Graded φ
-- ============================================================================

/--
Graded height scenario.

This demonstrates RSAScenario with non-Boolean φ.
The meaning function returns degrees, not indicators.
-/
def heightScenario : ExactRSAScenario where
  Utterance := Utterance
  World := Height
  φ := φ
  utterances := [.tall, .short, .silence]
  worlds := [.h150, .h160, .h170, .h180, .h190]

-- ============================================================================
-- RSA Computations
-- ============================================================================

/-- L0 for "tall" -/
def l0_tall : List (Height × ℚ) := RSA.L0 heightScenario .tall

/-- L0 for "short" -/
def l0_short : List (Height × ℚ) := RSA.L0 heightScenario .short

/-- S1 for height 190 (very tall person) -/
def s1_h190 : List (Utterance × ℚ) := RSA.S1 heightScenario .h190

/-- S1 for height 150 (short person) -/
def s1_h150 : List (Utterance × ℚ) := RSA.S1 heightScenario .h150

/-- S1 for height 170 (borderline) -/
def s1_h170 : List (Utterance × ℚ) := RSA.S1 heightScenario .h170

/-- L1 for "tall" -/
def l1_tall : List (Height × ℚ) := RSA.L1 heightScenario .tall

/-- L1 for "short" -/
def l1_short : List (Height × ℚ) := RSA.L1 heightScenario .short

-- ============================================================================
-- Evaluate
-- ============================================================================

#eval l0_tall      -- L0("tall"): weighted by tallDegree
#eval l0_short     -- L0("short"): weighted by shortDegree
#eval s1_h190      -- S1(190cm): should prefer "tall"
#eval s1_h150      -- S1(150cm): should prefer "short"
#eval s1_h170      -- S1(170cm): borderline, both possible
#eval l1_tall      -- L1("tall"): pragmatic interpretation
#eval l1_short     -- L1("short"): pragmatic interpretation

-- ============================================================================
-- Key Properties
-- ============================================================================

/-- L0 assigns highest probability to tallest for "tall" -/
theorem l0_tall_prefers_tallest :
    RSA.getScore l0_tall .h190 > RSA.getScore l0_tall .h150 := by
  native_decide

/-- L0 assigns highest probability to shortest for "short" -/
theorem l0_short_prefers_shortest :
    RSA.getScore l0_short .h150 > RSA.getScore l0_short .h190 := by
  native_decide

/-- S1 at 190cm prefers "tall" over "short" -/
theorem s1_tall_person_says_tall :
    RSA.getScore s1_h190 .tall > RSA.getScore s1_h190 .short := by
  native_decide

/-- S1 at 150cm prefers "short" over "tall" -/
theorem s1_short_person_says_short :
    RSA.getScore s1_h150 .short > RSA.getScore s1_h150 .tall := by
  native_decide

/-- L1 "tall" still prefers taller people -/
theorem l1_tall_pragmatic :
    RSA.getScore l1_tall .h190 > RSA.getScore l1_tall .h150 := by
  native_decide

-- ============================================================================
-- Comparison with Boolean Semantics
-- ============================================================================

/-
## What Graded Semantics Buys Us

### Boolean Semantics (threshold-based)
- "tall" is either true or false
- Need to pick a threshold (e.g., 175cm)
- Heights near threshold are problematic:
  - 174cm: false
  - 176cm: true
  - No gradient!

### Graded Semantics
- "tall" has degrees
- 190cm: very tall (0.9)
- 170cm: somewhat tall (0.5)
- 150cm: not very tall (0.1)
- Natural vagueness handling

### In RSA

L0 with Boolean φ:
  L0(w | "tall") = 1/n for all w above threshold, 0 otherwise

L0 with Graded φ:
  L0(w | "tall") ∝ tallDegree(w)
  Naturally captures that "tall" is more appropriate for taller people

### Empirical Advantage

Gradience in truth-value judgments:
- "Is a 170cm person tall?" → ~50% say yes
- "Is a 190cm person tall?" → ~90% say yes

Graded RSA predicts this naturally; Boolean RSA cannot.
-/

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Demonstrates

### Key Innovation
RSAScenario with non-Boolean φ:
- φ("tall", 190cm) = 0.9 (not just 1)
- φ("tall", 150cm) = 0.1 (not just 0)

### Results
- L0 assigns probability proportional to degree
- S1 chooses utterances that best convey the world state
- L1 does pragmatic inference with graded meanings

### Connection to Literature
This implements the core idea from:
- Lassiter & Goodman (2017), "Adjectival vagueness in a Bayesian model"
- Qing & Franke (2014), "Gradable adjectives, vagueness, and optimal language use"

### Future Extensions
- Prior beliefs about height distribution
- Cost of utterances
- Comparison classes ("tall for a jockey" vs "tall for a basketball player")
-/

end RSA.GradedSemantics
