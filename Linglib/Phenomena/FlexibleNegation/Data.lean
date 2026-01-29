/-
# Flexible Negation: Empirical Data

Tessler & Franke (2020) "Not unreasonable: Why two negatives don't make a positive"
-/

import Mathlib.Data.Rat.Defs

/-!

This file captures the empirical patterns around flexible negation, where:
- "not unhappy" ≠ "happy" (there's a gap region)
- "unhappy" is NOT the logical negation of "happy"
- Morphological negation (un-) and syntactic negation (not) can be
  either contradictory or contrary

## Key Distinction

**Contradictory negation**: P and ¬P partition the space
- "not happy" (contradictory) = x ≤ θ (complement of x > θ)
- Every point is either happy or not-happy

**Contrary negation**: P and Q can both be false (gap region)
- "happy" = x > θ_pos, "unhappy" = x < θ_neg where θ_neg < θ_pos
- Gap region: θ_neg ≤ x ≤ θ_pos (neither happy nor unhappy)

## References

- Tessler & Franke (2020). Not unreasonable: Why two negatives don't make a positive
- Horn (1989). A Natural History of Negation
- Kennedy & McNally (2005). Scale structure, degree modification
- Cruse (1986). Lexical Semantics (contraries vs. contradictories)
-/

namespace Phenomena.FlexibleNegation

-- ============================================================================
-- PART 1: Negation Types
-- ============================================================================

/--
Types of negation based on their logical relationship.

From traditional logic (Square of Opposition) and lexical semantics:
- **Contradictories**: Cannot both be true AND cannot both be false
  (exactly one must hold)
- **Contraries**: Cannot both be true BUT can both be false
  (gap where neither holds)

Source: Cruse (1986), Horn (1989)
-/
inductive NegationType where
  /-- Contradictory: complement (no gap). ¬(x > θ) = x ≤ θ -/
  | contradictory
  /-- Contrary: polar opposite with gap. x < θ₂ where θ₂ < θ₁ -/
  | contrary
  deriving Repr, DecidableEq, BEq

/--
Negation markers in English and their flexibility.

The key insight: both morphological (un-) and syntactic (not) negation
can receive either contradictory OR contrary interpretations.
The interpretation is pragmatically determined.

Source: Tessler & Franke (2020)
-/
inductive NegationMarker where
  /-- Syntactic negation: "not happy" -/
  | syntactic  -- "not"
  /-- Morphological negation: "unhappy" -/
  | morphological  -- "un-", "-less", "in-", etc.
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- PART 2: Flexible Negation Judgments
-- ============================================================================

/--
A judgment about the interpretation of a negated form.

Captures the empirical observation that negated forms can be
interpreted as contradictory or contrary, with varying strength.

Source: Tessler & Franke (2020) experiments
-/
structure FlexibleNegationDatum where
  /-- The base (positive) adjective -/
  adjective : String
  /-- The negated form being judged -/
  negatedForm : String
  /-- Which negation marker is used -/
  marker : NegationMarker
  /-- Expected primary interpretation -/
  expectedInterpretation : NegationType
  /-- Strength of preference (0-1 scale) -/
  strength : ℚ
  /-- Notes on the judgment -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- PART 3: Core Empirical Data
-- ============================================================================

/--
"unhappy" strongly prefers contrary interpretation.

Intuition: "unhappy" means positively unhappy (below a low threshold),
not just "not happy" (anything at or below the happy threshold).

Source: Tessler & Franke (2020) Experiment 1
-/
def unhappy_contrary : FlexibleNegationDatum :=
  { adjective := "happy"
  , negatedForm := "unhappy"
  , marker := .morphological
  , expectedInterpretation := .contrary
  , strength := 85/100  -- Strong preference for contrary
  , notes := "Morphological negation typically contrary (polar opposite)"
  }

/--
"not happy" is ambiguous between contradictory and contrary.

Intuition: "not happy" can mean either:
- Contradictory: anything at or below the happy threshold
- Contrary: positively unhappy (like "unhappy")

The costly form (2 words) licenses the marked (contradictory) reading.

Source: Tessler & Franke (2020) Experiment 1
-/
def not_happy_ambiguous : FlexibleNegationDatum :=
  { adjective := "happy"
  , negatedForm := "not happy"
  , marker := .syntactic
  , expectedInterpretation := .contradictory  -- More contradictory than "unhappy"
  , strength := 55/100  -- Ambiguous, slight preference for contradictory
  , notes := "Syntactic negation more flexible, cost licenses marked reading"
  }

/--
"not unhappy" ≠ "happy" - THE KEY EMPIRICAL FACT.

This is the central observation that motivates the paper:
"not unhappy" does NOT reduce to "happy".

Why? If "unhappy" is contrary (x < θ_neg), then:
- "not unhappy" = x ≥ θ_neg
- "happy" = x > θ_pos where θ_pos > θ_neg
- Gap region: θ_neg ≤ x ≤ θ_pos is "not unhappy" but NOT "happy"

Source: Tessler & Franke (2020) Section 1
-/
def not_unhappy_not_happy : FlexibleNegationDatum :=
  { adjective := "happy"
  , negatedForm := "not unhappy"
  , marker := .syntactic  -- outer negation is syntactic
  , expectedInterpretation := .contrary  -- inherits from inner "unhappy"
  , strength := 90/100  -- Very strong intuition that ≠ happy
  , notes := "KEY FACT: 'not unhappy' has positive probability in gap region"
  }

/--
"sad" as independent contrary antonym.

Note: "sad" is not morphologically derived from "happy" (unlike "unhappy"),
but still functions as a contrary antonym with a gap.

Source: Kennedy & McNally (2005)
-/
def sad_contrary : FlexibleNegationDatum :=
  { adjective := "happy"
  , negatedForm := "sad"
  , marker := .morphological  -- Treated as suppletive antonym
  , expectedInterpretation := .contrary
  , strength := 90/100
  , notes := "Suppletive antonym, same gap behavior as 'unhappy'"
  }

/--
All flexible negation examples.
-/
def flexibleNegationExamples : List FlexibleNegationDatum :=
  [unhappy_contrary, not_happy_ambiguous, not_unhappy_not_happy, sad_contrary]

-- ============================================================================
-- PART 4: Non-Equivalence Data
-- ============================================================================

/--
Data capturing the non-equivalence pattern: "not un-X" ≠ "X".

This is the central empirical claim: double negation doesn't cancel out
when the inner negation is contrary.

Source: Tessler & Franke (2020), Horn (1989)
-/
structure DoubleNegationDatum where
  /-- The positive adjective -/
  positive : String
  /-- The morphologically negated form -/
  antonym : String
  /-- The double negation -/
  doubleNeg : String
  /-- Are they equivalent? -/
  areEquivalent : Bool
  /-- Why or why not? -/
  explanation : String
  deriving Repr

/--
"not unhappy" ≠ "happy" because of the gap.

Someone in the gap region (neither happy nor unhappy) is:
- "not unhappy" ✓ (they're not below θ_neg)
- "happy" ✗ (they're not above θ_pos)

Source: Tessler & Franke (2020)
-/
def happy_double_neg : DoubleNegationDatum :=
  { positive := "happy"
  , antonym := "unhappy"
  , doubleNeg := "not unhappy"
  , areEquivalent := false
  , explanation := "Gap region: θ_neg ≤ x ≤ θ_pos is 'not unhappy' but not 'happy'"
  }

/--
"not unsafe" ≈ "safe" (closer to equivalent).

For closed-scale adjectives with minimum standard, the gap is smaller
or nonexistent, making double negation closer to canceling.

Source: Kennedy (2007)
-/
def safe_double_neg : DoubleNegationDatum :=
  { positive := "safe"
  , antonym := "unsafe"
  , doubleNeg := "not unsafe"
  , areEquivalent := false  -- Still not fully equivalent
  , explanation := "Minimum-standard adjective, smaller gap but still present"
  }

def doubleNegationExamples : List DoubleNegationDatum :=
  [happy_double_neg, safe_double_neg]

-- ============================================================================
-- PART 5: Cost and Length Effects
-- ============================================================================

/--
Cost asymmetry between negation forms.

Shorter/simpler forms are cheaper to produce, creating:
- Unmarked form (cheap) → unmarked meaning (default, most common)
- Marked form (costly) → marked meaning (special, contrastive)

This follows Horn's Division of Pragmatic Labor.

Source: Horn (1984), Tessler & Franke (2020)
-/
structure CostAsymmetryDatum where
  /-- Shorter/cheaper form -/
  cheapForm : String
  /-- Longer/costlier form -/
  costlyForm : String
  /-- Cost difference (words, morphemes, etc.) -/
  costDifference : String
  /-- Expected meaning of cheap form -/
  cheapMeaning : NegationType
  /-- Expected meaning of costly form -/
  costlyMeaning : NegationType
  deriving Repr

/--
"unhappy" (1 word) vs "not happy" (2 words).

The cheaper "unhappy" gets the default (contrary) reading.
The costlier "not happy" is available for the marked (contradictory) reading.

Source: Tessler & Franke (2020)
-/
def unhappy_vs_not_happy : CostAsymmetryDatum :=
  { cheapForm := "unhappy"
  , costlyForm := "not happy"
  , costDifference := "1 morpheme vs 2 words"
  , cheapMeaning := .contrary  -- default
  , costlyMeaning := .contradictory  -- marked, available when needed
  }

def costAsymmetryExamples : List CostAsymmetryDatum :=
  [unhappy_vs_not_happy]

-- ============================================================================
-- PART 6: Two-Threshold Structure
-- ============================================================================

/--
The two-threshold model for contrary antonyms.

For contrary pairs like happy/unhappy, there are TWO thresholds:
- θ_pos: threshold for "happy" (degree > θ_pos)
- θ_neg: threshold for "unhappy" (degree < θ_neg)
- Gap: θ_neg ≤ degree ≤ θ_pos (neither happy nor unhappy)

This is the key semantic insight that explains the non-equivalence.

Source: Tessler & Franke (2020), Kennedy (2007)
-/
structure TwoThresholdModel where
  /-- The positive adjective -/
  positive : String
  /-- The negative adjective -/
  negative : String
  /-- Relation between thresholds -/
  thresholdRelation : String  -- e.g., "θ_neg < θ_pos"
  /-- Description of gap region -/
  gapDescription : String
  /-- Example of gap case -/
  gapExample : String
  deriving Repr

/--
Happy/Unhappy two-threshold model.

The happiness scale has two thresholds creating three regions:
- Unhappy: degree < θ_neg (clearly unhappy)
- Gap: θ_neg ≤ degree ≤ θ_pos (neither/ambivalent)
- Happy: degree > θ_pos (clearly happy)

Source: Tessler & Franke (2020)
-/
def happyUnhappyThresholds : TwoThresholdModel :=
  { positive := "happy"
  , negative := "unhappy"
  , thresholdRelation := "θ_neg < θ_pos (strict inequality, gap exists)"
  , gapDescription := "Mildly positive or neutral emotional states"
  , gapExample := "Someone who is 'fine' or 'okay' - not unhappy, but not happy either"
  }

def twoThresholdExamples : List TwoThresholdModel :=
  [happyUnhappyThresholds]

-- ============================================================================
-- PART 7: Formal Predictions
-- ============================================================================

/--
Predictions that a theory of flexible negation should satisfy.

These are the empirical targets for the RSA implementation.

Source: Tessler & Franke (2020)
-/
structure FlexibleNegationPrediction where
  /-- Name of the prediction -/
  name : String
  /-- Formal statement -/
  statement : String
  /-- Why this matters -/
  explanation : String
  deriving Repr

def prediction_unhappy_contrary : FlexibleNegationPrediction :=
  { name := "Morphological negation prefers contrary"
  , statement := "P(contrary | 'unhappy') > P(contradictory | 'unhappy')"
  , explanation := "Morphological antonyms are lexicalized as polar opposites"
  }

def prediction_not_happy_flexible : FlexibleNegationPrediction :=
  { name := "Syntactic negation is flexible"
  , statement := "P(contrary | 'not happy') < P(contrary | 'unhappy')"
  , explanation := "Costly form licenses marked (contradictory) interpretation"
  }

def prediction_double_neg_gap : FlexibleNegationPrediction :=
  { name := "Double negation has gap probability"
  , statement := "∃d, P(d | 'not unhappy') > 0 ∧ P(d | 'happy') = 0"
  , explanation := "Gap region is possible for 'not unhappy' but not 'happy'"
  }

def prediction_cost_effect : FlexibleNegationPrediction :=
  { name := "Cost licenses marked reading"
  , statement := "P(contradictory | 'not happy') > P(contradictory | 'unhappy')"
  , explanation := "Longer form can express the marked contradictory meaning"
  }

def predictions : List FlexibleNegationPrediction :=
  [prediction_unhappy_contrary, prediction_not_happy_flexible,
   prediction_double_neg_gap, prediction_cost_effect]

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Summary: Flexible Negation Empirical Data

### Core Phenomenon

"not unhappy" ≠ "happy" because:
1. "unhappy" = contrary negation (x < θ_neg)
2. "not unhappy" = x ≥ θ_neg
3. "happy" = x > θ_pos where θ_pos > θ_neg
4. Gap region θ_neg ≤ x ≤ θ_pos is "not unhappy" but NOT "happy"

### Key Distinctions

**Contradictory negation** (complement):
- ¬(x > θ) = x ≤ θ
- No gap: every point is either P or ¬P

**Contrary negation** (polar opposite):
- P = x > θ_pos, Q = x < θ_neg
- Gap: θ_neg ≤ x ≤ θ_pos (neither P nor Q)

### Empirical Patterns

1. **Morphological negation (un-)**: Typically contrary (polar opposite)
2. **Syntactic negation (not)**: Flexible, can be either
3. **Cost effect**: Costly forms license marked readings
4. **Double negation**: Doesn't cancel when inner is contrary

### Predictions for RSA Model

1. `P(contrary | 'unhappy') > P(contradictory | 'unhappy')`
2. `P(contrary | 'not happy') < P(contrary | 'unhappy')`
3. Gap region has positive probability for "not unhappy"
4. `P(contradictory | 'not happy') > P(contradictory | 'unhappy')`

### References

- Tessler & Franke (2020). Not unreasonable: Why two negatives don't make a positive
- Horn (1989). A Natural History of Negation
- Kennedy & McNally (2005). Scale structure, degree modification
- Cruse (1986). Lexical Semantics
-/

end Phenomena.FlexibleNegation
