/-
# Evaluativity: Empirical Patterns

Evaluativity is the property of requiring a degree to exceed a contextual standard.
This file documents the distribution of evaluativity across adjectival constructions.

## Key Observation

Evaluativity is NOT uniformly distributed:
- Positive constructions: evaluative
- Comparatives: NOT evaluative
- Equatives: asymmetric (marked adjectives only)
- Measure phrases: NOT evaluative

## References

- Rett (2015). The Semantics of Evaluativity.
- Kennedy (2007). Vagueness and grammar.
- Bierwisch (1989). The semantics of gradation.
-/

import Mathlib.Data.Rat.Defs

namespace Phenomena.Semantics.Evaluativity

-- ============================================================================
-- Construction Types
-- ============================================================================

/--
Types of adjectival constructions.

Each construction type has different evaluativity properties.
-/
inductive AdjectivalConstruction where
  /-- "Adam is tall" - bare adjective predication -/
  | positive
  /-- "Adam is taller than Doug" - explicit comparison -/
  | comparative
  /-- "Adam is as tall as Doug" - equation -/
  | equative
  /-- "Adam is 6ft tall" - with measure phrase -/
  | measurePhrase
  /-- "How tall is Adam?" - degree question -/
  | degreeQuestion
  deriving Repr, DecidableEq, BEq

instance : ToString AdjectivalConstruction where
  toString
    | .positive => "positive"
    | .comparative => "comparative"
    | .equative => "equative"
    | .measurePhrase => "measurePhrase"
    | .degreeQuestion => "degreeQuestion"

-- ============================================================================
-- Evaluativity Judgments
-- ============================================================================

/--
Whether a construction is evaluative (requires exceeding a standard).
-/
inductive EvaluativityStatus where
  /-- Always evaluative -/
  | evaluative
  /-- Never evaluative -/
  | nonEvaluative
  /-- Evaluative only with marked (negative) adjectives -/
  | markedOnly
  /-- Ungrammatical -/
  | ungrammatical
  deriving Repr, DecidableEq, BEq

/--
An evaluativity judgment for a construction-adjective combination.
-/
structure EvaluativityDatum where
  /-- The construction type -/
  construction : AdjectivalConstruction
  /-- The adjective (surface form) -/
  adjective : String
  /-- Whether the adjective is positive-polar (tall) or negative-polar (short) -/
  isPositivePolar : Bool
  /-- Example sentence -/
  exampleSentence : String
  /-- Evaluativity status -/
  status : EvaluativityStatus
  /-- What is presupposed/entailed (if evaluative) -/
  presupposition : Option String := none
  /-- Notes -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- PART 1: Positive Constructions (Evaluative)
-- ============================================================================

/-!
## Positive Constructions

Positive constructions are ALWAYS evaluative, regardless of adjective polarity.

"Adam is tall" is true iff Adam's height exceeds the contextual standard for tallness.
"Adam is short" is true iff Adam's height is below the contextual standard for shortness.
-/

def positive_tall : EvaluativityDatum :=
  { construction := .positive
  , adjective := "tall"
  , isPositivePolar := true
  , exampleSentence := "Adam is tall."
  , status := .evaluative
  , presupposition := some "Adam's height exceeds the standard for tallness"
  , notes := "Positive construction with unmarked adjective"
  }

def positive_short : EvaluativityDatum :=
  { construction := .positive
  , adjective := "short"
  , isPositivePolar := false
  , exampleSentence := "Adam is short."
  , status := .evaluative
  , presupposition := some "Adam's height is below the standard for shortness"
  , notes := "Positive construction with marked adjective"
  }

-- ============================================================================
-- PART 2: Comparatives (Non-Evaluative)
-- ============================================================================

/-!
## Comparatives

Comparatives are NEVER evaluative, regardless of adjective polarity.

"Adam is taller than Doug" does NOT presuppose either is tall.
"Adam is shorter than Doug" does NOT presuppose either is short.

This is a key contrast with positive constructions.
-/

def comparative_tall : EvaluativityDatum :=
  { construction := .comparative
  , adjective := "tall"
  , isPositivePolar := true
  , exampleSentence := "Adam is taller than Doug."
  , status := .nonEvaluative
  , presupposition := none
  , notes := "True even if both Adam and Doug are short"
  }

def comparative_short : EvaluativityDatum :=
  { construction := .comparative
  , adjective := "short"
  , isPositivePolar := false
  , exampleSentence := "Adam is shorter than Doug."
  , status := .nonEvaluative
  , presupposition := none
  , notes := "True even if both Adam and Doug are tall"
  }

/--
Comparatives entail their equative counterpart but not vice versa.

"Adam is taller than Doug" → "Adam is as tall as Doug"
"Adam is as tall as Doug" ↛ "Adam is taller than Doug"
-/
def comparative_entails_equative : String :=
  "Adam is taller than Doug → Adam is as tall as Doug"

-- ============================================================================
-- PART 3: Equatives (Asymmetric!)
-- ============================================================================

/-!
## Equatives

Equatives show an ASYMMETRY based on adjective polarity:

- "Adam is as tall as Doug" → NOT evaluative
- "Adam is as short as Doug" → evaluative (presupposes both are short)

This asymmetry is evidence for a marked/unmarked distinction,
but the effect emerges from pragmatic competition, not lexical stipulation.

Source: Rett (2015), Bierwisch (1989)
-/

def equative_tall : EvaluativityDatum :=
  { construction := .equative
  , adjective := "tall"
  , isPositivePolar := true
  , exampleSentence := "Adam is as tall as Doug."
  , status := .nonEvaluative
  , presupposition := none
  , notes := "No presupposition that either is tall"
  }

def equative_short : EvaluativityDatum :=
  { construction := .equative
  , adjective := "short"
  , isPositivePolar := false
  , exampleSentence := "Adam is as short as Doug."
  , status := .evaluative
  , presupposition := some "Both Adam and Doug are short"
  , notes := "KEY ASYMMETRY: marked adjective triggers evaluativity"
  }

-- ============================================================================
-- PART 4: Measure Phrases (Non-Evaluative, Polarity Restricted)
-- ============================================================================

/-!
## Measure Phrase Constructions

Measure phrases are NOT evaluative - they specify exact degrees.

"Adam is 6ft tall" does NOT presuppose Adam is tall.

However, measure phrases are RESTRICTED to positive-polar adjectives:
- "Adam is 6ft tall" ✓
- *"Adam is 4ft short" ✗

Source: Schwarzschild (2005), Kennedy & McNally (2005)
-/

def mp_tall : EvaluativityDatum :=
  { construction := .measurePhrase
  , adjective := "tall"
  , isPositivePolar := true
  , exampleSentence := "Adam is 6ft tall."
  , status := .nonEvaluative
  , presupposition := none
  , notes := "Specifies degree without evaluativity"
  }

def mp_short : EvaluativityDatum :=
  { construction := .measurePhrase
  , adjective := "short"
  , isPositivePolar := false
  , exampleSentence := "*Adam is 4ft short."
  , status := .ungrammatical
  , presupposition := none
  , notes := "MPs don't combine with negative-polar adjectives"
  }

-- ============================================================================
-- PART 5: Degree Questions (Asymmetric)
-- ============================================================================

/-!
## Degree Questions

Degree questions show a similar asymmetry to equatives:

- "How tall is Adam?" → neutral (no presupposition)
- "How short is Adam?" → presupposes Adam is short

The unmarked form is used for neutral information-seeking.
The marked form presupposes the property holds.

Source: Rett (2015)
-/

def question_tall : EvaluativityDatum :=
  { construction := .degreeQuestion
  , adjective := "tall"
  , isPositivePolar := true
  , exampleSentence := "How tall is Adam?"
  , status := .nonEvaluative
  , presupposition := none
  , notes := "Neutral question - doesn't presuppose tall or short"
  }

def question_short : EvaluativityDatum :=
  { construction := .degreeQuestion
  , adjective := "short"
  , isPositivePolar := false
  , exampleSentence := "How short is Adam?"
  , status := .evaluative
  , presupposition := some "Adam is short"
  , notes := "Marked question - presupposes shortness"
  }

-- ============================================================================
-- Summary Data
-- ============================================================================

def allEvaluativityData : List EvaluativityDatum :=
  [ positive_tall, positive_short
  , comparative_tall, comparative_short
  , equative_tall, equative_short
  , mp_tall, mp_short
  , question_tall, question_short
  ]

/--
Summary table: Evaluativity by construction and polarity.

|                  | Positive-polar (tall) | Negative-polar (short) |
|------------------|----------------------|------------------------|
| Positive         | evaluative           | evaluative             |
| Comparative      | non-evaluative       | non-evaluative         |
| Equative         | non-evaluative       | EVALUATIVE             |
| Measure Phrase   | non-evaluative       | *ungrammatical         |
| Degree Question  | non-evaluative       | EVALUATIVE             |

The asymmetries in equatives and questions are the key evidence
for the marked/unmarked distinction.
-/
def evaluativitySummary : String :=
"
|                  | Positive-polar (tall) | Negative-polar (short) |
|------------------|----------------------|------------------------|
| Positive         | evaluative           | evaluative             |
| Comparative      | non-evaluative       | non-evaluative         |
| Equative         | non-evaluative       | EVALUATIVE             |
| Measure Phrase   | non-evaluative       | *ungrammatical         |
| Degree Question  | non-evaluative       | EVALUATIVE             |
"

-- ============================================================================
-- Theoretical Predictions
-- ============================================================================

/-!
## Theoretical Predictions

A theory of evaluativity should derive:

1. **Positive constructions are evaluative**
   - This falls out of threshold semantics + pragmatic inference (RSA)
   - Listener infers threshold jointly with degree

2. **Comparatives are non-evaluative**
   - The comparative morpheme (-er) binds the degree argument
   - No free threshold to infer

3. **Equative asymmetry**
   - "as tall as" and "as short as" are semantically equivalent
   - But pragmatic competition makes "as short as" marked
   - Using marked form implicates evaluativity

4. **MP restriction to positive adjectives**
   - Schwarzschild (2005): MPs measure "gaps" (bounded intervals)
   - Negative adjectives have unbounded intervals
   - *"4ft short" would measure an infinite interval

5. **Question asymmetry**
   - Parallel to equative: marked form presupposes property
   - "How short?" is only felicitous if shortness is salient
-/

/--
Predictions a pragmatic (RSA-style) theory should derive.
-/
structure EvaluativityPrediction where
  name : String
  claim : String
  mechanism : String
  deriving Repr

def prediction_positive : EvaluativityPrediction :=
  { name := "Positive evaluativity"
  , claim := "Positive constructions are evaluative"
  , mechanism := "Threshold inference: listener jointly infers degree and standard"
  }

def prediction_comparative : EvaluativityPrediction :=
  { name := "Comparative non-evaluativity"
  , claim := "Comparatives are not evaluative"
  , mechanism := "Degree argument is bound by -er, no free threshold"
  }

def prediction_equative_asymmetry : EvaluativityPrediction :=
  { name := "Equative asymmetry"
  , claim := "'as short as' is evaluative, 'as tall as' is not"
  , mechanism := "Pragmatic competition: marked form implicates evaluativity"
  }

def prediction_mp_restriction : EvaluativityPrediction :=
  { name := "MP restriction"
  , claim := "MPs only combine with positive-polar adjectives"
  , mechanism := "MPs measure bounded intervals; negative scales are unbounded"
  }

def prediction_question_asymmetry : EvaluativityPrediction :=
  { name := "Question asymmetry"
  , claim := "'How short?' presupposes shortness, 'How tall?' is neutral"
  , mechanism := "Parallel to equative: marked form presupposes property"
  }

def allPredictions : List EvaluativityPrediction :=
  [ prediction_positive
  , prediction_comparative
  , prediction_equative_asymmetry
  , prediction_mp_restriction
  , prediction_question_asymmetry
  ]

-- ============================================================================
-- Connection to Other Phenomena
-- ============================================================================

/-!
## Connections

**To FlexibleNegation (Tessler & Franke 2020)**:
- "not unhappy" ≠ "happy" involves evaluativity
- "unhappy" is evaluative (degree below θ_neg)
- "not unhappy" covers gap + positive region

**To Scalar Implicatures**:
- Evaluativity in equatives may be a manner implicature
- Using costly marked form signals something extra

**To Threshold Semantics (Lassiter & Goodman 2017)**:
- Positive construction evaluativity derives from threshold inference
- RSA listener infers threshold jointly with degree
-/

end Phenomena.Semantics.Evaluativity
