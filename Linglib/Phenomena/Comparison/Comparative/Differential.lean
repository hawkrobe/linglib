/-!
# Differential Comparatives

Empirical data on differential comparatives: constructions that specify
the extent of the comparison ("3 inches taller", "twice as expensive",
"much faster").

## Key Empirical Patterns

1. **Measure phrase differentials** require specific scale structure:
   "3 inches taller" ✓ but "*3 units more beautiful" ✗ (ratio scale needed).
2. **Factor phrases** ("twice as tall") require the equative, not the
   comparative (*"twice taller than").
3. **Degree modifiers** ("much", "slightly", "a lot") are less restrictive
   than measure phrases — they work with open scales.

## References

- Schwarzschild, R. (2005). Measure phrases as modifiers of adjectives.
- Solt, S. (2015). Q-adjectives and the semantics of quantity.
- Winter, Y. (2005). Cross-categorial restrictions on measure phrase modification.
-/

namespace Phenomena.Comparison.Comparative.Differential

-- ════════════════════════════════════════════════════
-- § 1. Measure Phrase Differentials
-- ════════════════════════════════════════════════════

/-- A measure phrase differential datum: a numeric amount specifying
    the extent of comparison. -/
structure MeasurePhraseComparativeDatum where
  sentence : String
  acceptable : Bool
  /-- What kind of scale does the adjective have? -/
  scaleType : String
  /-- The measure phrase -/
  measurePhrase : String
  deriving Repr

def measurePhraseExamples : List MeasurePhraseComparativeDatum :=
  [ { sentence := "Kim is 3 inches taller than Lee"
    , acceptable := true, scaleType := "ratio (height)"
    , measurePhrase := "3 inches" }
  , { sentence := "The room is 10 degrees warmer than outside"
    , acceptable := true, scaleType := "interval (temperature)"
    , measurePhrase := "10 degrees" }
  , { sentence := "??Kim is 3 units more beautiful than Lee"
    , acceptable := false, scaleType := "open (beauty)"
    , measurePhrase := "3 units" }
  , { sentence := "??Kim is 2 levels happier than Lee"
    , acceptable := false, scaleType := "open (happiness)"
    , measurePhrase := "2 levels" }
  ]

-- ════════════════════════════════════════════════════
-- § 2. Factor Phrases
-- ════════════════════════════════════════════════════

/-- Factor phrase data: multiplicative comparison ("twice", "three times"). -/
structure FactorPhraseDatum where
  sentence : String
  acceptable : Bool
  /-- Factor ("twice", "three times", etc.) -/
  factor : String
  /-- Equative or comparative? -/
  construction : String
  deriving Repr

def factorPhraseExamples : List FactorPhraseDatum :=
  [ { sentence := "Kim is twice as tall as Lee"
    , acceptable := true, factor := "twice"
    , construction := "equative" }
  , { sentence := "??Kim is twice taller than Lee"
    , acceptable := false, factor := "twice"
    , construction := "comparative" }
  , { sentence := "Kim earns three times as much as Lee"
    , acceptable := true, factor := "three times"
    , construction := "equative" }
  ]

-- ════════════════════════════════════════════════════
-- § 3. Degree Modifiers
-- ════════════════════════════════════════════════════

/-- Degree modifier data: "much", "slightly", "a lot", "far". -/
structure DegreeModifierDatum where
  sentence : String
  acceptable : Bool
  modifier : String
  /-- Does the modifier require a comparison construction? -/
  requiresComparison : Bool
  deriving Repr

def degreeModifierExamples : List DegreeModifierDatum :=
  [ { sentence := "Kim is much taller than Lee"
    , acceptable := true, modifier := "much"
    , requiresComparison := true }
  , { sentence := "Kim is slightly taller than Lee"
    , acceptable := true, modifier := "slightly"
    , requiresComparison := true }
  , { sentence := "Kim is far more expensive than Lee"
    , acceptable := true, modifier := "far"
    , requiresComparison := true }
  , { sentence := "Kim is a lot taller than Lee"
    , acceptable := true, modifier := "a lot"
    , requiresComparison := true }
  ]

end Phenomena.Comparison.Comparative.Differential
