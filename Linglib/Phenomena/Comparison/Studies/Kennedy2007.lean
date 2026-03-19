import Linglib.Theories.Semantics.Degree.Core
import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Core.Scales.Scale

/-!
# Kennedy Framework on Comparative Data
@cite{kennedy-2007} @cite{kennedy-mcnally-2005} @cite{schwarzschild-2005} @cite{solt-2015} @cite{winter-2005}

Bridge connecting @cite{kennedy-2007}'s measure function approach to the
comparative construction data in `Phenomena/Comparison/`.

## Key Bridges

1. **Morphological distribution**: Kennedy's ⟦-er⟧ and ⟦more⟧ are the
   same degree morpheme (comparative DegP head) with different
   spell-out — the framework is morphology-neutral.

2. **Scale structure predictions**: Kennedy's Interpretive Economy
   predicts that open-scale comparatives use contextual standards
   while closed-scale comparatives use endpoint standards.

3. **Measure phrase licensing**: Kennedy's approach naturally accounts
   for measure phrase differentials ("3 inches taller") because the
   degree argument IS a measure.

## Differential Comparative Data

Empirical data on differential comparatives (@cite{schwarzschild-2005},
@cite{solt-2015}): constructions that specify the extent of the
comparison ("3 inches taller", "twice as expensive", "much faster").

1. **Measure phrase differentials** require specific scale structure:
   "3 inches taller" ✓ but "*3 units more beautiful" ✗ (ratio scale needed).
2. **Factor phrases** ("twice as tall") require the equative, not the
   comparative (*"twice taller than").
3. **Degree modifiers** ("much", "slightly", "a lot") are less restrictive
   than measure phrases — they work with open scales.

-/

namespace Phenomena.Comparison.Studies.Kennedy2007

open Semantics.Degree
open Core.Scale (Boundedness)

-- ════════════════════════════════════════════════════
-- § 1. Interpretive Economy Predictions
-- ════════════════════════════════════════════════════

/-- Open-scale adjectives (Kennedy's "relative"; Class A here) use contextual standards. -/
theorem open_scale_contextual :
    interpretiveEconomy .open_ = .contextual := rfl

/-- Closed-scale adjectives (Kennedy's "absolute"; Class B here) use endpoint standards. -/
theorem closed_scale_endpoint :
    interpretiveEconomy .closed = .maxEndpoint := rfl

/-- Lower-bounded adjectives use minimum endpoint. -/
theorem lower_bounded_minEndpoint :
    interpretiveEconomy .lowerBounded = .minEndpoint := rfl

-- ════════════════════════════════════════════════════
-- § 2. Measure Phrase Differentials
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
-- § 3. Measure Phrase Licensing
-- ════════════════════════════════════════════════════

/-- Kennedy's approach predicts measure phrases are licensed when the
    degree type has subtraction (ratio/interval scale). The comparative
    data `measurePhraseExamples` reflects this: height (ratio) ✓,
    beauty (open, no conventional unit) ✗.

    This is a type-theoretic prediction: `differentialComparative`
    requires `ℚ` (with subtraction), not just an ordered type. -/
theorem measure_phrases_require_subtraction :
    ∀ d ∈ measurePhraseExamples,
      d.acceptable = true → d.scaleType = "ratio (height)" ∨
                             d.scaleType = "interval (temperature)" := by
  intro d hd hacc
  simp [measurePhraseExamples] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp_all

-- ════════════════════════════════════════════════════
-- § 4. Factor Phrases
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
-- § 5. Degree Modifiers
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

end Phenomena.Comparison.Studies.Kennedy2007
