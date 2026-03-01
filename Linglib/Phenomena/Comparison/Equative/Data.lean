/-!
# Equative Constructions: Empirical Data
@cite{haspelmath-buchholz-1998} @cite{kennedy-2007} @cite{rett-2020}

Empirical data on equative constructions ("as tall as"), including the
at-least vs. exactly ambiguity and cross-linguistic variation.

## Key Empirical Patterns

1. **At-least vs. exactly readings**: "Kim is as tall as Lee" can mean
   either "at least as tall" (the literal semantics) or "exactly as tall"
   (the pragmatically enriched reading).
2. **Scalar implicature**: the "exactly" reading arises via scalar
   implicature from the "at least" meaning, parallel to numeral
   strengthening (Kennedy 2007, Rett 2020).
3. **Negative equatives**: "not as tall as" is typically interpreted as
   strict inequality, not "not exactly as tall".

-/

namespace Phenomena.Comparison.Equative

-- ════════════════════════════════════════════════════
-- § 1. Basic Equative Data
-- ════════════════════════════════════════════════════

/-- An equative judgment. -/
structure EquativeJudgment where
  sentence : String
  acceptable : Bool
  /-- "at_least" or "exactly" -/
  availableReadings : List String
  note : String := ""
  deriving Repr

def equativeExamples : List EquativeJudgment :=
  [ { sentence := "Kim is as tall as Lee"
    , acceptable := true
    , availableReadings := ["at_least", "exactly"] }
  , { sentence := "Kim is as tall as Lee, if not taller"
    , acceptable := true
    , availableReadings := ["at_least"]
    , note := "'if not taller' cancels the exactly implicature" }
  , { sentence := "Kim is not as tall as Lee"
    , acceptable := true
    , availableReadings := ["strict_less"]
    , note := "negated equative = strict inequality" }
  , { sentence := "Kim ran as fast as Lee"
    , acceptable := true
    , availableReadings := ["at_least", "exactly"]
    , note := "adverbial equative" }
  ]

-- ════════════════════════════════════════════════════
-- § 2. Cross-Linguistic Equative Strategies
-- ════════════════════════════════════════════════════

/-- Equative encoding strategy (Haspelmath & Buchholz 1998, Rett 2020). -/
inductive EquativeStrategy where
  | parameterMarker  -- "as...as" (English, German)
  | reach            -- "tall reaching/to X" (many West African languages)
  | similative       -- "tall like X" (French "aussi...que", many languages)
  | exceed           -- "not exceed X in height" (Mandarin, Japanese)
  deriving DecidableEq, BEq, Repr

/-- Cross-linguistic equative strategy datum. -/
structure EquativeTypologyDatum where
  language : String
  strategy : EquativeStrategy
  exampleForm : String
  deriving Repr

def equativeTypology : List EquativeTypologyDatum :=
  [ { language := "English", strategy := .parameterMarker
    , exampleForm := "as tall as" }
  , { language := "German", strategy := .parameterMarker
    , exampleForm := "so groß wie" }
  , { language := "French", strategy := .similative
    , exampleForm := "aussi grand que" }
  , { language := "Mandarin", strategy := .exceed
    , exampleForm := "跟...一样高 (gēn...yíyàng gāo)" }
  , { language := "Japanese", strategy := .exceed
    , exampleForm := "...と同じぐらい高い (...to onaji gurai takai)" }
  ]

end Phenomena.Comparison.Equative
