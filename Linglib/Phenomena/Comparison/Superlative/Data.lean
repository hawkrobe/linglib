/-!
# Superlative Constructions: Empirical Data
@cite{hackl-2009} @cite{heim-1999} @cite{sharvit-stateva-2002} @cite{szabolcsi-1986}

Empirical data on superlative constructions, including the absolute
vs. relative reading ambiguity and the interaction with focus.

## Key Empirical Patterns

1. **Absolute vs. relative readings**:
   "Kim climbed the highest mountain" can mean either "the mountain
   that is highest of all" (absolute) or "the mountain that is
   higher than anyone else climbed" (relative).
2. **Focus sensitivity**: the relative reading is sensitive to focus —
   "KIM climbed the highest mountain" vs. "Kim climbed the HIGHEST
   mountain" pick out different comparison classes.
3. **Superlative morphology varies**: English uses "-est"/most,
   some languages use the comparative + definite article (Romance),
   and others use entirely different strategies.

-/

namespace Phenomena.Comparison.Superlative

-- ════════════════════════════════════════════════════
-- § 1. Absolute vs. Relative Readings
-- ════════════════════════════════════════════════════

/-- A superlative judgment datum. -/
structure SuperlativeJudgment where
  sentence : String
  /-- Available readings (absolute, relative, or both) -/
  readings : List String
  /-- Focus placement (if relevant) -/
  focus : Option String := none
  note : String := ""
  deriving Repr

def superlativeExamples : List SuperlativeJudgment :=
  [ { sentence := "Kim climbed the highest mountain"
    , readings := ["absolute", "relative"]
    , note := "ambiguous between absolute and relative" }
  , { sentence := "KIM climbed the highest mountain"
    , readings := ["relative"]
    , focus := some "Kim"
    , note := "focus on subject forces relative reading" }
  , { sentence := "Kim bought the most expensive book"
    , readings := ["absolute", "relative"] }
  , { sentence := "Everest is the highest mountain"
    , readings := ["absolute"]
    , note := "predicative: only absolute reading" }
  ]

-- ════════════════════════════════════════════════════
-- § 2. Superlative Strategies
-- ════════════════════════════════════════════════════

/-- How superlative meaning is encoded cross-linguistically. -/
inductive SuperlativeEncoding where
  | morphological    -- "-est" (English, German)
  | analytic         -- "most" (English polysyllabic, French)
  | comparativePlus  -- comparative + definite (Romance, Greek)
  | exceed           -- "exceed all in height" (some languages)
  deriving DecidableEq, BEq, Repr

/-- Cross-linguistic superlative strategy datum. -/
structure SuperlativeTypologyDatum where
  language : String
  supEncoding : SuperlativeEncoding
  exampleForm : String
  deriving Repr

def superlativeTypology : List SuperlativeTypologyDatum :=
  [ { language := "English", supEncoding := .morphological
    , exampleForm := "tallest" }
  , { language := "English", supEncoding := .analytic
    , exampleForm := "most beautiful" }
  , { language := "French", supEncoding := .comparativePlus
    , exampleForm := "le plus grand" }
  , { language := "Spanish", supEncoding := .comparativePlus
    , exampleForm := "el más alto" }
  , { language := "Italian", supEncoding := .comparativePlus
    , exampleForm := "il più alto" }
  ]

end Phenomena.Comparison.Superlative
