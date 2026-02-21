/-!
# Superlative Constructions: Empirical Data

Empirical data on superlative constructions, including the absolute
vs. relative reading ambiguity and the interaction with focus.

## Key Empirical Patterns

1. **Absolute vs. relative readings** (Heim 1999, Szabolcsi 1986):
   "Kim climbed the highest mountain" can mean either "the mountain
   that is highest of all" (absolute) or "the mountain that is
   higher than anyone else climbed" (relative).
2. **Focus sensitivity**: the relative reading is sensitive to focus —
   "KIM climbed the highest mountain" vs. "Kim climbed the HIGHEST
   mountain" pick out different comparison classes.
3. **Superlative morphology varies**: English uses "-est"/most,
   some languages use the comparative + definite article (Romance),
   and others use entirely different strategies.

## References

- Heim, I. (1999). Notes on superlatives. Ms., MIT.
- Szabolcsi, A. (1986). Comparative superlatives.
- Sharvit, Y. & Stateva, P. (2002). Superlative expressions, context, and focus.
- Hackl, M. (2009). On the grammar and processing of proportional quantifiers.
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
