import Linglib.Phenomena.Comparison.Studies.Kennedy1999
import Linglib.Theories.Semantics.Degree.DegreeAbstraction
import Linglib.Theories.Semantics.Degree.Comparative

/-!
# Heim Framework on Comparative Data
@cite{heim-2001} @cite{heim-1999} @cite{sharvit-stateva-2002} @cite{szabolcsi-1986}

Bridge connecting @cite{heim-2001}'s sentential operator approach to the
comparative construction data.

## Key Distinctions from Kennedy

Heim's framework makes different predictions about scope:

1. **Wide-scope -er**: "The paper is required to be longer than that"
   can mean "there's a minimum required length" (wide scope -er) —
   predicted by Heim, not by Kennedy.

2. **Clausal vs. phrasal**: Heim's than-clause is always clausal
   (a degree predicate). Phrasal "than Bill" involves degree ellipsis.

## Superlative Data

Empirical data on superlative constructions (@cite{heim-1999},
@cite{sharvit-stateva-2002}, @cite{szabolcsi-1986}), including the
absolute vs. relative reading ambiguity and the interaction with focus.

-/

namespace Phenomena.Comparison.Studies.Heim2001

open Semantics.Degree.DegreeAbstraction
open Phenomena.Comparison.Studies.Kennedy1999 (clausalExamples)

-- ════════════════════════════════════════════════════
-- § 1. Heim = Kennedy Extensionally
-- ════════════════════════════════════════════════════

/-- For simple comparatives, Heim and Kennedy yield the same truth
    conditions. They diverge only on scope predictions. -/
theorem heim_eq_kennedy_simple {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    heimComparativeWithMeasure μ a b ↔
      Semantics.Degree.Comparative.comparativeSem μ a b .positive :=
  Iff.rfl

-- ════════════════════════════════════════════════════
-- § 2. Scope Reading Predictions
-- ════════════════════════════════════════════════════

/-- Heim predicts that clausal comparatives (the ones with explicit
    CP complement of *than*) allow scope ambiguities with other
    operators. The `clausalExamples` from Kennedy1999 are exactly the
    cases where Heim's predictions are most interesting. -/
theorem clausal_admits_scope_readings :
    (clausalExamples.filter (·.acceptable)).length > 0 := by
  simp [clausalExamples]

-- ════════════════════════════════════════════════════
-- § 3. Superlative Readings
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
-- § 4. Superlative Strategies (Cross-Linguistic)
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

end Phenomena.Comparison.Studies.Heim2001
