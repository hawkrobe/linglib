/-!
# Fox & Hackl 2006: Degree Questions and Negative Islands
@cite{fox-hackl-2006} @cite{beck-rullmann-1999} @cite{fox-2007} @cite{rullmann-1995}

Empirical data on degree questions ("how tall is Kim?"), including
negative islands, modal obviation, and comparative subdeletion.

@cite{fox-hackl-2006}'s Universal Density of Measurement predicts that
degree questions fail under negation because the maximality presupposition
of "how" is undefined over dense scales with downward-monotone predicates.

## Key Empirical Patterns

1. **Negative islands**: "*How tall isn't Kim?" is unacceptable
   (@cite{fox-hackl-2006}: density of measurement blocks maximality).
2. **Modal obviation**: "How tall is Kim required to be?" is acceptable
   (universal modal rescues maximality).
3. **Existential modal fails**: "*How tall is Kim allowed to be?"
   remains unacceptable (existential modal doesn't help).

-/

namespace Phenomena.Comparison.Studies.FoxHackl2006

-- ════════════════════════════════════════════════════
-- § 1. Basic Degree Question Data
-- ════════════════════════════════════════════════════

/-- A degree question acceptability datum. -/
structure DegreeQuestionDatum where
  sentence : String
  acceptable : Bool
  /-- What blocks or rescues the question? -/
  mechanism : String
  note : String := ""
  deriving Repr

def degreeQuestionExamples : List DegreeQuestionDatum :=
  [ { sentence := "How tall is Kim?"
    , acceptable := true
    , mechanism := "simple degree question" }
  , { sentence := "How heavy is this package?"
    , acceptable := true
    , mechanism := "simple degree question" }
  ]

-- ════════════════════════════════════════════════════
-- § 2. Negative Islands
-- ════════════════════════════════════════════════════

/-- @cite{fox-hackl-2006} negative island data. -/
def negativeIslandExamples : List DegreeQuestionDatum :=
  [ { sentence := "*How tall isn't Kim?"
    , acceptable := false
    , mechanism := "negative island"
    , note := "negation of downward-monotone degree property on dense scale" }
  , { sentence := "*How many books didn't Kim read?"
    , acceptable := false
    , mechanism := "negative island"
    , note := "degree question + negation" }
  ]

-- ════════════════════════════════════════════════════
-- § 3. Modal Obviation
-- ════════════════════════════════════════════════════

/-- @cite{fox-hackl-2006} modal obviation data. -/
def modalObviationExamples : List DegreeQuestionDatum :=
  [ { sentence := "How tall is Kim required to be?"
    , acceptable := true
    , mechanism := "universal modal obviates negative island"
    , note := "necessity modal rescues" }
  , { sentence := "*How tall is Kim allowed to be?"
    , acceptable := false
    , mechanism := "existential modal fails to obviate"
    , note := "possibility modal doesn't rescue" }
  , { sentence := "How many books is Kim required to read?"
    , acceptable := true
    , mechanism := "universal modal obviates" }
  , { sentence := "*How many books is Kim allowed to read?"
    , acceptable := false
    , mechanism := "existential modal fails" }
  ]

end Phenomena.Comparison.Studies.FoxHackl2006
