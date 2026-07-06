import Linglib.Studies.Heim2001

/-!
# Fox & Hackl 2006: Degree Questions and Negative Islands
[fox-hackl-2006] [heim-2001] [beck-rullmann-1999]
[fox-2007] [rullmann-1995]

Empirical data on degree questions ("how tall is Kim?"), including
negative islands, modal obviation, and comparative subdeletion.

[fox-hackl-2006]'s Universal Density of Measurement predicts that
degree questions fail under negation because the maximality presupposition
of "how" is undefined over dense scales with downward-monotone predicates.

## Bridge to [heim-2001]

The negative-island mechanism is the same as Heim's §2.1 high-DegP-over-
negation argument: both invoke the failure of `IsGreatest (Ioi (μ a))` on
an unbounded scale. We discharge the negative-island prediction by
appeal to `Heim2001.negation_high_DegP_undefined` (chronological
dependency: 2006 imports 2001).

## Key Empirical Patterns

1. **Negative islands**: "*How tall isn't Kim?" is unacceptable
   ([fox-hackl-2006]: density of measurement blocks maximality).
2. **Modal obviation**: "How tall is Kim required to be?" is acceptable
   (universal modal rescues maximality).
3. **Existential modal fails**: "*How tall is Kim allowed to be?"
   remains unacceptable (existential modal doesn't help).

-/

namespace FoxHackl2006

open Heim2001 (negatedDegreePredicate)

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

/-- [fox-hackl-2006] negative island data. -/
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

/-- **Bridge to [heim-2001] §2.1**. The maximality-failure mechanism
behind the negative-island data is the same as Heim's high-DegP-over-
negation argument: on any `NoMaxOrder` scale, the negated degree
predicate `{d | ¬ μ(a) ≥ d}` has no greatest element, so the
maximality presupposition of `how` (which Fox & Hackl tie to Universal
Density of Measurement) cannot be satisfied. Re-export of
`Heim2001.negation_high_DegP_undefined`. -/
theorem negativeIsland_via_no_max {Entity D : Type*} [LinearOrder D]
    [NoMaxOrder D] (μ : Entity → D) (a : Entity) :
    ¬ ∃ m, IsGreatest {d | negatedDegreePredicate μ a d} m :=
  Heim2001.negation_high_DegP_undefined μ a

-- ════════════════════════════════════════════════════
-- § 3. Modal Obviation
-- ════════════════════════════════════════════════════

/-- [fox-hackl-2006] modal obviation data. -/
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

end FoxHackl2006
