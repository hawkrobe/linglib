/-
# Semantic Entailment Judgments

Empirical data: which sentences do people judge as entailing others?

These are the semantic "minimal pairs" - pairs of sentences where
native speakers judge that the first entails the second (or not).

## Data Source

Standard textbook examples from formal semantics literature:
- Barwise & Cooper (1981)
- Keenan & Stavi (1986)
- van Benthem (1986)
-/

import Linglib.Phenomena.EmpiricalData

namespace Phenomena.Semantics.Entailments

open Phenomena

-- ============================================================================
-- Entailment Judgment Data Structure
-- ============================================================================

/--
An entailment judgment: does sentence A entail sentence B?
-/
structure EntailmentJudgment where
  /-- The premise sentence -/
  premise : String
  /-- The conclusion sentence -/
  conclusion : String
  /-- Do speakers judge this as valid? -/
  judgedValid : Bool
  /-- Description of the pattern -/
  pattern : String
  deriving Repr

-- ============================================================================
-- Quantifier Entailments
-- ============================================================================

/--
"All" entails "some" (on same restrictor and scope).

"All students passed" ⊨ "Some students passed"
-/
def allEntailsSome : EntailmentJudgment :=
  { premise := "All students passed"
  , conclusion := "Some students passed"
  , judgedValid := true
  , pattern := "all → some (downward on Horn scale)"
  }

/--
"Some" does NOT entail "all".

"Some students passed" ⊭ "All students passed"
-/
def someNotEntailsAll : EntailmentJudgment :=
  { premise := "Some students passed"
  , conclusion := "All students passed"
  , judgedValid := false
  , pattern := "some ↛ all (upward on Horn scale invalid)"
  }

/--
"Most" entails "some".

"Most students passed" ⊨ "Some students passed"
-/
def mostEntailsSome : EntailmentJudgment :=
  { premise := "Most students passed"
  , conclusion := "Some students passed"
  , judgedValid := true
  , pattern := "most → some"
  }

/--
"All" entails "most" (in typical contexts).

"All students passed" ⊨ "Most students passed"
-/
def allEntailsMost : EntailmentJudgment :=
  { premise := "All students passed"
  , conclusion := "Most students passed"
  , judgedValid := true
  , pattern := "all → most"
  }

/--
"No" entails "not all".

"No students passed" ⊨ "Not all students passed"
-/
def noEntailsNotAll : EntailmentJudgment :=
  { premise := "No students passed"
  , conclusion := "Not all students passed"
  , judgedValid := true
  , pattern := "no → not all"
  }

-- ============================================================================
-- Conjunction/Disjunction Entailments
-- ============================================================================

/--
Conjunction entails each conjunct.

"John and Mary left" ⊨ "John left"
-/
def conjunctionElimination : EntailmentJudgment :=
  { premise := "John and Mary left"
  , conclusion := "John left"
  , judgedValid := true
  , pattern := "A ∧ B → A"
  }

/--
Disjunct entails disjunction.

"John left" ⊨ "John or Mary left"
-/
def disjunctionIntroduction : EntailmentJudgment :=
  { premise := "John left"
  , conclusion := "John or Mary left"
  , judgedValid := true
  , pattern := "A → A ∨ B"
  }

/--
Conjunction entails disjunction.

"John and Mary left" ⊨ "John or Mary left"
-/
def conjEntailsDisj : EntailmentJudgment :=
  { premise := "John and Mary left"
  , conclusion := "John or Mary left"
  , judgedValid := true
  , pattern := "A ∧ B → A ∨ B"
  }

/--
Disjunction does NOT entail conjunction.

"John or Mary left" ⊭ "John and Mary left"
-/
def disjNotEntailsConj : EntailmentJudgment :=
  { premise := "John or Mary left"
  , conclusion := "John and Mary left"
  , judgedValid := false
  , pattern := "A ∨ B ↛ A ∧ B"
  }

-- ============================================================================
-- Collected Data
-- ============================================================================

/-- All quantifier entailment judgments -/
def quantifierEntailments : List EntailmentJudgment :=
  [ allEntailsSome
  , someNotEntailsAll
  , mostEntailsSome
  , allEntailsMost
  , noEntailsNotAll
  ]

/-- All connective entailment judgments -/
def connectiveEntailments : List EntailmentJudgment :=
  [ conjunctionElimination
  , disjunctionIntroduction
  , conjEntailsDisj
  , disjNotEntailsConj
  ]

/-- All entailment judgments -/
def allEntailments : List EntailmentJudgment :=
  quantifierEntailments ++ connectiveEntailments

-- ============================================================================
-- Basic Theorems About the Data
-- ============================================================================

/-- The scale all > most > some is reflected in entailments -/
theorem hornScaleReflected :
    allEntailsSome.judgedValid = true ∧
    allEntailsMost.judgedValid = true ∧
    mostEntailsSome.judgedValid = true ∧
    someNotEntailsAll.judgedValid = false := by
  native_decide

/-- Conjunction is stronger than disjunction -/
theorem conjStrongerThanDisj :
    conjEntailsDisj.judgedValid = true ∧
    disjNotEntailsConj.judgedValid = false := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `EntailmentJudgment`: premise, conclusion, validity judgment

### Empirical Data
- `quantifierEntailments`: all→some, most→some, etc.
- `connectiveEntailments`: A∧B→A, A→A∨B, etc.

### Key Patterns
- Horn scale ordering matches entailment direction
- Conjunction is stronger than disjunction
- "All" at top, "some" at bottom of quantifier scale

### Theory Connection
Theories/Semantics/Composition.lean should prove it predicts these patterns.
-/

end Phenomena.Semantics.Entailments
