/-
# Entailment Phenomena

Core patterns in semantic entailment: truth conditions and entailment judgments.

## Phenomena Covered

1. **Truth Conditions**: Given a situation, speakers judge sentences true or false
2. **Entailment Judgments**: Speakers judge whether one sentence entails another

## Related Phenomena

- Monotonicity (see `Entailment/Monotonicity.lean`)
- Scalar implicatures (see `ScalarImplicatures/`)
- Negation (see `Negation/`)

## References

- Barwise & Cooper (1981). Generalized Quantifiers and Natural Language.
- Keenan & Stavi (1986). A semantic characterization of natural language determiners.
- van Benthem (1986). Essays in Logical Semantics.
-/

import Linglib.Phenomena.Core.EmpiricalData

namespace Phenomena.Entailment

open Phenomena

-- ============================================================================
-- PART 1: Truth Condition Judgments
-- ============================================================================

/--
A truth condition judgment: given a described situation, is the sentence true?
-/
structure TruthJudgment where
  /-- The sentence being evaluated -/
  sentence : String
  /-- Description of the model/situation -/
  situation : String
  /-- Do speakers judge this as true in the situation? -/
  judgedTrue : Bool
  /-- Description of the pattern being tested -/
  pattern : String
  deriving Repr

-- Simple Predication (Intransitive Verbs)

/-- "John sleeps" is true when John is asleep -/
def johnSleepsTrue : TruthJudgment :=
  { sentence := "John sleeps"
  , situation := "John is asleep, Mary is awake"
  , judgedTrue := true
  , pattern := "intransitive predication (subject in extension)"
  }

/-- "Mary sleeps" is false when Mary is awake -/
def marySleepsFalse : TruthJudgment :=
  { sentence := "Mary sleeps"
  , situation := "John is asleep, Mary is awake"
  , judgedTrue := false
  , pattern := "intransitive predication (subject not in extension)"
  }

/-- "John laughs" is true when John can laugh -/
def johnLaughsTrue : TruthJudgment :=
  { sentence := "John laughs"
  , situation := "John and Mary can both laugh"
  , judgedTrue := true
  , pattern := "intransitive predication"
  }

/-- "Mary laughs" is true when Mary can laugh -/
def maryLaughsTrue : TruthJudgment :=
  { sentence := "Mary laughs"
  , situation := "John and Mary can both laugh"
  , judgedTrue := true
  , pattern := "intransitive predication"
  }

-- Transitive Verbs

/-- "John sees Mary" is true when John sees Mary -/
def johnSeesMaryTrue : TruthJudgment :=
  { sentence := "John sees Mary"
  , situation := "John sees Mary, Mary sees John"
  , judgedTrue := true
  , pattern := "transitive predication (pair in relation)"
  }

/-- "Mary sees John" is true when Mary sees John -/
def marySeesJohnTrue : TruthJudgment :=
  { sentence := "Mary sees John"
  , situation := "John sees Mary, Mary sees John"
  , judgedTrue := true
  , pattern := "transitive predication (pair in relation)"
  }

/-- "John sees John" is false when John doesn't see himself -/
def johnSeesJohnFalse : TruthJudgment :=
  { sentence := "John sees John"
  , situation := "Neither John nor Mary sees themselves"
  , judgedTrue := false
  , pattern := "transitive predication (pair not in relation)"
  }

/-- "John eats pizza" is true -/
def johnEatsPizzaTrue : TruthJudgment :=
  { sentence := "John eats pizza"
  , situation := "John and Mary both eat pizza"
  , judgedTrue := true
  , pattern := "transitive predication"
  }

/-- "Mary eats pizza" is true -/
def maryEatsPizzaTrue : TruthJudgment :=
  { sentence := "Mary eats pizza"
  , situation := "John and Mary both eat pizza"
  , judgedTrue := true
  , pattern := "transitive predication"
  }

/-- "John eats Mary" is false (Mary is not food) -/
def johnEatsMaryFalse : TruthJudgment :=
  { sentence := "John eats Mary"
  , situation := "John and Mary eat pizza, not each other"
  , judgedTrue := false
  , pattern := "transitive predication (pair not in relation)"
  }

/-- "John reads book" is true -/
def johnReadsBookTrue : TruthJudgment :=
  { sentence := "John reads book"
  , situation := "John reads the book"
  , judgedTrue := true
  , pattern := "transitive predication"
  }

-- Collected Truth Judgments

/-- Intransitive verb truth judgments -/
def intransitiveJudgments : List TruthJudgment :=
  [ johnSleepsTrue
  , marySleepsFalse
  , johnLaughsTrue
  , maryLaughsTrue
  ]

/-- Transitive verb truth judgments -/
def transitiveJudgments : List TruthJudgment :=
  [ johnSeesMaryTrue
  , marySeesJohnTrue
  , johnSeesJohnFalse
  , johnEatsPizzaTrue
  , maryEatsPizzaTrue
  , johnEatsMaryFalse
  , johnReadsBookTrue
  ]

/-- All truth condition judgments -/
def allTruthJudgments : List TruthJudgment :=
  intransitiveJudgments ++ transitiveJudgments

-- ============================================================================
-- PART 2: Entailment Judgments
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

-- Quantifier Entailments

/-- "All" entails "some" (on same restrictor and scope). -/
def allEntailsSome : EntailmentJudgment :=
  { premise := "All students passed"
  , conclusion := "Some students passed"
  , judgedValid := true
  , pattern := "all → some (downward on Horn scale)"
  }

/-- "Some" does NOT entail "all". -/
def someNotEntailsAll : EntailmentJudgment :=
  { premise := "Some students passed"
  , conclusion := "All students passed"
  , judgedValid := false
  , pattern := "some ↛ all (upward on Horn scale invalid)"
  }

/-- "Most" entails "some". -/
def mostEntailsSome : EntailmentJudgment :=
  { premise := "Most students passed"
  , conclusion := "Some students passed"
  , judgedValid := true
  , pattern := "most → some"
  }

/-- "All" entails "most" (in typical contexts). -/
def allEntailsMost : EntailmentJudgment :=
  { premise := "All students passed"
  , conclusion := "Most students passed"
  , judgedValid := true
  , pattern := "all → most"
  }

/-- "No" entails "not all". -/
def noEntailsNotAll : EntailmentJudgment :=
  { premise := "No students passed"
  , conclusion := "Not all students passed"
  , judgedValid := true
  , pattern := "no → not all"
  }

-- Conjunction/Disjunction Entailments

/-- Conjunction entails each conjunct. -/
def conjunctionElimination : EntailmentJudgment :=
  { premise := "John and Mary left"
  , conclusion := "John left"
  , judgedValid := true
  , pattern := "A ∧ B → A"
  }

/-- Disjunct entails disjunction. -/
def disjunctionIntroduction : EntailmentJudgment :=
  { premise := "John left"
  , conclusion := "John or Mary left"
  , judgedValid := true
  , pattern := "A → A ∨ B"
  }

/-- Conjunction entails disjunction. -/
def conjEntailsDisj : EntailmentJudgment :=
  { premise := "John and Mary left"
  , conclusion := "John or Mary left"
  , judgedValid := true
  , pattern := "A ∧ B → A ∨ B"
  }

/-- Disjunction does NOT entail conjunction. -/
def disjNotEntailsConj : EntailmentJudgment :=
  { premise := "John or Mary left"
  , conclusion := "John and Mary left"
  , judgedValid := false
  , pattern := "A ∨ B ↛ A ∧ B"
  }

-- Collected Entailment Judgments

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
-- Theorems About the Data
-- ============================================================================

/-- Predication distinguishes individuals in/out of extension -/
theorem predication_discriminates :
    johnSleepsTrue.judgedTrue = true ∧
    marySleepsFalse.judgedTrue = false := by
  native_decide

/-- Transitive relations distinguish ordered pairs -/
theorem relations_discriminate :
    johnSeesMaryTrue.judgedTrue = true ∧
    johnSeesJohnFalse.judgedTrue = false := by
  native_decide

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

end Phenomena.Entailment
