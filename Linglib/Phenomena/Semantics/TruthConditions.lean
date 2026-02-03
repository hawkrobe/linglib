/-
# Truth Condition Judgments

Empirical data: which sentences do speakers judge as true or false
given specific situations/models.

## The Phenomenon

Compositional semantics should predict truth conditions: given a model
(who did what), speakers reliably judge sentences as true or false.

## Data Source

Standard textbook examples testing basic predication, transitive verbs,
and their interactions.
-/

import Linglib.Phenomena.Core.EmpiricalData

namespace Phenomena.Semantics.TruthConditions

open Phenomena

-- ============================================================================
-- Truth Judgment Data Structure
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

-- ============================================================================
-- Simple Predication (Intransitive Verbs)
-- ============================================================================

/-
Situation: John is asleep, Mary is awake, both can laugh.
-/

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

-- ============================================================================
-- Transitive Verbs
-- ============================================================================

/-
Situation: John sees Mary, Mary sees John, neither sees themselves.
          John and Mary both eat pizza. John reads a book.
-/

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

-- ============================================================================
-- Collected Data
-- ============================================================================

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
-- Basic Theorems About the Data
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

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `TruthJudgment`: sentence, situation description, truth value

### Empirical Data
- `intransitiveJudgments`: John sleeps (true), Mary sleeps (false), etc.
- `transitiveJudgments`: John sees Mary (true), John sees John (false), etc.

### Key Patterns
- Truth depends on whether subject is in predicate extension
- For transitives, truth depends on whether pair is in relation
- Same verb can be true of one individual, false of another

### Theory Connection
Montague semantics should predict these via function application:
- ⟦sleeps⟧(⟦John⟧) = true
- ⟦sleeps⟧(⟦Mary⟧) = false
-/

end Phenomena.Semantics.TruthConditions
