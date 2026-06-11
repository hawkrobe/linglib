/-
# Presupposition Phenomena Data


Theory-neutral presupposition examples and empirical patterns.

## Classic Examples

1. **The King Example**
   "If the king exists, the king is bald"
   → Does not presuppose king exists (filtering)

2. **Factive Verbs**
   "John knows that it's raining" presupposes it's raining
   "John doesn't know that it's raining" still presupposes it's raining

3. **Definite Descriptions**
   "The king is bald" presupposes there is a unique king

4. **Change-of-State**
   "John stopped smoking" presupposes John used to smoke

## Projection Patterns

Following [karttunen-1973] and [heim-1983]:
- Negation: preserves presupposition
- Conjunction: filtering (left-to-right)
- Conditional: filtering (antecedent → consequent)
- Disjunction: symmetric filtering

-/

import Linglib.Semantics.Presupposition.Basic
import Mathlib.Data.Fintype.Basic

namespace Phenomena.Presupposition

open Semantics.Presupposition


/--
World type for the king example.

Two possible states:
- kingExists: There is a (unique) king in this world
- noKing: There is no king in this world
-/
inductive KingWorld where
  | kingExists : KingWorld
  | noKing : KingWorld
  deriving DecidableEq, Repr, Inhabited

instance : Fintype KingWorld where
  elems := {.kingExists, .noKing}
  complete := λ w => by cases w <;> decide

/--
"The king exists" — a presuppositionless assertion.

This sentence has:
- No presupposition (trivially true)
- Assertion: the king exists
-/
def kingExists : PartialProp KingWorld :=
  { presup := λ _ => True
  , assertion := λ w => match w with
      | .kingExists => True
      | .noKing => False
  }

/--
"The king is bald" — presupposes king exists.

This sentence has:
- Presupposition: the king exists
- Assertion: the king is bald (true when king exists)
-/
def kingBald : PartialProp KingWorld :=
  { presup := λ w => match w with
      | .kingExists => True
      | .noKing => False
  , assertion := λ _ => True
  }

/--
"If the king exists, the king is bald" — using filtering implication.

Demonstrates presupposition filtering: the antecedent's assertion
satisfies the consequent's presupposition.
-/
def ifKingThenBald : PartialProp KingWorld :=
  PartialProp.impFilter kingExists kingBald

/--
"If the king exists, the king is bald" has no presupposition.

This demonstrates presupposition filtering.
-/
theorem ifKingThenBald_no_presup : ifKingThenBald.presup = λ _ => True := by
  funext w
  simp only [ifKingThenBald, PartialProp.impFilter, kingExists, kingBald]
  cases w <;> simp

/--
"The king isn't bald" — negation preserves presupposition.
-/
def kingNotBald : PartialProp KingWorld := PartialProp.neg kingBald

theorem kingNotBald_presupposes_existence :
    kingNotBald.presup = kingBald.presup := PartialProp.neg_presup kingBald


/--
World type for factive verb examples.

Models whether it's raining and whether John believes it.
-/
inductive RainWorld where
  | rainingBelieved    -- It's raining and John believes it
  | rainingNotBelieved -- It's raining but John doesn't believe it
  | notRaining         -- It's not raining
  deriving DecidableEq, Repr, Inhabited

instance : Fintype RainWorld where
  elems := {.rainingBelieved, .rainingNotBelieved, .notRaining}
  complete := λ w => by cases w <;> decide

/--
"It's raining" — no presupposition.
-/
def raining : PartialProp RainWorld :=
  { presup := λ _ => True
  , assertion := λ w => match w with
      | .rainingBelieved => True
      | .rainingNotBelieved => True
      | .notRaining => False
  }

/--
"John knows that it's raining" — factive presupposition.

Presupposes: it's raining
Asserts: John believes it's raining
-/
def johnKnowsRaining : PartialProp RainWorld :=
  { presup := λ w => match w with
      | .rainingBelieved => True
      | .rainingNotBelieved => True
      | .notRaining => False
  , assertion := λ w => match w with
      | .rainingBelieved => True
      | .rainingNotBelieved => False
      | .notRaining => False
  }

/--
"John doesn't know that it's raining" — negation preserves factive presupposition.
-/
def johnDoesntKnowRaining : PartialProp RainWorld := PartialProp.neg johnKnowsRaining

theorem negation_preserves_factive :
    johnDoesntKnowRaining.presup = johnKnowsRaining.presup :=
  PartialProp.neg_presup johnKnowsRaining


/--
World type for change-of-state examples.

Models John's smoking history.
-/
inductive SmokingWorld where
  | usedToNowQuit     -- John used to smoke, has stopped
  | usedToStillDoes   -- John used to smoke, still does
  | neverSmoked       -- John never smoked
  deriving DecidableEq, Repr, Inhabited

instance : Fintype SmokingWorld where
  elems := {.usedToNowQuit, .usedToStillDoes, .neverSmoked}
  complete := λ w => by cases w <;> decide

/--
"John stopped smoking" — presupposes prior smoking.

Presupposes: John used to smoke
Asserts: John no longer smokes
-/
def johnStoppedSmoking : PartialProp SmokingWorld :=
  { presup := λ w => match w with
      | .usedToNowQuit => True
      | .usedToStillDoes => True
      | .neverSmoked => False
  , assertion := λ w => match w with
      | .usedToNowQuit => True
      | .usedToStillDoes => False
      | .neverSmoked => False
  }

/--
"John didn't stop smoking" — preserves change-of-state presupposition.
-/
def johnDidntStopSmoking : PartialProp SmokingWorld := PartialProp.neg johnStoppedSmoking

theorem negation_preserves_change_of_state :
    johnDidntStopSmoking.presup = johnStoppedSmoking.presup :=
  PartialProp.neg_presup johnStoppedSmoking


/--
"John smokes and he stopped" — contradiction via filtering conjunction.

Left conjunct: John smokes (no presup)
Right conjunct: John stopped smoking (presupposes he used to smoke)

With filtering: left conjunct asserts smoking, right presupposes it was prior.
This creates a pragmatically odd sentence (you can't currently smoke AND have stopped).
-/
def johnSmokesAndStopped : PartialProp SmokingWorld :=
  let johnSmokes : PartialProp SmokingWorld :=
    { presup := λ _ => True
    , assertion := λ w => match w with
        | .usedToNowQuit => False
        | .usedToStillDoes => True
        | .neverSmoked => False
    }
  PartialProp.andFilter johnSmokes johnStoppedSmoking


/--
Summary of projection patterns across connectives.

These capture the empirical generalizations from [karttunen-1973].
-/
structure ProjectionPattern where
  /-- Name of the pattern -/
  name : String
  /-- Description -/
  description : String
  /-- Whether presupposition projects through -/
  projects : Bool

def negationPattern : ProjectionPattern :=
  { name := "Negation"
  , description := "Presupposition projects unchanged through negation"
  , projects := true
  }

def conditionalPattern : ProjectionPattern :=
  { name := "Conditional"
  , description := "Antecedent can satisfy consequent's presupposition"
  , projects := false  -- filtered
  }

def conjunctionPattern : ProjectionPattern :=
  { name := "Conjunction"
  , description := "Left conjunct can satisfy right's presupposition"
  , projects := false  -- filtered
  }

def disjunctionPattern : ProjectionPattern :=
  { name := "Disjunction"
  , description := "Each disjunct can satisfy the other's presupposition"
  , projects := false  -- filtered (symmetric)
  }

end Phenomena.Presupposition
