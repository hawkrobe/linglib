/-
# Presupposition Phenomena Data

Theory-neutral presupposition examples and empirical patterns.

## Classic Examples

1. **The King Example (Karttunen 1974)**
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

Following Karttunen (1974) and Heim (1983):
- Negation: preserves presupposition
- Conjunction: filtering (left-to-right)
- Conditional: filtering (antecedent → consequent)
- Disjunction: symmetric filtering

## References

- Karttunen (1974). Presupposition and linguistic context.
- Heim (1983). On the projection problem for presuppositions.
- Beaver & Geurts (2014). Presupposition. SEP.
- Kracht (2003). Mathematics of Language, Section 4.7.
-/

import Linglib.Theories.Core.Presupposition
import Linglib.Core.Proposition

namespace Phenomena.Presupposition

open Core.Presupposition
open Core.Proposition


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

instance : FiniteWorlds KingWorld where
  worlds := [.kingExists, .noKing]
  complete := λ w => by cases w <;> simp

/--
"The king exists" — a presuppositionless assertion.

This sentence has:
- No presupposition (trivially true)
- Assertion: the king exists
-/
def kingExists : PrProp KingWorld :=
  { presup := λ _ => true
  , assertion := λ w => match w with
      | .kingExists => true
      | .noKing => false
  }

/--
"The king is bald" — presupposes king exists.

This sentence has:
- Presupposition: the king exists
- Assertion: the king is bald (true when king exists)
-/
def kingBald : PrProp KingWorld :=
  { presup := λ w => match w with
      | .kingExists => true
      | .noKing => false
  , assertion := λ _ => true
  }

/--
"If the king exists, the king is bald" — using filtering implication.

Demonstrates presupposition filtering: the antecedent's assertion
satisfies the consequent's presupposition.
-/
def ifKingThenBald : PrProp KingWorld :=
  PrProp.impFilter kingExists kingBald

/--
"If the king exists, the king is bald" has no presupposition.

This demonstrates presupposition filtering.
-/
theorem ifKingThenBald_no_presup : ifKingThenBald.presup = λ _ => true := by
  funext w
  simp only [ifKingThenBald, PrProp.impFilter, kingExists, kingBald]
  cases w <;> rfl

/--
"The king isn't bald" — negation preserves presupposition.
-/
def kingNotBald : PrProp KingWorld := PrProp.neg kingBald

theorem kingNotBald_presupposes_existence :
    kingNotBald.presup = kingBald.presup := PrProp.neg_presup kingBald


/--
World type for factive verb examples.

Models whether it's raining and whether John believes it.
-/
inductive RainWorld where
  | rainingBelieved    -- It's raining and John believes it
  | rainingNotBelieved -- It's raining but John doesn't believe it
  | notRaining         -- It's not raining
  deriving DecidableEq, Repr, Inhabited

instance : FiniteWorlds RainWorld where
  worlds := [.rainingBelieved, .rainingNotBelieved, .notRaining]
  complete := λ w => by cases w <;> simp

/--
"It's raining" — no presupposition.
-/
def raining : PrProp RainWorld :=
  { presup := λ _ => true
  , assertion := λ w => match w with
      | .rainingBelieved => true
      | .rainingNotBelieved => true
      | .notRaining => false
  }

/--
"John knows that it's raining" — factive presupposition.

Presupposes: it's raining
Asserts: John believes it's raining
-/
def johnKnowsRaining : PrProp RainWorld :=
  { presup := λ w => match w with
      | .rainingBelieved => true
      | .rainingNotBelieved => true
      | .notRaining => false  -- Presupposition fails
  , assertion := λ w => match w with
      | .rainingBelieved => true
      | .rainingNotBelieved => false
      | .notRaining => false  -- Undefined, but we need a value
  }

/--
"John doesn't know that it's raining" — negation preserves factive presupposition.
-/
def johnDoesntKnowRaining : PrProp RainWorld := PrProp.neg johnKnowsRaining

theorem negation_preserves_factive :
    johnDoesntKnowRaining.presup = johnKnowsRaining.presup :=
  PrProp.neg_presup johnKnowsRaining


/--
World type for change-of-state examples.

Models John's smoking history.
-/
inductive SmokingWorld where
  | usedToNowQuit     -- John used to smoke, has stopped
  | usedToStillDoes   -- John used to smoke, still does
  | neverSmoked       -- John never smoked
  deriving DecidableEq, Repr, Inhabited

instance : FiniteWorlds SmokingWorld where
  worlds := [.usedToNowQuit, .usedToStillDoes, .neverSmoked]
  complete := λ w => by cases w <;> simp

/--
"John stopped smoking" — presupposes prior smoking.

Presupposes: John used to smoke
Asserts: John no longer smokes
-/
def johnStoppedSmoking : PrProp SmokingWorld :=
  { presup := λ w => match w with
      | .usedToNowQuit => true
      | .usedToStillDoes => true
      | .neverSmoked => false  -- Presupposition fails
  , assertion := λ w => match w with
      | .usedToNowQuit => true
      | .usedToStillDoes => false
      | .neverSmoked => false
  }

/--
"John didn't stop smoking" — preserves change-of-state presupposition.
-/
def johnDidntStopSmoking : PrProp SmokingWorld := PrProp.neg johnStoppedSmoking

theorem negation_preserves_change_of_state :
    johnDidntStopSmoking.presup = johnStoppedSmoking.presup :=
  PrProp.neg_presup johnStoppedSmoking


/--
"John smokes and he stopped" — contradiction via filtering conjunction.

Left conjunct: John smokes (no presup)
Right conjunct: John stopped smoking (presupposes he used to smoke)

With filtering: left conjunct asserts smoking, right presupposes it was prior.
This creates a pragmatically odd sentence (you can't currently smoke AND have stopped).
-/
def johnSmokesAndStopped : PrProp SmokingWorld :=
  let johnSmokes : PrProp SmokingWorld :=
    { presup := λ _ => true
    , assertion := λ w => match w with
        | .usedToNowQuit => false
        | .usedToStillDoes => true
        | .neverSmoked => false
    }
  PrProp.andFilter johnSmokes johnStoppedSmoking


/--
Summary of projection patterns across connectives.

These capture the empirical generalizations from Karttunen (1974).
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
