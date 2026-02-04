/-
# Wh-Question Complement Puzzle

"Who walks?" and "Who doesn't walk?" express the same partition but require
different answers. This is the wh-analogue of polar question polarity.

## The Puzzle

Consider a domain with John, Mary, Bill where John and Mary walk.

- Q1: "Who walks?"
  Partition: {{w: walkers = {j,m}}, {w: walkers = {j}}, ...}
  Correct answer: "John and Mary"

- Q2: "Who doesn't walk?"
  Partition: {{w: non-walkers = {b}}, {w: non-walkers = {j,b}}, ...}
  Correct answer: "Bill"

Both questions partition the same space, but:
- Q1 asks for the EXTENSION of "walk"
- Q2 asks for the EXTENSION of "not walk" (= ANTI-EXTENSION of "walk")

## Connection to Polar Question Polarity

Just as PPQ "Is it raining?" vs NPQ "Isn't it raining?" differ pragmatically
despite semantic equivalence, "Who P?" vs "Who doesn't P?" differ in what
counts as a direct answer.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. IV.
- Krifka (2011). Questions. In Semantics: An International Handbook.
-/

import Linglib.Phenomena.Questions.Basic

namespace Phenomena.Questions.WhComplement


/-- A complement question pair: Q and its negated counterpart.
    Key observation: same partition, different required answers.
-/
structure ComplementPair where
  /-- The positive question -/
  positiveQ : String
  /-- The negative question -/
  negativeQ : String
  /-- Domain description -/
  domain : String
  /-- Facts: who/what satisfies the predicate -/
  satisfiers : List String
  /-- Facts: who/what doesn't satisfy the predicate -/
  nonSatisfiers : List String
  /-- Correct answer to positive question -/
  positiveAnswer : String
  /-- Correct answer to negative question -/
  negativeAnswer : String
  /-- Source citation -/
  source : String := ""
  deriving Repr

/-- Classic example from G&S 1984: "Who walks?" vs "Who doesn't walk?"
    Source: G&S 1984, p. 280
-/
def whoWalks : ComplementPair :=
  { positiveQ := "Who walks?"
  , negativeQ := "Who doesn't walk?"
  , domain := "John, Mary, Bill"
  , satisfiers := ["John", "Mary"]
  , nonSatisfiers := ["Bill"]
  , positiveAnswer := "John and Mary"
  , negativeAnswer := "Bill"
  , source := "G&S 1984, p. 280"
  }

/-- "Which students passed?" vs "Which students didn't pass?" -/
def whichStudentsPassed : ComplementPair :=
  { positiveQ := "Which students passed?"
  , negativeQ := "Which students didn't pass?"
  , domain := "Alice, Bob, Carol (students in the class)"
  , satisfiers := ["Alice", "Carol"]
  , nonSatisfiers := ["Bob"]
  , positiveAnswer := "Alice and Carol"
  , negativeAnswer := "Bob"
  , source := "constructed"
  }

/-- "What did John buy?" vs "What didn't John buy?"
    (from a contextually salient set)
-/
def whatDidJohnBuy : ComplementPair :=
  { positiveQ := "What did John buy?"
  , negativeQ := "What didn't John buy?"
  , domain := "apples, oranges, bananas (available items)"
  , satisfiers := ["apples", "oranges"]
  , nonSatisfiers := ["bananas"]
  , positiveAnswer := "Apples and oranges"
  , negativeAnswer := "Bananas"
  , source := "constructed"
  }

def complementPairs : List ComplementPair :=
  [whoWalks, whichStudentsPassed, whatDidJohnBuy]


/-- Key theoretical claim: complement questions induce the same partition.

    Proof sketch (G&S 1984):
    - ⟦Who walks?⟧ = λw.λv. [walk_w = walk_v]
    - ⟦Who doesn't walk?⟧ = λw.λv. [¬walk_w = ¬walk_v]
    - But ¬walk_w = ¬walk_v iff walk_w = walk_v (set complement is injective)
    - Therefore the partitions are identical.
-/
theorem complement_same_partition_claim :
    True := by  -- Placeholder for the semantic equivalence
  trivial

/-- Yet the answers differ! This is the puzzle. -/
theorem answers_differ (cp : ComplementPair)
    (h : cp.positiveAnswer ≠ cp.negativeAnswer) :
    cp.positiveAnswer ≠ cp.negativeAnswer := h


/-- An answer is appropriate if it names the right set of individuals.
    For positive Q: name the satisfiers.
    For negative Q: name the non-satisfiers.
-/
structure AnswerAppropriateness where
  /-- The question -/
  question : String
  /-- Is this the positive or negative form? -/
  isPositive : Bool
  /-- The proposed answer -/
  answer : String
  /-- Is this answer appropriate? -/
  appropriate : Bool
  /-- Explanation -/
  explanation : String
  deriving Repr

/-- "John and Mary" is appropriate for "Who walks?" -/
def whoWalks_pos_correct : AnswerAppropriateness :=
  { question := "Who walks?"
  , isPositive := true
  , answer := "John and Mary"
  , appropriate := true
  , explanation := "Names exactly the walkers"
  }

/-- "Bill" is INappropriate for "Who walks?" -/
def whoWalks_pos_incorrect : AnswerAppropriateness :=
  { question := "Who walks?"
  , isPositive := true
  , answer := "Bill"
  , appropriate := false
  , explanation := "Bill doesn't walk; this answers the wrong question"
  }

/-- "Bill" is appropriate for "Who doesn't walk?" -/
def whoWalks_neg_correct : AnswerAppropriateness :=
  { question := "Who doesn't walk?"
  , isPositive := false
  , answer := "Bill"
  , appropriate := true
  , explanation := "Names exactly the non-walkers"
  }

/-- "John and Mary" is INappropriate for "Who doesn't walk?" -/
def whoWalks_neg_incorrect : AnswerAppropriateness :=
  { question := "Who doesn't walk?"
  , isPositive := false
  , answer := "John and Mary"
  , appropriate := false
  , explanation := "John and Mary walk; this answers the wrong question"
  }

def answerAppropriatenessExamples : List AnswerAppropriateness :=
  [ whoWalks_pos_correct
  , whoWalks_pos_incorrect
  , whoWalks_neg_correct
  , whoWalks_neg_incorrect
  ]


/-- The parallel between wh-complement and polar question polarity.

    Polar Questions:
    - PPQ "Is it raining?" → biased toward "yes"
    - NPQ "Isn't it raining?" → biased toward "yes" (= "no, it's not raining")

    Wh-Questions:
    - "Who P?" → answer names satisfiers of P
    - "Who doesn't P?" → answer names satisfiers of ¬P

    In both cases, the FORM of the question (positive vs negative) determines
    which answer is "direct" even when the partition is the same.
-/
structure PolarWhParallel where
  /-- Polar question example -/
  polarExample : String
  /-- Corresponding wh-question example -/
  whExample : String
  /-- What the positive form asks for -/
  positiveAsksFor : String
  /-- What the negative form asks for -/
  negativeAsksFor : String
  deriving Repr

def polarWhParallels : List PolarWhParallel :=
  [ { polarExample := "Is John here? / Isn't John here?"
    , whExample := "Who is here? / Who isn't here?"
    , positiveAsksFor := "Confirmation of presence"
    , negativeAsksFor := "Confirmation of absence"
    }
  , { polarExample := "Did it rain? / Didn't it rain?"
    , whExample := "Which days did it rain? / Which days didn't it rain?"
    , positiveAsksFor := "The rainy days"
    , negativeAsksFor := "The dry days"
    }
  ]


/-- Key observation: partition semantics alone cannot explain the asymmetry.

    If ⟦Who walks?⟧ = ⟦Who doesn't walk?⟧ (as partitions), then
    partition semantics predicts they should have the same answers.
    But they don't.

    Possible solutions:
    1. Questions denote MORE than partitions (e.g., structured meanings)
    2. Answer appropriateness is pragmatic, not purely semantic
    3. The "focus" or "aboutness" of the question matters
-/
inductive TheoreticalPosition where
  | structuredMeanings    -- Krifka, Groenendijk: questions have internal structure
  | pragmaticAnswerhood   -- The partition is semantic; answerhood is pragmatic
  | aboutnessFocus        -- Questions have a "topic" that determines answers
  deriving DecidableEq, Repr

/-- G&S's own solution involves the DENOTATION DOMAIN.
    "Who walks?" asks about the extension of "walk".
    "Who doesn't walk?" asks about the extension of "not walk".
    These are different semantic objects even if they induce the same partition.
-/
def gsolution : String :=
  "The question asks about a specific predicate's extension; " ++
  "negation changes which predicate we're asking about."

end Phenomena.Questions.WhComplement
