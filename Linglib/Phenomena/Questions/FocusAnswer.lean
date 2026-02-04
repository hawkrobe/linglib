/-
# Focus-Answer Correspondence

The same sentence can serve as different answers depending on focus placement,
which in turn depends on which question is being addressed.

## Core Observation

"JOHN called" answers "Who called?"
"John CALLED" answers "What did John do?"

The focus structure of the answer must match the question's wh-phrase.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. pp. 275-276.
- Rooth (1992). A theory of focus interpretation. Natural Language Semantics.
- Krifka (2011). Questions. Section on focus-answer congruence.
-/

import Linglib.Phenomena.Questions.Basic

namespace Phenomena.Questions.FocusAnswer


/-- A focus-answer datum: shows how focus placement determines question fit.
-/
structure FocusAnswerDatum where
  /-- The sentence (without focus marking) -/
  sentence : String
  /-- The question this answers (with focus on X) -/
  question : String
  /-- Which constituent is focused -/
  focusedConstituent : String
  /-- Focus marking (e.g., "JOHN called") -/
  focusedForm : String
  /-- Is this a congruent Q-A pair? -/
  congruent : Bool
  /-- Source citation -/
  source : String := ""
  deriving Repr

/-- G&S 1984, p. 275: "John called Mary" with different foci -/
def johnCalledMary_whoSubj : FocusAnswerDatum :=
  { sentence := "John called Mary"
  , question := "Who called Mary?"
  , focusedConstituent := "John"
  , focusedForm := "JOHN called Mary"
  , congruent := true
  , source := "G&S 1984, p. 275"
  }

def johnCalledMary_whoObj : FocusAnswerDatum :=
  { sentence := "John called Mary"
  , question := "Who did John call?"
  , focusedConstituent := "Mary"
  , focusedForm := "John called MARY"
  , congruent := true
  , source := "G&S 1984, p. 275"
  }

def johnCalledMary_whatDo : FocusAnswerDatum :=
  { sentence := "John called Mary"
  , question := "What did John do?"
  , focusedConstituent := "called Mary"
  , focusedForm := "John CALLED MARY"
  , congruent := true
  , source := "G&S 1984, p. 275"
  }

/-- Incongruent: wrong focus for the question -/
def johnCalledMary_incongruent : FocusAnswerDatum :=
  { sentence := "John called Mary"
  , question := "Who called Mary?"
  , focusedConstituent := "Mary"
  , focusedForm := "John called MARY"
  , congruent := false
  , source := "G&S 1984, p. 275 (constructed counterexample)"
  }

def focusAnswerExamples : List FocusAnswerDatum :=
  [ johnCalledMary_whoSubj
  , johnCalledMary_whoObj
  , johnCalledMary_whatDo
  , johnCalledMary_incongruent
  ]


/-- Shows how the same sentence answers multiple questions via focus shift.
-/
structure MultipleFocusDatum where
  /-- The base sentence -/
  sentence : String
  /-- Questions it can answer (with corresponding focus) -/
  questionFocusPairs : List (String × String)
  /-- Source -/
  source : String := ""
  deriving Repr

def maryBoughtBook : MultipleFocusDatum :=
  { sentence := "Mary bought a book"
  , questionFocusPairs :=
    [ ("Who bought a book?", "MARY bought a book")
    , ("What did Mary buy?", "Mary bought a BOOK")
    , ("What did Mary do?", "Mary BOUGHT A BOOK")
    , ("What happened?", "MARY BOUGHT A BOOK")  -- all-focus
    ]
  , source := "G&S 1984, constructed from examples"
  }

def multipleQuestionExamples : List MultipleFocusDatum :=
  [maryBoughtBook]


/-- Focus triggers exhaustification relative to the question.

    "JOHN called" (answering "Who called?") implies:
    - John called (assertion)
    - No one else called (exhaustive implicature)
-/
structure ExhaustiveFocusDatum where
  /-- The focused answer -/
  answer : String
  /-- The question -/
  question : String
  /-- The exhaustive interpretation -/
  exhaustiveReading : String
  /-- Is this exhaustive reading obligatory or optional? -/
  obligatory : Bool
  /-- Source -/
  source : String := ""
  deriving Repr

def johnCalled_exh : ExhaustiveFocusDatum :=
  { answer := "JOHN called"
  , question := "Who called?"
  , exhaustiveReading := "John called and no one else called"
  , obligatory := true
  , source := "G&S 1984, p. 276"
  }

def johnAndMary_exh : ExhaustiveFocusDatum :=
  { answer := "JOHN AND MARY called"
  , question := "Who called?"
  , exhaustiveReading := "John and Mary called and no one else called"
  , obligatory := true
  , source := "G&S 1984"
  }

def exhaustiveFocusExamples : List ExhaustiveFocusDatum :=
  [johnCalled_exh, johnAndMary_exh]


/-- When focus doesn't match the question, the result is infelicitous.
-/
structure FocusMismatchDatum where
  /-- The question -/
  question : String
  /-- The (mis)focused answer -/
  answer : String
  /-- What's wrong -/
  problem : String
  /-- Felicity judgment -/
  felicitous : Bool
  deriving Repr

def mismatch1 : FocusMismatchDatum :=
  { question := "Who called Mary?"
  , answer := "John called MARY"
  , problem := "Focus on object, but question asks about subject"
  , felicitous := false
  }

def mismatch2 : FocusMismatchDatum :=
  { question := "What did John buy?"
  , answer := "JOHN bought a book"
  , problem := "Focus on subject, but question asks about object"
  , felicitous := false
  }

def focusMismatchExamples : List FocusMismatchDatum :=
  [mismatch1, mismatch2]


/-- The formal congruence condition (Rooth 1992, building on G&S):

    An answer A is congruent to question Q iff:
    - The ordinary semantic value of A is in the question denotation
    - The focus semantic value of A equals the question denotation

    Informally: the alternatives generated by focus must match the
    alternatives denoted by the question.
-/
def congruenceCondition : String :=
  "⟦A⟧^f = ⟦Q⟧ (focus alternatives = question denotation)"

end Phenomena.Questions.FocusAnswer
