/-
# Question Exhaustivity

When are exhaustive answers required vs. when are partial answers acceptable?

## Exhaustive (Mention-All)

- "Who came to the party?" → expects complete list
- "Which students passed?" → expects all who passed

## Non-Exhaustive (Mention-Some)

- "Where can I buy coffee?" → any coffee shop suffices
- "Who has a pen I can borrow?" → just need one person

## Term Type Effects

Different answer types have different exhaustive requirements:
- Singular terms: exhaustive (uniqueness)
- Definite plurals: exhaustive
- Indefinites: non-exhaustive

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. IV.
- Van Rooy (2003). Questioning to Resolve Decision Problems.
- Dayal (2016). Questions. Ch. 2.
-/

import Linglib.Phenomena.Questions.Basic

namespace Phenomena.Questions.Exhaustivity


/-- A mention-some datum: questions where partial answers suffice.
-/
structure MentionSomeDatum where
  /-- The question -/
  question : String
  /-- A sufficient partial answer -/
  partialAnswer : String
  /-- Why partial answer suffices -/
  explanation : String
  /-- The implicit goal/decision problem -/
  implicitGoal : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Classic mention-some: "Where can I buy X?"
    Source: Groenendijk & Stokhof (1984)
-/
def whereBuyCoffee : MentionSomeDatum :=
  { question := "Where can I buy coffee?"
  , partialAnswer := "There's a Starbucks on Main Street"
  , explanation := "Questioner only needs ONE place to buy coffee"
  , implicitGoal := "Get coffee"
  , source := "G&S 1984"
  }

def whereBuyNewspaper : MentionSomeDatum :=
  { question := "Where can I buy a newspaper?"
  , partialAnswer := "At the corner store"
  , explanation := "One location suffices for the goal"
  , implicitGoal := "Obtain a newspaper"
  , source := "G&S 1984"
  }

def whoHasPen : MentionSomeDatum :=
  { question := "Who has a pen I can borrow?"
  , partialAnswer := "Mary does"
  , explanation := "Only need one pen-haver"
  , implicitGoal := "Borrow a pen"
  , source := "constructed"
  }

def mentionSomeExamples : List MentionSomeDatum :=
  [whereBuyCoffee, whereBuyNewspaper, whoHasPen]


/-- A mention-all datum: questions requiring exhaustive answers.
-/
structure MentionAllDatum where
  /-- The question -/
  question : String
  /-- Why exhaustive answer is required -/
  explanation : String
  /-- An incomplete answer -/
  partialAnswer : String
  /-- Why partial is insufficient -/
  whyInsufficient : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- "Who came?" typically requires exhaustive answer -/
def whoCame : MentionAllDatum :=
  { question := "Who came to the party?"
  , explanation := "Questioner wants complete information about attendees"
  , partialAnswer := "John came"
  , whyInsufficient := "Doesn't answer whether others came"
  , source := "G&S 1984"
  }

/-- "Which students passed?" requires all passers -/
def whichStudentsPassed : MentionAllDatum :=
  { question := "Which students passed the exam?"
  , explanation := "Teacher needs complete grade information"
  , partialAnswer := "Alice passed"
  , whyInsufficient := "Incomplete; other passers not mentioned"
  , source := "constructed"
  }

def mentionAllExamples : List MentionAllDatum :=
  [whoCame, whichStudentsPassed]


/-- G&S 1984, pp. 296-298: Term type determines exhaustive interpretation.
-/
structure TermTypeExhDatum where
  /-- The question -/
  question : String
  /-- Answer with specific term type -/
  answer : String
  /-- The term type used -/
  termType : TermType
  /-- Does this answer get exhaustive interpretation? -/
  exhaustive : Bool
  /-- The exhaustive reading (if applicable) -/
  exhaustiveReading : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Singular definite: exhaustive (uniqueness presupposition) -/
def singularDefinite : TermTypeExhDatum :=
  { question := "Who called?"
  , answer := "The student who arrived late"
  , termType := .singular
  , exhaustive := true
  , exhaustiveReading := "Exactly one person called: the late-arriving student"
  , source := "G&S 1984, p. 296"
  }

/-- Plural definite: exhaustive -/
def pluralDefinite : TermTypeExhDatum :=
  { question := "Who called?"
  , answer := "The students who arrived late"
  , termType := .definiteNP
  , exhaustive := true
  , exhaustiveReading := "All and only the late-arriving students called"
  , source := "G&S 1984, p. 297"
  }

/-- Indefinite: NON-exhaustive -/
def indefiniteTerm : TermTypeExhDatum :=
  { question := "Who called?"
  , answer := "A student who arrived late"
  , termType := .indefinite
  , exhaustive := false
  , exhaustiveReading := ""  -- no exhaustive reading
  , source := "G&S 1984, p. 297"
  }

/-- Universal: exhaustive (trivially - all satisfiers mentioned) -/
def universalTerm : TermTypeExhDatum :=
  { question := "Who will be invited?"
  , answer := "Everyone who passed"
  , termType := .universalNP
  , exhaustive := true
  , exhaustiveReading := "All and only those who passed will be invited"
  , source := "G&S 1984, p. 298"
  }

def termTypeExamples : List TermTypeExhDatum :=
  [singularDefinite, pluralDefinite, indefiniteTerm, universalTerm]

/-- Data consistency: for each concrete datum, if the term type predicts exhaustivity
    then the datum confirms it, and if the term type is non-exhaustive then so is the datum.

    This is a per-datum verification over our G&S 1984 examples, not a universal claim
    (arbitrary `TermTypeExhDatum` values can violate any pattern). -/
theorem termType_exhaustivity_data_consistent :
    termTypeExamples.all (λ d => d.termType.exhaustive == d.exhaustive) = true := by
  native_decide


/-- Some languages have overt markers for non-exhaustive answers.
-/
structure NonExhMarkerDatum where
  /-- Language -/
  language : String
  /-- The marker/construction -/
  marker : String
  /-- Example sentence -/
  example_ : String
  /-- Translation/gloss -/
  translation : String
  /-- Effect on exhaustivity -/
  effect : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- English "for example" blocks exhaustivity -/
def englishForExample : NonExhMarkerDatum :=
  { language := "English"
  , marker := "for example"
  , example_ := "Who came? John, for example."
  , translation := ""
  , effect := "Signals answer is non-exhaustive; others may have come"
  , source := "constructed"
  }

/-- German "zum Beispiel" -/
def germanZumBeispiel : NonExhMarkerDatum :=
  { language := "German"
  , marker := "zum Beispiel"
  , example_ := "Wer ist gekommen? Hans, zum Beispiel."
  , translation := "Who came? Hans, for example."
  , effect := "Signals non-exhaustive answer"
  , source := "constructed"
  }

/-- English "among others" -/
def englishAmongOthers : NonExhMarkerDatum :=
  { language := "English"
  , marker := "among others"
  , example_ := "Who came? John, among others."
  , translation := ""
  , effect := "Explicitly signals incompleteness"
  , source := "constructed"
  }

def nonExhMarkerExamples : List NonExhMarkerDatum :=
  [englishForExample, germanZumBeispiel, englishAmongOthers]


/-- Van Rooy (2003): Exhaustivity depends on the decision problem.

    Mention-some arises when:
    - Multiple answers resolve the decision problem equally
    - Knowing more doesn't help choose better

    Mention-all required when:
    - Complete information is needed to decide
-/
structure DecisionTheoreticDatum where
  /-- The question -/
  question : String
  /-- The decision problem -/
  decisionProblem : String
  /-- Does resolution require exhaustive answer? -/
  requiresExhaustive : Bool
  /-- Explanation -/
  explanation : String
  deriving Repr

def whereBuyCoffee_dt : DecisionTheoreticDatum :=
  { question := "Where can I buy coffee?"
  , decisionProblem := "Choose a location to get coffee"
  , requiresExhaustive := false
  , explanation := "Any single coffee location resolves the problem"
  }

def whoCame_dt : DecisionTheoreticDatum :=
  { question := "Who came to the meeting?"
  , decisionProblem := "Know complete attendance for minutes"
  , requiresExhaustive := true
  , explanation := "Partial list doesn't satisfy record-keeping goal"
  }

def decisionTheoreticExamples : List DecisionTheoreticDatum :=
  [whereBuyCoffee_dt, whoCame_dt]

end Phenomena.Questions.Exhaustivity
