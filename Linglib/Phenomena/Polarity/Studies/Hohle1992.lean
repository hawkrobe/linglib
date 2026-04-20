import Linglib.Core.Lexical.Word

/-!
# Polarity Stress @cite{hohle-1992}

Empirical data on prosodic stress patterns that affect polarity interpretation,
following @cite{hohle-1992}'s analysis of verum focus.

Stress (prosodic prominence) on auxiliaries or negation affects interpretation:

1. **Auxiliary stress** (emphatic affirmation):
   - "John DOES drink" → emphatic: contrary to expectation, John drinks
   - "DOES John drink?" → checking expected positive answer

2. **Negation stress**:
   - "Does John NOT drink?" → speaker expected negative answer
   - "John does NOT drink" → emphatic negation

Polarity stress targets truth/polarity rather than content alternatives:
"JOHN drinks" (content focus, who drinks?) vs. "John DOES drink"
(polarity focus, whether John drinks).
-/

namespace Phenomena.Polarity.Studies.Hohle1992

-- Data Structure

/-- The element bearing prosodic prominence in a polarity-stress datum.
    Polarity stress targets `auxiliary` or `negation`; `verb` is rare;
    `subject`/`object` are the content-focus controls. -/
inductive StressedElement where
  | auxiliary
  | negation
  | verb
  | subject
  | object
  deriving DecidableEq, Repr

/-- The clause type for a polarity-stress datum. -/
inductive ClauseType where
  | declarative
  | interrogative
  deriving DecidableEq, Repr

/-- A polarity stress datum records prosodic prominence affecting polarity. -/
structure PolarityStressDatum where
  /-- The sentence (CAPS marks prosodic prominence) -/
  sentence : String
  /-- What element is stressed -/
  stressedElement : StressedElement
  /-- Clause type -/
  clauseType : ClauseType
  /-- Interpretive effect -/
  effect : String
  /-- Notes -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

-- Auxiliary Stress (Declaratives)

/-- Emphatic DO in declaratives -/
def emphaticDoDeclarative : PolarityStressDatum := {
  sentence := "John DOES drink"
  stressedElement := .auxiliary
  clauseType := .declarative
  effect := "Emphatic affirmation: contrary to expectation or doubt, John drinks"
  notes := "Stress on DO signals polarity emphasis in declaratives"
  source := "@cite{hohle-1992}"
}

/-- Emphatic negation in declaratives -/
def emphaticNotDeclarative : PolarityStressDatum := {
  sentence := "John does NOT drink"
  stressedElement := .negation
  clauseType := .declarative
  effect := "Emphatic negation: contrary to expectation, John doesn't drink"
  notes := "Stress on NOT signals emphatic denial"
  source := "@cite{hohle-1992}"
}

/-- Emphatic auxiliary with modal -/
def emphaticCanDeclarative : PolarityStressDatum := {
  sentence := "John CAN swim"
  stressedElement := .auxiliary
  clauseType := .declarative
  effect := "Emphatic ability claim: despite doubt, John has the ability"
  notes := "Works with modals too"
  source := "@cite{hohle-1992}"
}

-- Auxiliary Stress (Interrogatives)

/-- Stressed auxiliary in yes/no question -/
def auxStressInterrogative : PolarityStressDatum := {
  sentence := "DOES John drink?"
  stressedElement := .auxiliary
  clauseType := .interrogative
  effect := "Speaker checking expected positive answer; positive bias"
  notes := "Pitch accent on auxiliary signals checking p (expected true)"
  source := "@cite{hohle-1992}"
}

/-- Stressed negation in yes/no question -/
def notStressInterrogative : PolarityStressDatum := {
  sentence := "Does John NOT drink?"
  stressedElement := .negation
  clauseType := .interrogative
  effect := "Speaker checking expected negative answer; negative bias"
  notes := "Pitch accent on NOT signals checking ¬p (expected true)"
  source := "@cite{romero-han-2004}"
}

-- Contrast with Content Focus

/-- Content focus for comparison -/
def contentFocusSubject : PolarityStressDatum := {
  sentence := "JOHN drinks"
  stressedElement := .subject
  clauseType := .declarative
  effect := "Identifies who drinks (content focus, not polarity)"
  notes := "Compare: JOHN drinks (who?) vs John DOES drink (whether?)"
  source := "@cite{rooth-1992}"
}

/-- Content focus on object -/
def contentFocusObject : PolarityStressDatum := {
  sentence := "John drinks BEER"
  stressedElement := .object
  clauseType := .declarative
  effect := "Identifies what John drinks (content focus, not polarity)"
  notes := "Not about whether John drinks, but what"
  source := "@cite{rooth-1992}"
}

-- Collected Data

/-- All polarity stress examples -/
def polarityStressData : List PolarityStressDatum := [
  emphaticDoDeclarative,
  emphaticNotDeclarative,
  emphaticCanDeclarative,
  auxStressInterrogative,
  notStressInterrogative
]

/-- Content focus examples for comparison -/
def contentFocusData : List PolarityStressDatum := [
  contentFocusSubject,
  contentFocusObject
]

/-- All data -/
def allData : List PolarityStressDatum :=
  polarityStressData ++ contentFocusData

end Phenomena.Polarity.Studies.Hohle1992
