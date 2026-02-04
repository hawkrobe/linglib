/-
# Focus Phenomena: Basic Data

Theory-neutral data on focus interpretation, including classic examples
from Rooth (1992) "A Theory of Focus Interpretation".

## The Phenomenon

Focus (prosodic prominence) affects interpretation in systematic ways:

1. **Association with focus** - Particles like "only" and "even" interact with focus
2. **Contrast** - Parallel focus in discourse triggers contrast effects
3. **Q-A Congruence** - Answer focus must match question (see Questions/FocusAnswer.lean)
4. **Scalar effects** - Focus on scalar items affects implicature strength

## What Counts as Focus?

At the phenomenon level, "focus" refers to prosodic prominence (pitch accent,
stress) that speakers use to mark information. The observable facts are:
- Certain words receive prosodic prominence (marked with CAPS in examples)
- This affects interpretation (exhaustivity, contrast, Q-A felicity)

## References

- Rooth, M. (1992). A Theory of Focus Interpretation. NLS 1(1): 75-116.
- Rooth, M. (1985). Association with Focus. PhD Dissertation, UMass Amherst.
- Jackendoff, R. (1972). Semantic Interpretation in Generative Grammar.
-/

import Linglib.Phenomena.Core.Basic

namespace Phenomena.Focus.Basic

-- Focus Data Structure

/-- FIP application type (Rooth 1992 §2) -/
inductive FIPApplication where
  /-- Focusing adverbs: only, even, also -/
  | focusingAdverb
  /-- Contrast/parallelism in discourse -/
  | contrast
  /-- Scalar implicature effects -/
  | scalarImplicature
  /-- Question-answer congruence -/
  | qaCongruence
  deriving DecidableEq, Repr, BEq

/-- A focus phenomenon datum -/
structure FocusDatum where
  /-- The sentence (CAPS marks prosodic prominence) -/
  sentence : String
  /-- The focused element(s) -/
  focus : String
  /-- Focus alternatives evoked -/
  alternatives : List String
  /-- Description of the interpretive effect -/
  effect : String
  /-- Which FIP application this exemplifies -/
  application : FIPApplication
  /-- Notes -/
  notes : String := ""
  /-- Source reference -/
  source : String := ""
  deriving Repr

-- Part 1: Association with Focus (Rooth 1992 §2.1)

/-!
## "Only" Associates with Focus

"Only" quantifies over focus alternatives:
- "Mary only introduced BILL to Sue" → Bill is the only one Mary introduced to Sue
- "Mary only introduced Bill to SUE" → Sue is the only one Mary introduced Bill to

The focus position determines what "only" excludes.
-/

/-- Rooth's classic "only" example: focus on direct object -/
def roothOnlyBill : FocusDatum := {
  sentence := "Mary only introduced BILL to Sue"
  focus := "Bill"
  alternatives := ["Bill", "John", "Tom", "Fred"]
  effect := "Bill is the only person Mary introduced to Sue"
  application := .focusingAdverb
  notes := "Focus on 'Bill' → only excludes alternative introducees"
  source := "Rooth (1992) §2.1"
}

/-- Same sentence, different focus position -/
def roothOnlySue : FocusDatum := {
  sentence := "Mary only introduced Bill to SUE"
  focus := "Sue"
  alternatives := ["Sue", "Jane", "Ann", "Beth"]
  effect := "Sue is the only person Mary introduced Bill to"
  application := .focusingAdverb
  notes := "Focus on 'Sue' → only excludes alternative recipients"
  source := "Rooth (1992) §2.1"
}

/-- "Even" associates with focus -/
def evenExample : FocusDatum := {
  sentence := "Even MARY passed the test"
  focus := "Mary"
  alternatives := ["Mary", "John", "Bill", "Sue"]
  effect := "Mary was the least likely person to pass (scalar presupposition)"
  application := .focusingAdverb
  notes := "Focus determines who EVEN compares to"
  source := "Rooth (1985)"
}

def focusingAdverbExamples : List FocusDatum :=
  [roothOnlyBill, roothOnlySue, evenExample]

-- Part 2: Contrast and Parallelism (Rooth 1992 §3)

/-!
## Contrast in Discourse

Parallel focus in adjacent clauses triggers a contrast interpretation:
- "An AMERICAN farmer was talking to a CANADIAN farmer"

The focused elements must be alternatives to each other.
-/

/-- Rooth's contrast example -/
def roothContrast : FocusDatum := {
  sentence := "An AMERICAN farmer was talking to a CANADIAN farmer"
  focus := "American, Canadian"
  alternatives := ["American", "Canadian", "British", "Mexican", "French"]
  effect := "American and Canadian are contrasted as nationality alternatives"
  application := .contrast
  notes := "Parallel focus triggers contrast presupposition"
  source := "Rooth (1992) §3"
}

/-- Contrastive topic example -/
def contrastiveTopic : FocusDatum := {
  sentence := "FRED ate the beans. BILL ate the rice."
  focus := "Fred, Bill"
  alternatives := ["Fred", "Bill", "Mary", "Sue"]
  effect := "Fred and Bill are contrasted; parallel structure on 'ate'"
  application := .contrast
  notes := "Contrastive topics partition the domain"
  source := "Büring (2003)"
}

/-- VP contrast -/
def vpContrast : FocusDatum := {
  sentence := "John BOUGHT a book, but Mary STOLE one"
  focus := "bought, stole"
  alternatives := ["bought", "stole", "borrowed", "found"]
  effect := "Buying and stealing are contrasted as acquisition methods"
  application := .contrast
  notes := "Parallel focus on verbs"
  source := "Rooth (1992)"
}

def contrastExamples : List FocusDatum :=
  [roothContrast, contrastiveTopic, vpContrast]

-- Part 3: Scalar Effects

/-!
## Focus and Scalar Implicature

Focus on scalar items affects implicature strength:
- "I PASSED the test" (stressed) → strong SI: didn't ace it
- "I passed the test" (unstressed) → weak SI: at least passed

See `ProsodicExhaustivity.lean` for detailed prosody data.
-/

/-- Scalar focus strengthens SI -/
def scalarFocusStrong : FocusDatum := {
  sentence := "Some of the students PASSED"
  focus := "passed"
  alternatives := ["passed", "aced", "did well on"]
  effect := "Strong implicature: they passed but didn't ace it"
  application := .scalarImplicature
  notes := "Focus on scalar item strengthens exhaustive reading"
  source := "Bergen & Goodman (2015)"
}

/-- Focus on quantifier -/
def quantifierFocus : FocusDatum := {
  sentence := "SOME of the students passed"
  focus := "some"
  alternatives := ["some", "all", "most", "few"]
  effect := "Strong SI: not all passed"
  application := .scalarImplicature
  notes := "Focus on scalar quantifier"
  source := "Rooth (1992)"
}

def scalarExamples : List FocusDatum :=
  [scalarFocusStrong, quantifierFocus]

-- Part 4: Q-A Congruence

/-!
## Question-Answer Congruence

The focus of an answer must match the question's wh-position:
- Q: "Who ate the beans?" → A: "FRED ate the beans" ✓
- Q: "Who ate the beans?" → A: "Fred ate the BEANS" ✗

See `Questions/FocusAnswer.lean` for detailed Q-A congruence data.
-/

/-- Q-A congruent example -/
def qaCongruent : FocusDatum := {
  sentence := "FRED ate the beans"
  focus := "Fred"
  alternatives := ["Fred", "Mary", "Bill", "Sue"]
  effect := "Congruent answer to 'Who ate the beans?'"
  application := .qaCongruence
  notes := "Focus matches wh-position"
  source := "Rooth (1992) §4"
}

/-- Q-A incongruent example -/
def qaIncongruent : FocusDatum := {
  sentence := "#Fred ate the BEANS"
  focus := "beans"
  alternatives := ["beans", "rice", "pasta", "salad"]
  effect := "Incongruent answer to 'Who ate the beans?' (marked #)"
  application := .qaCongruence
  notes := "Focus doesn't match wh-position → infelicitous"
  source := "Rooth (1992) §4"
}

def qaExamples : List FocusDatum :=
  [qaCongruent, qaIncongruent]

-- Collected Data

/-- All focus examples -/
def allFocusData : List FocusDatum :=
  focusingAdverbExamples ++ contrastExamples ++ scalarExamples ++ qaExamples

-- Summary

/-!
## What This Module Provides

### Data Types
- `FocusDatum`: Focus example with alternatives and interpretive effect
- `FIPApplication`: Type of focus interpretation application

### Key Examples (Rooth 1992)
- "Only" association with focus (§2.1)
- Contrast/parallelism (§3)
- Scalar implicature effects
- Q-A congruence (§4)

### Related Files
- `ProsodicExhaustivity.lean` - Prosody effects on exhaustivity
- `NegativeQuestions.lean` - Polarity emphasis in questions
- `Questions/FocusAnswer.lean` - Q-A congruence in detail
- `Theories/Montague/Sentence/FocusInterpretation.lean` - Rooth's FIP formalized
-/

end Phenomena.Focus.Basic
