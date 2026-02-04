/-
# Polarity Stress: Empirical Data

Theory-neutral data on prosodic stress patterns that affect polarity interpretation.

## The Phenomenon

Stress (prosodic prominence) on auxiliaries or negation affects interpretation:

1. **Auxiliary stress** (emphatic affirmation):
   - "John DOES drink" → emphatic: contrary to expectation, John drinks
   - "DOES John drink?" → checking expected positive answer

2. **Negation stress**:
   - "Does John NOT drink?" → speaker expected negative answer
   - "John does NOT drink" → emphatic negation

## Distinction from Other Focus Types

- **Content focus**: "JOHN drinks" (who drinks? → John)
- **Polarity stress**: "John DOES drink" (whether John drinks? → yes, emphatically)

Polarity stress targets truth/polarity rather than content alternatives.

## Related Files

- `ProsodicExhaustivity.lean` - Prosody effects on exhaustive interpretation
- `Basic.lean` - General focus phenomena (only, even, contrast)
- `Questions/NegativeQuestions.lean` - Negative question interpretation

## References

- Höhle, T. (1992). Über Verum-Fokus im Deutschen.
- Romero, M. & Han, C.-H. (2004). On Negative Yes/No Questions.
-/

import Linglib.Phenomena.Core.Basic

namespace Phenomena.Focus.PolarityStress

-- ============================================================================
-- Data Structure
-- ============================================================================

/-- A polarity stress datum records prosodic prominence affecting polarity -/
structure PolarityStressDatum where
  /-- The sentence (CAPS marks prosodic prominence) -/
  sentence : String
  /-- What element is stressed -/
  stressedElement : String  -- "auxiliary", "negation", "verb"
  /-- Clause type -/
  clauseType : String  -- "declarative", "interrogative"
  /-- Interpretive effect -/
  effect : String
  /-- Notes -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

-- ============================================================================
-- Auxiliary Stress (Declaratives)
-- ============================================================================

/-- Emphatic DO in declaratives -/
def emphaticDoDeclarative : PolarityStressDatum := {
  sentence := "John DOES drink"
  stressedElement := "auxiliary"
  clauseType := "declarative"
  effect := "Emphatic affirmation: contrary to expectation or doubt, John drinks"
  notes := "Stress on DO signals polarity emphasis in declaratives"
  source := "Höhle (1992)"
}

/-- Emphatic negation in declaratives -/
def emphaticNotDeclarative : PolarityStressDatum := {
  sentence := "John does NOT drink"
  stressedElement := "negation"
  clauseType := "declarative"
  effect := "Emphatic negation: contrary to expectation, John doesn't drink"
  notes := "Stress on NOT signals emphatic denial"
  source := "Höhle (1992)"
}

/-- Emphatic auxiliary with modal -/
def emphaticCanDeclarative : PolarityStressDatum := {
  sentence := "John CAN swim"
  stressedElement := "auxiliary"
  clauseType := "declarative"
  effect := "Emphatic ability claim: despite doubt, John has the ability"
  notes := "Works with modals too"
  source := "Höhle (1992)"
}

-- ============================================================================
-- Auxiliary Stress (Interrogatives)
-- ============================================================================

/-- Stressed auxiliary in yes/no question -/
def auxStressInterrogative : PolarityStressDatum := {
  sentence := "DOES John drink?"
  stressedElement := "auxiliary"
  clauseType := "interrogative"
  effect := "Speaker checking expected positive answer; positive bias"
  notes := "Pitch accent on auxiliary signals checking p (expected true)"
  source := "Höhle (1992)"
}

/-- Stressed negation in yes/no question -/
def notStressInterrogative : PolarityStressDatum := {
  sentence := "Does John NOT drink?"
  stressedElement := "negation"
  clauseType := "interrogative"
  effect := "Speaker checking expected negative answer; negative bias"
  notes := "Pitch accent on NOT signals checking ¬p (expected true)"
  source := "Romero & Han (2004)"
}

-- ============================================================================
-- Contrast with Content Focus
-- ============================================================================

/-- Content focus for comparison -/
def contentFocusSubject : PolarityStressDatum := {
  sentence := "JOHN drinks"
  stressedElement := "subject"
  clauseType := "declarative"
  effect := "Identifies who drinks (content focus, not polarity)"
  notes := "Compare: JOHN drinks (who?) vs John DOES drink (whether?)"
  source := "Rooth (1992)"
}

/-- Content focus on object -/
def contentFocusObject : PolarityStressDatum := {
  sentence := "John drinks BEER"
  stressedElement := "object"
  clauseType := "declarative"
  effect := "Identifies what John drinks (content focus, not polarity)"
  notes := "Not about whether John drinks, but what"
  source := "Rooth (1992)"
}

-- ============================================================================
-- Collected Data
-- ============================================================================

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

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Data Types
- `PolarityStressDatum`: Prosodic stress affecting polarity interpretation

### Key Examples
- "John DOES drink" (emphatic affirmation)
- "DOES John drink?" (checking expected positive)
- "Does John NOT drink?" (checking expected negative)

### Theoretical Neutrality

This module records the prosodic facts. Theoretical analyses include:
- **Verum Focus** (Höhle 1992): Focus on a VERUM operator
- **Polarity Focus**: Focus directly on truth value
- **Epistemic Focus**: Focus signals epistemic checking

### Key Distinction

Polarity stress targets truth/polarity:
- "John DOES drink" → whether John drinks (polarity)

Content focus targets alternatives:
- "JOHN drinks" → who drinks (content)

Both involve prosodic prominence but different semantic targets.
-/

end Phenomena.Focus.PolarityStress
