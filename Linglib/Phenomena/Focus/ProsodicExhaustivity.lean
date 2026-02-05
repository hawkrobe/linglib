/-
# Prosodic Exhaustivity: Empirical Data

Theory-neutral data on how prosodic focus affects exhaustive interpretation.

## The Phenomenon

Prosodic stress on an answer affects whether it's interpreted exhaustively:

  A: "Who went to the movies?"
  B: "BOB went to the movies" → ONLY Bob went (exhaustive)
  B: "Bob went to the movies" → Bob went, maybe others too (non-exhaustive)

## Key Properties

1. **Stress signals exhaustivity**: Focused element is the complete answer
2. **Dimension sensitivity**: Focus marks WHICH dimension is exhaustive
3. **Scalar items**: Stress on scalars strengthens implicature

## Distinction from Verum Focus

- **Verum focus**: Focus on truth/polarity ("John DOES drink")
- **Prosodic exhaustivity**: Focus on answer content ("BOB went")

See `Focus/VerumFocus.lean` for verum focus data.

## Connection to Question Exhaustivity

This phenomenon relates to mention-all vs mention-some:
- Stress can FORCE exhaustive (mention-all) interpretation
- See `Questions/Exhaustivity.lean` for general exhaustivity data

## References

- Bergen, L. & Goodman, N.D. (2015). The Strategic Use of Noise in Pragmatic
  Reasoning. Topics in Cognitive Science 7(2): 336-350.
- Groenendijk, J. & Stokhof, M. (1984). Studies on the Semantics of Questions.
- Rooth, M. (1992). A Theory of Focus Interpretation. NLS 1(1): 75-116.
-/

import Linglib.Core.Basic

/-!
## Connection to RSA Theory

This phenomenon is modeled by Bergen & Goodman (2015)'s noisy channel RSA.
See: `Theories/RSA/Implementations/BergenGoodman2015.lean`

The key insight: prosodic stress reduces noise rate on stressed words.
This signals exhaustive knowledge to the listener.

Connection to unified noise theory: `Theories/RSA/Core/Noise.lean`
-/

namespace Phenomena.Focus.ProsodicExhaustivity

-- Part 1: Basic Prosodic Exhaustivity Data

/-- Stress pattern -/
inductive StressPattern where
  | noStress      -- Normal intonation
  | subjectFocus  -- Stress on subject ("BOB went")
  | objectFocus   -- Stress on object ("gave FLOWERS")
  | verbFocus     -- Stress on verb ("PASSED the test")
  deriving DecidableEq, BEq, Repr

/-- Exhaustivity interpretation -/
inductive Exhaustivity where
  | exhaustive    -- Only the focused element
  | nonExhaustive -- At least the mentioned element
  | neutral       -- No clear preference
  deriving DecidableEq, BEq, Repr

/-- A prosodic exhaustivity datum -/
structure ProsodyDatum where
  /-- The question context -/
  question : String
  /-- The answer (CAPS = stress) -/
  answer : String
  /-- Stress pattern -/
  stress : StressPattern
  /-- Resulting interpretation -/
  reading : Exhaustivity
  /-- The exhaustive proposition (if applicable) -/
  exhaustiveContent : String := ""
  /-- Notes -/
  notes : String := ""
  /-- Source -/
  source : String := ""
  deriving Repr

-- Part 2: Subject Focus Data

/-- Stressed subject → exhaustive -/
def stressedSubject : ProsodyDatum := {
  question := "Who went to the movies?"
  answer := "BOB went to the movies"
  stress := .subjectFocus
  reading := .exhaustive
  exhaustiveContent := "Bob and only Bob went to the movies"
  notes := "Stress on 'Bob' signals speaker knows the complete answer."
  source := "Bergen & Goodman (2015)"
}

/-- Unstressed subject → non-exhaustive -/
def unstressedSubject : ProsodyDatum := {
  question := "Who went to the movies?"
  answer := "Bob went to the movies"
  stress := .noStress
  reading := .nonExhaustive
  exhaustiveContent := ""
  notes := "No stress allows that others may have gone too."
  source := "Bergen & Goodman (2015)"
}

/-- Contrast: stressed vs unstressed -/
def stressContrast : List ProsodyDatum := [stressedSubject, unstressedSubject]

-- Part 3: Selective/Dimensional Focus

/-!
## Selective Focus

In sentences with multiple potential focus positions, stress indicates
WHICH dimension the speaker has exhaustive knowledge about.

"John introduced MARY to Bill" → Mary was the only one introduced TO BILL
"John introduced Mary to BILL" → Bill was the only one Mary was introduced TO
-/

/-- Focus on first object -/
def selectiveFocusMary : ProsodyDatum := {
  question := "Who did John introduce at the party?"
  answer := "John introduced MARY to Bill"
  stress := .objectFocus
  reading := .exhaustive
  exhaustiveContent := "Mary was the only person John introduced to Bill"
  notes := "Exhaustive on the 'introducee' dimension, not the 'recipient' dimension."
  source := "Bergen & Goodman (2015)"
}

/-- Focus on second object -/
def selectiveFocusBill : ProsodyDatum := {
  question := "Who did John introduce Mary to?"
  answer := "John introduced Mary to BILL"
  stress := .objectFocus
  reading := .exhaustive
  exhaustiveContent := "Bill was the only person Mary was introduced to"
  notes := "Exhaustive on the 'recipient' dimension."
  source := "Bergen & Goodman (2015)"
}

def selectiveFocusData : List ProsodyDatum := [selectiveFocusMary, selectiveFocusBill]

-- Part 4: Scalar Item Focus

/-!
## Scalar Focus

Stress on scalar items strengthens scalar implicature:

- "I PASSED" → I know I didn't ace it (strong SI)
- "I passed" → I at least passed, maybe aced (weak SI)
-/

/-- Stressed scalar → strong implicature -/
def scalarStressed : ProsodyDatum := {
  question := "How did you do on the test?"
  answer := "I PASSED the test"
  stress := .verbFocus
  reading := .exhaustive
  exhaustiveContent := "I passed but did not ace the test"
  notes := "Stress on 'passed' signals speaker knows the stronger alternative is false."
  source := "Bergen & Goodman (2015)"
}

/-- Unstressed scalar → weak implicature -/
def scalarUnstressed : ProsodyDatum := {
  question := "How did you do on the test?"
  answer := "I passed the test"
  stress := .noStress
  reading := .nonExhaustive
  exhaustiveContent := ""
  notes := "No stress: speaker may or may not know if they aced it."
  source := "Bergen & Goodman (2015)"
}

def scalarFocusData : List ProsodyDatum := [scalarStressed, scalarUnstressed]

-- Part 5: Collected Data

def allProsodyData : List ProsodyDatum :=
  stressContrast ++ selectiveFocusData ++ scalarFocusData

-- Part 6: Theoretical Connections

/-!
## Noisy Channel Account (Bergen & Goodman 2015)

Prosodic stress **reduces noise rate** on stressed words.
- Louder, longer → more robust to environmental noise
- Speaker strategically protects important information

### Mechanism

1. Speaker with exhaustive knowledge needs listener to hear correctly
2. Mishearing "Bob" as "Alice" would convey false information
3. Therefore: stress "Bob" to reduce noise
4. Listener infers: stress → speaker had reason to protect → exhaustive knowledge

### Predictions

- Effect emerges at higher recursion depths (pragmatic inference)
- Stress increases exhaustive interpretation probability

See: `Theories/RSA/Implementations/BergenGoodman2015.lean`

## Alternative Accounts

### Focus Semantics (Rooth 1992)

- Focus introduces alternatives
- Exhaustivity via exhaustification operator (Exh)
- Stress marks what's "at issue"

### Question-Answer Congruence (G&S 1984)

- Stressed material must match question's "wh" position
- Exhaustivity from partition semantics of questions

### Connection to Verum Focus

Verum focus (see `VerumFocus.lean`) is focus on **truth/polarity**:
- "John DOES drink" (emphatic affirmation)

Prosodic exhaustivity is focus on **answer content**:
- "JOHN drinks" (John and only John)

Both involve focus interpretation but target different elements.

### Connection to Question Exhaustivity

See `Questions/Exhaustivity.lean` for:
- Mention-some vs mention-all distinction
- When exhaustive answers are required
- Term type effects on exhaustivity

Prosodic stress can OVERRIDE default exhaustivity:
- Mention-some question + stress → forced exhaustive reading
-/

end Phenomena.Focus.ProsodicExhaustivity
