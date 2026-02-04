/-
# Sluicing: Empirical Data

Theory-neutral data on sluicing and related ellipsis phenomena.

## The Phenomenon

Sluicing is ellipsis of the complement of a wh-phrase:

  "Someone left, but I don't know who __"

The elided material ("left") is reconstructed from the antecedent clause.

## Key Properties

1. **Inner antecedent**: The correlate in the antecedent (e.g., "someone")
2. **Case matching**: Wh-phrase case must match inner antecedent case
3. **Scope constraint**: Inner antecedent must scope over rest of antecedent
4. **Sprouting**: Sluicing without overt inner antecedent

## Theoretical Connections (Promissory Notes)

### Continuation-Based Analysis (B&S 2014, Ch. 16)

Barker & Shan analyze sluicing as **anaphora to a continuation**:
- The sluice = wh-phrase + (antecedent − inner-antecedent)
- SLUICEGAP is a proform of category `(DP⦵S)^(DP⦵S)`
- This explains scope constraints: inner antecedent must take scope

This connects to `Theories/Montague/Anaphora.lean`:
- Sluicing as continuation anaphora parallels binding as duplication (W combinator)
- Both involve "reusing" semantic material from elsewhere

### Answer Ban (Chung, Ladusaw & McCloskey 1995)

The antecedent clause must NOT resolve the sluiced interrogative's issue.
This is a pragmatic constraint connecting to question semantics.

See `Theories/Montague/Questions.lean` for partition semantics.

### Case Matching as Syntactic Bookkeeping

Case matching follows from the continuation analysis:
- The wh-phrase's case comes from its syntactic position
- This position is determined by the reconstructed continuation

## References

- Ross, J.R. (1969). Guess who? (introduced "sluicing")
- Chung, S., Ladusaw, W., & McCloskey, J. (1995). Sluicing and Logical Form.
- Merchant, J. (2001). The Syntax of Silence.
- Barker, C. & Shan, C. (2014). Continuations and Natural Language. Ch. 16.
-/

import Linglib.Phenomena.Core.Basic

namespace Phenomena.Ellipsis.Sluicing

-- Part 1: Basic Sluicing Data

/-- A sluicing datum records a sentence with its ellipsis site -/
structure SluicingDatum where
  /-- The full sentence with sluice -/
  sentence : String
  /-- The antecedent clause -/
  antecedent : String
  /-- The inner antecedent (correlate) -/
  innerAntecedent : String
  /-- The wh-phrase -/
  whPhrase : String
  /-- Reconstructed/elided material -/
  elided : String
  /-- Is the sentence grammatical? -/
  grammatical : Bool := true
  /-- Notes -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

/-- Basic sluicing example -/
def basicSluice : SluicingDatum := {
  sentence := "Someone left, but I don't know who"
  antecedent := "someone left"
  innerAntecedent := "someone"
  whPhrase := "who"
  elided := "left"
  notes := "Classic sluicing. Wh-phrase 'who' correlates with 'someone'."
  source := "Ross (1969)"
}

/-- Sluicing with object correlate -/
def objectSluice : SluicingDatum := {
  sentence := "John ate something, but I don't know what"
  antecedent := "John ate something"
  innerAntecedent := "something"
  whPhrase := "what"
  elided := "John ate"
  notes := "Object sluicing. Inner antecedent is direct object."
  source := "Merchant (2001)"
}

/-- Embedded sluicing -/
def embeddedSluice : SluicingDatum := {
  sentence := "Someone said that Mary left, but I don't know who"
  antecedent := "someone said that Mary left"
  innerAntecedent := "someone"
  whPhrase := "who"
  elided := "said that Mary left"
  notes := "Embedded antecedent. Wh-phrase extracts from matrix subject."
  source := "Merchant (2001)"
}

-- Part 2: Case Matching Data

/-- Case matching in sluicing -/
structure CaseMatchingDatum where
  sentence : String
  whPhraseCase : String
  innerAntecedentCase : String
  grammatical : Bool
  language : String := "English"
  notes : String := ""
  source : String := ""
  deriving Repr

/-- German case matching - matching cases -/
def germanCaseMatch : CaseMatchingDatum := {
  sentence := "Er will jemandem schmeicheln, aber sie wissen nicht, wem"
  whPhraseCase := "dative"
  innerAntecedentCase := "dative"
  grammatical := true
  language := "German"
  notes := "'wem' (dative) matches 'jemandem' (dative). Grammatical."
  source := "Merchant (2001)"
}

/-- German case mismatch -/
def germanCaseMismatch : CaseMatchingDatum := {
  sentence := "*Er will jemandem schmeicheln, aber sie wissen nicht, wen"
  whPhraseCase := "accusative"
  innerAntecedentCase := "dative"
  grammatical := false
  language := "German"
  notes := "'wen' (accusative) doesn't match 'jemandem' (dative). Ungrammatical."
  source := "Merchant (2001)"
}

/-- English shows weaker case effects -/
def englishCaseWeak : CaseMatchingDatum := {
  sentence := "Someone called, but I don't know who/whom"
  whPhraseCase := "nominative or accusative"
  innerAntecedentCase := "nominative"
  grammatical := true
  language := "English"
  notes := "English allows both 'who' and 'whom' (case neutralization)."
  source := "Merchant (2001)"
}

-- Part 3: Sprouting Data

/-- Sprouting: sluicing without overt correlate -/
structure SproutingDatum where
  sentence : String
  antecedent : String
  /-- The implicit argument that licenses sprouting -/
  implicitArgument : String
  whPhrase : String
  grammatical : Bool := true
  notes : String := ""
  source : String := ""
  deriving Repr

/-- Basic sprouting -/
def basicSprouting : SproutingDatum := {
  sentence := "John was eating, but I don't know what"
  antecedent := "John was eating"
  implicitArgument := "something (implicit object of 'eat')"
  whPhrase := "what"
  notes := "No overt correlate. 'what' corresponds to implicit object of 'eat'."
  source := "Chung et al. (1995)"
}

/-- Temporal sprouting -/
def temporalSprouting : SproutingDatum := {
  sentence := "John left, but I don't know when"
  antecedent := "John left"
  implicitArgument := "some time (implicit temporal argument)"
  whPhrase := "when"
  notes := "Sprouting with adjunct. 'when' corresponds to implicit time."
  source := "Merchant (2001)"
}

/-- Locative sprouting -/
def locativeSprouting : SproutingDatum := {
  sentence := "John put the book, but I don't know where"
  antecedent := "John put the book"
  implicitArgument := "somewhere (required locative of 'put')"
  whPhrase := "where"
  grammatical := true
  notes := "'put' requires a location; sprouting picks up this implicit argument."
  source := "Chung et al. (1995)"
}

/-- Failed sprouting - no implicit argument -/
def failedSprouting : SproutingDatum := {
  sentence := "*John slept, but I don't know what"
  antecedent := "John slept"
  implicitArgument := "none"
  whPhrase := "what"
  grammatical := false
  notes := "'sleep' has no implicit object. Sprouting fails."
  source := "Merchant (2001)"
}

-- Part 4: Scope Constraint Data

/-- Scope constraint: inner antecedent must scope over rest -/
structure ScopeConstraintDatum where
  sentence : String
  innerAntecedent : String
  /-- Does inner antecedent scope over rest of antecedent? -/
  innerAntecedentWidescope : Bool
  grammatical : Bool
  notes : String := ""
  source : String := ""
  deriving Repr

/-- Wide scope inner antecedent - grammatical -/
def wideScopeOK : ScopeConstraintDatum := {
  sentence := "Someone from every city attended, but I don't know who"
  innerAntecedent := "someone"
  innerAntecedentWidescope := true
  grammatical := true
  notes := "'someone' can scope over 'every city'. Sluicing OK."
  source := "B&S (2014)"
}

/-- Narrow scope inner antecedent - ungrammatical -/
def narrowScopeBad : ScopeConstraintDatum := {
  sentence := "*Every student read something, but I don't know what [∀ > ∃]"
  innerAntecedent := "something"
  innerAntecedentWidescope := false
  grammatical := false
  notes := "On narrow-scope reading of 'something', sluicing fails."
  source := "B&S (2014), Chung et al. (1995)"
}

/-- Wide scope reading available - grammatical -/
def wideScopeAvailable : ScopeConstraintDatum := {
  sentence := "Every student read something, but I don't know what [∃ > ∀]"
  innerAntecedent := "something"
  innerAntecedentWidescope := true
  grammatical := true
  notes := "On wide-scope reading of 'something' (specific), sluicing OK."
  source := "B&S (2014)"
}

-- Part 5: Andrews Amalgams

/-- Andrews Amalgam: recursive embedding of interrogative -/
structure AndrewsAmalgamDatum where
  sentence : String
  /-- The embedded interrogative -/
  embeddedInterrogative : String
  /-- What the interrogative fills (gap position) -/
  gapPosition : String
  grammatical : Bool := true
  notes : String := ""
  source : String := ""
  deriving Repr

/-- Basic Andrews Amalgam -/
def basicAmalgam : AndrewsAmalgamDatum := {
  sentence := "Sally will eat I don't know what today"
  embeddedInterrogative := "I don't know what"
  gapPosition := "direct object of 'eat'"
  notes := "Interrogative fills argument position. Recursive scope."
  source := "Andrews (1975)"
}

/-- Wh-clause amalgam -/
def whClauseAmalgam : AndrewsAmalgamDatum := {
  sentence := "Sally arrived at I'm not sure when"
  embeddedInterrogative := "I'm not sure when"
  gapPosition := "temporal PP complement"
  notes := "Temporal wh-phrase in amalgam position."
  source := "Lakoff (1974)"
}

-- Part 6: Answer Ban Data

/-- Answer Ban: antecedent must not resolve the sluiced question -/
structure AnswerBanDatum where
  sentence : String
  /-- Does antecedent resolve the question? -/
  antecedentResolvesQuestion : Bool
  grammatical : Bool
  notes : String := ""
  source : String := ""
  deriving Repr

/-- Answer Ban satisfied -/
def answerBanSatisfied : AnswerBanDatum := {
  sentence := "Someone left, but I don't know who"
  antecedentResolvesQuestion := false
  grammatical := true
  notes := "'Someone left' doesn't tell us WHO left. Answer Ban satisfied."
  source := "Chung et al. (1995)"
}

/-- Answer Ban violated -/
def answerBanViolated : AnswerBanDatum := {
  sentence := "*John left, but I don't know who"
  antecedentResolvesQuestion := true
  grammatical := false
  notes := "'John left' already answers 'who left'. Answer Ban violated."
  source := "Chung et al. (1995)"
}

/-- Definite violates Answer Ban -/
def definiteViolatesAnswerBan : AnswerBanDatum := {
  sentence := "*The president resigned, but I don't know who"
  antecedentResolvesQuestion := true
  grammatical := false
  notes := "Definite description resolves the question. Ungrammatical."
  source := "Merchant (2001)"
}

-- Part 7: Collected Data

/-- All basic sluicing data -/
def basicSluicingData : List SluicingDatum := [
  basicSluice,
  objectSluice,
  embeddedSluice
]

/-- All case matching data -/
def caseMatchingData : List CaseMatchingDatum := [
  germanCaseMatch,
  germanCaseMismatch,
  englishCaseWeak
]

/-- All sprouting data -/
def sproutingData : List SproutingDatum := [
  basicSprouting,
  temporalSprouting,
  locativeSprouting,
  failedSprouting
]

/-- All scope constraint data -/
def scopeConstraintData : List ScopeConstraintDatum := [
  wideScopeOK,
  narrowScopeBad,
  wideScopeAvailable
]

/-- All Andrews Amalgam data -/
def amalgamData : List AndrewsAmalgamDatum := [
  basicAmalgam,
  whClauseAmalgam
]

/-- All Answer Ban data -/
def answerBanData : List AnswerBanDatum := [
  answerBanSatisfied,
  answerBanViolated,
  definiteViolatesAnswerBan
]

-- Summary

/-!
## What This Module Provides

### Data Types
- `SluicingDatum`: Basic sluicing with antecedent and correlate
- `CaseMatchingDatum`: Case matching effects across languages
- `SproutingDatum`: Sluicing without overt correlate
- `ScopeConstraintDatum`: Inner antecedent scope requirement
- `AndrewsAmalgamDatum`: Recursive interrogative embedding
- `AnswerBanDatum`: Pragmatic constraint on antecedent

### Key Examples
- Basic sluicing: "Someone left, but I don't know who"
- Sprouting: "John was eating, but I don't know what"
- Case matching: German dative matching
- Scope constraint: Wide scope requirement for inner antecedent
- Andrews Amalgams: "Sally will eat I don't know what"
- Answer Ban: "*John left, but I don't know who"

### Theoretical Neutrality

This module records WHAT the data is. Theoretical analyses include:
- **Continuation-based** (B&S 2014): Sluicing as anaphora to continuation
- **LF-copying** (Merchant 2001): PF deletion with LF identity
- **Direct interpretation** (Chung et al. 1995): Semantic reconstruction

All theories must account for:
1. Case matching in morphologically rich languages
2. Scope constraints on inner antecedent
3. Sprouting from implicit arguments
4. Answer Ban effects

### Promissory Notes: Future Theoretical Work

**Continuation Analysis** (`Theories/Montague/Anaphora.lean`):
- SLUICEGAP as proform: `(DP⦵S)^(DP⦵S)`
- Parasitic scope parallels W combinator binding
- Tower notation for in-situ scope

**Question Semantics** (`Theories/Montague/Questions.lean`):
- Answer Ban as partition semantics constraint
- Sluiced question must remain open
- Connects to pragmatic answerhood

**Type-Logical Grammar**:
- NLλ analysis of sluicing
- Product categories for implicit arguments
- Hypothetical reasoning with continuations
-/

end Phenomena.Ellipsis.Sluicing
