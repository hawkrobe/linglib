/-
# Bathroom Sentences: Empirical Data

Theory-neutral data on "bathroom sentences" - disjunctions where a pronoun
in the second disjunct is anaphoric to an indefinite in the negated first
disjunct.

## The Phenomenon

"Either there's no bathroom, or it's upstairs."

The pronoun "it" in the second disjunct refers to "a bathroom" which is
negated in the first disjunct. This is surprising because:
1. Standard dynamic semantics: negation blocks dref introduction
2. Yet the anaphora is clearly felicitous

## Key Properties

1. **Cross-disjunct anaphora**: Pronoun in one disjunct, antecedent in another
2. **Under negation**: The antecedent is inside a negated existential
3. **Free choice**: These typically involve modal possibility
4. **Double negation pattern**: ¬¬∃x accessible iff ∃x accessible

## References

- Partee, B. (1972). Opacity, Coreference, and Pronouns.
- Elliott, P. (2023). Donkey disjunctions and overlapping updates. SALT 33.
- Elliott, P. & Sudo, Y. (2025). Free choice with anaphora. S&P 18.
- Hofmann, L. (2025). Anaphoric accessibility with flat update. S&P.
-/

namespace Phenomena.DynamicSemantics.BathroomSentences

-- ============================================================================
-- Part 1: Classic Bathroom Sentences
-- ============================================================================

/--
A bathroom sentence datum.
-/
structure BathroomDatum where
  /-- The full sentence -/
  sentence : String
  /-- First disjunct (typically negated existential) -/
  disjunct1 : String
  /-- Second disjunct (with anaphora) -/
  disjunct2 : String
  /-- The anaphoric element -/
  anaphor : String
  /-- The antecedent (under negation) -/
  antecedent : String
  /-- Is the sentence felicitous? -/
  felicitous : Bool
  /-- Does it have a modal? -/
  hasModal : Bool := false
  /-- Notes -/
  notes : String := ""
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Classic bathroom sentence -/
def classicBathroom : BathroomDatum := {
  sentence := "Either there's no bathroom, or it's upstairs"
  disjunct1 := "there's no bathroom"
  disjunct2 := "it's upstairs"
  anaphor := "it"
  antecedent := "bathroom"
  felicitous := true
  hasModal := false
  notes := "The classic example. No overt modal but epistemic reading."
  source := "Partee (1972)"
}

/-- Bathroom with explicit modal -/
def bathroomWithMight : BathroomDatum := {
  sentence := "Either there might be no bathroom, or it might be upstairs"
  disjunct1 := "there might be no bathroom"
  disjunct2 := "it might be upstairs"
  anaphor := "it"
  antecedent := "bathroom"
  felicitous := true
  hasModal := true
  notes := "Explicit epistemic modal"
  source := "Elliott & Sudo (2025)"
}

/-- Bathroom with definite article -/
def bathroomDefinite : BathroomDatum := {
  sentence := "Either there's no bathroom, or the bathroom is upstairs"
  disjunct1 := "there's no bathroom"
  disjunct2 := "the bathroom is upstairs"
  anaphor := "the bathroom"
  antecedent := "bathroom"
  felicitous := true
  hasModal := false
  notes := "Definite 'the bathroom' instead of pronoun"
  source := "Elliott & Sudo (2025)"
}

-- ============================================================================
-- Part 2: Variants and Extensions
-- ============================================================================

/-- Lost key example -/
def lostKey : BathroomDatum := {
  sentence := "Either I lost my key, or it's in my other bag"
  disjunct1 := "I lost my key"
  disjunct2 := "it's in my other bag"
  anaphor := "it"
  antecedent := "my key"
  felicitous := true
  hasModal := false
  notes := "Not literally 'bathroom' but same pattern"
  source := "Elliott & Sudo (2025)"
}

/-- Nobody came variant -/
def nobodyCame : BathroomDatum := {
  sentence := "Either nobody came, or they left early"
  disjunct1 := "nobody came"
  disjunct2 := "they left early"
  anaphor := "they"
  antecedent := "somebody (implicit)"
  felicitous := true
  hasModal := false
  notes := "Negative universal instead of negated existential"
  source := "Elliott & Sudo (2025)"
}

/-- With quantificational adverb -/
def neverBathroom : BathroomDatum := {
  sentence := "Either there's never a bathroom when you need one, or it's occupied"
  disjunct1 := "there's never a bathroom when you need one"
  disjunct2 := "it's occupied"
  anaphor := "it"
  antecedent := "bathroom"
  felicitous := true
  hasModal := false
  notes := "Negative adverb 'never' instead of 'no'"
  source := "Novel example"
}

-- ============================================================================
-- Part 3: Conditional Variants
-- ============================================================================

/-- If-then version (same pattern) -/
def conditionalVersion : BathroomDatum := {
  sentence := "If there's a bathroom, it's upstairs"
  disjunct1 := "there's a bathroom (antecedent)"
  disjunct2 := "it's upstairs (consequent)"
  anaphor := "it"
  antecedent := "bathroom"
  felicitous := true
  hasModal := false
  notes := "Conditional version - same binding pattern"
  source := "Heim (1982)"
}

/-- Unless version -/
def unlessVersion : BathroomDatum := {
  sentence := "The bathroom is upstairs, unless there isn't one"
  disjunct1 := "the bathroom is upstairs"
  disjunct2 := "there isn't one"
  anaphor := "one"
  antecedent := "bathroom"
  felicitous := true
  hasModal := false
  notes := "Reversed order with 'unless'"
  source := "Novel example"
}

-- ============================================================================
-- Part 4: Infelicitous Contrasts
-- ============================================================================

/-- Standard negation blocks (not bathroom pattern) -/
def standardNegation : BathroomDatum := {
  sentence := "There's no bathroom. It's upstairs."
  disjunct1 := "There's no bathroom"
  disjunct2 := "It's upstairs"
  anaphor := "it"
  antecedent := "bathroom"
  felicitous := false
  hasModal := false
  notes := "Across sentence boundary without disjunction - fails"
  source := "Contrast case"
}

/-- Conjunction instead of disjunction -/
def conjunctionVersion : BathroomDatum := {
  sentence := "There's no bathroom and it's upstairs"
  disjunct1 := "there's no bathroom"
  disjunct2 := "it's upstairs"
  anaphor := "it"
  antecedent := "bathroom"
  felicitous := false
  hasModal := false
  notes := "Conjunction doesn't license the pattern"
  source := "Contrast case"
}

/-- Wrong disjunction order -/
def wrongOrder : BathroomDatum := {
  sentence := "Either it's upstairs, or there's no bathroom"
  disjunct1 := "it's upstairs"
  disjunct2 := "there's no bathroom"
  anaphor := "it"
  antecedent := "bathroom"
  felicitous := false
  hasModal := false
  notes := "Cataphora to negated existential doesn't work"
  source := "Contrast case"
}

-- ============================================================================
-- Part 5: Modal Subordination Connection
-- ============================================================================

/--
Connection to modal subordination.

"A wolf might come in. It would eat you first."

Similar pattern: anaphora to hypothetical/modal entity.
-/
structure ModalSubordinationDatum where
  sentences : List String
  anaphor : String
  antecedent : String
  felicitous : Bool
  notes : String := ""
  source : String := ""
  deriving Repr

def wolfExample : ModalSubordinationDatum := {
  sentences := ["A wolf might come in.", "It would eat you first."]
  anaphor := "it"
  antecedent := "a wolf"
  felicitous := true
  notes := "Modal subordination - 'would' continues the modal context"
  source := "Roberts (1989)"
}

def burglarExample : ModalSubordinationDatum := {
  sentences := ["A burglar might break in.", "He would steal the jewelry."]
  anaphor := "he"
  antecedent := "a burglar"
  felicitous := true
  notes := "Same pattern with 'would'"
  source := "Roberts (1989)"
}

-- ============================================================================
-- Part 6: Double Negation Pattern
-- ============================================================================

/--
Double negation enables anaphora.

"It's not the case that there's no bathroom. It's upstairs."

DNE: ¬¬∃x ≈ ∃x, so x becomes accessible.
-/
structure DoubleNegationDatum where
  sentence : String
  followUp : String
  anaphor : String
  antecedent : String
  felicitous : Bool
  notes : String := ""
  source : String := ""
  deriving Repr

def doubleNegBathroom : DoubleNegationDatum := {
  sentence := "It's not the case that there's no bathroom."
  followUp := "It's upstairs."
  anaphor := "it"
  antecedent := "bathroom"
  felicitous := true
  notes := "DNE makes the bathroom accessible"
  source := "Elliott & Sudo (2025)"
}

def doubleNegNobody : DoubleNegationDatum := {
  sentence := "It's not the case that nobody came."
  followUp := "They're in the garden."
  anaphor := "they"
  antecedent := "people (implicit)"
  felicitous := true
  notes := "DNE with negative quantifier"
  source := "Elliott & Sudo (2025)"
}

-- ============================================================================
-- Part 7: Collected Data
-- ============================================================================

/-- All bathroom sentence examples -/
def bathroomData : List BathroomDatum := [
  classicBathroom,
  bathroomWithMight,
  bathroomDefinite,
  lostKey,
  nobodyCame,
  neverBathroom,
  conditionalVersion,
  unlessVersion,
  standardNegation,
  conjunctionVersion,
  wrongOrder
]

/-- Felicitous bathroom sentences -/
def felicitousBathroom : List BathroomDatum :=
  bathroomData.filter (·.felicitous)

/-- Infelicitous contrasts -/
def infelicitousBathroom : List BathroomDatum :=
  bathroomData.filter (!·.felicitous)

/-- Modal subordination examples -/
def modalSubordinationData : List ModalSubordinationDatum := [
  wolfExample,
  burglarExample
]

/-- Double negation examples -/
def doubleNegationData : List DoubleNegationDatum := [
  doubleNegBathroom,
  doubleNegNobody
]

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Data Types
- `BathroomDatum`: Bathroom-type disjunction
- `ModalSubordinationDatum`: Related modal subordination
- `DoubleNegationDatum`: DNE accessibility pattern

### Key Examples
- `classicBathroom`: "Either there's no bathroom, or it's upstairs"
- `standardNegation`: Contrast showing sentence boundary blocks
- `doubleNegBathroom`: DNE enables anaphora

### Collections
- `bathroomData`: 11 bathroom-type examples
- `felicitousBathroom`: 8 felicitous cases
- `infelicitousBathroom`: 3 infelicitous contrasts
- `modalSubordinationData`: 2 modal subordination examples
- `doubleNegationData`: 2 DNE examples

### Theoretical Relevance

Key data for:
- BUS (Bilateral Update Semantics): Negation swaps positive/negative
- ICDRT (Intensional CDRT): Flat update with propositional drefs
- DRT: Extended accessibility conditions
- E-type: Domain widening analysis
-/

end Phenomena.DynamicSemantics.BathroomSentences
