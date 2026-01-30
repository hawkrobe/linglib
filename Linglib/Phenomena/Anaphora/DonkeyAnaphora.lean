/-
# Donkey Anaphora: Empirical Data

Theory-neutral data on donkey anaphora and related binding puzzles.

## The Phenomenon

Donkey sentences involve pronouns that are apparently bound by indefinites
in syntactically "inaccessible" positions:

  "Every farmer who owns a donkey beats it"

The indefinite "a donkey" is inside a relative clause, yet "it" seems
to depend on it for its reference.

## Key Properties

1. **Scope puzzle**: The indefinite doesn't c-command the pronoun
2. **Universal force**: Often interpreted as "...beats every donkey they own"
3. **Weak readings**: Sometimes "...beats some donkey they own"
4. **Proportion problem**: "Most farmers who own a donkey beat it"

## References

- Geach, P. (1962). Reference and Generality. (introduced the puzzle)
- Evans, G. (1977). Pronouns, Quantifiers, and Relative Clauses.
- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases.
- Groenendijk & Stokhof (1991). Dynamic Predicate Logic.
- Kanazawa, M. (1994). Weak vs. Strong Readings of Donkey Sentences.
-/

import Linglib.Phenomena.Basic

namespace Phenomena.Anaphora.DonkeyAnaphora

-- ============================================================================
-- Part 1: Basic Donkey Sentence Data
-- ============================================================================

/-- A donkey anaphora datum records a sentence with its readings -/
structure DonkeyDatum where
  /-- The sentence -/
  sentence : String
  /-- Does the pronoun depend on the indefinite? -/
  boundReading : Bool
  /-- Is a universal ("strong") reading available? -/
  strongReading : Bool
  /-- Is an existential ("weak") reading available? -/
  weakReading : Bool
  /-- Is the sentence grammatical? -/
  grammatical : Bool := true
  /-- Notes on the reading -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

/-- Classic Geach donkey sentence -/
def geachDonkey : DonkeyDatum := {
  sentence := "Every farmer who owns a donkey beats it"
  boundReading := true
  strongReading := true  -- every donkey they own
  weakReading := true    -- some donkey they own (less salient)
  notes := "The original donkey sentence. Strong reading preferred."
  source := "Geach (1962)"
}

/-- Conditional donkey -/
def conditionalDonkey : DonkeyDatum := {
  sentence := "If a farmer owns a donkey, he beats it"
  boundReading := true
  strongReading := true
  weakReading := true
  notes := "Conditional variant. Similar to relative clause version."
  source := "Heim (1982)"
}

/-- Negated donkey -/
def negatedDonkey : DonkeyDatum := {
  sentence := "No farmer who owns a donkey beats it"
  boundReading := true
  strongReading := true  -- no farmer beats any donkey they own
  weakReading := false   -- weak reading incoherent here
  notes := "Negation context. Universal reading only."
  source := "Kanazawa (1994)"
}

/-- "Most" donkey (proportion problem) -/
def mostDonkey : DonkeyDatum := {
  sentence := "Most farmers who own a donkey beat it"
  boundReading := true
  strongReading := true
  weakReading := true
  notes := "The proportion problem: is this about farmer-donkey pairs or farmers?"
  source := "Kadmon (1987)"
}

-- ============================================================================
-- Part 2: Weak vs Strong Readings
-- ============================================================================

/-- Data on weak vs strong reading availability -/
structure WeakStrongDatum where
  sentence : String
  strongAvailable : Bool
  weakAvailable : Bool
  preferredReading : String  -- "strong", "weak", or "both"
  context : String := ""
  source : String := ""
  deriving Repr

/-- Strong reading dominant -/
def strongDominant : WeakStrongDatum := {
  sentence := "Every farmer who owns a donkey beats it"
  strongAvailable := true
  weakAvailable := true
  preferredReading := "strong"
  context := "Out of the blue"
  source := "Kanazawa (1994)"
}

/-- Weak reading facilitated by context -/
def weakFacilitated : WeakStrongDatum := {
  sentence := "Every person who has a credit card uses it to pay"
  strongAvailable := true
  weakAvailable := true
  preferredReading := "weak"
  context := "Buying groceries (single transaction)"
  source := "Chierchia (1995)"
}

/-- Only strong reading possible -/
def onlyStrong : WeakStrongDatum := {
  sentence := "No farmer who owns a donkey mistreats it"
  strongAvailable := true
  weakAvailable := false
  preferredReading := "strong"
  context := "Negative quantifier forces universal"
  source := "Kanazawa (1994)"
}

-- ============================================================================
-- Part 3: Related Anaphora Puzzles
-- ============================================================================

/-- Bathroom sentences (Partee) -/
def bathroomSentence : DonkeyDatum := {
  sentence := "Either there is no bathroom, or it is in a funny place"
  boundReading := true
  strongReading := false
  weakReading := false
  notes := "Pronoun 'it' depends on 'bathroom' across disjunction."
  source := "Partee (1972)"
}

/-- Paycheck pronouns -/
def paycheckSentence : DonkeyDatum := {
  sentence := "The man who gave his paycheck to his wife was wiser than the man who gave it to his mistress"
  boundReading := true
  strongReading := false
  weakReading := false
  notes := "'it' = 'his paycheck', but with second man's paycheck"
  source := "Karttunen (1969)"
}

/-- Sage plant sentences (Evans) -/
def sagePlant : DonkeyDatum := {
  sentence := "Few congressmen admire Kennedy, and they are very junior"
  boundReading := true
  strongReading := false
  weakReading := false
  notes := "'they' refers to the few congressmen who do admire Kennedy"
  source := "Evans (1977)"
}

-- ============================================================================
-- Part 4: Cross-sentential Donkey Anaphora
-- ============================================================================

/-- Discourse-level donkey anaphora -/
structure DiscourseDonkeyDatum where
  sentences : List String
  pronounSentenceIdx : Nat  -- which sentence contains the pronoun
  antecedentSentenceIdx : Nat  -- which sentence contains the antecedent
  grammatical : Bool
  notes : String := ""
  source : String := ""
  deriving Repr

/-- Cross-sentential binding -/
def crossSententialDonkey : DiscourseDonkeyDatum := {
  sentences := ["Every farmer owns a donkey.", "He beats it."]
  pronounSentenceIdx := 1
  antecedentSentenceIdx := 0
  grammatical := false  -- binding doesn't cross sentence boundary
  notes := "Quantifier scope doesn't extend across sentences"
  source := "Heim (1982)"
}

/-- Indefinite persists across sentences -/
def indefinitePersists : DiscourseDonkeyDatum := {
  sentences := ["A man walked in.", "He sat down."]
  pronounSentenceIdx := 1
  antecedentSentenceIdx := 0
  grammatical := true
  notes := "Indefinite introduces discourse referent that persists"
  source := "Heim (1982)"
}

-- ============================================================================
-- Part 5: Proportion Problem Data
-- ============================================================================

/-- The proportion problem: what is being counted? -/
structure ProportionDatum where
  sentence : String
  /-- Farmer-counting: proportion of farmers (who own donkeys) -/
  farmerCountingReading : String
  /-- Pair-counting: proportion of farmer-donkey pairs -/
  pairCountingReading : String
  /-- Which reading is more natural? -/
  preferredReading : String
  source : String := ""
  deriving Repr

/-- Classic proportion problem case -/
def proportionProblem : ProportionDatum := {
  sentence := "Most farmers who own a donkey beat it"
  farmerCountingReading := "Most farmers (among those who own donkeys) beat their donkey(s)"
  pairCountingReading := "Most farmer-donkey pairs are such that the farmer beats the donkey"
  preferredReading := "farmer-counting"
  source := "Kadmon (1987)"
}

-- ============================================================================
-- Part 6: Collected Data
-- ============================================================================

/-- All basic donkey data -/
def donkeyData : List DonkeyDatum := [
  geachDonkey,
  conditionalDonkey,
  negatedDonkey,
  mostDonkey,
  bathroomSentence,
  paycheckSentence,
  sagePlant
]

/-- All weak/strong reading data -/
def weakStrongData : List WeakStrongDatum := [
  strongDominant,
  weakFacilitated,
  onlyStrong
]

/-- All discourse-level data -/
def discourseDonkeyData : List DiscourseDonkeyDatum := [
  crossSententialDonkey,
  indefinitePersists
]

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Data Types
- `DonkeyDatum`: Basic donkey sentence with reading information
- `WeakStrongDatum`: Weak vs strong reading availability
- `DiscourseDonkeyDatum`: Cross-sentential anaphora
- `ProportionDatum`: Proportion problem cases

### Key Examples
- `geachDonkey`: Classic "Every farmer who owns a donkey beats it"
- `conditionalDonkey`: "If a farmer owns a donkey, he beats it"
- `bathroomSentence`: "Either there is no bathroom, or it is in a funny place"
- `paycheckSentence`: Paycheck pronouns (functional reading)

### Theoretical Neutrality

This module records WHAT the data is, not how to analyze it:
- Dynamic semantics (Heim, G&S): Indefinites introduce discourse referents
- E-type (Evans): Pronouns are disguised definite descriptions
- Choice functions (Reinhart): Indefinites denote choice functions
- DRT (Kamp): Boxes and accessibility

All theories must account for this data; none is privileged here.
-/

end Phenomena.Anaphora.DonkeyAnaphora
