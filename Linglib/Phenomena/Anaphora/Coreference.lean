/-
# Coreference Patterns

## The Phenomenon

Languages constrain when two nominal expressions can refer to the same entity.
These patterns concern the distribution of reflexives, pronouns, and full
nominal expressions (names, descriptions) with respect to potential antecedents.

## The Data

### Reflexive Coreference

Reflexives require a local antecedent - an expression in the same local domain
(roughly, the same clause) that they can be interpreted as coreferent with.

  (1a)  John saw himself.                 ✓  reflexive has local antecedent
  (1b) *Himself saw John.                 ✗  no c-commanding antecedent
  (1c) *John thinks Mary saw himself.     ✗  antecedent not in local domain

### Pronominal Disjoint Reference

Pronouns resist coreference with a local antecedent - they prefer to refer
to a different entity than a nearby (clause-mate) nominal.

  (2a)  John thinks Mary saw him.         ✓  pronoun refers to non-local John
  (2b) *John saw him. (him = John)        ✗  pronoun resists local coreference
  (2c)  John saw him. (him ≠ John)        ✓  disjoint reference is fine

### Referential Expression Freedom

Full nominals (names, descriptions) generally cannot be interpreted as
coreferent with a c-commanding expression.

  (3a)  He thinks Mary likes John.        ✓  (he ≠ John) disjoint reference
  (3b) *He likes John. (he = John)        ✗  name resists bound reading

### Complementary Distribution

Reflexives and pronouns show complementary distribution in the local domain:
where reflexives are required, pronouns are blocked (for coreference), and
vice versa.

  (4a)  John saw himself.                 ✓  local → reflexive
  (4b) *John saw him. (him = John)        ✗  local → pronoun blocked
  (4c) *John thinks Mary saw himself.     ✗  non-local → reflexive blocked
  (4d)  John thinks Mary saw him.         ✓  non-local → pronoun ok

## References

- Chomsky, N. (1981). Lectures on Government and Binding. (theoretical)
- Büring, D. (2005). Binding Theory. (overview)
- Pollard, C. & I. Sag (1994). Head-Driven Phrase Structure Grammar, Ch. 6.
- Langacker, R. (1991). Foundations of Cognitive Grammar, Vol. 2. (reference points)
- König, E. & P. Siemund (2000). "Intensifiers and Reflexives" in Haspelmath et al.
-/

import Linglib.Phenomena.Core.Basic

open Lexicon

-- Reflexive Coreference

/-- Reflexives require a local antecedent for coreference -/
def reflexiveCoreferenceData : PhenomenonData := {
  name := "Reflexive Coreference"
  generalization := "Reflexives require a c-commanding antecedent in the local domain"
  pairs := [
    -- Local antecedent required
    { grammatical := [john, sees, himself]
      ungrammatical := [himself, sees, john]
      clauseType := .declarative
      description := "Reflexive needs c-commanding antecedent"
      citation := some "Chomsky (1981); Pollard & Sag (1994)" },

    { grammatical := [mary, sees, herself]
      ungrammatical := [herself, sees, mary]
      clauseType := .declarative
      description := "Reflexive needs c-commanding antecedent" },

    { grammatical := [they, see, themselves]
      ungrammatical := [themselves, see, them]
      clauseType := .declarative
      description := "Plural reflexive needs plural antecedent" },

    -- Agreement required
    { grammatical := [john, sees, himself]
      ungrammatical := [john, sees, herself]
      clauseType := .declarative
      description := "Reflexive must agree with antecedent (gender)" },

    { grammatical := [they, see, themselves]
      ungrammatical := [they, see, himself]
      clauseType := .declarative
      description := "Reflexive must agree with antecedent (number)" }
  ]
}

-- Pronominal Disjoint Reference

/-- Pronouns resist coreference with local antecedents -/
def pronominalDisjointReferenceData : PhenomenonData := {
  name := "Pronominal Disjoint Reference"
  generalization := "Pronouns cannot corefer with a c-commanding nominal in the local domain"
  pairs := [
    -- Coreference blocked locally (the ungrammatical reading is with coreference)
    { grammatical := [john, sees, mary]
      ungrammatical := [john, sees, him]  -- intended: John₁ sees him₁
      clauseType := .declarative
      description := "Pronoun resists coreference with local subject"
      citation := some "Chomsky (1981)" },

    { grammatical := [mary, sees, john]
      ungrammatical := [mary, sees, her]  -- intended: Mary₁ sees her₁
      clauseType := .declarative
      description := "Pronoun resists coreference with local subject" }
  ]
}

-- Referential Expression Freedom

/-- Full nominals resist coreference with c-commanding expressions -/
def referentialExpressionFreedomData : PhenomenonData := {
  name := "Referential Expression Freedom"
  generalization := "Names and descriptions cannot corefer with a c-commanding pronoun"
  pairs := [
    { grammatical := [john, sees, mary]
      ungrammatical := [he, sees, john]  -- intended: He₁ sees John₁
      clauseType := .declarative
      description := "Name resists coreference with c-commanding pronoun"
      citation := some "Chomsky (1981)" }
  ]
}

-- Complementary Distribution

/-- Reflexives and pronouns are in complementary distribution for coreference -/
def complementaryDistributionData : PhenomenonData := {
  name := "Complementary Distribution"
  generalization := "In the local domain, coreference requires reflexive; pronouns are blocked"
  pairs := [
    { grammatical := [john, sees, himself]
      ungrammatical := [john, sees, him]  -- intended coreference
      clauseType := .declarative
      description := "Local coreference: reflexive required, pronoun blocked"
      citation := some "Chomsky (1981)" },

    { grammatical := [mary, sees, herself]
      ungrammatical := [mary, sees, her]  -- intended coreference
      clauseType := .declarative
      description := "Local coreference: reflexive required, pronoun blocked" }
  ]
}

-- Combined Coreference Data

/-- All coreference pattern data -/
def coreferenceData : List PhenomenonData := [
  reflexiveCoreferenceData,
  pronominalDisjointReferenceData,
  referentialExpressionFreedomData,
  complementaryDistributionData
]

-- Coreference Pattern Types

/-- Types of anaphoric expressions -/
inductive AnaphorType where
  | reflexive    -- himself, herself, themselves
  | reciprocal   -- each other
  | pronoun      -- he, she, they, him, her, them
  | name         -- John, Mary
  | description  -- the man, a woman
  deriving Repr, DecidableEq

/-- Domain types for coreference constraints -/
inductive Domain where
  | local_     -- within the same clause
  | nonlocal   -- across clause boundaries
  | any        -- no domain restriction
  deriving Repr, DecidableEq

/-- Coreference requirement for an anaphor type -/
structure CoreferencePattern where
  anaphorType : AnaphorType
  requiresAntecedent : Bool           -- must have an antecedent?
  antecedentDomain : Option Domain    -- where must/can't antecedent be?
  deriving Repr

/-- English reflexives require local antecedents -/
def reflexivePattern : CoreferencePattern := {
  anaphorType := .reflexive
  requiresAntecedent := true
  antecedentDomain := some .local_
}

/-- English pronouns are free locally (antecedent must be non-local or absent) -/
def pronounPattern : CoreferencePattern := {
  anaphorType := .pronoun
  requiresAntecedent := false
  antecedentDomain := some .nonlocal  -- if coreferent, must be non-local
}

/-- Names are referentially free -/
def namePattern : CoreferencePattern := {
  anaphorType := .name
  requiresAntecedent := false
  antecedentDomain := none  -- cannot have c-commanding antecedent
}

-- Tests

#eval wordsToString [john, sees, himself]   -- "John sees himself"
#eval wordsToString [mary, sees, herself]   -- "Mary sees herself"
#eval wordsToString [they, see, themselves] -- "they see themselves"
