/-
# Coreference Patterns


Empirical data on coreference constraints for reflexives, pronouns, and full nominals.

## Main definitions

- `reflexiveCoreferenceData`: Reflexives require local c-commanding antecedent
- `pronominalDisjointReferenceData`: Pronouns cannot corefer locally
- `complementaryDistributionData`: Reflexives and pronouns in complementary distribution
- `AnaphorType`, `CoreferencePattern`: Classification of anaphoric expressions

-/

import Linglib.Core.Grammar

namespace Phenomena.Anaphora.Coreference

private def john : Word := ⟨"John", .PROPN, { number := some .sg, person := some .third }⟩
private def sees : Word := ⟨"sees", .VERB, { valence := some .transitive, number := some .sg, person := some .third }⟩
private def himself : Word := ⟨"himself", .PRON, { person := some .third, number := some .sg }⟩
private def mary : Word := ⟨"Mary", .PROPN, { number := some .sg, person := some .third }⟩
private def herself : Word := ⟨"herself", .PRON, { person := some .third, number := some .sg }⟩
private def they : Word := ⟨"they", .PRON, { person := some .third, number := some .pl, case_ := some .nom }⟩
private def see : Word := ⟨"see", .VERB, { valence := some .transitive, number := some .pl }⟩
private def themselves : Word := ⟨"themselves", .PRON, { person := some .third, number := some .pl }⟩
private def him : Word := ⟨"him", .PRON, { person := some .third, number := some .sg, case_ := some .acc }⟩
private def her : Word := ⟨"her", .PRON, { person := some .third, number := some .sg, case_ := some .acc }⟩
private def he : Word := ⟨"he", .PRON, { person := some .third, number := some .sg, case_ := some .nom }⟩
private def them : Word := ⟨"them", .PRON, { person := some .third, number := some .pl, case_ := some .acc }⟩

/-- Reflexives require local c-commanding antecedent. -/
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

/-- Pronouns cannot corefer with local c-commanding antecedent. -/
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

/-- Full nominals cannot corefer with c-commanding pronoun. -/
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

/-- Reflexives and pronouns in complementary distribution. -/
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

-- ============================================================================
-- Reciprocal Coreference Data
-- ============================================================================

private def sam : Word := ⟨"Sam", .PROPN, { number := some .sg, person := some .third }⟩
private def pat : Word := ⟨"Pat", .PROPN, { number := some .sg, person := some .third }⟩
private def and_ : Word := ⟨"and", .CCONJ, {}⟩
private def saw : Word := ⟨"saw", .VERB, { valence := some .transitive }⟩
private def eachOther : Word := ⟨"each other", .PRON, { person := some .third, number := some .pl }⟩

/-- Reciprocals require a plural/coordinated antecedent and local binding. -/
def reciprocalCoreferenceData : PhenomenonData := {
  name := "Reciprocal Coreference"
  generalization := "Reciprocals require a c-commanding semantically plural antecedent in the local domain"
  pairs := [
    -- Coordinated antecedent required
    { grammatical := [sam, and_, pat, saw, eachOther]
      ungrammatical := [eachOther, saw, sam, and_, pat]
      clauseType := .declarative
      description := "Reciprocal needs c-commanding antecedent"
      citation := some "Dalrymple et al. (1998)" },

    -- Reciprocal vs reflexive complementary distribution
    { grammatical := [sam, and_, pat, saw, eachOther]
      ungrammatical := [sam, and_, pat, saw, themselves]  -- awkward as reciprocal reading
      clauseType := .declarative
      description := "Reciprocal preferred for symmetric reading with coordinated subject" },

    -- Plural antecedent requirement
    { grammatical := [they, see, eachOther]
      ungrammatical := [john, sees, eachOther]  -- singular antecedent fails
      clauseType := .declarative
      description := "Reciprocal requires semantically plural antecedent" }
  ]
}

def coreferenceData : List PhenomenonData := [
  reflexiveCoreferenceData,
  pronominalDisjointReferenceData,
  referentialExpressionFreedomData,
  complementaryDistributionData,
  reciprocalCoreferenceData
]

/-- Types of anaphoric expressions. -/
inductive AnaphorType where
  | reflexive
  | reciprocal
  | pronoun
  | name
  | description
  deriving Repr, DecidableEq

/-- Domain types for coreference constraints. -/
inductive Domain where
  | local_
  | nonlocal
  | any
  deriving Repr, DecidableEq

/-- Coreference requirements for an anaphor type. -/
structure CoreferencePattern where
  anaphorType : AnaphorType
  requiresAntecedent : Bool
  antecedentDomain : Option Domain
  deriving Repr

def reflexivePattern : CoreferencePattern := {
  anaphorType := .reflexive
  requiresAntecedent := true
  antecedentDomain := some .local_
}

def pronounPattern : CoreferencePattern := {
  anaphorType := .pronoun
  requiresAntecedent := false
  antecedentDomain := some .nonlocal
}

def namePattern : CoreferencePattern := {
  anaphorType := .name
  requiresAntecedent := false
  antecedentDomain := none
}

/-- Reciprocal coreference pattern: requires a c-commanding antecedent
    that denotes a plurality. The antecedent can be syntactically singular
    in some languages (e.g., Hungarian null pronouns bound by a plural
    matrix subject; @cite{rakosi-2019}, @cite{dalrymple-haug-2024} §2).
    The domain is local for the pronoun antecedent, but the reciprocal's
    semantic contribution can scope wider (I-reading). -/
def reciprocalPattern : CoreferencePattern := {
  anaphorType := .reciprocal
  requiresAntecedent := true
  antecedentDomain := some .local_
}

end Phenomena.Anaphora.Coreference
