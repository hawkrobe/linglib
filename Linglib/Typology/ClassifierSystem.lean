import Linglib.Core.Lexical.NounCategorization
import Linglib.Datasets.WALS.Features.F55A

/-!
# Noun categorization typology: per-language system schema
@cite{aikhenvald-2000}

Per-language schema for the `classifierSystem` def in each
`Fragments/{Lang}/ClassifierSystem.lean`, parallel to `Typology.WordOrder`
and `Typology.Adposition`. Captures @cite{aikhenvald-2000}'s 7 definitional
properties (A–G from §1.5) of a noun categorization system.

## What lives here vs. `Core.Lexical.NounCategorization`

- `Core.Lexical.NounCategorization` (sibling file) carries the
  framework-agnostic *vocabulary* (`ClassifierType`, `SemanticParameter`,
  `ShapeDimension`, `ClassifierStrategy`, `ClassifierEntry`).
- This file carries the *per-language description*
  (`NounCategorizationSystem`) that bundles a language's choices on
  those vocabulary types.

## What does NOT live here

Theoretical commitments about *which strategy* mediates the numeral-noun
composition (`forNoun` per Chierchia, `sudoBlocking` per Sudo) live in
the relevant `Phenomena/Classifiers/Studies/` files, not on this
description. Cross-paper disagreement is proved as theorems, not
embedded as metadata.
-/

namespace Typology

open Core.NounCategorization

/-- A noun categorization system in a language.

    Captures @cite{aikhenvald-2000}'s 7 definitional properties (A–G from §1.5):
    (A) morphosyntactic locus → `scopes`
    (B) scope/domain → `classifierType` + `scopes`
    (C) assignment principles → `assignment`
    (D) surface realization → `realizations`
    (E) agreement → `hasAgreement`
    (F) markedness → `hasUnmarkedDefault`
    (G) grammaticalization → `isObligatory` -/
structure NounCategorizationSystem where
  /-- Language family (e.g., "Indo-European", "Sino-Tibetan", "Bantu"). -/
  family : String
  /-- Aikhenvald classifier type. -/
  classifierType : ClassifierType
  /-- Morphosyntactic scopes this system operates in (A, B). -/
  scopes : List CategorizationScope
  /-- How nouns are assigned to classes/classifiers (C). -/
  assignment : AssignmentPrinciple
  /-- Morphological realization types used (D). -/
  realizations : List SurfaceRealization
  /-- Does the system involve agreement? (E) — definitional for noun classes.
      Stored as `Bool` so the struct stays decidable as a whole; the
      user-facing predicate is `HasAgreement : Prop`. -/
  hasAgreement : Bool
  /-- Inventory size (number of classes or classifiers). -/
  inventorySize : Nat
  /-- Is realization obligatory or optional? (G). User-facing predicate:
      `IsObligatory : Prop`. -/
  isObligatory : Bool
  /-- Is there a formally/functionally unmarked default? (F). User-facing
      predicate: `HasUnmarkedDefault : Prop`. -/
  hasUnmarkedDefault : Bool := false
  /-- Preferred semantic parameters (§11.2, Table 11.13). -/
  preferredSemantics : List SemanticParameter := []
  /-- Does the language have obligatory grammatical number marking?
      User-facing predicate: `HasObligatoryNumber : Prop`. -/
  hasObligatoryNumber : Bool := false
  /-- Can classifiers and plural marking co-occur? Predicted by CLF-for-NUM
      (@cite{little-moroney-royer-2022} §3.4: CLF and PL are in different
      projections) but not by CLF-for-N (same projection, complementary
      distribution per @cite{borer-2005}). User-facing predicate:
      `PluralClfCooccur : Prop`. -/
  pluralClfCooccur : Bool := false
  /-- Citation backing the hand-coded values. -/
  source : String := ""
  deriving Repr, DecidableEq

namespace NounCategorizationSystem

/-! ## Prop API for the boolean property fields

The struct's `hasAgreement`/`isObligatory`/`hasUnmarkedDefault`/
`hasObligatoryNumber`/`pluralClfCooccur` fields are stored as `Bool` so
the struct itself stays decidably equal. The user-facing predicates are
the `Prop` versions defined here, each with a `Decidable` instance via
the underlying `Bool`. Theorem statements should prefer the `Prop` form
(`s.HasAgreement` rather than `s.hasAgreement = true`); `decide` works
for either since the Bool projection reduces structurally for concrete
fragment values. -/

/-- The system involves agreement (E). -/
abbrev HasAgreement (s : NounCategorizationSystem) : Prop := s.hasAgreement = true

/-- Realization is obligatory (G). -/
abbrev IsObligatory (s : NounCategorizationSystem) : Prop := s.isObligatory = true

/-- The system has a formally/functionally unmarked default (F). -/
abbrev HasUnmarkedDefault (s : NounCategorizationSystem) : Prop :=
  s.hasUnmarkedDefault = true

/-- The language has obligatory grammatical number marking. -/
abbrev HasObligatoryNumber (s : NounCategorizationSystem) : Prop :=
  s.hasObligatoryNumber = true

/-- Classifiers and plural marking can co-occur. -/
abbrev PluralClfCooccur (s : NounCategorizationSystem) : Prop :=
  s.pluralClfCooccur = true

/-- @cite{dixon-1982}'s noun-class vs. classifier divide (Table 1.2).
    Noun classes: small, closed, grammaticalized, agreement.
    Classifiers: large, open, lexical, no agreement. -/
def isNounClassType (t : ClassifierType) : Bool :=
  t == .nounClass

/-- All non-noun-class types are "classifier" types in the broad sense. -/
def isClassifierType (t : ClassifierType) : Bool :=
  !isNounClassType t

end NounCategorizationSystem

/-- Grammatical categories that interact with classifier types
    (@cite{aikhenvald-2000} Table 10.17). -/
inductive GrammaticalCategory where
  | definiteness | number | case_ | tenseAspect | possession
  deriving DecidableEq, Repr

/-- Whether a classifier type typically interacts with a grammatical category
    (@cite{aikhenvald-2000} Table 10.17). -/
def interacts : ClassifierType → GrammaticalCategory → Bool
  | .nounClass, .definiteness => true
  | .nounClass, .number => true
  | .nounClass, .case_ => true
  | .nounClass, .tenseAspect => true
  | .nounClass, .possession => true
  | .numeralClassifier, .definiteness => true
  | .numeralClassifier, .number => true
  | .numeralClassifier, .possession => false
  | .numeralClassifier, .case_ => false
  | .numeralClassifier, .tenseAspect => false
  | .verbalClassifier, .tenseAspect => true
  | .verbalClassifier, .number => true
  | .relationalClassifier, .possession => true
  | .possessedClassifier, .possession => true
  | _, _ => false

/-- Whether a language uses numeral classifiers (@cite{wals-2013} Ch 55). -/
inductive ClassifierStatus where
  /-- No numeral classifiers (e.g., English, Spanish, Arabic). -/
  | absent
  /-- Classifiers available but not required (e.g., Turkish, Bengali). -/
  | optional
  /-- Classifiers required (e.g., Mandarin, Japanese, Thai). -/
  | obligatory
  deriving DecidableEq, Repr

end Typology

-- ============================================================================
-- WALS Chapter 55 — Numeral Classifiers (Gil)
-- ============================================================================

namespace Typology

/-- Convert WALS 55A numeral classifier values to the local `ClassifierStatus`. -/
def fromWALS55A : Datasets.WALS.F55A.NumeralClassifiers → ClassifierStatus
  | .absent => .absent
  | .optional => .optional
  | .obligatory => .obligatory

/-- WALS Chapter 55 distribution: language counts per classifier status.
    Total: 400 languages. -/
structure ClassifierDistribution where
  absent : Nat
  optional : Nat
  obligatory : Nat
  deriving Repr

def ClassifierDistribution.total (d : ClassifierDistribution) : Nat :=
  d.absent + d.optional + d.obligatory

/-- Actual WALS Ch 55 counts (260 absent + 62 optional + 78 obligatory = 400). -/
def ch55Distribution : ClassifierDistribution :=
  { absent := 260
  , optional := 62
  , obligatory := 78 }

end Typology
