import Linglib.Core.Lexical.NounCategorization

/-!
# Noun categorization typology: per-language system schema
@cite{aikhenvald-2000}

Per-language schema for `Typology.LanguageProfile`'s
`classifierSystem` field, parallel to `Typology.WordOrder` and
`Typology.Adposition`. Captures @cite{aikhenvald-2000}'s 7
definitional properties (A–G from §1.5) of a noun categorization
system.

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
  /-- Does the system involve agreement? (E) — definitional for noun classes. -/
  hasAgreement : Bool
  /-- Inventory size (number of classes or classifiers). -/
  inventorySize : Nat
  /-- Is realization obligatory or optional? (G) -/
  isObligatory : Bool
  /-- Is there a formally/functionally unmarked default? (F) -/
  hasUnmarkedDefault : Bool := false
  /-- Preferred semantic parameters (§11.2, Table 11.13). -/
  preferredSemantics : List SemanticParameter := []
  /-- Does the language have obligatory grammatical number marking? -/
  hasObligatoryNumber : Bool := false
  /-- Can classifiers and plural marking co-occur? Predicted by CLF-for-NUM
      (@cite{little-moroney-royer-2022} §3.4: CLF and PL are in different
      projections) but not by CLF-for-N (same projection, complementary
      distribution per @cite{borer-2005}). -/
  pluralClfCooccur : Bool := false
  /-- Citation backing the hand-coded values. -/
  source : String := ""
  deriving Repr, DecidableEq

namespace NounCategorizationSystem

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

end Typology
