/-
# Basic Word Order

## The Phenomenon

English is an SVO (Subject-Verb-Object) language in declarative sentences.
The subject precedes the verb, and the object follows the verb.

## The Data

  (1a)  John sees Mary.              ✓  SVO order
  (1b) *John Mary sees.              ✗  SOV order
  (1c) *Sees John Mary.              ✗  VSO order

  (2a)  The cat eats pizza.          ✓  SVO order
  (2b) *The cat pizza eats.          ✗  SOV order
-/

import Linglib.Phenomena.Core.Basic
import Linglib.Theories.Surface.Basic

open Lexicon

-- ============================================================================
-- The Empirical Data
-- ============================================================================

/-- Basic word order data -/
def wordOrderData : PhenomenonData := {
  name := "Basic Word Order"
  generalization := "English declaratives have SVO order"
  pairs := [
    { grammatical := [john, sees, mary]
      ungrammatical := [john, mary, sees]
      clauseType := .declarative
      description := "SVO, not SOV" },

    { grammatical := [john, sees, mary]
      ungrammatical := [sees, john, mary]
      clauseType := .declarative
      description := "SVO, not VSO" },

    { grammatical := [mary, eats, pizza]
      ungrammatical := [mary, pizza, eats]
      clauseType := .declarative
      description := "SVO, not SOV" },

    { grammatical := [he, sees, her]
      ungrammatical := [he, her, sees]
      clauseType := .declarative
      description := "SVO with pronouns" }
  ]
}

-- ============================================================================
-- Tests
-- ============================================================================

#eval Surface.wordOrderOk [john, sees, mary] .declarative  -- true (SVO)
#eval Surface.wordOrderOk [john, mary, sees] .declarative  -- true (verb still after subj)
-- Note: the current simple checker only verifies S < V, not full SVO
-- A more complete implementation would check V < O as well
