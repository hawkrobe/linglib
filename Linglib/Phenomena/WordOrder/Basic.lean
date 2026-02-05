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

import Linglib.Core.Basic

namespace Phenomena.WordOrder

/-- Basic word order data.

Pure empirical data with no theoretical commitments.
Theories interpret this via their Bridge modules. -/
def data : StringPhenomenonData := {
  name := "Basic Word Order"
  generalization := "English declaratives have SVO order"
  pairs := [
    { grammatical := "John sees Mary"
      ungrammatical := "John Mary sees"
      clauseType := .declarative
      description := "SVO, not SOV" },

    { grammatical := "John sees Mary"
      ungrammatical := "sees John Mary"
      clauseType := .declarative
      description := "SVO, not VSO" },

    { grammatical := "Mary eats pizza"
      ungrammatical := "Mary pizza eats"
      clauseType := .declarative
      description := "SVO, not SOV" },

    { grammatical := "he sees her"
      ungrammatical := "he her sees"
      clauseType := .declarative
      description := "SVO with pronouns" }
  ]
}

end Phenomena.WordOrder
