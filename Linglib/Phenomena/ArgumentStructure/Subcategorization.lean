/-
# Subcategorization (Argument Structure)

## The Phenomenon

Verbs select for a specific number and type of arguments.
- Intransitive verbs: no object (*John slept the bed)
- Transitive verbs: require an object (*John devoured)
- Ditransitive verbs: require two objects (*John gave Mary / *John gave the book)

## The Data

  (1a)  John sleeps.                 ✓  intransitive, no object
  (1b) *John sleeps the bed.         ✗  intransitive with object

  (2a)  John devours pizza.          ✓  transitive with object
  (2b) *John devours.                ✗  transitive without object

  (3a)  John gives Mary the book.    ✓  ditransitive with two objects
  (3b) *John gives Mary.             ✗  ditransitive with one object
  (3c) *John gives the book.         ✗  ditransitive with one object
-/

import Linglib.Core.Basic

namespace Phenomena.ArgumentStructure.Subcategorization

/-- Subcategorization data.

Pure empirical data with no theoretical commitments.
Theories interpret this via their Bridge modules. -/
def data : StringPhenomenonData := {
  name := "Subcategorization"
  generalization := "Verbs require a specific number of arguments"
  pairs := [
    -- Intransitive verbs
    { grammatical := "John sleeps"
      ungrammatical := "John sleeps book"
      clauseType := .declarative
      description := "Intransitive verb cannot take an object" },

    { grammatical := "Mary arrives"
      ungrammatical := "Mary arrives John"
      clauseType := .declarative
      description := "Intransitive verb cannot take an object" },

    -- Transitive verbs
    { grammatical := "John devours pizza"
      ungrammatical := "John devours"
      clauseType := .declarative
      description := "Transitive verb requires an object" },

    { grammatical := "Mary sees John"
      ungrammatical := "Mary sees"
      clauseType := .declarative
      description := "Transitive verb requires an object" },

    -- Ditransitive verbs
    { grammatical := "John gives Mary book"
      ungrammatical := "John gives Mary"
      clauseType := .declarative
      description := "Ditransitive verb requires two objects" }
  ]
}

end Phenomena.ArgumentStructure.Subcategorization
