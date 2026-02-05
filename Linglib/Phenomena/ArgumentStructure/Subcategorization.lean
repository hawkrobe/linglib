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
import Linglib.Theories.Surface.Basic

private def john : Word := ⟨"John", .D, { number := some .sg, person := some .third }⟩
private def sleeps : Word := ⟨"sleeps", .V, { valence := some .intransitive, number := some .sg, person := some .third }⟩
private def mary : Word := ⟨"Mary", .D, { number := some .sg, person := some .third }⟩
private def arrives : Word := ⟨"arrives", .V, { valence := some .intransitive, number := some .sg, person := some .third }⟩
private def devours : Word := ⟨"devours", .V, { valence := some .transitive, number := some .sg, person := some .third }⟩
private def pizza : Word := ⟨"pizza", .N, { number := some .sg }⟩
private def sees : Word := ⟨"sees", .V, { valence := some .transitive, number := some .sg, person := some .third }⟩
private def gives : Word := ⟨"gives", .V, { valence := some .ditransitive, number := some .sg, person := some .third }⟩
private def book : Word := ⟨"book", .N, { number := some .sg, countable := some true }⟩

-- The Empirical Data

/-- Subcategorization data -/
def subcatData : PhenomenonData := {
  name := "Subcategorization"
  generalization := "Verbs require a specific number of arguments"
  pairs := [
    -- Intransitive verbs
    { grammatical := [john, sleeps]
      ungrammatical := [john, sleeps, book]
      clauseType := .declarative
      description := "Intransitive verb cannot take an object" },

    { grammatical := [mary, arrives]
      ungrammatical := [mary, arrives, john]
      clauseType := .declarative
      description := "Intransitive verb cannot take an object" },

    -- Transitive verbs
    { grammatical := [john, devours, pizza]
      ungrammatical := [john, devours]
      clauseType := .declarative
      description := "Transitive verb requires an object" },

    { grammatical := [mary, sees, john]
      ungrammatical := [mary, sees]
      clauseType := .declarative
      description := "Transitive verb requires an object" },

    -- Ditransitive verbs
    { grammatical := [john, gives, mary, book]
      ungrammatical := [john, gives, mary]
      clauseType := .declarative
      description := "Ditransitive verb requires two objects" }
  ]
}

-- Tests

#eval Surface.subcatOk [john, sleeps]           -- true (intrans, 0 obj)
#eval Surface.subcatOk [john, sleeps, book]     -- false (intrans, 1 obj)
#eval Surface.subcatOk [john, devours, pizza]   -- true (trans, 1 obj)
#eval Surface.subcatOk [john, devours]          -- false (trans, 0 obj)
#eval Surface.subcatOk [john, gives, mary, book] -- true (ditrans, 2 obj)
#eval Surface.subcatOk [john, gives, mary]      -- false (ditrans, 1 obj)
