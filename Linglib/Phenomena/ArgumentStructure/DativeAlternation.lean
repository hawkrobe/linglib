/-
# Dative Alternation (Ditransitive Constructions)

## The Phenomenon

English has two ways to express transfer events:
1. Double object construction: "give Mary the book" (V NP NP)
2. Prepositional dative: "give the book to Mary" (V NP PP)

Both express the same meaning but with different argument structures.
The choice depends on information structure and other factors.

## The Data

  (1a)  John gives Mary the book.       ✓  double object
  (1b)  John gives the book to Mary.    ✓  prepositional dative

  (2a)  Mary sends John a letter.       ✓  double object
  (2b)  Mary sends a letter to John.    ✓  prepositional dative

  (3a) *John gives Mary.                ✗  ditransitive missing object
  (3b) *John gives the book.            ✗  ditransitive missing recipient

  (4a) *John puts the book.             ✗  locative missing PP
  (4b)  John puts the book on the table. ✓  locative with PP

## Note on lexical entries

In this formalization, we use separate lexical entries for the two frames:
- `gives` has valence=ditransitive (double object frame)
- `gives_dat` has valence=dative (prepositional dative frame)

A full analysis would derive both from a single lexical entry via lexical rules.
-/

import Linglib.Core.Grammar

namespace Phenomena.ArgumentStructure.DativeAlternation

/-- Dative alternation data.

Pure empirical data with no theoretical commitments.
Theories interpret this via their Bridge modules. -/
def data : StringPhenomenonData := {
  name := "Dative Alternation"
  generalization := "Transfer verbs allow double-object or prepositional frames"
  pairs := [
    -- Double object requires two NPs
    { grammatical := "John gives Mary book"
      ungrammatical := "John gives Mary"
      clauseType := .declarative
      description := "Double object requires two objects" },

    { grammatical := "Mary sends John book"
      ungrammatical := "Mary sends book"
      clauseType := .declarative
      description := "Double object requires recipient and theme" },

    -- Prepositional dative requires NP + PP
    { grammatical := "John gives book to Mary"
      ungrammatical := "John gives book"
      clauseType := .declarative
      description := "Dative requires prepositional phrase" },

    -- Locative verbs require PP
    { grammatical := "John puts book on table"
      ungrammatical := "John puts book"
      clauseType := .declarative
      description := "Locative verb requires prepositional phrase" }
  ]
}

end Phenomena.ArgumentStructure.DativeAlternation
