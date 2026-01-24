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

import LingLean.Phenomena.Basic
import LingLean.Syntax.Surface.Basic

open Lexicon

-- ============================================================================
-- The Empirical Data
-- ============================================================================

/-- Dative alternation data -/
def dativeAlternationData : PhenomenonData := {
  name := "Dative Alternation"
  generalization := "Transfer verbs allow double-object or prepositional frames"
  pairs := [
    -- Double object requires two NPs
    { grammatical := [john, gives, mary, book]
      ungrammatical := [john, gives, mary]
      clauseType := .declarative
      description := "Double object requires two objects" },

    { grammatical := [mary, sends, john, book]
      ungrammatical := [mary, sends, book]
      clauseType := .declarative
      description := "Double object requires recipient and theme" },

    -- Prepositional dative requires NP + PP
    { grammatical := [john, gives_dat, book, to, mary]
      ungrammatical := [john, gives_dat, book]
      clauseType := .declarative
      description := "Dative requires prepositional phrase" },

    -- Locative verbs require PP
    { grammatical := [john, puts, book, on, table]
      ungrammatical := [john, puts, book]
      clauseType := .declarative
      description := "Locative verb requires prepositional phrase" }
  ]
}

-- ============================================================================
-- Tests
-- ============================================================================

-- Double object frame
#eval Surface.subcatOk [john, gives, mary, book]    -- true (ditrans, 2 obj)
#eval Surface.subcatOk [john, gives, mary]          -- false (ditrans, 1 obj)
#eval Surface.subcatOk [john, gives, book]          -- false (ditrans, 1 obj)

-- Prepositional dative frame
#eval Surface.subcatOk [john, gives_dat, book, to, mary]  -- true (dative, 1 obj + PP)
#eval Surface.subcatOk [john, gives_dat, book]            -- false (dative, no PP)

-- Locative frame
#eval Surface.subcatOk [john, puts, book, on, table]  -- true (locative, 1 obj + PP)
#eval Surface.subcatOk [john, puts, book]             -- false (locative, no PP)
