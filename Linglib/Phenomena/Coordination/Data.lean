/-
# Coordination

## The Phenomenon

Coordination allows two or more elements to be joined by a conjunction.
Key constraints:
1. Coordinated elements must have matching categories
2. Coordinated verbs must have matching argument structures

## The Data

  (1a)  John and Mary sleep           ✓  NP coordination
  (1b) *John and sleeps               ✗  category mismatch (D + V)

  (2a)  John sleeps and Mary sleeps   ✓  S coordination
  (2b) *John sleeps and Mary          ✗  incomplete second conjunct

  (3a)  John sees and hears Mary      ✓  VP coordination (shared args)
  (3b) *John sees and sleeps Mary     ✗  valence mismatch (trans + intrans)

Reference: Gibson (2025) "Syntax", MIT Press, Section 3.8
-/

import Linglib.Phenomena.Basic

open Lexicon

-- ============================================================================
-- Coordination Lexicon
-- ============================================================================

def and_ : Word := ⟨"and", Cat.C, {}⟩
def or_ : Word := ⟨"or", Cat.C, {}⟩
def but_ : Word := ⟨"but", Cat.C, {}⟩

-- ============================================================================
-- The Empirical Data
-- ============================================================================

/-- NP coordination minimal pairs -/
def npCoordinationData : PhenomenonData := {
  name := "NP Coordination"
  generalization := "Coordinated NPs must have matching categories"
  pairs := [
    { grammatical := [john, and_, mary, sleep]
      ungrammatical := [john, and_, sleeps]
      clauseType := .declarative
      description := "NP coordination requires matching categories" },

    { grammatical := [the, boy, and_, the, girl, sleep]
      ungrammatical := [the, boy, and_, sleeps]
      clauseType := .declarative
      description := "Complex NP coordination" }
  ]
}

/-- VP coordination minimal pairs -/
def vpCoordinationData : PhenomenonData := {
  name := "VP Coordination"
  generalization := "Coordinated VPs must have matching argument structures"
  pairs := [
    { grammatical := [john, sees, and_, sees, mary]  -- sees twice for "sees and hears"
      ungrammatical := [john, sees, and_, sleeps, mary]
      clauseType := .declarative
      description := "VP coordination requires matching valence (trans + trans)" },

    { grammatical := [john, sleeps, and_, sleeps]  -- sleeps twice for "sleeps and snores"
      ungrammatical := [john, sleeps, and_, sees]
      clauseType := .declarative
      description := "Intransitive VP coordination" }
  ]
}

/-- S coordination minimal pairs -/
def sCoordinationData : PhenomenonData := {
  name := "S Coordination"
  generalization := "Coordinated sentences must each be complete"
  pairs := [
    { grammatical := [john, sleeps, and_, mary, sleeps]
      ungrammatical := [john, sleeps, and_, mary]
      clauseType := .declarative
      description := "S coordination requires complete clauses" },

    { grammatical := [john, sees, mary, and_, mary, sees, john]
      ungrammatical := [john, sees, mary, and_, sees, john]
      clauseType := .declarative
      description := "Each conjunct needs a subject" }
  ]
}

-- ============================================================================
-- Specification Typeclass
-- ============================================================================

/-- A grammar captures coordination -/
class CapturesCoordination (G : Type) [Grammar G] where
  grammar : G
  capturesNPCoord : Grammar.capturesPhenomenon G grammar npCoordinationData
  capturesVPCoord : Grammar.capturesPhenomenon G grammar vpCoordinationData
  capturesSCoord : Grammar.capturesPhenomenon G grammar sCoordinationData

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Find conjunction positions in a word list -/
def findConjunctions (ws : List Word) : List Nat :=
  (List.range ws.length).zip ws |>.filterMap fun (i, w) =>
    if w.form == "and" || w.form == "or" || w.form == "but" then some i else none

/-- Check if a word list has coordination -/
def hasCoordination (ws : List Word) : Bool :=
  ws.any fun w => w.form == "and" || w.form == "or" || w.form == "but"
