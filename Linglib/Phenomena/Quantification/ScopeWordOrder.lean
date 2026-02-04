/-
# Scope-Word Order Interactions

Empirical data on how word order affects available quantifier scope readings.

## Overview

Different word orders can constrain which scope readings are available:
- "Verb raising" order often allows scope ambiguity
- "Verb projection raising" order often forces surface scope

## Key Phenomenon

In Dutch/German, when an embedded verb takes its object BEFORE combining
with higher verbs (verb raising), inverse scope is possible. When the
higher verb combines first (verb projection raising), inverse scope is blocked.

## References

- Bayer (1990, 1996) on German scope restrictions
- Haegeman & van Riemsdijk (1986) on West Flemish
- Steedman (2000) "The Syntactic Process" Chapter 6, Section 6.8
- Kayne (1983, 1998) on scope and word order
-/

import Linglib.Theories.Montague.Derivation.Scope

namespace Phenomena.ScopeWordOrder

open Montague.Scope

-- Word Order Types

/--
Word order patterns in verb-final constructions.

These capture the key distinction from Steedman (2000) §6.8:
- VerbRaising: embedded verb combines with object first, then with higher verb
- VerbProjectionRaising: higher verb combines first, embedded VP is complete
-/
inductive VerbOrder where
  | verbRaising          -- NP ... V_emb V_matrix (object precedes all verbs)
  | verbProjectionRaising -- V_matrix ... NP V_emb (object follows matrix verb)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Whether a word order blocks inverse scope -/
def blocksInverseScope : VerbOrder → Bool
  | .verbRaising => false          -- allows both readings
  | .verbProjectionRaising => true -- blocks inverse scope

-- Scope Availability

/--
Available scope readings for a sentence.

`surfaceOnly` means only the surface scope reading is available.
`ambiguous` means both surface and inverse scope are available.
-/
inductive ScopeAvailability where
  | surfaceOnly  -- Only ∃>∀ or ∀>¬ (whichever is surface)
  | ambiguous    -- Both readings available
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Convert word order to scope availability -/
def wordOrderToAvailability : VerbOrder → ScopeAvailability
  | .verbRaising => .ambiguous
  | .verbProjectionRaising => .surfaceOnly

-- Empirical Data: German (Bayer 1990, 1996; Kayne 1998)

/--
German sentence data from Bayer/Kayne.

(96) (Weil) irgendjemand auf jeden gespannt ist.
     (Since) someone on everybody curious is
     "Since someone is curious about everybody."
     → AMBIGUOUS (∃>∀ and ∀>∃)

(97) (Weil) jemand versucht hat jeden reinzulegen.
     (Since) someone tried has everyone cheat
     "Since someone has tried to cheat everyone."
     → UNAMBIGUOUS (only ∃>∀)
-/
structure GermanScopeExample where
  /-- Surface string -/
  surface : String
  /-- English translation -/
  translation : String
  /-- Word order type -/
  wordOrder : VerbOrder
  /-- Observed scope availability -/
  observed : ScopeAvailability
  deriving Repr

def german_96 : GermanScopeExample :=
  { surface := "(Weil) irgendjemand auf jeden gespannt ist"
  , translation := "Since someone is curious about everybody"
  , wordOrder := .verbRaising
  , observed := .ambiguous }

def german_97 : GermanScopeExample :=
  { surface := "(Weil) jemand versucht hat jeden reinzulegen"
  , translation := "Since someone has tried to cheat everyone"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly }

-- Empirical Data: West Flemish (Haegeman & van Riemsdijk 1986)

/--
West Flemish data from Haegeman & van Riemsdijk (1986).

(98a) (da) Jan vee boeken hee willen lezen
      (that) Jan many books has wanted read
      "that Jan wanted to read many books"
      → AMBIGUOUS

(98b) (da) Jan hee willen vee boeken lezen
      (that) Jan has wanted many books read
      "that Jan wanted to read many books"
      → UNAMBIGUOUS (many books < wanted)
-/
structure WestFlemishScopeExample where
  surface : String
  translation : String
  wordOrder : VerbOrder
  observed : ScopeAvailability
  deriving Repr

def westFlemish_98a : WestFlemishScopeExample :=
  { surface := "(da) Jan vee boeken hee willen lezen"
  , translation := "that Jan wanted to read many books"
  , wordOrder := .verbRaising
  , observed := .ambiguous }

def westFlemish_98b : WestFlemishScopeExample :=
  { surface := "(da) Jan hee willen vee boeken lezen"
  , translation := "that Jan wanted to read many books"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly }

-- Empirical Data: Standard Dutch (Steedman 2000)

/--
Dutch equi verb data from Steedman (2000) §6.8.

(99a) (omdat) Jan veel liederen probeert te zingen
      (because) Jan many songs tries to sing
      "because Jan tries to sing many songs"
      → AMBIGUOUS

(99b) (omdat) Jan probeert veel liederen te zingen
      (because) Jan tries many songs to sing
      "because Jan tries to sing many songs"
      → UNAMBIGUOUS

(100a) (omdat) iemand alle liederen probeert te zingen
       (because) someone every song tries to sing
       → AMBIGUOUS

(100b) (omdat) iemand probeert alle liederen te zingen
       (because) someone tries every song to sing
       → UNAMBIGUOUS
-/
structure DutchScopeExample where
  surface : String
  translation : String
  wordOrder : VerbOrder
  observed : ScopeAvailability
  /-- Quantifiers involved -/
  quantifiers : List String := []
  deriving Repr

def dutch_99a : DutchScopeExample :=
  { surface := "(omdat) Jan veel liederen probeert te zingen"
  , translation := "because Jan tries to sing many songs"
  , wordOrder := .verbRaising
  , observed := .ambiguous
  , quantifiers := ["veel/many"] }

def dutch_99b : DutchScopeExample :=
  { surface := "(omdat) Jan probeert veel liederen te zingen"
  , translation := "because Jan tries to sing many songs"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly
  , quantifiers := ["veel/many"] }

def dutch_100a : DutchScopeExample :=
  { surface := "(omdat) iemand alle liederen probeert te zingen"
  , translation := "because someone tries to sing every song"
  , wordOrder := .verbRaising
  , observed := .ambiguous
  , quantifiers := ["iemand/someone", "alle/every"] }

def dutch_100b : DutchScopeExample :=
  { surface := "(omdat) iemand probeert alle liederen te zingen"
  , translation := "because someone tries to sing every song"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly
  , quantifiers := ["iemand/someone", "alle/every"] }

-- Collected Data

def allDutchExamples : List DutchScopeExample :=
  [dutch_99a, dutch_99b, dutch_100a, dutch_100b]

def allWestFlemishExamples : List WestFlemishScopeExample :=
  [westFlemish_98a, westFlemish_98b]

def allGermanExamples : List GermanScopeExample :=
  [german_96, german_97]

-- Predictions

/-- Word order correctly predicts scope availability -/
theorem wordOrder_predicts_dutch_99a :
    wordOrderToAvailability dutch_99a.wordOrder = dutch_99a.observed := rfl

theorem wordOrder_predicts_dutch_99b :
    wordOrderToAvailability dutch_99b.wordOrder = dutch_99b.observed := rfl

theorem wordOrder_predicts_dutch_100a :
    wordOrderToAvailability dutch_100a.wordOrder = dutch_100a.observed := rfl

theorem wordOrder_predicts_dutch_100b :
    wordOrderToAvailability dutch_100b.wordOrder = dutch_100b.observed := rfl

theorem wordOrder_predicts_german_96 :
    wordOrderToAvailability german_96.wordOrder = german_96.observed := rfl

theorem wordOrder_predicts_german_97 :
    wordOrderToAvailability german_97.wordOrder = german_97.observed := rfl

-- Summary

/-
## What This Module Provides

### Empirical Data
- German scope examples (Bayer 1990, 1996)
- West Flemish scope examples (Haegeman & van Riemsdijk 1986)
- Dutch scope examples (Steedman 2000)

### Key Generalization
Word order (verb raising vs verb projection raising) determines
whether inverse scope is available:
- Verb raising: object combines with embedded verb first → ambiguous
- Verb projection raising: matrix verb combines first → surface scope only

### Connection to CCG
In CCG terms:
- Verb raising = composition of verbs, then NP combines with composite
- Verb projection raising = NP combines with embedded VP, then VP combines

The derivational structure directly determines scope possibilities.

### What's NOT Here (belongs in Theories/)
- CCG derivations for these sentences
- Formal proofs connecting derivation structure to scope
- RSA preferences over available readings
-/

end Phenomena.ScopeWordOrder
