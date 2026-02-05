/-
# Scope-Word Order Interactions

Word order affects available quantifier scope readings in verb-final constructions.

## Main definitions
- `VerbOrder`, `ScopeAvailability`
- `GermanScopeExample`, `WestFlemishScopeExample`, `DutchScopeExample`

## References
- Bayer (1990, 1996). German scope restrictions.
- Haegeman & van Riemsdijk (1986). West Flemish.
- Steedman (2000). The Syntactic Process, Chapter 6.
- Kayne (1983, 1998). Scope and word order.
-/

import Linglib.Theories.TruthConditional.Derivation.Scope

namespace Phenomena.ScopeWordOrder

open TruthConditional.Scope

/-- Word order patterns in verb-final constructions. -/
inductive VerbOrder where
  | verbRaising          -- NP ... V_emb V_matrix (object precedes all verbs)
  | verbProjectionRaising -- V_matrix ... NP V_emb (object follows matrix verb)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Whether a word order blocks inverse scope -/
def blocksInverseScope : VerbOrder → Bool
  | .verbRaising => false          -- allows both readings
  | .verbProjectionRaising => true -- blocks inverse scope

/-- Available scope readings for a sentence. -/
inductive ScopeAvailability where
  | surfaceOnly  -- Only ∃>∀ or ∀>¬ (whichever is surface)
  | ambiguous    -- Both readings available
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Convert word order to scope availability -/
def wordOrderToAvailability : VerbOrder → ScopeAvailability
  | .verbRaising => .ambiguous
  | .verbProjectionRaising => .surfaceOnly

/-- German sentence data from Bayer/Kayne. -/
structure GermanScopeExample where
  surface : String
  translation : String
  wordOrder : VerbOrder
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

/-- West Flemish data from Haegeman & van Riemsdijk (1986). -/
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

/-- Dutch equi verb data from Steedman (2000). -/
structure DutchScopeExample where
  surface : String
  translation : String
  wordOrder : VerbOrder
  observed : ScopeAvailability
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

end Phenomena.ScopeWordOrder
