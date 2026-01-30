/-
# Adjective Lexicon Fragment

Lexical entries for adjectives.

Links to the semantic theory in `Montague.Lexicon.Adjectives.Theory`.
-/

import Linglib.Core.Basic
import Linglib.Theories.Montague.Lexicon.Adjectives.Theory

namespace Fragments.Adjectives

open Montague.Lexicon.Adjectives

-- ============================================================================
-- Adjective Entry Structure
-- ============================================================================

/--
A lexical entry for an adjective.
-/
structure AdjEntry where
  /-- Positive form -/
  form : String
  /-- Comparative form -/
  formComp : Option String := none
  /-- Superlative form -/
  formSuper : Option String := none
  /-- Scale type (from Montague theory) -/
  scaleType : ScaleType := .open_
  /-- What dimension is being measured? -/
  dimension : String := ""
  /-- Antonym (if any) -/
  antonym : Option String := none
  /-- Is this a "negative" adjective on its scale? -/
  negative : Bool := false
  deriving Repr, BEq

-- ============================================================================
-- Gradable Adjectives (Open Scale)
-- ============================================================================

def tall : AdjEntry :=
  { form := "tall", formComp := "taller", formSuper := "tallest"
  , scaleType := .open_, dimension := "height", antonym := "short" }

def short : AdjEntry :=
  { form := "short", formComp := "shorter", formSuper := "shortest"
  , scaleType := .open_, dimension := "height", antonym := "tall", negative := true }

def happy : AdjEntry :=
  { form := "happy", formComp := "happier", formSuper := "happiest"
  , scaleType := .open_, dimension := "happiness", antonym := "unhappy" }

def unhappy : AdjEntry :=
  { form := "unhappy", formComp := "unhappier", formSuper := "unhappiest"
  , scaleType := .open_, dimension := "happiness", antonym := "happy", negative := true }

def expensive : AdjEntry :=
  { form := "expensive", formComp := "more expensive", formSuper := "most expensive"
  , scaleType := .open_, dimension := "price", antonym := "cheap" }

def cheap : AdjEntry :=
  { form := "cheap", formComp := "cheaper", formSuper := "cheapest"
  , scaleType := .open_, dimension := "price", antonym := "expensive", negative := true }

def good : AdjEntry :=
  { form := "good", formComp := "better", formSuper := "best"
  , scaleType := .open_, dimension := "quality", antonym := "bad" }

def bad : AdjEntry :=
  { form := "bad", formComp := "worse", formSuper := "worst"
  , scaleType := .open_, dimension := "quality", antonym := "good", negative := true }

def smart : AdjEntry :=
  { form := "smart", formComp := "smarter", formSuper := "smartest"
  , scaleType := .open_, dimension := "intelligence" }

-- ============================================================================
-- Closed Scale Adjectives
-- ============================================================================

def full : AdjEntry :=
  { form := "full", formComp := "fuller", formSuper := "fullest"
  , scaleType := .closed, dimension := "fullness", antonym := "empty" }

def empty : AdjEntry :=
  { form := "empty", formComp := "emptier", formSuper := "emptiest"
  , scaleType := .closed, dimension := "fullness", antonym := "full", negative := true }

def wet : AdjEntry :=
  { form := "wet", formComp := "wetter", formSuper := "wettest"
  , scaleType := .lowerClosed, dimension := "wetness", antonym := "dry" }

def dry : AdjEntry :=
  { form := "dry", formComp := "drier", formSuper := "driest"
  , scaleType := .upperClosed, dimension := "wetness", antonym := "wet", negative := true }

-- ============================================================================
-- Non-Gradable / Absolute Adjectives
-- ============================================================================

def dead : AdjEntry :=
  { form := "dead", scaleType := .closed, dimension := "alive" }

def pregnant : AdjEntry :=
  { form := "pregnant", scaleType := .closed }

-- ============================================================================
-- Conversion to Word
-- ============================================================================

def toWord (a : AdjEntry) : Word :=
  { form := a.form, cat := .Adj, features := {} }

-- ============================================================================
-- All Adjectives
-- ============================================================================

def allAdjectives : List AdjEntry := [
  tall, short, happy, unhappy, expensive, cheap, good, bad, smart,
  full, empty, wet, dry, dead, pregnant
]

def lookup (form : String) : Option AdjEntry :=
  allAdjectives.find? fun a => a.form == form

end Fragments.Adjectives
