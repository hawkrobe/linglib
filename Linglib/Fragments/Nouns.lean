/-
# Noun Lexicon Fragment

Lexical entries for nouns (common nouns and proper names).

## Structure

Each `NounEntry` bundles:
- Surface forms (singular, plural)
- Count/mass distinction
- Semantic sort (if relevant)
-/

import Linglib.Core.Basic

namespace Fragments.Nouns

-- ============================================================================
-- Noun Entry Structure
-- ============================================================================

/--
A lexical entry for a noun.
-/
structure NounEntry where
  /-- Singular form -/
  formSg : String
  /-- Plural form (none for mass nouns) -/
  formPl : Option String := none
  /-- Is this a count noun? -/
  countable : Bool := true
  /-- Is this a proper name? -/
  proper : Bool := false
  deriving Repr, BEq

-- ============================================================================
-- Common Nouns
-- ============================================================================

def pizza : NounEntry := { formSg := "pizza", formPl := "pizzas" }
def book : NounEntry := { formSg := "book", formPl := "books" }
def cat : NounEntry := { formSg := "cat", formPl := "cats" }
def dog : NounEntry := { formSg := "dog", formPl := "dogs" }
def girl : NounEntry := { formSg := "girl", formPl := "girls" }
def boy : NounEntry := { formSg := "boy", formPl := "boys" }
def ball : NounEntry := { formSg := "ball", formPl := "balls" }
def table : NounEntry := { formSg := "table", formPl := "tables" }
def squirrel : NounEntry := { formSg := "squirrel", formPl := "squirrels" }
def man : NounEntry := { formSg := "man", formPl := "men" }
def woman : NounEntry := { formSg := "woman", formPl := "women" }
def person : NounEntry := { formSg := "person", formPl := "people" }

-- Mass nouns
def water : NounEntry := { formSg := "water", formPl := none, countable := false }
def sand : NounEntry := { formSg := "sand", formPl := none, countable := false }

-- ============================================================================
-- Proper Names
-- ============================================================================

def john : NounEntry := { formSg := "John", formPl := none, proper := true }
def mary : NounEntry := { formSg := "Mary", formPl := none, proper := true }

-- ============================================================================
-- Conversion to Word
-- ============================================================================

/-- Convert a noun entry to a singular Word -/
def toWordSg (n : NounEntry) : Word :=
  { form := n.formSg
  , cat := if n.proper then .D else .N
  , features := {
      number := some .sg
      , person := if n.proper then some .third else none
      , countable := some n.countable
    }
  }

/-- Convert a noun entry to a plural Word (if countable) -/
def toWordPl (n : NounEntry) : Option Word :=
  n.formPl.map fun pl =>
    { form := pl
    , cat := .N
    , features := {
        number := some .pl
        , countable := some true
      }
    }

-- ============================================================================
-- All Nouns
-- ============================================================================

def allNouns : List NounEntry := [
  pizza, book, cat, dog, girl, boy, ball, table, squirrel,
  man, woman, person, water, sand, john, mary
]

def lookup (form : String) : Option NounEntry :=
  allNouns.find? fun n => n.formSg == form || n.formPl == some form

end Fragments.Nouns
