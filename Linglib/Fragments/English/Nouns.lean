/-
# English Noun Lexicon Fragment

English-specific noun entries and NP structure.

## Bare Argument Licensing in English

English is a [+arg, +pred] language (Chierchia 1998):
- Bare plurals OK: "Dogs bark", "I saw dogs"
- Bare mass nouns OK: "Water is wet", "I drank water"
- Bare singulars OUT: *"Dog barks", *"I saw dog"

The restriction follows from:
1. ∩ (kind formation) is only defined for plurals and mass nouns
2. ι (definite) is blocked by "the"
3. ∃ (indefinite singular) is blocked by "a"

## References

- Chierchia (1998). Reference to Kinds Across Languages.
-/

import Linglib.Core.Basic
import Linglib.Theories.Montague.Lexicon.Kinds

namespace Fragments.English.Nouns

open Montague.Lexicon.Kinds (BlockingPrinciple)

-- ============================================================================
-- English NP Structure
-- ============================================================================

/-- A lexical entry for an English noun. -/
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

/-- Number marking on an English NP -/
inductive NPNumber where
  | sg    -- Singular
  | pl    -- Plural
  | mass  -- Mass (no number distinction)
  deriving DecidableEq, Repr, BEq

/-- An English noun phrase. -/
structure NP where
  /-- The underlying noun -/
  noun : NounEntry
  /-- Number marking -/
  number : NPNumber
  /-- Is this a bare NP (no determiner)? -/
  isBare : Bool
  /-- The determiner (if not bare) -/
  determiner : Option String := none
  deriving Repr, BEq

/-- Is this NP a bare plural? -/
def NP.isBarePlural (np : NP) : Bool :=
  np.isBare && np.number == .pl

/-- Is this NP a bare mass noun? -/
def NP.isBareMass (np : NP) : Bool :=
  np.isBare && np.number == .mass

/-- Is this NP a bare singular? -/
def NP.isBareSingular (np : NP) : Bool :=
  np.isBare && np.number == .sg

-- ============================================================================
-- NP Constructors
-- ============================================================================

/-- Create a bare plural NP -/
def barePlural (n : NounEntry) : NP :=
  { noun := n, number := .pl, isBare := true }

/-- Create a bare mass NP -/
def bareMass (n : NounEntry) : NP :=
  { noun := n, number := .mass, isBare := true }

/-- Create a bare singular NP (ungrammatical in English) -/
def bareSingular (n : NounEntry) : NP :=
  { noun := n, number := .sg, isBare := true }

/-- Create a definite NP with "the" -/
def theNP (n : NounEntry) (num : NPNumber := .sg) : NP :=
  { noun := n, number := num, isBare := false, determiner := some "the" }

/-- Create an indefinite singular NP with "a" -/
def aNP (n : NounEntry) : NP :=
  { noun := n, number := .sg, isBare := false, determiner := some "a" }

/-- Create an NP with a specific determiner -/
def withDet (n : NounEntry) (det : String) (num : NPNumber := .sg) : NP :=
  { noun := n, number := num, isBare := false, determiner := some det }

-- ============================================================================
-- English Blocking Configuration
-- ============================================================================

/--
English has articles that block covert type shifts:
- "the" blocks ι (iota, definite description)
- "a/some" blocks ∃ for singulars
- Nothing blocks ∩ (kind formation)

Result: bare singulars cannot occur as arguments.
-/
def englishBlocking : BlockingPrinciple :=
  { determiners := ["the", "a", "some", "every", "no"]
  , iotaBlocked := true
  , existsBlocked := true
  , downBlocked := false }

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
def child : NounEntry := { formSg := "child", formPl := "children" }
def lawyer : NounEntry := { formSg := "lawyer", formPl := "lawyers" }
def student : NounEntry := { formSg := "student", formPl := "students" }
def teacher : NounEntry := { formSg := "teacher", formPl := "teachers" }
def fireman : NounEntry := { formSg := "fireman", formPl := "firemen" }
def soldier : NounEntry := { formSg := "soldier", formPl := "soldiers" }
def horse : NounEntry := { formSg := "horse", formPl := "horses" }

-- Mass nouns
def water : NounEntry := { formSg := "water", formPl := none, countable := false }
def sand : NounEntry := { formSg := "sand", formPl := none, countable := false }
def furniture : NounEntry := { formSg := "furniture", formPl := none, countable := false }
def rice : NounEntry := { formSg := "rice", formPl := none, countable := false }
def gold : NounEntry := { formSg := "gold", formPl := none, countable := false }
def air : NounEntry := { formSg := "air", formPl := none, countable := false }

-- ============================================================================
-- Proper Names
-- ============================================================================

def john : NounEntry := { formSg := "John", formPl := none, proper := true }
def mary : NounEntry := { formSg := "Mary", formPl := none, proper := true }
def bill : NounEntry := { formSg := "Bill", formPl := none, proper := true }
def sue : NounEntry := { formSg := "Sue", formPl := none, proper := true }

-- ============================================================================
-- Lookup
-- ============================================================================

def allNouns : List NounEntry := [
  pizza, book, cat, dog, girl, boy, ball, table, squirrel,
  man, woman, person, child, lawyer, student, teacher, fireman, soldier, horse,
  water, sand, furniture, rice, gold, air,
  john, mary, bill, sue
]

def lookup (form : String) : Option NounEntry :=
  allNouns.find? fun n => n.formSg == form || n.formPl == some form

-- ============================================================================
-- Bare Argument Licensing
-- ============================================================================

/-- In English, bare plurals are licensed -/
def barePluralLicensed : Bool := !englishBlocking.downBlocked

/-- In English, bare mass nouns are licensed -/
def bareMassLicensed : Bool := !englishBlocking.downBlocked

/-- In English, bare singulars are NOT licensed -/
def bareSingularLicensed : Bool :=
  !englishBlocking.iotaBlocked ∨ !englishBlocking.existsBlocked

-- Verify our expectations
example : barePluralLicensed = true := rfl
example : bareMassLicensed = true := rfl
example : bareSingularLicensed = false := rfl

-- ============================================================================
-- Example NPs
-- ============================================================================

/-- "dogs" as bare plural -/
def dogs : NP := barePlural dog

/-- "water" as bare mass -/
def waterNP : NP := bareMass water

/-- "the dog" -/
def theDog : NP := theNP dog

/-- "a dog" -/
def aDog : NP := aNP dog

/-- "every dog" -/
def everyDog : NP := withDet dog "every"

-- Examples verifying structure
example : dogs.isBarePlural = true := rfl
example : waterNP.isBareMass = true := rfl
example : theDog.isBare = false := rfl
example : aDog.determiner = some "a" := rfl

end Fragments.English.Nouns
