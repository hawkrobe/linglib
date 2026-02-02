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

-- ============================================================================
-- NP Structure (with bare plural tracking)
-- ============================================================================

/-- Number marking on an NP -/
inductive NPNumber where
  | sg    -- Singular
  | pl    -- Plural
  | mass  -- Mass (no number distinction)
  deriving DecidableEq, Repr, BEq

/--
A noun phrase, tracking whether it's bare (no determiner).

Bare plurals and bare mass nouns are kind-denoting (Chierchia 1998).
Non-bare NPs are either definite or indefinite GQs.
-/
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

/-- Is this NP a bare plural? (kind-denoting via ∩) -/
def NP.isBarePlural (np : NP) : Bool :=
  np.isBare && np.number == .pl

/-- Is this NP a bare mass noun? (kind-denoting via ∩) -/
def NP.isBareMass (np : NP) : Bool :=
  np.isBare && np.number == .mass

/-- Is this NP kind-denoting? (bare plural or bare mass) -/
def NP.isKindDenoting (np : NP) : Bool :=
  np.isBarePlural || np.isBareMass

/-- Is this a bare singular? (ungrammatical in English) -/
def NP.isBareSingular (np : NP) : Bool :=
  np.isBare && np.number == .sg && np.noun.countable

-- ============================================================================
-- NP Constructors
-- ============================================================================

/-- Create a bare plural NP -/
def barePlural (n : NounEntry) : NP :=
  { noun := n, number := .pl, isBare := true }

/-- Create a bare mass NP -/
def bareMass (n : NounEntry) : NP :=
  { noun := n, number := .mass, isBare := true }

/-- Create a definite singular NP -/
def theNP (n : NounEntry) : NP :=
  { noun := n, number := .sg, isBare := false, determiner := some "the" }

/-- Create an indefinite singular NP -/
def aNP (n : NounEntry) : NP :=
  { noun := n, number := .sg, isBare := false, determiner := some "a" }

-- ============================================================================
-- Examples
-- ============================================================================

/-- "dogs" (bare plural) is kind-denoting -/
example : (barePlural dog).isKindDenoting = true := rfl

/-- "water" (bare mass) is kind-denoting -/
example : (bareMass water).isKindDenoting = true := rfl

/-- "the dog" is NOT kind-denoting -/
example : (theNP dog).isKindDenoting = false := rfl

/-- "a dog" is NOT kind-denoting -/
example : (aNP dog).isKindDenoting = false := rfl

/-- Bare singular would be ungrammatical -/
example : ({ noun := dog, number := .sg, isBare := true } : NP).isBareSingular = true := rfl

-- ============================================================================
-- Sentence-Level Properties (relevant for NP interpretation)
-- ============================================================================

/--
Sentence aspect: episodic vs generic/habitual.
Affects how bare plurals are interpreted.
-/
inductive Aspect where
  | episodic  -- "Dogs are barking in the yard"
  | generic   -- "Dogs bark"
  deriving DecidableEq, Repr, BEq

/--
Possible readings for a bare plural in a sentence.
Which readings are available depends on the theory.
-/
inductive BarePluralReading where
  | existential  -- ∃x[P(x) ∧ Q(x)]
  | universal    -- ∀x[P(x) → Q(x)] (modulo normalcy)
  | kind         -- Direct kind predication: rare(dogs)
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- Mass/Count and Bare Arguments
-- ============================================================================

/--
Whether a noun can appear bare as an argument.

In English (Germanic, [+arg,+pred]):
- Mass nouns: always OK bare (kind-denoting via ∩)
- Count nouns: only plural OK bare (∩ undefined for singulars)

In French (Romance, [-arg,+pred]):
- Neither mass nor count can appear bare (D must be projected)
-/
def NounEntry.canAppearBare (n : NounEntry) (num : NPNumber) : Bool :=
  match n.countable, num with
  | false, _ => true        -- Mass nouns always OK
  | true, .pl => true       -- Count plurals OK
  | true, .mass => false    -- Count nouns aren't mass
  | true, .sg => false      -- *Bare singular count noun

/-- Mass nouns can appear bare -/
example : water.canAppearBare .mass = true := rfl

/-- Plural count nouns can appear bare -/
example : dog.canAppearBare .pl = true := rfl

/-- Singular count nouns cannot appear bare -/
example : dog.canAppearBare .sg = false := rfl

-- ============================================================================
-- Grammaticality Check
-- ============================================================================

/--
Is this NP grammatical in English?

Bare singulars are out; everything else is fine.
-/
def NP.isGrammatical (np : NP) : Bool :=
  !np.isBareSingular

/-- "dogs" (bare plural) is grammatical -/
example : (barePlural dog).isGrammatical = true := rfl

/-- "water" (bare mass) is grammatical -/
example : (bareMass water).isGrammatical = true := rfl

/-- "the dog" is grammatical -/
example : (theNP dog).isGrammatical = true := rfl

/-- "*dog" (bare singular) is ungrammatical -/
example : ({ noun := dog, number := .sg, isBare := true } : NP).isGrammatical = false := rfl

end Fragments.Nouns
