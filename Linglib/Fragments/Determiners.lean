/-
# Determiner Lexicon Fragment

Lexical entries for determiners and quantifiers.
-/

import Linglib.Core.Basic

namespace Fragments.Determiners

-- ============================================================================
-- Determiner Entry Structure
-- ============================================================================

/--
Quantificational force of a determiner.
-/
inductive QForce where
  | universal    -- every, all, each
  | existential  -- a, some
  | definite     -- the, this, that
  | negative     -- no, neither
  | proportional -- most, few, many
  deriving DecidableEq, Repr, BEq

/--
A lexical entry for a determiner.
-/
structure DetEntry where
  /-- Surface form -/
  form : String
  /-- Quantificational force -/
  qforce : QForce
  /-- Number restriction (none = either) -/
  numberRestriction : Option Number := none
  /-- Can combine with mass nouns? -/
  allowsMass : Bool := false
  deriving Repr, BEq

-- ============================================================================
-- Determiners
-- ============================================================================

-- Definite
def the : DetEntry := { form := "the", qforce := .definite, allowsMass := true }
def this : DetEntry := { form := "this", qforce := .definite, numberRestriction := some .sg }
def that : DetEntry := { form := "that", qforce := .definite, numberRestriction := some .sg }
def these : DetEntry := { form := "these", qforce := .definite, numberRestriction := some .pl }
def those : DetEntry := { form := "those", qforce := .definite, numberRestriction := some .pl }

-- Existential
def a : DetEntry := { form := "a", qforce := .existential, numberRestriction := some .sg }
def an : DetEntry := { form := "an", qforce := .existential, numberRestriction := some .sg }
def some_ : DetEntry := { form := "some", qforce := .existential, allowsMass := true }

-- Universal
def every : DetEntry := { form := "every", qforce := .universal, numberRestriction := some .sg }
def all : DetEntry := { form := "all", qforce := .universal, numberRestriction := some .pl, allowsMass := true }
def each : DetEntry := { form := "each", qforce := .universal, numberRestriction := some .sg }

-- Negative
def no_ : DetEntry := { form := "no", qforce := .negative, allowsMass := true }

-- Proportional
def most : DetEntry := { form := "most", qforce := .proportional, numberRestriction := some .pl, allowsMass := true }
def many : DetEntry := { form := "many", qforce := .proportional, numberRestriction := some .pl }
def few : DetEntry := { form := "few", qforce := .proportional, numberRestriction := some .pl }

-- ============================================================================
-- Conversion to Word
-- ============================================================================

def toWord (d : DetEntry) : Word :=
  { form := d.form
  , cat := .D
  , features := { number := d.numberRestriction }
  }

-- ============================================================================
-- All Determiners
-- ============================================================================

def allDeterminers : List DetEntry := [
  the, this, that, these, those,
  a, an, some_,
  every, all, each,
  no_,
  most, many, few
]

def lookup (form : String) : Option DetEntry :=
  allDeterminers.find? fun d => d.form == form

end Fragments.Determiners
