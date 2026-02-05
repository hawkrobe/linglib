/-
# English Pronoun Lexicon Fragment

Lexical entries for English pronouns (personal, reflexive, wh-).
-/

import Linglib.Core.Basic

namespace Fragments.English.Pronouns

-- ============================================================================
-- Pronoun Entry Structure
-- ============================================================================

/--
Type of pronoun.
-/
inductive PronounType where
  | personal    -- I, you, he, she, it, we, they
  | reflexive   -- myself, yourself, himself, herself, itself, ourselves, themselves
  | wh          -- who, what, which, where, when, why, how
  | relative    -- who, which, that (in relative clauses)
  | demonstrative -- this, that (pronominal use)
  deriving DecidableEq, Repr, BEq

/--
A lexical entry for a pronoun.
-/
structure PronounEntry where
  /-- Surface form -/
  form : String
  /-- Pronoun type -/
  pronounType : PronounType
  /-- Person (for personal/reflexive) -/
  person : Option Person := none
  /-- Number -/
  number : Option Number := none
  /-- Case (for personal pronouns) -/
  case_ : Option Case := none
  /-- Is this a wh-word? -/
  wh : Bool := false
  deriving Repr, BEq

-- ============================================================================
-- Personal Pronouns
-- ============================================================================

-- First person
def i : PronounEntry := { form := "I", pronounType := .personal, person := some .first, number := some .sg, case_ := some .nom }
def me : PronounEntry := { form := "me", pronounType := .personal, person := some .first, number := some .sg, case_ := some .acc }
def we : PronounEntry := { form := "we", pronounType := .personal, person := some .first, number := some .pl, case_ := some .nom }
def us : PronounEntry := { form := "us", pronounType := .personal, person := some .first, number := some .pl, case_ := some .acc }

-- Second person
def you : PronounEntry := { form := "you", pronounType := .personal, person := some .second, number := some .sg }
def you_pl : PronounEntry := { form := "you", pronounType := .personal, person := some .second, number := some .pl }

-- Third person
def he : PronounEntry := { form := "he", pronounType := .personal, person := some .third, number := some .sg, case_ := some .nom }
def him : PronounEntry := { form := "him", pronounType := .personal, person := some .third, number := some .sg, case_ := some .acc }
def she : PronounEntry := { form := "she", pronounType := .personal, person := some .third, number := some .sg, case_ := some .nom }
def her : PronounEntry := { form := "her", pronounType := .personal, person := some .third, number := some .sg, case_ := some .acc }
def it : PronounEntry := { form := "it", pronounType := .personal, person := some .third, number := some .sg }
def they : PronounEntry := { form := "they", pronounType := .personal, person := some .third, number := some .pl, case_ := some .nom }
def them : PronounEntry := { form := "them", pronounType := .personal, person := some .third, number := some .pl, case_ := some .acc }

-- ============================================================================
-- Reflexive Pronouns
-- ============================================================================

def myself : PronounEntry := { form := "myself", pronounType := .reflexive, person := some .first, number := some .sg }
def yourself : PronounEntry := { form := "yourself", pronounType := .reflexive, person := some .second, number := some .sg }
def himself : PronounEntry := { form := "himself", pronounType := .reflexive, person := some .third, number := some .sg }
def herself : PronounEntry := { form := "herself", pronounType := .reflexive, person := some .third, number := some .sg }
def itself : PronounEntry := { form := "itself", pronounType := .reflexive, person := some .third, number := some .sg }
def ourselves : PronounEntry := { form := "ourselves", pronounType := .reflexive, person := some .first, number := some .pl }
def yourselves : PronounEntry := { form := "yourselves", pronounType := .reflexive, person := some .second, number := some .pl }
def themselves : PronounEntry := { form := "themselves", pronounType := .reflexive, person := some .third, number := some .pl }

-- ============================================================================
-- Wh-Pronouns
-- ============================================================================

def who : PronounEntry := { form := "who", pronounType := .wh, wh := true }
def whom : PronounEntry := { form := "whom", pronounType := .wh, wh := true, case_ := some .acc }
def what : PronounEntry := { form := "what", pronounType := .wh, wh := true }
def which : PronounEntry := { form := "which", pronounType := .wh, wh := true }
def where_ : PronounEntry := { form := "where", pronounType := .wh, wh := true }
def when_ : PronounEntry := { form := "when", pronounType := .wh, wh := true }
def why : PronounEntry := { form := "why", pronounType := .wh, wh := true }
def how : PronounEntry := { form := "how", pronounType := .wh, wh := true }

-- ============================================================================
-- Conversion to Word
-- ============================================================================

def PronounEntry.toWord (p : PronounEntry) : Word :=
  { form := p.form
  , cat := if p.wh then .Wh else .D
  , features := {
      person := p.person
      , number := p.number
      , case_ := p.case_
      , wh := p.wh
    }
  }

-- ============================================================================
-- All Pronouns
-- ============================================================================

def allPronouns : List PronounEntry := [
  i, me, we, us, you, you_pl,
  he, him, she, her, it, they, them,
  myself, yourself, himself, herself, itself, ourselves, yourselves, themselves,
  who, whom, what, which, where_, when_, why, how
]

def lookup (form : String) : Option PronounEntry :=
  allPronouns.find? λ p => p.form == form

end Fragments.English.Pronouns
