/-
# English Pronoun Lexicon Fragment

Lexical entries for English pronouns (personal, reflexive, wh-).
-/

import Linglib.Core.Lexical.Word

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
  | reciprocal  -- each other, one another
  | wh          -- who, what, which, where, when, why, how
  | relative    -- who, which, that (in relative clauses)
  | demonstrative -- this, that (pronominal use)
  deriving DecidableEq, Repr

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
-- Reciprocal Pronouns
-- ============================================================================

def eachOther : PronounEntry := { form := "each other", pronounType := .reciprocal }
def oneAnother : PronounEntry := { form := "one another", pronounType := .reciprocal }

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
-- Gender Paradigm
-- ============================================================================

/-- English pronominal gender paradigm. Used for binding agreement
    (Principle A/B), since `Word.Features` currently lacks a gender
    field. Each paradigm class groups the personal and reflexive
    pronouns that must agree in gender. -/
inductive GenderParadigm where
  | masculine   -- he/him/himself
  | feminine    -- she/her/herself
  | neuter      -- it/itself
  | plural      -- they/them/themselves (number-only, no gender)
  | unspecified -- first/second person, reciprocals, etc.
  deriving DecidableEq, Repr

/-- Map a pronoun form to its gender paradigm. -/
def genderOf (form : String) : GenderParadigm :=
  if form ∈ ["he", "him", "himself"] then .masculine
  else if form ∈ ["she", "her", "herself"] then .feminine
  else if form ∈ ["it", "itself"] then .neuter
  else if form ∈ ["they", "them", "themselves"] then .plural
  else .unspecified

/-- Map a proper noun to its gender paradigm, if known.
    Returns `.unspecified` for unknown names. -/
def nameGender (form : String) : GenderParadigm :=
  if form ∈ ["John", "Bill", "Fred"] then .masculine
  else if form ∈ ["Mary", "Sue"] then .feminine
  else .unspecified

/-- Do two forms agree in gender? Unspecified gender agrees with anything. -/
def genderAgrees (form1 form2 : String) : Bool :=
  let g1 := match nameGender form1 with
    | .unspecified => genderOf form1
    | g => g
  let g2 := match nameGender form2 with
    | .unspecified => genderOf form2
    | g => g
  match g1, g2 with
  | .unspecified, _ => true
  | _, .unspecified => true
  | .plural, .plural => true
  | .masculine, .masculine => true
  | .feminine, .feminine => true
  | .neuter, .neuter => true
  | _, _ => false

-- ============================================================================
-- Conversion to Word
-- ============================================================================

/-- Is this a wh-adverb (where, when, why, how) rather than a wh-pronoun? -/
def PronounEntry.isWhAdverb (p : PronounEntry) : Bool :=
  p.form ∈ ["where", "when", "why", "how"]

def PronounEntry.toWord (p : PronounEntry) : Word :=
  { form := p.form
  , cat := if p.isWhAdverb then .ADV else .PRON
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
  eachOther, oneAnother,
  who, whom, what, which, where_, when_, why, how
]

def lookup (form : String) : Option PronounEntry :=
  allPronouns.find? λ p => p.form == form

end Fragments.English.Pronouns
