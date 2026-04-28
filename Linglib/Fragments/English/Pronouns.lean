/-
# English Pronoun Lexicon Fragment

Lexical entries for English pronouns (personal, reflexive, wh-).
-/

import Linglib.Core.Lexical.Word
import Linglib.Core.Lexical.Pronouns
import Linglib.Typology.Pronouns

namespace Fragments.English.Pronouns

-- ============================================================================
-- Gender Paradigm
-- ============================================================================

/-- English pronominal gender paradigm.

    Each paradigm class groups the personal and reflexive pronouns that
    must agree in gender. Used for binding agreement (Principle A/B).

    **Epicene** covers singular *they/them/themself* — animate referents
    whose gender is either unspecified in the discourse or whose personal
    pronouns are *they/them*. This replaces the earlier `.plural`
    constructor, which incorrectly conflated number (plural) with gender
    (ungendered). Singular *they* has been attested since Middle English
    (@cite{balhorn-2004}); @cite{arnold-2026} distinguishes two pragmatic
    uses (underspecified vs. personal). -/
inductive GenderParadigm where
  | masculine   -- he/him/himself
  | feminine    -- she/her/herself
  | neuter      -- it/itself (inanimate)
  | epicene     -- they/them/themself (animate, ungendered)
  | unspecified -- first/second person, reciprocals, etc.
  deriving DecidableEq, Repr

/-- Coarsening from English gender paradigm to cross-linguistic surface
    gender. Returns `none` for epicene (no single `SurfaceGender` for
    animate-ungendered) and unspecified. -/
def GenderParadigm.toSurfaceGender : GenderParadigm → Option Features.SurfaceGender
  | .masculine => some .masculine
  | .feminine  => some .feminine
  | .neuter    => some .neuter
  | .epicene   => none
  | .unspecified => none

/-- Map a personal pronoun specification to its English gender paradigm. -/
def Core.Pronouns.PronounSpec.toGenderParadigm : Core.Pronouns.PronounSpec → GenderParadigm
  | .heHim   => .masculine
  | .sheHer  => .feminine
  | .theyThem => .epicene

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
  /-- Gender paradigm class (3rd-person singular agreement).
      Epicene covers singular *they*; `none` for 1st/2nd person,
      reciprocals, and wh-pronouns. -/
  genderParadigm : Option GenderParadigm := none
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
def he : PronounEntry := { form := "he", pronounType := .personal, person := some .third, number := some .sg, case_ := some .nom, genderParadigm := some .masculine }
def him : PronounEntry := { form := "him", pronounType := .personal, person := some .third, number := some .sg, case_ := some .acc, genderParadigm := some .masculine }
def she : PronounEntry := { form := "she", pronounType := .personal, person := some .third, number := some .sg, case_ := some .nom, genderParadigm := some .feminine }
def her : PronounEntry := { form := "her", pronounType := .personal, person := some .third, number := some .sg, case_ := some .acc, genderParadigm := some .feminine }
def it : PronounEntry := { form := "it", pronounType := .personal, person := some .third, number := some .sg, genderParadigm := some .neuter }
def they : PronounEntry := { form := "they", pronounType := .personal, person := some .third, number := some .pl, case_ := some .nom, genderParadigm := some .epicene }
def them : PronounEntry := { form := "them", pronounType := .personal, person := some .third, number := some .pl, case_ := some .acc, genderParadigm := some .epicene }

-- Third person singular *they* (@cite{arnold-2026}, @cite{balhorn-2004}).
-- The same phonological form as plural *they* but with singular number.
-- Covers both underspecified singular *they* (gender unknown/irrelevant)
-- and personal singular *they* (referent's pronouns are they/them).
def they_sg : PronounEntry := { form := "they", pronounType := .personal, person := some .third, number := some .sg, case_ := some .nom, genderParadigm := some .epicene }
def them_sg : PronounEntry := { form := "them", pronounType := .personal, person := some .third, number := some .sg, case_ := some .acc, genderParadigm := some .epicene }

-- ============================================================================
-- Reflexive Pronouns
-- ============================================================================

def myself : PronounEntry := { form := "myself", pronounType := .reflexive, person := some .first, number := some .sg }
def yourself : PronounEntry := { form := "yourself", pronounType := .reflexive, person := some .second, number := some .sg }
def himself : PronounEntry := { form := "himself", pronounType := .reflexive, person := some .third, number := some .sg, genderParadigm := some .masculine }
def herself : PronounEntry := { form := "herself", pronounType := .reflexive, person := some .third, number := some .sg, genderParadigm := some .feminine }
def itself : PronounEntry := { form := "itself", pronounType := .reflexive, person := some .third, number := some .sg, genderParadigm := some .neuter }
def ourselves : PronounEntry := { form := "ourselves", pronounType := .reflexive, person := some .first, number := some .pl }
def yourselves : PronounEntry := { form := "yourselves", pronounType := .reflexive, person := some .second, number := some .pl }
def themselves : PronounEntry := { form := "themselves", pronounType := .reflexive, person := some .third, number := some .pl, genderParadigm := some .epicene }
def themself : PronounEntry := { form := "themself", pronounType := .reflexive, person := some .third, number := some .sg, genderParadigm := some .epicene }

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
-- Gender Lookup Functions
-- ============================================================================

/-- Map a pronoun form to its gender paradigm. -/
def genderOf (form : String) : GenderParadigm :=
  if form ∈ ["he", "him", "himself"] then .masculine
  else if form ∈ ["she", "her", "herself"] then .feminine
  else if form ∈ ["it", "itself"] then .neuter
  else if form ∈ ["they", "them", "themselves", "themself"] then .epicene
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
  | .epicene, .epicene => true
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
  he, him, she, her, it, they, them, they_sg, them_sg,
  myself, yourself, himself, herself, itself, ourselves, yourselves, themselves, themself,
  eachOther, oneAnother,
  who, whom, what, which, where_, when_, why, how
]

def lookup (form : String) : Option PronounEntry :=
  allPronouns.find? λ p => p.form == form

-- ============================================================================
-- Consistency: structural gender field agrees with genderOf string function
-- ============================================================================

/-- Every 3rd-person pronoun's structural `genderParadigm` field agrees
    with the string-based `genderOf` function. This makes the field
    redundant for these forms but proves the two representations are
    consistent — future code can use either. -/
theorem he_gender_consistent : he.genderParadigm = some (genderOf "he") := rfl
theorem she_gender_consistent : she.genderParadigm = some (genderOf "she") := rfl
theorem it_gender_consistent : it.genderParadigm = some (genderOf "it") := rfl
theorem they_gender_consistent : they.genderParadigm = some (genderOf "they") := rfl
theorem they_sg_gender_consistent : they_sg.genderParadigm = some (genderOf "they") := rfl
theorem themself_gender_consistent : themself.genderParadigm = some (genderOf "themself") := rfl

/-- Singular and plural *they* share the same gender paradigm despite
    differing in number. This is the structural correlate of Arnold's
    observation that underspecified and personal *they* share phonological
    form and the ungendered morphosyntactic feature. -/
theorem sg_pl_same_gender :
    they_sg.genderParadigm = they.genderParadigm := rfl

end Fragments.English.Pronouns

namespace Fragments.English

/-- English (Indo-European, Germanic) WALS pronoun typology profile.
    No incl/excl; gender in 3rd sg only (he/she/it); no politeness;
    generic-noun-based indefinites (somebody, something); intensifier
    and reflexive identical (himself); no person marking on
    adpositions. (WALS Chs 39, 40, 44–48.) -/
def pronounProfile : Typology.PronounProfile :=
  { language := "English"
  , family := "Indo-European"
  , iso := "eng"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .weEqualsI
  , genderInPronouns := some .in3rdPersonSgOnly
  , politeness := some .none
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .noPersonMarking }

/-- English pronoun phonological shape (WALS Chs 136–137,
    @cite{nichols-peterson-2013}): no M-T pattern (1SG *I*/*me*, 2SG *you*),
    but 1SG has /m/ in *me*/*my*; no N-M pattern; no /m/ in 2SG. -/
def pronounShapeProfile : Typology.PronounShapeProfile :=
  { language := "English"
  , iso := "eng"
  , mtPronouns := some .absent
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent }

end Fragments.English
