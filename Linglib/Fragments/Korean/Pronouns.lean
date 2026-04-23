/-
# Korean Pronoun & Allocutive Fragment
@cite{kwon-lee-2026} @cite{sohn-1999}

Personal pronouns and allocutive particles in Korean. Korean has
particle-based allocutive marking (*-yo* polite, *-(su)pnida* formal)
hosted in the SAP layer, restricted to root clauses. 1st person has a
plain/humble distinction (*na* / *jeo*).

## 3rd-Person Reference

Korean is discourse-oriented: the unmarked 3rd-person reference is **null**
(*pro*). The 3rd-person pronoun system splits by register, with a strong
written/spoken asymmetry (corpus counts from Lee et al. 2010 cited in
@cite{kwon-lee-2026} fn. 2):

* *geu* (그) — literary 3sg masculine. 76,235 tokens in written vs only
  145 in oral data. Yale romanization: *ku*.
* *geunyeo* (그녀) — literary 3sg feminine. 25,085 written vs 9 oral.
  Compound of *ku* ('that') + *nye* ('female'); developed under Western
  influence in the early 20th century. Yale romanization: *kunye*.
* *gyae* (걔) — colloquial gender-neutral 3sg. The reverse pattern: 1,160
  oral tokens vs 226 written. Contracted from *ku ay* ('that' + contracted
  *ai* 'child'). Implies the speaker has familiarity with the referent
  (@cite{kwon-lee-2026} §5). Yale romanization: *kyay* (used in
  @cite{kwon-lee-2026}).

Traditional Korean relies on null reference, demonstratives, and full
NPs (e.g., *ku chinkwu* 'that friend'). Per @cite{kwon-lee-2026},
the three form types null *pro*, overt *gyae*, and demonstrative+noun
full NPs instantiate three points on @cite{ariel-2001}'s Accessibility
Marking Scale.

## Romanization

This file uses **Revised Romanization** for `form` fields (consistent
with other entries: *na*, *neo*, *geu*). Yale romanizations (used in
much of the linguistics literature) appear in docstrings only.

-/

import Linglib.Core.Lexical.Pronouns

namespace Fragments.Korean.Pronouns

open Core.Pronouns
open Features.Register (Level)

-- ============================================================================
-- First Person
-- ============================================================================

/-- 나 *na* — 1sg plain. -/
def na : PronounEntry :=
  { form := "na", script := some "나", person := some .first, number := some .sg, register := .informal }

/-- 저 *jeo* — 1sg humble. -/
def jeo : PronounEntry :=
  { form := "jeo", script := some "저", person := some .first, number := some .sg, register := .formal }

/-- 우리 *uri* — 1pl. -/
def uri : PronounEntry :=
  { form := "uri", script := some "우리", person := some .first, number := some .pl }

-- ============================================================================
-- Second Person (T/V)
-- ============================================================================

/-- 너 *neo* — 2sg plain. -/
def neo : PronounEntry :=
  { form := "neo", script := some "너", person := some .second, number := some .sg, register := .informal }

/-- 당신 *dangsin* — 2sg polite. -/
def dangsin : PronounEntry :=
  { form := "dangsin", script := some "당신", person := some .second, number := some .sg, register := .formal }

-- ============================================================================
-- Third Person
-- ============================================================================

/-- 그 *geu* (Yale: *ku*) — 3sg masculine, **literary** register.
    76,235 written vs 145 oral tokens (@cite{kwon-lee-2026} fn. 2). -/
def geu : PronounEntry :=
  { form := "geu", script := some "그", person := some .third, number := some .sg
  , gender := some .masculine, register := .formal }

/-- 그녀 *geunyeo* (Yale: *kunye*) — 3sg feminine, **literary** register.
    Compound of *ku* ('that') + *nye* ('female'). 25,085 written vs
    9 oral tokens (@cite{kwon-lee-2026} fn. 2). -/
def geunyeo : PronounEntry :=
  { form := "geunyeo", script := some "그녀", person := some .third, number := some .sg
  , gender := some .feminine, register := .formal }

/-- 걔 *gyae* (Yale: *kyay*) — 3sg gender-neutral, **colloquial** pronoun.
    Contracted from *ku ay* ('that' + contracted *ai* 'child'). 1,160
    oral vs 226 written tokens — the reverse register pattern of
    *geu*/*geunyeo*. Implies familiarity between speaker and referent
    (@cite{kwon-lee-2026} §5). The overt-pronoun referential form
    tested in @cite{kwon-lee-2026}'s experiments. -/
def gyae : PronounEntry :=
  { form := "gyae", script := some "걔", person := some .third, number := some .sg
  , register := .informal }

/-- 그들 *geudeul* — 3pl. Plural of *geu*; literary in register
    (the colloquial plural is the proximal demonstrative + *ai-tul*). -/
def geudeul : PronounEntry :=
  { form := "geudeul", script := some "그들", person := some .third, number := some .pl
  , register := .formal }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PronounEntry := [neo, dangsin]

/-- 3rd-person pronouns: literary *geu*/*geunyeo*/*geudeul* and
    colloquial *gyae*. Yale-romanization variants (*ku*/*kunye*/*kutul*/
    *kyay*) refer to the same lexical items. -/
def thirdPersonPronouns : List PronounEntry := [geu, geunyeo, geudeul, gyae]

def allPronouns : List PronounEntry :=
  [na, jeo, uri] ++ secondPersonPronouns ++ thirdPersonPronouns

-- ============================================================================
-- Allocutive Particles (SAP-layer)
-- ============================================================================

/-- *-yo* polite particle. -/
def yo : AllocutiveEntry :=
  { form := "-yo", register := .neutral, gloss := "POL" }

/-- *-(su)pnida* formal particle. -/
def supnida : AllocutiveEntry :=
  { form := "-(su)pnida", register := .formal, gloss := "FORM" }

def allAllocParticles : List AllocutiveEntry := [yo, supnida]

-- ============================================================================
-- Verb Agreement Examples
-- ============================================================================

/-- A verb form showing speech-level inflection. -/
structure VerbForm where
  form : String
  gloss : String
  register : Level
  deriving Repr, BEq

/-- 가 *ga* — "go" (plain/intimate). -/
def ga : VerbForm := { form := "ga", gloss := "go.PLN", register := .informal }

/-- 가요 *gayo* — "go" (polite). -/
def gayo : VerbForm := { form := "gayo", gloss := "go.POL", register := .neutral }

/-- 갑니다 *gamnida* — "go" (formal). -/
def gamnida : VerbForm := { form := "gamnida", gloss := "go.FORM", register := .formal }

-- ============================================================================
-- Verification
-- ============================================================================

/-- All three persons are attested. -/
theorem has_all_persons :
    allPronouns.any (·.person == some .first) = true ∧
    allPronouns.any (·.person == some .second) = true ∧
    allPronouns.any (·.person == some .third) = true := ⟨rfl, rfl, rfl⟩

/-- Both singular and plural are attested. -/
theorem has_both_numbers :
    allPronouns.any (·.number == some .sg) = true ∧
    allPronouns.any (·.number == some .pl) = true := ⟨rfl, rfl⟩

/-- 1st person has plain/humble register distinction. -/
theorem first_person_humble :
    na.register = .informal ∧ jeo.register = .formal := ⟨rfl, rfl⟩

/-- 2nd person pronouns are all second person. -/
theorem second_person_all_2p :
    secondPersonPronouns.all (·.person == some .second) = true := rfl

/-- The T/V register distinction is present in 2nd person. -/
theorem tv_distinction :
    secondPersonPronouns.any (·.register == .informal) = true ∧
    secondPersonPronouns.any (·.register == .formal) = true := ⟨rfl, rfl⟩

/-- Verb forms span all three speech levels. -/
theorem verb_three_levels :
    ga.register = .informal ∧ gayo.register = .neutral ∧ gamnida.register = .formal := ⟨rfl, rfl, rfl⟩

/-- 3rd-person pronouns split by register: *gyae* is colloquial,
    *geu*/*geunyeo*/*geudeul* are literary (@cite{kwon-lee-2026} fn. 2). -/
theorem third_person_register_split :
    gyae.register = .informal ∧
    geu.register = .formal ∧
    geunyeo.register = .formal ∧
    geudeul.register = .formal := ⟨rfl, rfl, rfl, rfl⟩

/-- *gyae* is gender-neutral; *geu*/*geunyeo* are gendered. This is the
    central asymmetry of the Korean 3rd-person system: the colloquial
    pronoun lacks the gender contrast carried by the literary forms. -/
theorem gyae_gender_neutral :
    gyae.gender = none ∧
    geu.gender = some .masculine ∧
    geunyeo.gender = some .feminine := ⟨rfl, rfl, rfl⟩

end Fragments.Korean.Pronouns
