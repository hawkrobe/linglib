/-
# Korean pronouns and speech-style particles
[kwon-lee-2026] [sohn-1999]

Personal pronouns of Korean and its sentence-final speech-style particles
(*-yo* polite, *-(su)pnida* formal), which encode the speaker–addressee
relation and the formality of the discourse and are confined to root clauses
([alok-bhalla-2026] (8), (13)). The first person has a plain/humble contrast
(*na* / *jeo*).

## 3rd-Person Reference

Korean is discourse-oriented: the unmarked 3rd-person reference is **null**
(*pro*). The 3rd-person pronoun system splits by register, with a strong
written/spoken asymmetry (corpus counts from Lee et al. 2010 cited in
[kwon-lee-2026] fn. 2):

* *geu* (그) — literary 3sg masculine. 76,235 tokens in written vs only
  145 in oral data. Yale romanization: *ku*.
* *geunyeo* (그녀) — literary 3sg feminine. 25,085 written vs 9 oral.
  Compound of *ku* ('that') + *nye* ('female'); developed under Western
  influence in the early 20th century. Yale romanization: *kunye*.
* *gyae* (걔) — colloquial gender-neutral 3sg. The reverse pattern: 1,160
  oral tokens vs 226 written. Contracted from *ku ay* ('that' + contracted
  *ai* 'child'). Implies the speaker has familiarity with the referent
  ([kwon-lee-2026] §5). Yale romanization: *kyay* (used in
  [kwon-lee-2026]).

Traditional Korean relies on null reference, demonstratives, and full
NPs (e.g., *ku chinkwu* 'that friend'). Per [kwon-lee-2026],
the three form types null *pro*, overt *gyae*, and demonstrative+noun
full NPs instantiate three points on [ariel-2001]'s Accessibility
Marking Scale.

## Romanization

This file uses **Revised Romanization** for `form` fields (consistent
with other entries: *na*, *neo*, *geu*). Yale romanizations (used in
much of the linguistics literature) appear in docstrings only.

-/

import Linglib.Syntax.Category.Pronoun.Basic

namespace Korean.Pronouns

open Pronoun

-- ============================================================================
-- First Person
-- ============================================================================

/-- 나 *na* — 1sg plain. -/
def na : PersonalPronoun :=
  { form := "na", script := some "나", person := some .first, number := some .singular,
    register := .informal }

/-- 저 *jeo* — 1sg humble. -/
def jeo : PersonalPronoun :=
  { form := "jeo", script := some "저", person := some .first, number := some .singular,
    register := .formal }

/-- 우리 *uri* — 1pl. -/
def uri : PersonalPronoun :=
  { form := "uri", script := some "우리", person := some .first, number := some .plural }

-- ============================================================================
-- Second Person (T/V)
-- ============================================================================

/-- 너 *neo* — 2sg plain. -/
def neo : PersonalPronoun :=
  { form := "neo", script := some "너", person := some .second, number := some .singular,
    register := .informal }

/-- 당신 *dangsin* — 2sg polite. -/
def dangsin : PersonalPronoun :=
  { form := "dangsin", script := some "당신", person := some .second, number := some .singular,
    register := .formal }

-- ============================================================================
-- Third Person
-- ============================================================================

/-- 그 *geu* (Yale: *ku*) — 3sg masculine, **literary** register.
    76,235 written vs 145 oral tokens ([kwon-lee-2026] fn. 2). -/
def geu : PersonalPronoun :=
  { form := "geu", script := some "그", person := some .third, number := some .singular
  , gender := some .masculine, register := .formal }

/-- 그녀 *geunyeo* (Yale: *kunye*) — 3sg feminine, **literary** register.
    Compound of *ku* ('that') + *nye* ('female'). 25,085 written vs
    9 oral tokens ([kwon-lee-2026] fn. 2). -/
def geunyeo : PersonalPronoun :=
  { form := "geunyeo", script := some "그녀", person := some .third, number := some .singular
  , gender := some .feminine, register := .formal }

/-- 걔 *gyae* (Yale: *kyay*) — 3sg gender-neutral, **colloquial** pronoun.
    Contracted from *ku ay* ('that' + contracted *ai* 'child'). 1,160
    oral vs 226 written tokens — the reverse register pattern of
    *geu*/*geunyeo*. Implies familiarity between speaker and referent
    ([kwon-lee-2026] §5). The overt-pronoun referential form
    tested in [kwon-lee-2026]'s experiments. -/
def gyae : PersonalPronoun :=
  { form := "gyae", script := some "걔", person := some .third, number := some .singular
  , register := .informal }

/-- 그들 *geudeul* — 3pl. Plural of *geu*; literary in register
    (the colloquial plural is the proximal demonstrative + *ai-tul*). -/
def geudeul : PersonalPronoun :=
  { form := "geudeul", script := some "그들", person := some .third, number := some .plural
  , register := .formal }

/-- The pronoun inventory: the literary third-person forms *geu*, *geunyeo*,
    *geudeul* and the colloquial *gyae* (Yale *ku*, *kunye*, *kutul*, *kyay*). -/
def pronouns : List PersonalPronoun :=
  [na, jeo, uri, neo, dangsin, geu, geunyeo, geudeul, gyae]

/-- *-yo* — the polite speech-style particle. -/
def yo : AllocutiveEntry := { form := "-yo", register := .neutral, gloss := "POL" }

/-- *-(su)pnida* — the formal speech-style particle. -/
def supnida : AllocutiveEntry := { form := "-(su)pnida", register := .formal, gloss := "FORM" }

/-- The speech-style particles recorded here. -/
def allocutiveParticles : List AllocutiveEntry := [yo, supnida]

end Korean.Pronouns
