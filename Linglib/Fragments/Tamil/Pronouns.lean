import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Tamil pronouns and the allocutive marker

Personal pronouns of Tamil — an inclusive/exclusive contrast in the first
person plural (*naam* / *naangaL*), the honorific contrast *nii* / *niingaL*
in the second person, and gendered and honorific third-person forms — and
the allocutive marker *-ŋgæ*, which is the nominal plural suffix
([alok-bhalla-2026] (7), Table 1; McFadden 2020). In root clauses the marker
can appear both below and above the question particle; when embedded, only
below the complementizer.
-/

namespace Tamil.Pronouns

open Pronoun

/-- *naan* — 1sg. -/
def naan : PersonalPronoun := { form := "naan", person := some .first, number := some .singular }

/-- *naam* — 1pl inclusive. -/
def naam : PersonalPronoun :=
  { form := "naam", person := some .firstInclusive, number := some .plural }

/-- *naangaL* — 1pl exclusive. -/
def naangaL : PersonalPronoun :=
  { form := "naangaL", person := some .firstExclusive, number := some .plural }

/-- *nii* — 2sg nonhonorific. -/
def nii : PersonalPronoun :=
  { form := "nii", person := some .second, number := some .singular, register := .informal }

/-- *niingaL* — 2sg honorific, also 2pl. -/
def niingaL : PersonalPronoun :=
  { form := "niingaL", person := some .second, number := some .singular, register := .formal }

/-- *avan* — 3sg masculine. -/
def avan : PersonalPronoun :=
  { form := "avan", person := some .third, number := some .singular, gender := some .masculine }

/-- *avaL* — 3sg feminine. -/
def avaL : PersonalPronoun :=
  { form := "avaL", person := some .third, number := some .singular, gender := some .feminine }

/-- *avar* — 3sg honorific. -/
def avar : PersonalPronoun :=
  { form := "avar", person := some .third, number := some .singular, register := .formal }

/-- *avarkaL* — 3pl human. -/
def avarkaL : PersonalPronoun :=
  { form := "avarkaL", person := some .third, number := some .plural }

/-- The pronoun inventory. -/
def pronouns : List PersonalPronoun :=
  [naan, naam, naangaL, nii, niingaL, avan, avaL, avar, avarkaL]

/-- The nominal plural suffix. -/
def pluralSuffix : String := "-ŋgæ"

/-- *-ŋgæ* — politeness to the addressee; the plural suffix itself. -/
def alloc : AllocutiveEntry := { form := pluralSuffix, register := .formal, gloss := "ALLOC" }

/-- Number marking on nominals, singular and plural (Table 1 of
    [alok-bhalla-2026], after McFadden 2020). -/
def numberPairs : List (String × String) :=
  [("naan", "naan-ŋgæ"), ("nii", "nii-ŋgæ"), ("avan", "avan-ŋgæ"), ("poɳɳǔ", "poɳɳǔ-ŋgæ"),
   ("maram", "maram-ŋgæ")]

end Tamil.Pronouns
