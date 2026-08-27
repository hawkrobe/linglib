import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Basque pronouns and allocutive markers

Personal pronouns of Basque, with the T/V contrast *hi* (familiar) vs *zu*
(formal) in the second-person singular, and the Souletin allocutive auxiliary
suffixes of [alok-bhalla-2026]'s (1): *-k* and *-n* for a nonhonorific male
and female addressee, *-zü* for an honorific addressee. The same suffixes
serve as ordinary agreement with a second-person subject.
-/

namespace Basque.Pronouns

open Pronoun

/-- *ni* — 1sg. -/
def ni : PersonalPronoun := { form := "ni", person := some .first, number := some .singular }

/-- *gu* — 1pl. -/
def gu : PersonalPronoun := { form := "gu", person := some .first, number := some .plural }

/-- *hi* — 2sg familiar. -/
def hi : PersonalPronoun :=
  { form := "hi", person := some .second, number := some .singular, register := .informal }

/-- *zu* — 2sg formal. -/
def zu : PersonalPronoun :=
  { form := "zu", person := some .second, number := some .singular, register := .formal }

/-- *zuek* — 2pl. -/
def zuek : PersonalPronoun :=
  { form := "zuek", person := some .second, number := some .plural }

/-- *hura* — 3sg. -/
def hura : PersonalPronoun :=
  { form := "hura", person := some .third, number := some .singular }

/-- *haiek* — 3pl. -/
def haiek : PersonalPronoun :=
  { form := "haiek", person := some .third, number := some .plural }

/-- The pronoun inventory. -/
def pronouns : List PersonalPronoun := [ni, gu, hi, zu, zuek, hura, haiek]

/-- *-k* — nonhonorific male addressee. -/
def allocM : AllocutiveEntry := { form := "-k", register := .informal, gloss := "M.NHA" }

/-- *-n* — nonhonorific female addressee. -/
def allocF : AllocutiveEntry := { form := "-n", register := .informal, gloss := "F.NHA" }

/-- *-zü* — honorific addressee. -/
def allocH : AllocutiveEntry := { form := "-zü", register := .formal, gloss := "HA" }

/-- The Souletin allocutive markers. -/
def allocutiveMarkers : List AllocutiveEntry := [allocM, allocF, allocH]

end Basque.Pronouns
