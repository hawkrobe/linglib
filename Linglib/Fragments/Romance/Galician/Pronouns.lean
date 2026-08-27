import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Galician pronouns and allocutive clitics

Personal pronouns of Galician, with the T/V contrast *ti* / *vostede* in the
singular and *vós* / *vostedes* in the plural, and the familiar dative
clitics *che* and *vos* that double as allocutive markers ([alok-bhalla-2026]
(9)–(10)): the same morphemes serve as thematic datives, and the allocutive
use occurs in every finite embedded clause and inside infinitives.
-/

namespace Galician.Pronouns

open Pronoun

/-- *eu* — 1sg. -/
def eu : PersonalPronoun := { form := "eu", person := some .first, number := some .singular }

/-- *nós* — 1pl. -/
def nos : PersonalPronoun := { form := "nós", person := some .first, number := some .plural }

/-- *ti* — 2sg familiar. -/
def ti : PersonalPronoun :=
  { form := "ti", person := some .second, number := some .singular, register := .informal }

/-- *vostede* — 2sg formal. -/
def vostede : PersonalPronoun :=
  { form := "vostede", person := some .second, number := some .singular, register := .formal }

/-- *vós* — 2pl familiar. -/
def vosPl : PersonalPronoun :=
  { form := "vós", person := some .second, number := some .plural, register := .informal }

/-- *vostedes* — 2pl formal. -/
def vostedes : PersonalPronoun :=
  { form := "vostedes", person := some .second, number := some .plural, register := .formal }

/-- *el* — 3sg masculine. -/
def el : PersonalPronoun :=
  { form := "el", person := some .third, number := some .singular, gender := some .masculine }

/-- *ela* — 3sg feminine. -/
def ela : PersonalPronoun :=
  { form := "ela", person := some .third, number := some .singular, gender := some .feminine }

/-- *eles* — 3pl masculine. -/
def eles : PersonalPronoun :=
  { form := "eles", person := some .third, number := some .plural, gender := some .masculine }

/-- *elas* — 3pl feminine. -/
def elas : PersonalPronoun :=
  { form := "elas", person := some .third, number := some .plural, gender := some .feminine }

/-- The pronoun inventory. -/
def pronouns : List PersonalPronoun :=
  [eu, nos, ti, vostede, vosPl, vostedes, el, ela, eles, elas]

/-- *che* — familiar dative clitic, singular addressee. -/
def che : AllocutiveEntry := { form := "che", register := .informal, gloss := "2sg.DAT.fam" }

/-- *vos* — familiar dative clitic, plural addressee. -/
def vos : AllocutiveEntry := { form := "vos", register := .informal, gloss := "2pl.DAT.fam" }

/-- The allocutive clitics. -/
def allocutiveClitics : List AllocutiveEntry := [che, vos]

end Galician.Pronouns
