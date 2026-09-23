module

public import Linglib.Syntax.Agreement.Allocutive
public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Galician pronouns and allocutive clitics

Personal pronouns of Galician, with the T/V contrast *ti* / *vostede* in the
singular and *vós* / *vostedes* in the plural, and the familiar dative
clitics *che* and *vos* that double as allocutive markers ([alok-bhalla-2026]
(9)–(10)): the same morphemes serve as thematic datives, and the allocutive
use occurs in every finite embedded clause and inside infinitives.

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

@[expose] public section

namespace Galician.Pronouns

/-- *eu* — 1sg. -/
def eu : PersonalPronoun := { form := "eu", person := some .first, number := some .singular }

/-- *nós* — 1pl. -/
def nos : PersonalPronoun := { form := "nós", person := some .first, number := some .plural }

/-- *ti* — 2sg familiar. -/
def ti : PersonalPronoun :=
  { form := "ti", person := some .second, number := some .singular,
    honorific := some .nonhonorific }

/-- *vostede* — 2sg formal. -/
def vostede : PersonalPronoun :=
  { form := "vostede", person := some .second, number := some .singular,
    honorific := some .honorific }

/-- *vós* — 2pl familiar. -/
def vosPl : PersonalPronoun :=
  { form := "vós", person := some .second, number := some .plural, honorific := some .nonhonorific }

/-- *vostedes* — 2pl formal. -/
def vostedes : PersonalPronoun :=
  { form := "vostedes", person := some .second, number := some .plural,
    honorific := some .honorific }

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
def pronouns : Finset PersonalPronoun :=
  {eu, nos, ti, vostede, vosPl, vostedes, el, ela, eles, elas}

/-- *che* — familiar dative clitic, singular addressee. -/
def che : AllocutiveMarker :=
  { form := "che", honorific := .nonhonorific, number := some .singular }

/-- *vos* — familiar dative clitic, plural addressee. -/
def vos : AllocutiveMarker := { form := "vos", honorific := .nonhonorific, number := some .plural }

/-- The allocutive clitics. -/
def allocutiveClitics : List AllocutiveMarker := [che, vos]

end Galician.Pronouns
