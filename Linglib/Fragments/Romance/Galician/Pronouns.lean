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

namespace Galician

/-- The honorific grades of Galician pronouns, lowest first. -/
inductive Grade where
  /-- The familiar grade, *ti* and *vós*. -/
  | familiar
  /-- The formal grade, *vostede* and *vostedes*. -/
  | formal
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- *eu* — 1sg. -/
def eu : PersonalPronoun Grade :=
  { form := "eu", person := some .first, number := some .singular }

/-- *nós* — 1pl. -/
def nos : PersonalPronoun Grade :=
  { form := "nós", person := some .first, number := some .plural }

/-- *ti* — 2sg familiar. -/
def ti : PersonalPronoun Grade :=
  { form := "ti", person := some .second, number := some .singular,
    grades := {.familiar} }

/-- *vostede* — 2sg formal. -/
def vostede : PersonalPronoun Grade :=
  { form := "vostede", person := some .second, number := some .singular,
    grades := {.formal} }

/-- *vós* — 2pl familiar. -/
def vosPl : PersonalPronoun Grade :=
  { form := "vós", person := some .second, number := some .plural, grades := {.familiar} }

/-- *vostedes* — 2pl formal. -/
def vostedes : PersonalPronoun Grade :=
  { form := "vostedes", person := some .second, number := some .plural,
    grades := {.formal} }

/-- *el* — 3sg masculine. -/
def el : PersonalPronoun Grade :=
  { form := "el", person := some .third, number := some .singular, gender := some .masculine }

/-- *ela* — 3sg feminine. -/
def ela : PersonalPronoun Grade :=
  { form := "ela", person := some .third, number := some .singular, gender := some .feminine }

/-- *eles* — 3pl masculine. -/
def eles : PersonalPronoun Grade :=
  { form := "eles", person := some .third, number := some .plural, gender := some .masculine }

/-- *elas* — 3pl feminine. -/
def elas : PersonalPronoun Grade :=
  { form := "elas", person := some .third, number := some .plural, gender := some .feminine }

/-- The pronoun inventory. -/
def pronouns : Finset (PersonalPronoun Grade) :=
  {eu, nos, ti, vostede, vosPl, vostedes, el, ela, eles, elas}

/-- *che* — familiar dative clitic, singular addressee. -/
def che : AllocutiveMarker Grade :=
  { form := "che", grade := .familiar, number := some .singular }

/-- *vos* — familiar dative clitic, plural addressee. -/
def vos : AllocutiveMarker Grade :=
  { form := "vos", grade := .familiar, number := some .plural }

/-- The allocutive clitics. -/
def allocutiveClitics : List (AllocutiveMarker Grade) := [che, vos]

end Pronouns

end Galician
