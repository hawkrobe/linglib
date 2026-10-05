module

public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Hindi-Urdu pronouns

The personal pronouns of Hindi-Urdu show a three-level honorific contrast in the second person
(*tuu* / *tum* / *aap*) and demonstrative-based third-person forms (*vah* / *ve*). There is no
allocutive agreement; an honorific subject co-opts plural verb agreement, as Alok and Bhalla
describe for Hindi ((48)).

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

@[expose] public section

namespace HindiUrdu.Pronouns

/-- *maiṃ* — 1sg. -/
def maiN : PersonalPronoun := { form := "maiṃ", person := some .first, number := some .singular }

/-- *ham* — 1pl. -/
def ham : PersonalPronoun := { form := "ham", person := some .first, number := some .plural }

/-- *tuu* — 2sg nonhonorific. -/
def tuu : PersonalPronoun :=
  { form := "tuu", person := some .second, number := some .singular,
    honorific := some .nonhonorific }

/-- *tum* — 2sg honorific. -/
def tum : PersonalPronoun :=
  { form := "tum", person := some .second, number := some .singular, honorific := some .honorific }

/-- *aap* — 2sg high honorific. -/
def aap : PersonalPronoun :=
  { form := "aap", person := some .second, number := some .singular,
    honorific := some .highHonorific }

/-- *vah* — 3sg, the distal demonstrative. -/
def vah : PersonalPronoun := { form := "vah", person := some .third, number := some .singular }

/-- *ve* — 3pl, the distal demonstrative plural. -/
def ve : PersonalPronoun := { form := "ve", person := some .third, number := some .plural }

/-- The pronoun inventory. -/
def pronouns : Finset PersonalPronoun := {maiN, ham, tuu, tum, aap, vah, ve}

end HindiUrdu.Pronouns
