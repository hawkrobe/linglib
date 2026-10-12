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

namespace HindiUrdu

/-- The honorific grades of the Hindi-Urdu second person, lowest first. -/
inductive Grade where
  /-- The nonhonorific grade, *tuu*. -/
  | nonhonorific
  /-- The honorific grade, *tum*. -/
  | honorific
  /-- The high honorific grade, *aap*. -/
  | highHonorific
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- *maiṃ* — 1sg. -/
def maiN : PersonalPronoun Grade :=
  { form := "maiṃ", person := some .first, number := some .singular }

/-- *ham* — 1pl. -/
def ham : PersonalPronoun Grade := { form := "ham", person := some .first, number := some .plural }

/-- *tuu* — 2sg nonhonorific. -/
def tuu : PersonalPronoun Grade :=
  { form := "tuu", person := some .second, number := some .singular,
    grades := {.nonhonorific} }

/-- *tum* — 2sg honorific. -/
def tum : PersonalPronoun Grade :=
  { form := "tum", person := some .second, number := some .singular, grades := {.honorific} }

/-- *aap* — 2sg high honorific. -/
def aap : PersonalPronoun Grade :=
  { form := "aap", person := some .second, number := some .singular,
    grades := {.highHonorific} }

/-- *vah* — 3sg, the distal demonstrative. -/
def vah : PersonalPronoun Grade :=
  { form := "vah", person := some .third, number := some .singular }

/-- *ve* — 3pl, the distal demonstrative plural. -/
def ve : PersonalPronoun Grade := { form := "ve", person := some .third, number := some .plural }

/-- The pronoun inventory. -/
def pronouns : Finset (PersonalPronoun Grade) := {maiN, ham, tuu, tum, aap, vah, ve}

end Pronouns

end HindiUrdu
