import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Maithili pronouns

Personal pronouns of Maithili: a three-level honorific contrast in the second
person (*tõ* / *ahã* / *apne*) and a two-level one in the third (*ũ* / *o*).
Maithili has allocutive agreement, blocked with a second-person subject and
incompatible with object agreement ([alok-bhalla-2026], after Kumari 2022);
its marker forms are not recorded here.

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

namespace Maithili.Pronouns

/-- *hum* — 1sg. -/
def hum : PersonalPronoun := { form := "hum", person := some .first, number := some .singular }

/-- *hum sab* — 1pl. -/
def humSab : PersonalPronoun :=
  { form := "hum sab", person := some .first, number := some .plural }

/-- *tõ* — 2sg nonhonorific. -/
def toN : PersonalPronoun :=
  { form := "tõ", person := some .second, number := some .singular,
    honorific := some .nonhonorific }

/-- *ahã* — 2sg honorific. -/
def ahaN : PersonalPronoun :=
  { form := "ahã", person := some .second, number := some .singular, honorific := some .honorific }

/-- *apne* — 2sg high honorific. -/
def apne : PersonalPronoun :=
  { form := "apne", person := some .second, number := some .singular,
    honorific := some .highHonorific }

/-- *ũ* — 3sg nonhonorific. -/
def uN : PersonalPronoun :=
  { form := "ũ", person := some .third, number := some .singular, honorific := some .nonhonorific }

/-- *o* — 3sg honorific. -/
def o : PersonalPronoun :=
  { form := "o", person := some .third, number := some .singular, honorific := some .honorific }

/-- *ũ sab* — 3pl. -/
def uNSab : PersonalPronoun := { form := "ũ sab", person := some .third, number := some .plural }

/-- The pronoun inventory. -/
def pronouns : Finset PersonalPronoun := {hum, humSab, toN, ahaN, apne, uN, o, uNSab}

end Maithili.Pronouns
