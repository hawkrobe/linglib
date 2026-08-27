import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Maithili pronouns

Personal pronouns of Maithili: a three-level honorific contrast in the second
person (*tõ* / *ahã* / *apne*) and a two-level one in the third (*ũ* / *o*).
Maithili has allocutive agreement, blocked with a second-person subject and
incompatible with object agreement ([alok-bhalla-2026], after Kumari 2022);
its marker forms are not recorded here.
-/

namespace Maithili.Pronouns

open Pronoun

/-- *hum* — 1sg. -/
def hum : PersonalPronoun := { form := "hum", person := some .first, number := some .singular }

/-- *hum sab* — 1pl. -/
def humSab : PersonalPronoun :=
  { form := "hum sab", person := some .first, number := some .plural }

/-- *tõ* — 2sg nonhonorific. -/
def toN : PersonalPronoun :=
  { form := "tõ", person := some .second, number := some .singular, register := .informal }

/-- *ahã* — 2sg honorific. -/
def ahaN : PersonalPronoun :=
  { form := "ahã", person := some .second, number := some .singular, register := .neutral }

/-- *apne* — 2sg high honorific. -/
def apne : PersonalPronoun :=
  { form := "apne", person := some .second, number := some .singular, register := .formal }

/-- *ũ* — 3sg nonhonorific. -/
def uN : PersonalPronoun :=
  { form := "ũ", person := some .third, number := some .singular, register := .informal }

/-- *o* — 3sg honorific. -/
def o : PersonalPronoun :=
  { form := "o", person := some .third, number := some .singular, register := .neutral }

/-- *ũ sab* — 3pl. -/
def uNSab : PersonalPronoun := { form := "ũ sab", person := some .third, number := some .plural }

/-- The pronoun inventory. -/
def pronouns : List PersonalPronoun := [hum, humSab, toN, ahaN, apne, uN, o, uNSab]

end Maithili.Pronouns
