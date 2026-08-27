import Linglib.Syntax.Category.Pronoun.Basic

/-!
# German Pronoun Fragment
[adamson-zompi-2025]

Personal pronouns for German, including the polite pronoun SIE.

## T/V distinction

German has a T/V distinction:
- Singular: *du* (familiar T) vs *Sie* (formal V, 3pl agreement)
- Plural: *ihr* (familiar) vs *Sie* (formal V, 3pl agreement)

Unlike Italian LEI (3sg.f) and Spanish USTED (3sg), German SIE uses the
3rd person **plural** series. SIE triggers 3pl verbal agreement ((45)),
binds 3rd person reflexive *sich* (not 2sg *dich* or 2pl *euch*), and can
refer to either a singular or plural addressee.

## Person hierarchy effects

SIE triggers PCC effects in German's limited PCC environments (Wackernagel
clusters, [anagnostopoulou-2008]), patterning with 2nd person ((47)–(48)).
In contrast, SIE does NOT trigger the exponence-based person hierarchy effect
in assumed-identity copular constructions ([keine-et-al-2019],
[coon-keine-2021]), patterning with 3rd person ((52)–(53)).
-/

namespace German.Pronouns

open Pronoun

/-- *ich* — 1sg. -/
def ich : PersonalPronoun :=
  { form := "ich", person := some .first, number := some .singular }

/-- *du* — 2sg familiar (T form). -/
def du : PersonalPronoun :=
  { form := "du", person := some .second, number := some .singular, register := .informal }

/-- *Sie* — polite 2nd person (V form, triggers 3pl agreement).
    Unlike Italian LEI (3sg.f) and Spanish USTED (3sg), German SIE uses
    the 3pl series. Agreement person is 3rd (plural), interpretable person
    is 2nd. Can refer to singular or plural addressees.
    [adamson-zompi-2025] -/
def sie_polite : PersonalPronoun :=
  { form := "Sie", person := some .third, number := some .plural, register := .formal,
    referentialPerson := some .second }

/-- *er* — 3sg masculine. -/
def er : PersonalPronoun :=
  { form := "er", person := some .third, number := some .singular, gender := some .masculine }

/-- *sie* — 3sg feminine. -/
def sie_f : PersonalPronoun :=
  { form := "sie", person := some .third, number := some .singular, gender := some .feminine }

/-- *es* — 3sg neuter. -/
def es : PersonalPronoun :=
  { form := "es", person := some .third, number := some .singular, gender := some .neuter }

/-- *wir* — 1pl. -/
def wir : PersonalPronoun :=
  { form := "wir", person := some .first, number := some .plural }

/-- *ihr* — 2pl familiar. -/
def ihr : PersonalPronoun :=
  { form := "ihr", person := some .second, number := some .plural, register := .informal }

/-- *sie* — 3pl. -/
def sie_pl : PersonalPronoun :=
  { form := "sie", person := some .third, number := some .plural }

/-- The pronoun inventory. -/
def pronouns : List PersonalPronoun :=
  [ich, du, sie_polite, er, sie_f, es, wir, ihr, sie_pl]

end German.Pronouns
