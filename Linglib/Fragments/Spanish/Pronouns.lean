import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Spanish Pronoun Fragment
[adamson-zompi-2025]

Personal pronouns (strong forms) for Spanish, including the polite
pronoun USTED.

## T/V distinction

Spanish has a T/V distinction:
- Singular: *tú* (familiar T) vs *usted* (formal V, 3sg agreement)
- Plural: *vosotros* (familiar, Peninsular) vs *ustedes* (formal / general)

## USTED and the PCC

Like Italian LEI, USTED triggers 3sg verbal agreement but is interpretably
2nd person. [rezac-2011] observes PCC effects with USTED: the
accusative clitic *la* is grammatical in a 3>3 configuration if its
referent is 3rd person, but ungrammatical as polite USTED (§6.1, (43)).

USTED's forms are identical to the 3sg feminine series in some cases
(like LEI), though it also has the dedicated citation form *usted*.
Unlike Italian LEI, USTED can also be used in *laísta* varieties where
3rd person clitics for animates are *le* (syncretic with dative).
-/

namespace Spanish.Pronouns

open Pronoun

/-- *yo* — 1sg. -/
def yo : PersonalPronoun :=
  { form := "yo", person := some .first, number := some .singular }

/-- *tú* — 2sg familiar (T form). -/
def tu : PersonalPronoun :=
  { form := "tú", person := some .second, number := some .singular, register := .informal }

/-- *usted* — polite 2sg (V form, triggers 3sg agreement).
    Agreement person is 3rd, interpretable person is 2nd. Triggers PCC
    effects: *la* as USTED.ACC is banned in 3>USTED configurations
    ([rezac-2011], [adamson-zompi-2025] §6.1).
    [adamson-zompi-2025] -/
def usted : PersonalPronoun :=
  { form := "usted", person := some .third, number := some .singular, register := .formal,
    referentialPerson := some .second }

/-- *él* — 3sg masculine. -/
def el : PersonalPronoun :=
  { form := "él", person := some .third, number := some .singular, gender := some .masculine }

/-- *ella* — 3sg feminine. -/
def ella : PersonalPronoun :=
  { form := "ella", person := some .third, number := some .singular, gender := some .feminine }

/-- *nosotros* — 1pl. -/
def nosotros : PersonalPronoun :=
  { form := "nosotros", person := some .first, number := some .plural }

/-- *vosotros* — 2pl familiar (Peninsular). -/
def vosotros : PersonalPronoun :=
  { form := "vosotros", person := some .second, number := some .plural, register := .informal }

/-- *ustedes* — 2pl formal / general (triggers 3pl agreement). -/
def ustedes : PersonalPronoun :=
  { form := "ustedes", person := some .third, number := some .plural, register := .formal,
    referentialPerson := some .second }

/-- *ellos* — 3pl masculine. -/
def ellos : PersonalPronoun :=
  { form := "ellos", person := some .third, number := some .plural, gender := some .masculine }

/-- *ellas* — 3pl feminine. -/
def ellas : PersonalPronoun :=
  { form := "ellas", person := some .third, number := some .plural, gender := some .feminine }

/-- The strong-pronoun inventory. -/
def pronouns : List PersonalPronoun :=
  [yo, tu, usted, el, ella, nosotros, vosotros, ustedes, ellos, ellas]

end Spanish.Pronouns
