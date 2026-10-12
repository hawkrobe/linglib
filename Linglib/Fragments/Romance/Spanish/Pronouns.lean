module

public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Spanish personal pronouns

The subject pronouns are *yo*, *tú*, *usted*, *él* and *ella* in the singular and *nosotros*,
*nosotras*, *vosotros*, *vosotras*, *ustedes*, *ellos* and *ellas* in the plural, with *vos* for
*tú* in some Latin-American countries. *Tú* and *vosotros* address familiars, *usted* and
*ustedes* others; *vosotros* is used in Spain only, and in Latin America *ustedes* is the plural of
*tú* as well as of *usted*. Descending from *Vuestra Merced* 'Your Grace', *usted* and *ustedes*
take third-person verb forms ([butt-benjamin-2019]). *Usted* is third person in its clitics and
reflexives as well, *yo la respeto (a usted)* 'I respect you', and it shows a person-case effect:
the accusative *la* of *se la presentaré a los estudiantes* 'I will introduce her to the
students' cannot refer to the addressee ([adamson-zompi-2025], after [rezac-2011]).

## References

* [adamson-zompi-2025]
* [butt-benjamin-2019]
* [rezac-2011]
-/

@[expose] public section

namespace Spanish

/-- The honorific grades of Spanish pronouns, lowest first. -/
inductive Grade where
  /-- The familiar grade, *tú*, *vos*, *vosotros* and *vosotras*. -/
  | familiar
  /-- The polite grade, *usted* and *ustedes*. -/
  | polite
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- *yo* 'I'. -/
def yo : PersonalPronoun Grade :=
  { form := "yo", person := some .first, number := some .singular }

/-- *tú* 'you', familiar. -/
def tu : PersonalPronoun Grade :=
  { form := "tú", person := some .second, number := some .singular,
    grades := {.familiar} }

/-- *vos* 'you', familiar, in some Latin-American countries. -/
def vos : PersonalPronoun Grade :=
  { form := "vos", person := some .second, number := some .singular,
    grades := {.familiar} }

/-- *usted* 'you', polite, with third-person agreement. -/
def usted : PersonalPronoun Grade :=
  { form := "usted", person := some .third, number := some .singular, grades := {.polite},
    referential := {.addressee} }

/-- *él* 'he, it'. -/
def el : PersonalPronoun Grade :=
  { form := "él", person := some .third, number := some .singular, gender := some .masculine }

/-- *ella* 'she, it'. -/
def ella : PersonalPronoun Grade :=
  { form := "ella", person := some .third, number := some .singular, gender := some .feminine }

/-- *nosotros* 'we', masculine or mixed. -/
def nosotros : PersonalPronoun Grade :=
  { form := "nosotros", person := some .first, number := some .plural,
    gender := some .masculine }

/-- *nosotras* 'we', feminine. -/
def nosotras : PersonalPronoun Grade :=
  { form := "nosotras", person := some .first, number := some .plural,
    gender := some .feminine }

/-- *vosotros* 'you', familiar plural, masculine or mixed, used in Spain. -/
def vosotros : PersonalPronoun Grade :=
  { form := "vosotros", person := some .second, number := some .plural,
    gender := some .masculine, grades := {.familiar} }

/-- *vosotras* 'you', familiar plural, feminine, used in Spain. -/
def vosotras : PersonalPronoun Grade :=
  { form := "vosotras", person := some .second, number := some .plural,
    gender := some .feminine, grades := {.familiar} }

/-- *ustedes* 'you', plural with third-person agreement: polite in Spain, the only plural of
address in Latin America. -/
def ustedes : PersonalPronoun Grade :=
  { form := "ustedes", person := some .third, number := some .plural, grades := {.polite},
    referential := {.addresseeOthers} }

/-- *ellos* 'they', masculine or mixed. -/
def ellos : PersonalPronoun Grade :=
  { form := "ellos", person := some .third, number := some .plural, gender := some .masculine }

/-- *ellas* 'they', feminine. -/
def ellas : PersonalPronoun Grade :=
  { form := "ellas", person := some .third, number := some .plural, gender := some .feminine }

/-- The subject pronouns. -/
def pronouns : Finset (PersonalPronoun Grade) :=
  {yo, tu, vos, usted, el, ella, nosotros, nosotras, vosotros, vosotras, ustedes, ellos, ellas}

end Pronouns

end Spanish
