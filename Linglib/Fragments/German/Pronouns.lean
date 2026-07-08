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
open Features.Register (Level)

-- ============================================================================
-- § 1: Strong Pronouns
-- ============================================================================

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
  { form := "er", person := some .third, number := some .singular }

/-- *sie* — 3sg feminine. -/
def sie_f : PersonalPronoun :=
  { form := "sie", person := some .third, number := some .singular }

/-- *es* — 3sg neuter. -/
def es : PersonalPronoun :=
  { form := "es", person := some .third, number := some .singular }

/-- *wir* — 1pl. -/
def wir : PersonalPronoun :=
  { form := "wir", person := some .first, number := some .plural }

/-- *ihr* — 2pl familiar. -/
def ihr : PersonalPronoun :=
  { form := "ihr", person := some .second, number := some .plural, register := .informal }

/-- *sie* — 3pl. -/
def sie_pl : PersonalPronoun :=
  { form := "sie", person := some .third, number := some .plural }

def allPronouns : List PersonalPronoun :=
  [ich, du, sie_polite, er, sie_f, es, wir, ihr, sie_pl]

-- ============================================================================
-- § 2: Verification Theorems
-- ============================================================================

/-- T/V distinction: *du* is informal, *Sie* is formal. -/
theorem tv_distinction :
    du.register = .informal ∧ sie_polite.register = .formal := ⟨rfl, rfl⟩

/-- SIE has 3rd person (plural) agreement features but 2nd person
    interpretable features. [adamson-zompi-2025] -/
theorem sie_polite_dual_person :
    sie_polite.person = some .third ∧
    sie_polite.referentialPerson = some .second := ⟨rfl, rfl⟩

/-- SIE uses 3pl, unlike Italian LEI (3sg) and Spanish USTED (3sg). -/
theorem sie_is_plural : sie_polite.number = some .plural := rfl

/-- All three persons are attested. -/
theorem has_all_persons :
    allPronouns.any (·.person == some .first) = true ∧
    allPronouns.any (·.person == some .second) = true ∧
    allPronouns.any (·.person == some .third) = true := ⟨rfl, rfl, rfl⟩

end German.Pronouns
