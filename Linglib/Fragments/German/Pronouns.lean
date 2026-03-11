import Linglib.Core.Lexical.Pronouns

/-!
# German Pronoun Fragment
@cite{adamson-zompi-2025}

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
clusters, @cite{anagnostopoulou-2008}), patterning with 2nd person ((47)–(48)).
In contrast, SIE does NOT trigger the exponence-based person hierarchy effect
in assumed-identity copular constructions (@cite{keine-et-al-2019},
@cite{coon-keine-2021}), patterning with 3rd person ((52)–(53)).
-/

namespace Fragments.German.Pronouns

open Core.Pronouns
open Core.Register (Level)

-- ============================================================================
-- § 1: Strong Pronouns
-- ============================================================================

/-- *ich* — 1sg. -/
def ich : PronounEntry :=
  { form := "ich", person := some .first, number := some .sg }

/-- *du* — 2sg familiar (T form). -/
def du : PronounEntry :=
  { form := "du", person := some .second, number := some .sg, register := .informal }

/-- *Sie* — polite 2nd person (V form, triggers 3pl agreement).
    Unlike Italian LEI (3sg.f) and Spanish USTED (3sg), German SIE uses
    the 3pl series. Agreement person is 3rd (plural), interpretable person
    is 2nd. Can refer to singular or plural addressees.
    @cite{adamson-zompi-2025} -/
def sie_polite : PronounEntry :=
  { form := "Sie", person := some .third, number := some .pl, register := .formal,
    referentialPerson := some .second }

/-- *er* — 3sg masculine. -/
def er : PronounEntry :=
  { form := "er", person := some .third, number := some .sg }

/-- *sie* — 3sg feminine. -/
def sie_f : PronounEntry :=
  { form := "sie", person := some .third, number := some .sg }

/-- *es* — 3sg neuter. -/
def es : PronounEntry :=
  { form := "es", person := some .third, number := some .sg }

/-- *wir* — 1pl. -/
def wir : PronounEntry :=
  { form := "wir", person := some .first, number := some .pl }

/-- *ihr* — 2pl familiar. -/
def ihr : PronounEntry :=
  { form := "ihr", person := some .second, number := some .pl, register := .informal }

/-- *sie* — 3pl. -/
def sie_pl : PronounEntry :=
  { form := "sie", person := some .third, number := some .pl }

def allPronouns : List PronounEntry :=
  [ich, du, sie_polite, er, sie_f, es, wir, ihr, sie_pl]

-- ============================================================================
-- § 2: Verification Theorems
-- ============================================================================

/-- T/V distinction: *du* is informal, *Sie* is formal. -/
theorem tv_distinction :
    du.register = .informal ∧ sie_polite.register = .formal := ⟨rfl, rfl⟩

/-- SIE has 3rd person (plural) agreement features but 2nd person
    interpretable features. @cite{adamson-zompi-2025} -/
theorem sie_polite_dual_person :
    sie_polite.person = some .third ∧
    sie_polite.referentialPerson = some .second := ⟨rfl, rfl⟩

/-- SIE uses 3pl, unlike Italian LEI (3sg) and Spanish USTED (3sg). -/
theorem sie_is_plural : sie_polite.number = some .pl := rfl

/-- All three persons are attested. -/
theorem has_all_persons :
    allPronouns.any (·.person == some .first) = true ∧
    allPronouns.any (·.person == some .second) = true ∧
    allPronouns.any (·.person == some .third) = true := ⟨rfl, rfl, rfl⟩

end Fragments.German.Pronouns
