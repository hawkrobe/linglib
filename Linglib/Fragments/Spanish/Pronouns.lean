import Linglib.Core.Lexical.Pronouns

/-!
# Spanish Pronoun Fragment
@cite{adamson-zompi-2025}

Personal pronouns (strong forms) for Spanish, including the polite
pronoun USTED.

## T/V distinction

Spanish has a T/V distinction:
- Singular: *tú* (familiar T) vs *usted* (formal V, 3sg agreement)
- Plural: *vosotros* (familiar, Peninsular) vs *ustedes* (formal / general)

## USTED and the PCC

Like Italian LEI, USTED triggers 3sg verbal agreement but is interpretably
2nd person. @cite{rezac-2011} observes PCC effects with USTED: the
accusative clitic *la* is grammatical in a 3>3 configuration if its
referent is 3rd person, but ungrammatical as polite USTED (§6.1, (43)).

USTED's forms are identical to the 3sg feminine series in some cases
(like LEI), though it also has the dedicated citation form *usted*.
Unlike Italian LEI, USTED can also be used in *laísta* varieties where
3rd person clitics for animates are *le* (syncretic with dative).
-/

namespace Fragments.Spanish.Pronouns

open Core.Pronouns
open Features.Register (Level)

-- ============================================================================
-- § 1: Strong Pronouns
-- ============================================================================

/-- *yo* — 1sg. -/
def yo : PronounEntry :=
  { form := "yo", person := some .first, number := some .sg }

/-- *tú* — 2sg familiar (T form). -/
def tu : PronounEntry :=
  { form := "tú", person := some .second, number := some .sg, register := .informal }

/-- *usted* — polite 2sg (V form, triggers 3sg agreement).
    Agreement person is 3rd, interpretable person is 2nd. Triggers PCC
    effects: *la* as USTED.ACC is banned in 3>USTED configurations
    (@cite{rezac-2011}, @cite{adamson-zompi-2025} §6.1).
    @cite{adamson-zompi-2025} -/
def usted : PronounEntry :=
  { form := "usted", person := some .third, number := some .sg, register := .formal,
    referentialPerson := some .second }

/-- *él* — 3sg masculine. -/
def el : PronounEntry :=
  { form := "él", person := some .third, number := some .sg }

/-- *ella* — 3sg feminine. -/
def ella : PronounEntry :=
  { form := "ella", person := some .third, number := some .sg }

/-- *nosotros* — 1pl. -/
def nosotros : PronounEntry :=
  { form := "nosotros", person := some .first, number := some .pl }

/-- *vosotros* — 2pl familiar (Peninsular). -/
def vosotros : PronounEntry :=
  { form := "vosotros", person := some .second, number := some .pl, register := .informal }

/-- *ustedes* — 2pl formal / general (triggers 3pl agreement). -/
def ustedes : PronounEntry :=
  { form := "ustedes", person := some .third, number := some .pl, register := .formal,
    referentialPerson := some .second }

/-- *ellos* — 3pl masculine. -/
def ellos : PronounEntry :=
  { form := "ellos", person := some .third, number := some .pl }

def allPronouns : List PronounEntry :=
  [yo, tu, usted, el, ella, nosotros, vosotros, ustedes, ellos]

-- ============================================================================
-- § 2: Verification Theorems
-- ============================================================================

/-- T/V distinction: *tú* is informal, *usted* is formal. -/
theorem tv_distinction :
    tu.register = .informal ∧ usted.register = .formal := ⟨rfl, rfl⟩

/-- USTED has 3rd person agreement features but 2nd person interpretable
    features. @cite{adamson-zompi-2025} -/
theorem usted_dual_person :
    usted.person = some .third ∧
    usted.referentialPerson = some .second := ⟨rfl, rfl⟩

/-- *ustedes* (2pl formal) also has dual person features. -/
theorem ustedes_dual_person :
    ustedes.person = some .third ∧
    ustedes.referentialPerson = some .second := ⟨rfl, rfl⟩

/-- All three persons are attested. -/
theorem has_all_persons :
    allPronouns.any (·.person == some .first) = true ∧
    allPronouns.any (·.person == some .second) = true ∧
    allPronouns.any (·.person == some .third) = true := ⟨rfl, rfl, rfl⟩

end Fragments.Spanish.Pronouns
