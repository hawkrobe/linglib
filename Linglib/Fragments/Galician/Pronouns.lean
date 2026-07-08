/-
# Galician Pronoun & Allocutive Fragment

Personal pronouns and allocutive clitic in Galician (Romance).
Galician has a T/V distinction (*ti* familiar vs *vostede* formal) and a
familiar dative clitic *che* that attaches to the verb for allocutive marking.
2nd person plural distinguishes familiar *vós* from formal *vostedes*.
3rd person distinguishes masculine and feminine in both singular and plural.
AA is Fin-based and freely embeddable.

-/

import Linglib.Syntax.Category.Pronoun.Basic

namespace Galician.Pronouns

open Pronoun
open Features.Register (Level)

-- ============================================================================
-- First Person
-- ============================================================================

/-- *eu* — 1sg. -/
def eu : PersonalPronoun :=
  { form := "eu", person := some .first, number := some .singular }

/-- *nós* — 1pl. -/
def nos : PersonalPronoun :=
  { form := "nós", person := some .first, number := some .plural }

-- ============================================================================
-- Second Person (T/V, sg and pl)
-- ============================================================================

/-- *ti* — 2sg familiar (T form). -/
def ti : PersonalPronoun :=
  { form := "ti", person := some .second, number := some .singular, register := .informal }

/-- *vostede* — 2sg formal (V form). -/
def vostede : PersonalPronoun :=
  { form := "vostede", person := some .second, number := some .singular, register := .formal }

/-- *vós* — 2pl familiar. -/
def vos_pl : PersonalPronoun :=
  { form := "vós", person := some .second, number := some .plural, register := .informal }

/-- *vostedes* — 2pl formal. -/
def vostedes : PersonalPronoun :=
  { form := "vostedes", person := some .second, number := some .plural, register := .formal }

-- ============================================================================
-- Third Person
-- ============================================================================

/-- *el* — 3sg masculine. -/
def el : PersonalPronoun :=
  { form := "el", person := some .third, number := some .singular }

/-- *ela* — 3sg feminine. -/
def ela : PersonalPronoun :=
  { form := "ela", person := some .third, number := some .singular }

/-- *eles* — 3pl masculine. -/
def eles : PersonalPronoun :=
  { form := "eles", person := some .third, number := some .plural }

/-- *elas* — 3pl feminine. -/
def elas : PersonalPronoun :=
  { form := "elas", person := some .third, number := some .plural }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PersonalPronoun := [ti, vostede]

def allPronouns : List PersonalPronoun :=
  [eu, nos] ++ secondPersonPronouns ++ [vos_pl, vostedes, el, ela, eles, elas]

-- ============================================================================
-- Allocutive Clitic
-- ============================================================================

/-- *che* — familiar dative clitic (2sg ethical dative). -/
def che : AllocutiveEntry :=
  { form := "che", register := .informal, gloss := "2sg.DAT.fam" }

def allAllocClitics : List AllocutiveEntry := [che]

-- ============================================================================
-- Verb Agreement Examples
-- ============================================================================

/-- A verb form with optional allocutive clitic. -/
structure VerbForm where
  form : String
  gloss : String
  register : Level
  deriving Repr, BEq

/-- *vas* — "you go" (familiar, can host *che*). -/
def vas : VerbForm := { form := "vas", gloss := "go.2sg.fam", register := .informal }

-- ============================================================================
-- Verification
-- ============================================================================

/-- All three persons are attested. -/
theorem has_all_persons :
    allPronouns.any (·.person == some .first) = true ∧
    allPronouns.any (·.person == some .second) = true ∧
    allPronouns.any (·.person == some .third) = true := ⟨rfl, rfl, rfl⟩

/-- Both singular and plural are attested. -/
theorem has_both_numbers :
    allPronouns.any (·.number == some .singular) = true ∧
    allPronouns.any (·.number == some .plural) = true := ⟨rfl, rfl⟩

/-- 2nd person pronouns are all second person. -/
theorem second_person_all_2p :
    secondPersonPronouns.all (·.person == some .second) = true := rfl

/-- The T/V register distinction is present in 2nd person. -/
theorem tv_distinction :
    secondPersonPronouns.any (·.register == .informal) = true ∧
    secondPersonPronouns.any (·.register == .formal) = true := ⟨rfl, rfl⟩

/-- The allocutive clitic *che* is informal-level. -/
theorem che_is_informal : che.register = .informal := rfl

/-- 2pl preserves the T/V distinction (vós fam / vostedes form). -/
theorem plural_tv :
    vos_pl.register = .informal ∧ vostedes.register = .formal := ⟨rfl, rfl⟩

end Galician.Pronouns
