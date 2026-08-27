/-
# Maithili Pronoun Fragment

Personal pronouns of Maithili (Indo-Aryan): a three-level honorific system for
2nd person (non-hon / hon / high-hon); 3rd person also distinguishes honorific
levels (*ũ* non-hon / *o* hon). Maithili has allocutive agreement, blocked with
a second-person subject and incompatible with object agreement
([alok-bhalla-2026], after Kumari 2022); its marker forms are not recorded
here.

-/

import Linglib.Syntax.Category.Pronoun.Basic

namespace Maithili.Pronouns

open Pronoun

-- ============================================================================
-- First Person
-- ============================================================================

/-- *hum* — 1sg. -/
def hum : PersonalPronoun :=
  { form := "hum", person := some .first, number := some .singular }

/-- *hum sab* — 1pl. -/
def humSab : PersonalPronoun :=
  { form := "hum sab", person := some .first, number := some .plural }

-- ============================================================================
-- Second Person (three-level honorific)
-- ============================================================================

/-- *tõ* — 2sg non-honorific. -/
def toN : PersonalPronoun :=
  { form := "tõ", person := some .second, number := some .singular, register := .informal }

/-- *ahã* — 2sg honorific. -/
def ahaN : PersonalPronoun :=
  { form := "ahã", person := some .second, number := some .singular, register := .neutral }

/-- *apne* — 2sg high-honorific. -/
def apne : PersonalPronoun :=
  { form := "apne", person := some .second, number := some .singular, register := .formal }

-- ============================================================================
-- Third Person (honorific-sensitive)
-- ============================================================================

/-- *ũ* — 3sg non-honorific (distal). -/
def uN : PersonalPronoun :=
  { form := "ũ", person := some .third, number := some .singular, register := .informal }

/-- *o* — 3sg honorific. -/
def o : PersonalPronoun :=
  { form := "o", person := some .third, number := some .singular, register := .neutral }

/-- *ũ sab* — 3pl. -/
def uNSab : PersonalPronoun :=
  { form := "ũ sab", person := some .third, number := some .plural }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PersonalPronoun := [toN, ahaN, apne]

def allPronouns : List PersonalPronoun :=
  [hum, humSab] ++ secondPersonPronouns ++ [uN, o, uNSab]

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

/-- Three-level register distinction in 2nd person. -/
theorem three_levels :
    secondPersonPronouns.map (·.register) = [.informal, .neutral, .formal] := rfl

/-- 3rd person also has a register distinction. -/
theorem third_person_honorific :
    uN.register = .informal ∧ o.register = .neutral := ⟨rfl, rfl⟩

end Maithili.Pronouns
