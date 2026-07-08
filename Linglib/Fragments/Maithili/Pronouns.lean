/-
# Maithili Pronoun & Allocutive Fragment

Personal pronouns and allocutive verbal morphology in Maithili (Indo-Aryan).
Maithili has a three-level honorific system for 2nd person (non-hon / hon /
high-hon) realized as verbal agreement morphemes on finite verbs. 3rd person
also distinguishes honorific levels (*ũ* non-hon / *o* hon). AA is Fin-based
and freely embeddable.

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
-- Allocutive Markers (verbal agreement suffixes)
-- ============================================================================

/-- Non-honorific finite suffix. -/
def suffNH : AllocutiveEntry :=
  { form := "-ah", register := .informal, gloss := "FIN.NH" }

/-- Honorific finite suffix. -/
def suffH : AllocutiveEntry :=
  { form := "-thunh", register := .neutral, gloss := "FIN.H" }

/-- High-honorific finite suffix. -/
def suffHH : AllocutiveEntry :=
  { form := "-lnhi", register := .formal, gloss := "FIN.HH" }

def allAllocMarkers : List AllocutiveEntry := [suffNH, suffH, suffHH]

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

/-- Allocutive markers have three levels matching 2nd person pronouns. -/
theorem markers_three_levels :
    allAllocMarkers.map (·.register) = [.informal, .neutral, .formal] := rfl

/-- 3rd person also has a register distinction. -/
theorem third_person_honorific :
    uN.register = .informal ∧ o.register = .neutral := ⟨rfl, rfl⟩

end Maithili.Pronouns
