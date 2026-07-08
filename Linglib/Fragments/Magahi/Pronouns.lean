/-
# Magahi Pronoun & Allocutive Fragment

Personal pronouns and allocutive verbal morphology in Magahi (Indo-Aryan).
Magahi has a three-level honorific system for 2nd person (non-hon / hon /
high-hon) realized as verbal agreement morphemes. 3rd person uses demonstrative
forms (*i* proximal / *ũ* distal). AA is Fin-based and freely embeddable.

-/

import Linglib.Syntax.Category.Pronoun.Basic

namespace Magahi.Pronouns

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

/-- *tũ* — 2sg honorific. -/
def tuN : PersonalPronoun :=
  { form := "tũ", person := some .second, number := some .singular, register := .neutral }

/-- *apne* — 2sg high-honorific. -/
def apne : PersonalPronoun :=
  { form := "apne", person := some .second, number := some .singular, register := .formal }

-- ============================================================================
-- Third Person (demonstrative-based)
-- ============================================================================

/-- *i* — 3sg proximal. -/
def i_prox : PersonalPronoun :=
  { form := "i", person := some .third, number := some .singular }

/-- *ũ* — 3sg distal. -/
def uN : PersonalPronoun :=
  { form := "ũ", person := some .third, number := some .singular }

/-- *ũ sab* — 3pl distal. -/
def uNSab : PersonalPronoun :=
  { form := "ũ sab", person := some .third, number := some .plural }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PersonalPronoun := [toN, tuN, apne]

def allPronouns : List PersonalPronoun :=
  [hum, humSab] ++ secondPersonPronouns ++ [i_prox, uN, uNSab]

-- ============================================================================
-- Allocutive Markers (verbal agreement suffixes)
-- ============================================================================

/-- *-l* non-honorific past suffix. -/
def suffNH : AllocutiveEntry :=
  { form := "-l", register := .informal, gloss := "PST.NH" }

/-- *-lah* honorific past suffix. -/
def suffH : AllocutiveEntry :=
  { form := "-lah", register := .neutral, gloss := "PST.H" }

/-- *-lnhi* high-honorific past suffix. -/
def suffHH : AllocutiveEntry :=
  { form := "-lnhi", register := .formal, gloss := "PST.HH" }

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

end Magahi.Pronouns
