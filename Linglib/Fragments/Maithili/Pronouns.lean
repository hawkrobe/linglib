/-
# Maithili Pronoun & Allocutive Fragment

Personal pronouns and allocutive verbal morphology in Maithili (Indo-Aryan).
Maithili has a three-level honorific system for 2nd person (non-hon / hon /
high-hon) realized as verbal agreement morphemes on finite verbs. 3rd person
also distinguishes honorific levels (*ũ* non-hon / *o* hon). AA is Fin-based
and freely embeddable.

## References

- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Pronouns

namespace Fragments.Maithili.Pronouns

open Core.Pronouns

-- ============================================================================
-- First Person
-- ============================================================================

/-- *hum* — 1sg. -/
def hum : PronounEntry :=
  { form := "hum", person := some .first, number := some .sg }

/-- *hum sab* — 1pl. -/
def humSab : PronounEntry :=
  { form := "hum sab", person := some .first, number := some .pl }

-- ============================================================================
-- Second Person (three-level honorific)
-- ============================================================================

/-- *tõ* — 2sg non-honorific. -/
def toN : PronounEntry :=
  { form := "tõ", person := some .second, number := some .sg, register := .informal }

/-- *ahã* — 2sg honorific. -/
def ahaN : PronounEntry :=
  { form := "ahã", person := some .second, number := some .sg, register := .neutral }

/-- *apne* — 2sg high-honorific. -/
def apne : PronounEntry :=
  { form := "apne", person := some .second, number := some .sg, register := .formal }

-- ============================================================================
-- Third Person (honorific-sensitive)
-- ============================================================================

/-- *ũ* — 3sg non-honorific (distal). -/
def uN : PronounEntry :=
  { form := "ũ", person := some .third, number := some .sg, register := .informal }

/-- *o* — 3sg honorific. -/
def o : PronounEntry :=
  { form := "o", person := some .third, number := some .sg, register := .neutral }

/-- *ũ sab* — 3pl. -/
def uNSab : PronounEntry :=
  { form := "ũ sab", person := some .third, number := some .pl }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PronounEntry := [toN, ahaN, apne]

def allPronouns : List PronounEntry :=
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
    allPronouns.any (·.number == some .sg) = true ∧
    allPronouns.any (·.number == some .pl) = true := ⟨rfl, rfl⟩

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

end Fragments.Maithili.Pronouns
