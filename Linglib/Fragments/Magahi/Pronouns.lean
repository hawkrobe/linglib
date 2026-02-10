/-
# Magahi Pronoun & Allocutive Fragment

Personal pronouns and allocutive verbal morphology in Magahi (Indo-Aryan).
Magahi has a three-level honorific system for 2nd person (non-hon / hon /
high-hon) realized as verbal agreement morphemes. 3rd person uses demonstrative
forms (*i* proximal / *ũ* distal). AA is Fin-based and freely embeddable.

## References

- Alok, D. (2020). The syntax and semantics of allocutive agreement in Magahi.
  PhD dissertation, Rutgers University.
- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Pronouns

namespace Fragments.Magahi.Pronouns

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
  { form := "tõ", person := some .second, number := some .sg, formality := 0 }

/-- *tũ* — 2sg honorific. -/
def tuN : PronounEntry :=
  { form := "tũ", person := some .second, number := some .sg, formality := 1 }

/-- *apne* — 2sg high-honorific. -/
def apne : PronounEntry :=
  { form := "apne", person := some .second, number := some .sg, formality := 2 }

-- ============================================================================
-- Third Person (demonstrative-based)
-- ============================================================================

/-- *i* — 3sg proximal. -/
def i_prox : PronounEntry :=
  { form := "i", person := some .third, number := some .sg }

/-- *ũ* — 3sg distal. -/
def uN : PronounEntry :=
  { form := "ũ", person := some .third, number := some .sg }

/-- *ũ sab* — 3pl distal. -/
def uNSab : PronounEntry :=
  { form := "ũ sab", person := some .third, number := some .pl }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PronounEntry := [toN, tuN, apne]

def allPronouns : List PronounEntry :=
  [hum, humSab] ++ secondPersonPronouns ++ [i_prox, uN, uNSab]

-- ============================================================================
-- Allocutive Markers (verbal agreement suffixes)
-- ============================================================================

/-- *-l* non-honorific past suffix (Alok 2020). -/
def suffNH : AllocutiveEntry :=
  { form := "-l", formality := 0, gloss := "PST.NH" }

/-- *-lah* honorific past suffix. -/
def suffH : AllocutiveEntry :=
  { form := "-lah", formality := 1, gloss := "PST.H" }

/-- *-lnhi* high-honorific past suffix. -/
def suffHH : AllocutiveEntry :=
  { form := "-lnhi", formality := 2, gloss := "PST.HH" }

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

/-- Three-level formality distinction in 2nd person. -/
theorem three_levels :
    secondPersonPronouns.map (·.formality) = [0, 1, 2] := rfl

/-- Allocutive markers have three levels matching 2nd person pronouns. -/
theorem markers_three_levels :
    allAllocMarkers.map (·.formality) = [0, 1, 2] := rfl

end Fragments.Magahi.Pronouns
