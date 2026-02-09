/-
# Magahi Pronoun & Allocutive Fragment

Second-person pronouns and allocutive verbal morphology in Magahi (Indo-Aryan).
Magahi has a three-level honorific system (non-hon / hon / high-hon) realized
as verbal agreement morphemes. AA is Fin-based and freely embeddable.

## References

- Alok, D. (2020). The syntax and semantics of allocutive agreement in Magahi.
  PhD dissertation, Rutgers University.
- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Basic

namespace Fragments.Magahi.Pronouns


-- ============================================================================
-- Pronoun Entries
-- ============================================================================

/-- A Magahi pronoun entry with formality level. -/
structure PronounEntry where
  form : String
  person : Option Person := none
  number : Option Number := none
  /-- 0 = non-hon, 1 = hon, 2 = high-hon -/
  formality : Nat := 0
  deriving Repr, BEq

/-- *tõ* — 2sg non-honorific. -/
def toN : PronounEntry :=
  { form := "tõ", person := some .second, number := some .sg, formality := 0 }

/-- *tũ* — 2sg honorific. -/
def tuN : PronounEntry :=
  { form := "tũ", person := some .second, number := some .sg, formality := 1 }

/-- *apne* — 2sg high-honorific. -/
def apne : PronounEntry :=
  { form := "apne", person := some .second, number := some .sg, formality := 2 }

def allPronouns : List PronounEntry := [toN, tuN, apne]

-- ============================================================================
-- Allocutive Markers (verbal agreement suffixes)
-- ============================================================================

/-- An allocutive marker entry: verbal suffix realizing AA. -/
structure AllocMarkerEntry where
  form : String
  /-- 0 = non-hon, 1 = hon, 2 = high-hon -/
  formality : Nat
  gloss : String
  deriving Repr, BEq

/-- *-l* non-honorific past suffix (Alok 2020). -/
def suffNH : AllocMarkerEntry :=
  { form := "-l", formality := 0, gloss := "PST.NH" }

/-- *-lah* honorific past suffix. -/
def suffH : AllocMarkerEntry :=
  { form := "-lah", formality := 1, gloss := "PST.H" }

/-- *-lnhi* high-honorific past suffix. -/
def suffHH : AllocMarkerEntry :=
  { form := "-lnhi", formality := 2, gloss := "PST.HH" }

def allAllocMarkers : List AllocMarkerEntry := [suffNH, suffH, suffHH]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All pronouns are 2nd person. -/
theorem all_second_person :
    allPronouns.all (·.person == some .second) = true := rfl

/-- Three-level formality distinction is present. -/
theorem three_levels :
    allPronouns.map (·.formality) = [0, 1, 2] := rfl

/-- Allocutive markers have three levels matching pronouns. -/
theorem markers_three_levels :
    allAllocMarkers.map (·.formality) = [0, 1, 2] := rfl

end Fragments.Magahi.Pronouns
