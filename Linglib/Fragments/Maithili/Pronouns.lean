/-
# Maithili Pronoun & Allocutive Fragment

Second-person pronouns and allocutive verbal morphology in Maithili (Indo-Aryan).
Maithili has a three-level honorific system (non-hon / hon / high-hon) realized
as verbal agreement morphemes on finite verbs. AA is Fin-based and freely
embeddable.

## References

- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Basic

namespace Fragments.Maithili.Pronouns


-- ============================================================================
-- Pronoun Entries
-- ============================================================================

/-- A Maithili pronoun entry with formality level. -/
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

/-- *ahã* — 2sg honorific. -/
def ahaN : PronounEntry :=
  { form := "ahã", person := some .second, number := some .sg, formality := 1 }

/-- *apne* — 2sg high-honorific. -/
def apne : PronounEntry :=
  { form := "apne", person := some .second, number := some .sg, formality := 2 }

def allPronouns : List PronounEntry := [toN, ahaN, apne]

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

/-- Non-honorific finite suffix. -/
def suffNH : AllocMarkerEntry :=
  { form := "-ah", formality := 0, gloss := "FIN.NH" }

/-- Honorific finite suffix. -/
def suffH : AllocMarkerEntry :=
  { form := "-thunh", formality := 1, gloss := "FIN.H" }

/-- High-honorific finite suffix. -/
def suffHH : AllocMarkerEntry :=
  { form := "-lnhi", formality := 2, gloss := "FIN.HH" }

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

end Fragments.Maithili.Pronouns
