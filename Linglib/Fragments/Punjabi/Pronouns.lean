/-
# Punjabi Pronoun & Allocutive Fragment

Second-person pronouns and allocutive verbal morphology in Punjabi (Indo-Aryan).
Punjabi has a two-level honorific system (non-hon *tũ* / hon *tusii*) realized
as verbal agreement suffixes. AA is Fin-based with limited embeddability.

## References

- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Basic

namespace Fragments.Punjabi.Pronouns


-- ============================================================================
-- Pronoun Entries
-- ============================================================================

/-- A Punjabi pronoun entry with formality level. -/
structure PronounEntry where
  form : String
  person : Option Person := none
  number : Option Number := none
  /-- 0 = non-hon, 1 = hon -/
  formality : Nat := 0
  deriving Repr, BEq

/-- *tũ* — 2sg non-honorific. -/
def tuN : PronounEntry :=
  { form := "tũ", person := some .second, number := some .sg, formality := 0 }

/-- *tusii* — 2sg honorific (also 2pl). -/
def tusii : PronounEntry :=
  { form := "tusii", person := some .second, number := some .sg, formality := 1 }

def allPronouns : List PronounEntry := [tuN, tusii]

-- ============================================================================
-- Allocutive Markers (verbal agreement suffixes)
-- ============================================================================

/-- An allocutive marker entry: verbal suffix realizing AA. -/
structure AllocMarkerEntry where
  form : String
  /-- 0 = non-hon, 1 = hon -/
  formality : Nat
  gloss : String
  deriving Repr, BEq

/-- Non-honorific agreement suffix. -/
def suffNH : AllocMarkerEntry :=
  { form := "-ẽ", formality := 0, gloss := "AGR.NH" }

/-- Honorific agreement suffix. -/
def suffH : AllocMarkerEntry :=
  { form := "-o", formality := 1, gloss := "AGR.H" }

def allAllocMarkers : List AllocMarkerEntry := [suffNH, suffH]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All pronouns are 2nd person. -/
theorem all_second_person :
    allPronouns.all (·.person == some .second) = true := rfl

/-- The T/V formality distinction is present. -/
theorem tv_distinction :
    allPronouns.any (·.formality == 0) = true ∧
    allPronouns.any (·.formality == 1) = true := ⟨rfl, rfl⟩

/-- Allocutive markers match pronoun formality levels. -/
theorem markers_match_pronouns :
    allAllocMarkers.map (·.formality) = allPronouns.map (·.formality) := rfl

end Fragments.Punjabi.Pronouns
