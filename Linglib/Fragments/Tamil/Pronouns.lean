/-
# Tamil Pronoun & Allocutive Fragment

Second-person pronouns and allocutive verbal morphology in Tamil (Dravidian).
Tamil has a two-level honorific system (non-hon / hon) realized as verbal
agreement suffixes. AA is Fin-based with limited embeddability (under
speech/thought predicates).

## References

- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Basic

namespace Fragments.Tamil.Pronouns


-- ============================================================================
-- Pronoun Entries
-- ============================================================================

/-- A Tamil pronoun entry with formality level. -/
structure PronounEntry where
  form : String
  person : Option Person := none
  number : Option Number := none
  /-- 0 = non-hon, 1 = hon -/
  formality : Nat := 0
  deriving Repr, BEq

/-- *nii* — 2sg non-honorific. -/
def nii : PronounEntry :=
  { form := "nii", person := some .second, number := some .sg, formality := 0 }

/-- *niingaL* — 2sg honorific (also 2pl). -/
def niingaL : PronounEntry :=
  { form := "niingaL", person := some .second, number := some .sg, formality := 1 }

def allPronouns : List PronounEntry := [nii, niingaL]

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

/-- *-aay* non-honorific suffix. -/
def suffNH : AllocMarkerEntry :=
  { form := "-aay", formality := 0, gloss := "2sg.NH" }

/-- *-iingaL* honorific suffix. -/
def suffH : AllocMarkerEntry :=
  { form := "-iingaL", formality := 1, gloss := "2sg.H" }

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

end Fragments.Tamil.Pronouns
