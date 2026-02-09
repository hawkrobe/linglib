/-
# Hindi Pronoun & Allocutive Fragment

Second-person pronouns and allocutive verbal morphology in Hindi (Indo-Aryan).
Hindi has a three-level honorific system (non-hon *tuu* / hon *tum* / high-hon
*aap*) realized as imperative agreement suffixes. AA is Fin-based and freely
embeddable.

Note: This is separate from `Fragments.HindiUrdu.Particles` which covers
discourse particles shared between Hindi and Urdu.

## References

- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Basic

namespace Fragments.Hindi.Pronouns


-- ============================================================================
-- Pronoun Entries
-- ============================================================================

/-- A Hindi pronoun entry with formality level. -/
structure PronounEntry where
  form : String
  person : Option Person := none
  number : Option Number := none
  /-- 0 = non-hon, 1 = hon, 2 = high-hon -/
  formality : Nat := 0
  deriving Repr, BEq

/-- *tuu* — 2sg non-honorific (intimate/inferior). -/
def tuu : PronounEntry :=
  { form := "tuu", person := some .second, number := some .sg, formality := 0 }

/-- *tum* — 2sg honorific (neutral). -/
def tum : PronounEntry :=
  { form := "tum", person := some .second, number := some .sg, formality := 1 }

/-- *aap* — 2sg high-honorific (respectful). -/
def aap : PronounEntry :=
  { form := "aap", person := some .second, number := some .sg, formality := 2 }

def allPronouns : List PronounEntry := [tuu, tum, aap]

-- ============================================================================
-- Allocutive Markers (imperative agreement suffixes)
-- ============================================================================

/-- An allocutive marker entry: verbal suffix realizing AA. -/
structure AllocMarkerEntry where
  form : String
  /-- 0 = non-hon, 1 = hon, 2 = high-hon -/
  formality : Nat
  gloss : String
  deriving Repr, BEq

/-- *-aa* non-honorific imperative suffix (e.g., *jaa* "go!"). -/
def suffNH : AllocMarkerEntry :=
  { form := "-aa", formality := 0, gloss := "IMP.NH" }

/-- *-e* honorific imperative suffix (e.g., *jao* "go"). -/
def suffH : AllocMarkerEntry :=
  { form := "-e", formality := 1, gloss := "IMP.H" }

/-- *-iye* high-honorific imperative suffix (e.g., *jaaiye* "please go"). -/
def suffHH : AllocMarkerEntry :=
  { form := "-iye", formality := 2, gloss := "IMP.HH" }

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

end Fragments.Hindi.Pronouns
