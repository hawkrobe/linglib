/-
# Basque Pronoun & Allocutive Fragment

Second-person pronouns and allocutive verbal morphology in Souletian Basque.
Basque has a T/V distinction (*hi* familiar vs *zu* formal) and SA-based
allocutive verbal suffixes that are restricted to root clauses.

## References

- Oyharçabal, B. (1993). Verb agreement with non-arguments: On allocutive
  agreement. In J. I. Hualde & J. Ortiz de Urbina (eds.), Generative Studies
  in Basque Linguistics.
- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Basic

namespace Fragments.Basque.Pronouns


-- ============================================================================
-- Pronoun Entries
-- ============================================================================

/-- A Basque pronoun entry with formality level. -/
structure PronounEntry where
  form : String
  person : Option Person := none
  number : Option Number := none
  /-- 0 = plain/familiar, 1 = polite/formal -/
  formality : Nat := 0
  deriving Repr, BEq

/-- *hi* — 2sg familiar (T form). -/
def hi : PronounEntry :=
  { form := "hi", person := some .second, number := some .sg, formality := 0 }

/-- *zu* — 2sg formal (V form). -/
def zu : PronounEntry :=
  { form := "zu", person := some .second, number := some .sg, formality := 1 }

def allPronouns : List PronounEntry := [hi, zu]

-- ============================================================================
-- Allocutive Markers (verbal suffixes)
-- ============================================================================

/-- An allocutive marker entry: verbal suffix realizing AA. -/
structure AllocMarkerEntry where
  form : String
  /-- 0 = familiar, 1 = formal -/
  formality : Nat
  /-- Description of the morphosyntactic realization -/
  gloss : String
  deriving Repr, BEq

/-- *-n* familiar allocutive suffix (Oyharçabal 1993). -/
def allocFamiliar : AllocMarkerEntry :=
  { form := "-n", formality := 0, gloss := "2sg.familiar.alloc" }

/-- *-zu* formal allocutive suffix. -/
def allocFormal : AllocMarkerEntry :=
  { form := "-zu", formality := 1, gloss := "2sg.formal.alloc" }

def allAllocMarkers : List AllocMarkerEntry := [allocFamiliar, allocFormal]

-- ============================================================================
-- Verb Agreement Examples
-- ============================================================================

/-- A verb form showing allocutive inflection. -/
structure VerbForm where
  form : String
  gloss : String
  formality : Nat
  deriving Repr, BEq

/-- *duk* — "you have" (familiar). -/
def duk : VerbForm := { form := "duk", gloss := "have.2sg.fam", formality := 0 }

/-- *duzu* — "you have" (formal). -/
def duzu : VerbForm := { form := "duzu", gloss := "have.2sg.for", formality := 1 }

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

/-- Verb forms have matching formality levels with pronouns. -/
theorem verb_formality_matches_pronouns :
    duk.formality = hi.formality ∧ duzu.formality = zu.formality := ⟨rfl, rfl⟩

end Fragments.Basque.Pronouns
