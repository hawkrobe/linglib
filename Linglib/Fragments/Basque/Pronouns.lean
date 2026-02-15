/-
# Basque Pronoun & Allocutive Fragment

Personal pronouns and allocutive verbal morphology in Souletian Basque.
Basque has a T/V distinction (*hi* familiar vs *zu* formal) and SA-based
allocutive verbal suffixes that are restricted to root clauses. 2nd person
plural *zuek* is distinct from formal singular *zu*.

## References

- Oyharçabal, B. (1993). Verb agreement with non-arguments: On allocutive
  agreement. In J. I. Hualde & J. Ortiz de Urbina (eds.), Generative Studies
  in Basque Linguistics.
- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Pronouns

namespace Fragments.Basque.Pronouns

open Core.Pronouns
open Core.Register (Level)

-- ============================================================================
-- First Person
-- ============================================================================

/-- *ni* — 1sg. -/
def ni : PronounEntry :=
  { form := "ni", person := some .first, number := some .sg }

/-- *gu* — 1pl. -/
def gu : PronounEntry :=
  { form := "gu", person := some .first, number := some .pl }

-- ============================================================================
-- Second Person (T/V)
-- ============================================================================

/-- *hi* — 2sg familiar (T form). -/
def hi : PronounEntry :=
  { form := "hi", person := some .second, number := some .sg, register := .informal }

/-- *zu* — 2sg formal (V form). -/
def zu : PronounEntry :=
  { form := "zu", person := some .second, number := some .sg, register := .formal }

/-- *zuek* — 2pl. -/
def zuek : PronounEntry :=
  { form := "zuek", person := some .second, number := some .pl }

-- ============================================================================
-- Third Person
-- ============================================================================

/-- *hura* — 3sg. -/
def hura : PronounEntry :=
  { form := "hura", person := some .third, number := some .sg }

/-- *haiek* — 3pl. -/
def haiek : PronounEntry :=
  { form := "haiek", person := some .third, number := some .pl }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PronounEntry := [hi, zu]

def allPronouns : List PronounEntry :=
  [ni, gu] ++ secondPersonPronouns ++ [zuek, hura, haiek]

-- ============================================================================
-- Allocutive Markers (verbal suffixes)
-- ============================================================================

/-- *-n* familiar allocutive suffix (Oyharçabal 1993). -/
def allocFamiliar : AllocutiveEntry :=
  { form := "-n", register := .informal, gloss := "2sg.familiar.alloc" }

/-- *-zu* formal allocutive suffix. -/
def allocFormal : AllocutiveEntry :=
  { form := "-zu", register := .formal, gloss := "2sg.formal.alloc" }

def allAllocMarkers : List AllocutiveEntry := [allocFamiliar, allocFormal]

-- ============================================================================
-- Verb Agreement Examples
-- ============================================================================

/-- A verb form showing allocutive inflection. -/
structure VerbForm where
  form : String
  gloss : String
  register : Level
  deriving Repr, BEq

/-- *duk* — "you have" (familiar). -/
def duk : VerbForm := { form := "duk", gloss := "have.2sg.fam", register := .informal }

/-- *duzu* — "you have" (formal). -/
def duzu : VerbForm := { form := "duzu", gloss := "have.2sg.for", register := .formal }

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

/-- The T/V register distinction is present in 2nd person. -/
theorem tv_distinction :
    secondPersonPronouns.any (·.register == .informal) = true ∧
    secondPersonPronouns.any (·.register == .formal) = true := ⟨rfl, rfl⟩

/-- Verb forms have matching register levels with 2nd person pronouns. -/
theorem verb_register_matches_pronouns :
    duk.register = hi.register ∧ duzu.register = zu.register := ⟨rfl, rfl⟩

end Fragments.Basque.Pronouns
