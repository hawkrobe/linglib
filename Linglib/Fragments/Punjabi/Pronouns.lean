/-
# Punjabi Pronoun Fragment

Personal pronouns of Punjabi (Indo-Aryan): a two-level honorific system for
2nd person (non-hon *tũ* / hon *tusii*); 3rd person uses demonstrative forms
(*uh* for both sg and pl). Punjabi has allocutive agreement with third-person
subjects only ([alok-bhalla-2026], after Kaur 2020); its marker forms are not
recorded here.

-/

import Linglib.Syntax.Category.Pronoun.Basic

namespace Punjabi.Pronouns

open Pronoun

-- ============================================================================
-- First Person
-- ============================================================================

/-- *maiṃ* — 1sg. -/
def maiN : PersonalPronoun :=
  { form := "maiṃ", person := some .first, number := some .singular }

/-- *asiiṃ* — 1pl. -/
def asiiN : PersonalPronoun :=
  { form := "asiiṃ", person := some .first, number := some .plural }

-- ============================================================================
-- Second Person (two-level honorific)
-- ============================================================================

/-- *tũ* — 2sg non-honorific. -/
def tuN : PersonalPronoun :=
  { form := "tũ", person := some .second, number := some .singular, register := .informal }

/-- *tusii* — 2sg honorific (also 2pl). -/
def tusii : PersonalPronoun :=
  { form := "tusii", person := some .second, number := some .singular, register := .formal }

-- ============================================================================
-- Third Person (demonstrative-based)
-- ============================================================================

/-- *uh* — 3sg (distal demonstrative). -/
def uh_sg : PersonalPronoun :=
  { form := "uh", person := some .third, number := some .singular }

/-- *uh* — 3pl (same form as 3sg in standard Punjabi). -/
def uh_pl : PersonalPronoun :=
  { form := "uh", person := some .third, number := some .plural }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PersonalPronoun := [tuN, tusii]

def allPronouns : List PersonalPronoun :=
  [maiN, asiiN] ++ secondPersonPronouns ++ [uh_sg, uh_pl]

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

/-- The T/V register distinction is present in 2nd person. -/
theorem tv_distinction :
    secondPersonPronouns.any (·.register == .informal) = true ∧
    secondPersonPronouns.any (·.register == .formal) = true := ⟨rfl, rfl⟩

/-- 3sg and 3pl share the same form (demonstrative-based). -/
theorem third_person_homophony :
    uh_sg.form = uh_pl.form := rfl

end Punjabi.Pronouns
