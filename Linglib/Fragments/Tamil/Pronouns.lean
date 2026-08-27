/-
# Tamil Pronoun & Allocutive Fragment

Personal pronouns and allocutive verbal morphology in Tamil (Dravidian).
Tamil has a two-level honorific system (non-hon / hon) realized as verbal
agreement suffixes. 1st person plural distinguishes inclusive (*naam*) vs
exclusive (*naangaL*). 3rd person distinguishes masculine (*avan*), feminine
(*avaL*), and honorific (*avar*). The allocutive marker *-ŋgæ* is the plural
suffix; it appears twice in root clauses and only below the complementizer
when embedded ([alok-bhalla-2026]).

-/

import Linglib.Syntax.Category.Pronoun.Basic

namespace Tamil.Pronouns

open Pronoun

-- ============================================================================
-- First Person
-- ============================================================================

/-- *naan* — 1sg. -/
def naan : PersonalPronoun :=
  { form := "naan", person := some .first, number := some .singular }

/-- *naam* — 1pl inclusive (speaker + addressee). -/
def naam : PersonalPronoun :=
  { form := "naam", person := some .firstInclusive, number := some .plural }

/-- *naangaL* — 1pl exclusive (speaker + others, not addressee). -/
def naangaL : PersonalPronoun :=
  { form := "naangaL", person := some .firstExclusive, number := some .plural }

-- ============================================================================
-- Second Person (two-level honorific)
-- ============================================================================

/-- *nii* — 2sg non-honorific. -/
def nii : PersonalPronoun :=
  { form := "nii", person := some .second, number := some .singular, register := .informal }

/-- *niingaL* — 2sg honorific (also 2pl). -/
def niingaL : PersonalPronoun :=
  { form := "niingaL", person := some .second, number := some .singular, register := .formal }

-- ============================================================================
-- Third Person
-- ============================================================================

/-- *avan* — 3sg masculine. -/
def avan : PersonalPronoun :=
  { form := "avan", person := some .third, number := some .singular }

/-- *avaL* — 3sg feminine. -/
def avaL : PersonalPronoun :=
  { form := "avaL", person := some .third, number := some .singular }

/-- *avar* — 3sg honorific. -/
def avar : PersonalPronoun :=
  { form := "avar", person := some .third, number := some .singular, register := .formal }

/-- *avarkaL* — 3pl (human). -/
def avarkaL : PersonalPronoun :=
  { form := "avarkaL", person := some .third, number := some .plural }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PersonalPronoun := [nii, niingaL]

def allPronouns : List PersonalPronoun :=
  [naan, naam, naangaL] ++ secondPersonPronouns ++ [avan, avaL, avar, avarkaL]

-- ============================================================================
-- Allocutive Marker ([alok-bhalla-2026] (7), Table 1; McFadden 2020)
-- ============================================================================

/-- *-ŋgæ* — politeness to the addressee. -/
def alloc : AllocutiveEntry := { form := "-ŋgæ", register := .formal, gloss := "ALLOC" }

def allAllocMarkers : List AllocutiveEntry := [alloc]

/-- The nominal plural suffix, homophonous with the allocutive marker. -/
def pluralSuffix : String := "-ŋgæ"

/-- Number marking on nominals (Table 1 of [alok-bhalla-2026], after McFadden
    2020): singular and plural forms. -/
def numberPairs : List (String × String) :=
  [("naan", "naan-ŋgæ"), ("nii", "nii-ŋgæ"), ("avan", "avan-ŋgæ"), ("poɳɳǔ", "poɳɳǔ-ŋgæ"),
   ("maram", "maram-ŋgæ")]

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

/-- Tamil has the inclusive/exclusive distinction in 1pl — carried on the
    person values themselves. -/
theorem has_incl_excl :
    allPronouns.any (·.person == some .firstInclusive) = true ∧
    allPronouns.any (·.person == some .firstExclusive) = true := ⟨rfl, rfl⟩

/-- 2nd person pronouns are all second person. -/
theorem second_person_all_2p :
    secondPersonPronouns.all (·.person == some .second) = true := rfl

/-- The T/V register distinction is present in 2nd person. -/
theorem tv_distinction :
    secondPersonPronouns.any (·.register == .informal) = true ∧
    secondPersonPronouns.any (·.register == .formal) = true := ⟨rfl, rfl⟩

/-- The allocutive marker is the plural suffix. -/
theorem alloc_eq_pluralSuffix : alloc.form = pluralSuffix := rfl

end Tamil.Pronouns
