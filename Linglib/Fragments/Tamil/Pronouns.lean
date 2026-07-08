/-
# Tamil Pronoun & Allocutive Fragment

Personal pronouns and allocutive verbal morphology in Tamil (Dravidian).
Tamil has a two-level honorific system (non-hon / hon) realized as verbal
agreement suffixes. 1st person plural distinguishes inclusive (*naam*) vs
exclusive (*naangaL*). 3rd person distinguishes masculine (*avan*), feminine
(*avaL*), and honorific (*avar*). AA is Fin-based with limited embeddability
(under speech/thought predicates).

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
-- Allocutive Markers (verbal agreement suffixes)
-- ============================================================================

/-- *-aay* non-honorific suffix. -/
def suffNH : AllocutiveEntry :=
  { form := "-aay", register := .informal, gloss := "2sg.NH" }

/-- *-iingaL* honorific suffix. -/
def suffH : AllocutiveEntry :=
  { form := "-iingaL", register := .formal, gloss := "2sg.H" }

def allAllocMarkers : List AllocutiveEntry := [suffNH, suffH]

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

/-- Allocutive markers match 2nd person pronoun register levels. -/
theorem markers_match_2p :
    allAllocMarkers.map (·.register) = secondPersonPronouns.map (·.register) := rfl

end Tamil.Pronouns
