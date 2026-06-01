/-
# Tamil Pronoun & Allocutive Fragment

Personal pronouns and allocutive verbal morphology in Tamil (Dravidian).
Tamil has a two-level honorific system (non-hon / hon) realized as verbal
agreement suffixes. 1st person plural distinguishes inclusive (*naam*) vs
exclusive (*naangaL*). 3rd person distinguishes masculine (*avan*), feminine
(*avaL*), and honorific (*avar*). AA is Fin-based with limited embeddability
(under speech/thought predicates).

-/

import Linglib.Typology.Pronoun.Basic
import Linglib.Typology.Pronoun.WALS

namespace Tamil.Pronouns

open Pronoun

-- ============================================================================
-- First Person
-- ============================================================================

/-- *naan* — 1sg. -/
def naan : PersonalPronoun :=
  { form := "naan", person := some .first, number := some .sg }

/-- *naam* — 1pl inclusive (speaker + addressee). -/
def naam : PersonalPronoun :=
  { form := "naam", person := some .first, number := some .pl }

/-- *naangaL* — 1pl exclusive (speaker + others, not addressee). -/
def naangaL : PersonalPronoun :=
  { form := "naangaL", person := some .first, number := some .pl }

-- ============================================================================
-- Second Person (two-level honorific)
-- ============================================================================

/-- *nii* — 2sg non-honorific. -/
def nii : PersonalPronoun :=
  { form := "nii", person := some .second, number := some .sg, register := .informal }

/-- *niingaL* — 2sg honorific (also 2pl). -/
def niingaL : PersonalPronoun :=
  { form := "niingaL", person := some .second, number := some .sg, register := .formal }

-- ============================================================================
-- Third Person
-- ============================================================================

/-- *avan* — 3sg masculine. -/
def avan : PersonalPronoun :=
  { form := "avan", person := some .third, number := some .sg }

/-- *avaL* — 3sg feminine. -/
def avaL : PersonalPronoun :=
  { form := "avaL", person := some .third, number := some .sg }

/-- *avar* — 3sg honorific. -/
def avar : PersonalPronoun :=
  { form := "avar", person := some .third, number := some .sg, register := .formal }

/-- *avarkaL* — 3pl (human). -/
def avarkaL : PersonalPronoun :=
  { form := "avarkaL", person := some .third, number := some .pl }

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
    allPronouns.any (·.number == some .sg) = true ∧
    allPronouns.any (·.number == some .pl) = true := ⟨rfl, rfl⟩

/-- Tamil has inclusive/exclusive distinction in 1pl. -/
theorem has_incl_excl :
    (allPronouns.filter (fun p => p.person == some .first && p.number == some .pl)).length = 2 := rfl

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

namespace Tamil

/-- Tamil (Dravidian) pronoun typology profile, read off this fragment's
    lexical inventory rather than asserted from a WALS datapoint: full
    inclusive/exclusive 1pl (*naam* vs *naangaL*), a two-level honorific
    register split in 2nd person (*nii*/*niingaL*, a binary T/V-style
    distinction), and gender in the 3rd-person singular (*avan*/*avaL*).
    Fields not evidenced by the inventory are left unsurveyed (`.none`). -/
def pronounProfile : Pronoun.Profile :=
  { language := "Tamil"
  , family := "Dravidian"
  , iso := "tam"
  , inclusiveExclusive := some .inclusiveExclusive
  , politeness := some .binary
  , genderInPronouns := some .in3rdPersonSgOnly }

end Tamil
