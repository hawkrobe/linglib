/-
# Tamil Pronoun & Allocutive Fragment

Personal pronouns and allocutive verbal morphology in Tamil (Dravidian).
Tamil has a two-level honorific system (non-hon / hon) realized as verbal
agreement suffixes. 1st person plural distinguishes inclusive (*naam*) vs
exclusive (*naangaL*). 3rd person distinguishes masculine (*avan*), feminine
(*avaL*), and honorific (*avar*). AA is Fin-based with limited embeddability
(under speech/thought predicates).

## References

- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Pronouns

namespace Fragments.Tamil.Pronouns

open Core.Pronouns

-- ============================================================================
-- First Person
-- ============================================================================

/-- *naan* — 1sg. -/
def naan : PronounEntry :=
  { form := "naan", person := some .first, number := some .sg }

/-- *naam* — 1pl inclusive (speaker + addressee). -/
def naam : PronounEntry :=
  { form := "naam", person := some .first, number := some .pl }

/-- *naangaL* — 1pl exclusive (speaker + others, not addressee). -/
def naangaL : PronounEntry :=
  { form := "naangaL", person := some .first, number := some .pl }

-- ============================================================================
-- Second Person (two-level honorific)
-- ============================================================================

/-- *nii* — 2sg non-honorific. -/
def nii : PronounEntry :=
  { form := "nii", person := some .second, number := some .sg, register := .informal }

/-- *niingaL* — 2sg honorific (also 2pl). -/
def niingaL : PronounEntry :=
  { form := "niingaL", person := some .second, number := some .sg, register := .formal }

-- ============================================================================
-- Third Person
-- ============================================================================

/-- *avan* — 3sg masculine. -/
def avan : PronounEntry :=
  { form := "avan", person := some .third, number := some .sg }

/-- *avaL* — 3sg feminine. -/
def avaL : PronounEntry :=
  { form := "avaL", person := some .third, number := some .sg }

/-- *avar* — 3sg honorific. -/
def avar : PronounEntry :=
  { form := "avar", person := some .third, number := some .sg, register := .formal }

/-- *avarkaL* — 3pl (human). -/
def avarkaL : PronounEntry :=
  { form := "avarkaL", person := some .third, number := some .pl }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PronounEntry := [nii, niingaL]

def allPronouns : List PronounEntry :=
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

end Fragments.Tamil.Pronouns
