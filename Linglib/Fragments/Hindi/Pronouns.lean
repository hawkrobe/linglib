/-
# Hindi Pronoun Fragment

Personal pronouns of Hindi (Indo-Aryan): a three-level honorific system for
2nd person (non-hon *tuu* / hon *tum* / high-hon *aap*); 3rd person uses
distal demonstrative forms (*vah* sg / *ve* pl). Hindi has no allocutive
agreement; an honorific subject co-opts plural verb agreement
([alok-bhalla-2026] (48), after Bhatt & Davis 2023).

-/

import Linglib.Syntax.Category.Pronoun.Basic

namespace Hindi.Pronouns

open Pronoun

-- ============================================================================
-- First Person
-- ============================================================================

/-- *maiṃ* — 1sg. -/
def maiN : PersonalPronoun :=
  { form := "maiṃ", person := some .first, number := some .singular }

/-- *ham* — 1pl. -/
def ham : PersonalPronoun :=
  { form := "ham", person := some .first, number := some .plural }

-- ============================================================================
-- Second Person (three-level honorific)
-- ============================================================================

/-- *tuu* — 2sg non-honorific (intimate/inferior). -/
def tuu : PersonalPronoun :=
  { form := "tuu", person := some .second, number := some .singular, register := .informal }

/-- *tum* — 2sg honorific (neutral). -/
def tum : PersonalPronoun :=
  { form := "tum", person := some .second, number := some .singular, register := .neutral }

/-- *aap* — 2sg high-honorific (respectful). -/
def aap : PersonalPronoun :=
  { form := "aap", person := some .second, number := some .singular, register := .formal }

-- ============================================================================
-- Third Person (demonstrative-based)
-- ============================================================================

/-- *vah* — 3sg (distal demonstrative, standard pronoun). -/
def vah : PersonalPronoun :=
  { form := "vah", person := some .third, number := some .singular }

/-- *ve* — 3pl (distal demonstrative plural). -/
def ve : PersonalPronoun :=
  { form := "ve", person := some .third, number := some .plural }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PersonalPronoun := [tuu, tum, aap]

def allPronouns : List PersonalPronoun :=
  [maiN, ham] ++ secondPersonPronouns ++ [vah, ve]

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

/-- Three-level register distinction in 2nd person. -/
theorem three_levels :
    secondPersonPronouns.map (·.register) = [.informal, .neutral, .formal] := rfl


end Hindi.Pronouns
