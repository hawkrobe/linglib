/-
# Korean Pronoun & Allocutive Fragment

Personal pronouns and allocutive particles in Korean. Korean has
particle-based allocutive marking (*-yo* polite, *-(su)pnida* formal)
hosted in the SAP layer, restricted to root clauses. 1st person has a
plain/humble distinction (*na* / *jeo*). 3rd person pronouns (*geu*, *geunyeo*)
are relatively recent Sino-Korean innovations; traditional Korean relies
on null reference and demonstratives.

## References

- Portner, P., M. Pak & R. Zanuttini (2019). The speaker-addressee relation at
  the syntax-semantics interface.
- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Pronouns

namespace Fragments.Korean.Pronouns

open Core.Pronouns

-- ============================================================================
-- First Person
-- ============================================================================

/-- 나 *na* — 1sg plain. -/
def na : PronounEntry :=
  { form := "na", script := some "나", person := some .first, number := some .sg, formality := 0 }

/-- 저 *jeo* — 1sg humble. -/
def jeo : PronounEntry :=
  { form := "jeo", script := some "저", person := some .first, number := some .sg, formality := 1 }

/-- 우리 *uri* — 1pl. -/
def uri : PronounEntry :=
  { form := "uri", script := some "우리", person := some .first, number := some .pl }

-- ============================================================================
-- Second Person (T/V)
-- ============================================================================

/-- 너 *neo* — 2sg plain. -/
def neo : PronounEntry :=
  { form := "neo", script := some "너", person := some .second, number := some .sg, formality := 0 }

/-- 당신 *dangsin* — 2sg polite. -/
def dangsin : PronounEntry :=
  { form := "dangsin", script := some "당신", person := some .second, number := some .sg, formality := 1 }

-- ============================================================================
-- Third Person
-- ============================================================================

/-- 그 *geu* — 3sg masculine. -/
def geu : PronounEntry :=
  { form := "geu", script := some "그", person := some .third, number := some .sg }

/-- 그녀 *geunyeo* — 3sg feminine. -/
def geunyeo : PronounEntry :=
  { form := "geunyeo", script := some "그녀", person := some .third, number := some .sg }

/-- 그들 *geudeul* — 3pl. -/
def geudeul : PronounEntry :=
  { form := "geudeul", script := some "그들", person := some .third, number := some .pl }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PronounEntry := [neo, dangsin]

def allPronouns : List PronounEntry :=
  [na, jeo, uri] ++ secondPersonPronouns ++ [geu, geunyeo, geudeul]

-- ============================================================================
-- Allocutive Particles (SAP-layer)
-- ============================================================================

/-- *-yo* polite particle (Portner, Pak & Zanuttini 2019). -/
def yo : AllocutiveEntry :=
  { form := "-yo", formality := 1, gloss := "POL" }

/-- *-(su)pnida* formal particle. -/
def supnida : AllocutiveEntry :=
  { form := "-(su)pnida", formality := 2, gloss := "FORM" }

def allAllocParticles : List AllocutiveEntry := [yo, supnida]

-- ============================================================================
-- Verb Agreement Examples
-- ============================================================================

/-- A verb form showing speech-level inflection. -/
structure VerbForm where
  form : String
  gloss : String
  formality : Nat
  deriving Repr, BEq

/-- 가 *ga* — "go" (plain/intimate). -/
def ga : VerbForm := { form := "ga", gloss := "go.PLN", formality := 0 }

/-- 가요 *gayo* — "go" (polite). -/
def gayo : VerbForm := { form := "gayo", gloss := "go.POL", formality := 1 }

/-- 갑니다 *gamnida* — "go" (formal). -/
def gamnida : VerbForm := { form := "gamnida", gloss := "go.FORM", formality := 2 }

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

/-- 1st person has plain/humble formality distinction. -/
theorem first_person_humble :
    na.formality = 0 ∧ jeo.formality = 1 := ⟨rfl, rfl⟩

/-- 2nd person pronouns are all second person. -/
theorem second_person_all_2p :
    secondPersonPronouns.all (·.person == some .second) = true := rfl

/-- The T/V formality distinction is present in 2nd person. -/
theorem tv_distinction :
    secondPersonPronouns.any (·.formality == 0) = true ∧
    secondPersonPronouns.any (·.formality == 1) = true := ⟨rfl, rfl⟩

/-- Verb forms span all three speech levels. -/
theorem verb_three_levels :
    ga.formality = 0 ∧ gayo.formality = 1 ∧ gamnida.formality = 2 := ⟨rfl, rfl, rfl⟩

end Fragments.Korean.Pronouns
